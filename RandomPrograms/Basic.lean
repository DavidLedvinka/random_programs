import Mathlib

open ENNReal MeasureTheory Measure

class RandomBool (m : Type → Type) : Type where
  randomBool : m Bool

instance : RandomBool IO where
  randomBool := IO.rand 0 1

def Distr (α : Type) : Type := α → ℝ≥0∞

-- assume all types are finite so I can sum over `α`
axiom finite_types (α : Type) : Fintype α

noncomputable instance {α : Type} : Fintype α := finite_types _

noncomputable instance : Monad Distr where
  pure x := fun y => open Classical in if x = y then 1 else 0
  bind {α _} μ f := open Classical in fun y ↦ ∑ x : α, μ x * f x y

noncomputable instance : RandomBool Distr where
  randomBool
  | true => 1 / 2
  | false => 1 / 2

def random_Bool {m} [Monad m] [RandomBool m] : m Bool := do
  return ← RandomBool.randomBool

#eval random_Bool (m := IO) -- returns a random Bool

def random_notBool {m} [Monad m] [RandomBool m] : m Bool := do
  return not (← RandomBool.randomBool)

#eval random_notBool (m := IO) -- returns a random not Bool

/- prove that under the assumption of uniformly distributed Booleans,
random_Bool has the same distribution as random_notBool -/
example : random_Bool (m := Distr) = random_notBool (m := Distr) := by
  simp [Distr, random_Bool, random_notBool, RandomBool.randomBool,
    Bind.bind, Pure.pure]
  ext x
  cases x <;> simp
