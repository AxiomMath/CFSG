module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.SzC4

@[expose] def IsExpTwo (A : Type) [Group A] : Prop := ∀ x : A, x * x = 1

structure DeltaAPI : Type 1 where
  delta : (A : Type) → [Group A] → [Finite A] → MulAut A → ℤ
  delta_congr : ∀ {A A' : Type} [Group A] [Group A'] [Finite A] [Finite A'], IsExpTwo A →
    ∀ (e : A ≃* A') (φ : MulAut A) (φ' : MulAut A'), (∀ x : A, e (φ x) = φ' (e x)) →
      delta A' φ' = delta A φ
  delta_one : ∀ (A : Type) [Group A] [Finite A], IsExpTwo A → delta A 1 = 0
  delta_exact : ∀ {A M B : Type} [Group A] [Group M] [Group B] [Finite A] [Finite M] [Finite B],
    IsExpTwo M → ∀ (ι : A →* M) (π : M →* B), Function.Injective ι → Function.Surjective π →
      ι.range = π.ker → ∀ (φA : MulAut A) (φM : MulAut M) (φB : MulAut B), φM ^ 7 = 1 →
        (∀ a : A, φM (ι a) = ι (φA a)) → (∀ m : M, π (φM m) = φB (π m)) →
          delta M φM = delta A φA + delta B φB

end CFSG.Quasithin.SzC4
