module

public import Mathlib.Algebra.Group.End
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.Quasithin.SzC4.ChiMod

@[expose] def Kp {A : Type} [Group A] (φ : MulAut A) : Set A :=
  {x | φ (φ (φ x)) * φ (φ x) * x = 1}

@[expose] def Kt {A : Type} [Group A] (φ : MulAut A) : Set A :=
  {x | φ (φ (φ x)) * φ x * x = 1}

@[expose] noncomputable def delta (A : Type) [Group A] (φ : MulAut A) : ℤ :=
  (padicValNat 2 (Nat.card (Kp φ)) : ℤ) - padicValNat 2 (Nat.card (Kt φ))

theorem mem_Kp_congr {A A' : Type} [Group A] [Group A'] (e : A ≃* A') (φ : MulAut A)
    (φ' : MulAut A') (h : ∀ x : A, e (φ x) = φ' (e x)) (x : A) : e x ∈ Kp φ' ↔ x ∈ Kp φ := by
  simp only [Kp, Set.mem_ofPred_eq, ← h]
  rw [← map_mul, ← map_mul, map_eq_one_iff e e.injective]

theorem mem_Kt_congr {A A' : Type} [Group A] [Group A'] (e : A ≃* A') (φ : MulAut A)
    (φ' : MulAut A') (h : ∀ x : A, e (φ x) = φ' (e x)) (x : A) : e x ∈ Kt φ' ↔ x ∈ Kt φ := by
  simp only [Kt, Set.mem_ofPred_eq, ← h]
  rw [← map_mul, ← map_mul, map_eq_one_iff e e.injective]

theorem card_Kp_congr {A A' : Type} [Group A] [Group A'] (e : A ≃* A') (φ : MulAut A)
    (φ' : MulAut A') (h : ∀ x : A, e (φ x) = φ' (e x)) : Nat.card (Kp φ') = Nat.card (Kp φ) :=
  (Nat.card_congr (e.toEquiv.subtypeEquiv (p := (· ∈ Kp φ)) (q := (· ∈ Kp φ'))
    fun x => (mem_Kp_congr e φ φ' h x).symm)).symm

theorem card_Kt_congr {A A' : Type} [Group A] [Group A'] (e : A ≃* A') (φ : MulAut A)
    (φ' : MulAut A') (h : ∀ x : A, e (φ x) = φ' (e x)) : Nat.card (Kt φ') = Nat.card (Kt φ) :=
  (Nat.card_congr (e.toEquiv.subtypeEquiv (p := (· ∈ Kt φ)) (q := (· ∈ Kt φ'))
    fun x => (mem_Kt_congr e φ φ' h x).symm)).symm

theorem delta_congr {A A' : Type} [Group A] [Group A'] (e : A ≃* A') (φ : MulAut A)
    (φ' : MulAut A') (h : ∀ x : A, e (φ x) = φ' (e x)) : delta A' φ' = delta A φ := by
  rw [delta, delta, card_Kp_congr e φ φ' h, card_Kt_congr e φ φ' h]

theorem delta_one (A : Type) [Group A] : delta A 1 = 0 := by
  have : Kp (1 : MulAut A) = Kt (1 : MulAut A) := by
    ext x
    simp [Kp, Kt]
  rw [delta, this, sub_self]

end CFSG.Quasithin.SzC4.ChiMod
