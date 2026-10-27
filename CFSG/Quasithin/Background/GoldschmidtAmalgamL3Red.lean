module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Sz

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

@[expose] def B3CardInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → Nat.card (conjClosure V B) = 8

@[expose] def B3KernelBoundInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) ≤ 16

@[expose] def B3IntersectionInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → ∃ y ∈ A, coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B ⊓
      conjSub y (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) ≤ V

theorem b3KernelBoundInput_of_intersection (hc : B3CardInput.{u})
    (hi : B3IntersectionInput.{u}) : B3KernelBoundInput.{u} := by
  intro D _ _ A B z V h
  obtain ⟨y, hy, hN⟩ := hi D A B z V h
  have h1 := h.card_coreIn_le_four_mul_inf_conjSub (hc D A B z V h) hy
  have h2 := Subgroup.card_le_of_le hN
  rw [h.natural.card_eq] at h2
  omega

theorem b3_critDist_card_of_inputs (hc : B3CardInput.{u}) (hk : B3KernelBoundInput.{u})
    {D : Type u} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}
    (h : GoldHyp3 A B z V) :
    critDist (A ⊔ B) A B V = 3 ∧ (Nat.card ↥(A ⊓ B) = 64 ∨ Nat.card ↥(A ⊓ B) = 128) :=
  h.critDist_eq_three_and_card_inf_eq_of_card_coreIn_le (hc D A B z V h) (hk D A B z V h)

end GoldAmL3

end F6

end CFSG.Quasithin
