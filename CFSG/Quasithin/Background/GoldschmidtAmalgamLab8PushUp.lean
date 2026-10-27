module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Slide

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D}

theorem pushUp_of_not_normal (h : GoldHyp A B)
    (hA : ¬ A ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D))
    (hB : ¬ B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D)) :
    PushUp A B := by
  intro x y hxy
  cases hx : vtype x with
  | false =>
    obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hxy hx
    rw [stab_smul, ballStab_smul, ballStab_smul, ← conjSub_inf,
      stab_γ₀ (le_sup_left : A ≤ A ⊔ B), ballStab_one_γ₀_eq_pCoreOf h,
      ballStab_one_γ₁_eq_pCoreOf h]
    intro hle
    apply hA
    rw [conjSub_normalizer, conjSub_le_iff, conjSub_conjSub_inv] at hle
    exact hle
  | true =>
    have hy : vtype y = false := vtype_eq_false_of_adj hxy hx
    obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hxy.symm hy
    rw [stab_smul, ballStab_smul, ballStab_smul, ← conjSub_inf,
      stab_γ₁ (le_sup_right : B ≤ A ⊔ B), ballStab_one_γ₁_eq_pCoreOf h,
      ballStab_one_γ₀_eq_pCoreOf h, inf_comm]
    intro hle
    apply hB
    rw [conjSub_normalizer, conjSub_le_iff, conjSub_conjSub_inv] at hle
    exact hle

end GoldAmLab8

end F6

end CFSG.Quasithin
