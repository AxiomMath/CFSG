module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Dual
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab9Empty
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Red
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8PushUp
public import CFSG.Quasithin.Background.GoldschmidtAmalgamVBHyp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7 CFSG.Quasithin.F6.GoldAmL3

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

@[expose] def NotNormalBTwoSys (D : Type*) [Group D] [Finite D] : Prop :=
  ∀ (A B : Subgroup D) (z : D) (V : Subgroup D) (c : D) (V₂ : Subgroup D),
    TwoSys A B z V c V₂ → GoldHyp3 A B z V → 5 ≤ critDist (A ⊔ B) A B V →
      ¬ B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D)

theorem pushUp_one_of_not_normal (h : GoldHyp A B)
    (hB : ¬ B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D)) :
    ∀ x y : CosetGeom (A ⊔ B) A B, vtype x = true → (graph (A ⊔ B) A B).Adj x y →
      ¬ stab x ≤ Subgroup.normalizer ((ballStab 1 x ⊓ ballStab 1 y : Subgroup D) : Set D) := by
  intro x y hx hxy
  have hy : vtype y = false := vtype_eq_false_of_adj hxy hx
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hxy.symm hy
  rw [stab_smul, ballStab_smul, ballStab_smul, ← conjSub_inf,
    stab_γ₁ (le_sup_right : B ≤ A ⊔ B), ballStab_one_γ₁_eq_pCoreOf h,
    ballStab_one_γ₀_eq_pCoreOf h, inf_comm]
  intro hle
  apply hB
  rw [conjSub_normalizer, conjSub_le_iff, conjSub_conjSub_inv] at hle
  exact hle

omit [Finite D] in
theorem twoSys_swap (h : TwoSys A B z V c V₂) : TwoSys B A c V₂ z V where
  gold := h.gold.symm
  card_ge := by rw [inf_comm]; exact h.card_ge
  nat := by rw [inf_comm]; exact h.nat₂
  nat₂ := by rw [inf_comm]; exact h.nat
  V_le := h.V₂_le
  V₂_le := h.V_le

theorem not_le_normalizer_left_of_doubled (hP : NotNormalBTwoSys D)
    (d : Doubled A B z V c V₂) (h3 : GoldHyp3 A B z V) (hb : 5 ≤ critDist (A ⊔ B) A B V) :
    ¬ A ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D) := by
  have h := hP B A c V₂ z V (twoSys_swap d.sys) (goldHyp3_swap d h3 (by omega))
    (five_le_critDist_swap d h3 hb)
  rwa [inf_comm] at h

theorem noACentral_of_notNormalBTwoSys (hP : NotNormalBTwoSys D) (h3 : GoldHyp3 A B z V)
    (hb : 5 ≤ critDist (A ⊔ B) A B V) : NoACentral A B := by
  intro ω hωZ hω2 hωA
  by_contra hne
  by_cases hBω : ∀ y ∈ B, y * ω * y⁻¹ = ω
  · exact hne (h3.gold.eq_one_of_commute_both hωZ.1 (fun g hg => mul_eq_of_conj_eq (hωA g hg))
      (fun g hg => mul_eq_of_conj_eq (hBω g hg)))
  · push Not at hBω
    obtain ⟨y, hyB, hy⟩ := hBω
    obtain ⟨x, c, V₂, -, -, -, -, hn₂, -⟩ :=
      exists_natural_data h3.gold.vertex_right hωZ hω2 ⟨y, hyB, hy⟩
    have h64 := h3.sixty_four_le_card_inf
    have h : TwoSys A B z V c V₂ := TwoSys.of_goldHyp3 h3 (by omega) hn₂
    have hBn := hP A B z V c V₂ h h3 hb
    by_cases hcA : ∀ a ∈ A, a * c * a⁻¹ = c
    · have d : Doubled A B z V c V₂ := ⟨h, h3.central, hcA⟩
      exact false_of_doubled d h3 hb
        (pushUp_of_not_normal h3.gold (not_le_normalizer_left_of_doubled hP d h3 hb) hBn)
    · push Not at hcA
      exact GoldAmLab9.aMovedEmpty_of_pushUp h3 hb (pushUp_one_of_not_normal h3.gold hBn) c V₂
        hn₂ hcA

end GoldAmLab8

end F6

end CFSG.Quasithin
