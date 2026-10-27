module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Assembly.LowTwoRank

theorem center_specialLinearGroup_three_eq_bot_of_card_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hA⟩ := hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hr
    exact zero_ne_one hr
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 5 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h4 : r ^ 4 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [hcard] at this
  have hr1 : r = 1 := by
    calc r = r * r ^ 3 := by rw [hr, mul_one]
      _ = r ^ 4 := by ring
      _ = 1 := h4
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [← hA, hr1]; simp)

theorem center_eq_bot_of_sl3 {p : ℕ} [Fact p.Prime] (hp : p = 5) {X : Type} [Group X]
    (h : Nonempty (X ≃* ↥(StatedSL 3 (ZMod p)))) : Subgroup.center X = ⊥ := by
  subst hp
  obtain ⟨e⟩ := h
  have hZ := center_specialLinearGroup_three_eq_bot_of_card_five (K := ZMod 5)
    (Nat.card_zmod 5)
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 5) :=
    e.trans (specialLinearGroupEquivStatedSL 3 (ZMod 5)).symm
  rw [eq_bot_iff]
  intro x hx
  have hx' : e' x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 5)) :=
    (MulEquivClass.apply_mem_center_iff e').2 hx
  rw [hZ, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  exact e'.injective (hx'.trans (map_one e').symm)

end CFSG.Quasithin.S146zX
