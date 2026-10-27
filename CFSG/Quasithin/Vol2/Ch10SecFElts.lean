module

public import CFSG.Quasithin.Vol2.Ch10SecFS5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv

theorem a0_orderOf : orderOf CFSG.QuasithinUnique.A5.Delta5.a0 = 5 :=
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  orderOf_eq_prime (by decide) (by decide)

theorem cThree_orderOf : orderOf SecE.cThree = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime (by decide) (by decide)

theorem cThree_fix_four : SecE.cThree 4 = 4 := by decide

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_pow_orderOf_eq {H K : Type*} [Group H] [Group K] [Finite H] (φ : H →* K) (y : H)
    {p : ℕ} (hy : orderOf (φ y) = p) : orderOf (y ^ (orderOf y / p)) = p := by
  have hdvd : p ∣ orderOf y := hy ▸ orderOf_map_dvd φ y
  exact orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd

theorem exists_orderOf_eq_five (h2 : Ch10.Case10_1_1Two T L I) :
    ∃ x ∈ L, orderOf x = 5 := by
  obtain ⟨e⟩ := h2.1
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm CFSG.QuasithinUnique.A5.Delta5.a0')
  have h5 : orderOf ((e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) y) = 5 := by
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
    rw [hy, MulEquiv.apply_symm_apply, Subgroup.orderOf_mk]
    exact a0_orderOf
  refine ⟨((y ^ (orderOf y / 5) : ↥L) : G), (y ^ (orderOf y / 5)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact exists_pow_orderOf_eq _ y h5

section Data

variable {hyp : Hyp10 G T L I} {t : G} (D : SecE.Case2Data hyp t)

theorem exists_orderOf_eq_three_fix_vOne :
    ∃ z ∈ L, orderOf z = 3 ∧ z ∈ Subgroup.centralizer ({vOne D} : Set G) := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hgo : orderOf (D.θ₁.symm SecE.cThree).1 = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, cThree_orderOf]
  have hgO : (D.θ₁.symm SecE.cThree).1 ∈ oTwoUpper D.K₁ :=
    Subgroup.subset_closure ⟨(D.θ₁.symm SecE.cThree).2, by rw [hgo]; decide⟩
  rw [D.oTwo₁] at hgO
  obtain ⟨gg, hggL, hgg⟩ := (mem_autI _).mp hgO
  have hfix : convI hV gg (vOneW D).1 = (vOneW D).1 := by
    rw [hgg]
    refine fix_vOneW_of_mem_K₁ D (D.θ₁.symm SecE.cThree).2 ?_
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact cThree_fix_four
  have hc := conj_vOne_of_fix D gg hfix
  have hgC : (gg : G) ∈ Subgroup.centralizer ({vOne D} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    calc vOne D * gg = ((gg : G) * vOne D * (gg : G)⁻¹) * gg := by rw [hc]
      _ = gg * vOne D := by group
  have h3 : orderOf (convI hV gg) = 3 := by rw [hgg]; exact hgo
  refine ⟨((gg ^ (orderOf gg / 3) : Subgroup.normalizer (fsuVM T L I : Set G)) : G), ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact L.pow_mem hggL _
  · rw [Subgroup.orderOf_coe]
    exact exists_pow_orderOf_eq (convI hV) gg h3
  · rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hgC _

theorem exists_orderOf_eq_three_conjugate (h113 : ASInputs.AS_C_1_13)
    (h37 : Vol2Native.A37ForSQTKCat) (h2 : Ch10.Case10_1_1Two T L I)
    (hb : IsShort2 L ∧ IsAltType L 5) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ∃ z ∈ CFSG.conjugate L t, orderOf z = 3 ∧ z ∈ Subgroup.centralizer (L : Set G) ∧
      z ∈ Subgroup.centralizer ({t⁻¹ * vOne D * t} : Set G) := by
  obtain ⟨z₀, hz₀L, hz₀o, hz₀C⟩ := exists_orderOf_eq_three_fix_vOne D
  have hcomm := commutator_conjugate_eq_bot h113 h37 hyp h2 hb ht htn
  have hLC : L ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hzt : t⁻¹ * z₀ * t ∈ CFSG.conjugate L t := by
    rw [mem_conjugate_iff']
    simpa [mul_assoc] using hz₀L
  refine ⟨t⁻¹ * z₀ * t, hzt, ?_, ?_, ?_⟩
  · rw [← hz₀o]
    exact (SemiconjBy.orderOf_eq t⁻¹ (show t⁻¹ * z₀ = (t⁻¹ * z₀ * t) * t⁻¹ by group)).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hLC hl) _ hzt).symm
  · have h1 := Subgroup.mem_centralizer_iff.mp hz₀C (vOne D) rfl
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    calc t⁻¹ * vOne D * t * (t⁻¹ * z₀ * t) = t⁻¹ * (vOne D * z₀) * t := by group
      _ = t⁻¹ * (z₀ * vOne D) * t := by rw [h1]
      _ = t⁻¹ * z₀ * t * (t⁻¹ * vOne D * t) := by group

end Data

end CFSG.Quasithin.Vol2.Ch10.SecF
