module

public import CFSG.LocalAnalysis.StandardType.FF81.PropTwoDict
import CFSG.RankThree.PartTwo.Sec21.FF81P51Pat

@[expose] public section

namespace CFSG.StandardType.FF81

open CFSG.RankThree.PartTwo.Sec21.FF81.P51 (V GL4 cfgOf mA mB e_mem_Om mem_Om_of_mA
  mem_Om_of_mB)

private theorem zpowers_pow_val {G : Type} [Group G] {a : G} (ha : a ^ 3 = 1) {c : ZMod 3}
    (hc : c ≠ 0) : Subgroup.zpowers (a ^ c.val) = Subgroup.zpowers a := by
  have hc' : c = 1 ∨ c = 2 := by revert c; decide
  rcases hc' with rfl | rfl
  · rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
  · have : a ^ (2 : ZMod 3).val = a⁻¹ := by
      show a ^ 2 = a⁻¹
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, ha]
    rw [this, Subgroup.zpowers_inv]

theorem conjLinesOfB_of_mA {G : Type} [Group G] [Finite G]
    {K : Subgroup G} {b : G} {z : Fin 3 → K} {Γ : Subgroup GL4} {cv : G → V}
    (h : GGFF.SettingCore b K z) (hM : BCoordModel b z Γ cv) (hA : (cfgOf Γ).1 = mA) :
    ConjLinesOfB b z (coordLines b z) := by
  intro Z hZ _
  constructor
  · rintro ⟨g, rfl⟩
    have hy : g * b * g⁻¹ ∈ GGFF.Bt b z := hZ (Subgroup.mem_zpowers _)
    obtain ⟨i, c, hc, hcv⟩ := (mem_Om_of_mA hM.hyp hA _).1 ((hM.conj_iff_mem_Om h hy).1 ⟨g, rfl⟩)
    refine ⟨i, ?_⟩
    have hyi : g * b * g⁻¹ = xs b z i ^ c.val := by
      refine hM.inj _ hy _ ((GGFF.Bt b z).pow_mem (xs_mem_Bt b z i) _) ?_
      rw [hcv, hM.cv_xs_pow, ZMod.natCast_zmod_val]
    rw [hyi, zpowers_pow_val (hM.xs_pow_three i) hc]
  · rintro ⟨i, rfl⟩
    obtain ⟨g, hg⟩ := (hM.conj_iff_mem_Om h (xs_mem_Bt b z i)).2
      (by rw [hM.basis i]; exact e_mem_Om hM.hyp hA i)
    exact ⟨g, by rw [hg]⟩

theorem conjLinesOfB_of_mB {G : Type} [Group G] [Finite G]
    {K : Subgroup G} {b : G} {z : Fin 3 → K} {Γ : Subgroup GL4} {cv : G → V}
    (h : GGFF.SettingCore b K z) (hM : BCoordModel b z Γ cv) (hB : (cfgOf Γ).1 = mB) :
    ConjLinesOfB b z (coordLines b z ∪ weightFourLines b z) := by
  intro Z hZ _
  constructor
  · rintro ⟨g, rfl⟩
    have hy : g * b * g⁻¹ ∈ GGFF.Bt b z := hZ (Subgroup.mem_zpowers _)
    rcases (mem_Om_of_mB hM.hyp hB _).1 ((hM.conj_iff_mem_Om h hy).1 ⟨g, rfl⟩) with
      ⟨i, c, hc, hcv⟩ | hall
    · refine Or.inl ⟨i, ?_⟩
      have hyi : g * b * g⁻¹ = xs b z i ^ c.val := by
        refine hM.inj _ hy _ ((GGFF.Bt b z).pow_mem (xs_mem_Bt b z i) _) ?_
        rw [hcv, hM.cv_xs_pow, ZMod.natCast_zmod_val]
      rw [hyi, zpowers_pow_val (hM.xs_pow_three i) hc]
    · refine Or.inr ⟨cv (g * b * g⁻¹) 0, fun j => cv (g * b * g⁻¹) j.succ, hall 0,
        fun j => hall j.succ, ?_⟩
      congr 1
      refine hM.inj _ hy _ (four_mem_Bt b z _ _) ?_
      rw [hM.cv_four]
      ext j
      fin_cases j <;> rfl
  · rintro (⟨i, rfl⟩ | ⟨ε, v, hε, hv, rfl⟩)
    · obtain ⟨g, hg⟩ := (hM.conj_iff_mem_Om h (xs_mem_Bt b z i)).2 (by
        rw [hM.basis i, mem_Om_of_mB hM.hyp hB]
        exact Or.inl ⟨i, 1, one_ne_zero, by rw [one_smul]⟩)
      exact ⟨g, by rw [hg]⟩
    · obtain ⟨g, hg⟩ := (hM.conj_iff_mem_Om h (four_mem_Bt b z ε.val v)).2 (by
        rw [hM.cv_four, mem_Om_of_mB hM.hyp hB]
        refine Or.inr fun j => ?_
        fin_cases j
        · exact hε
        · exact hv 0
        · exact hv 1
        · exact hv 2)
      exact ⟨g, by rw [hg]⟩

end CFSG.StandardType.FF81

end
