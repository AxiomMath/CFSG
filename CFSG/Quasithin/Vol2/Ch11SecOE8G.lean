module

public import CFSG.Quasithin.Vol2.Ch11SecOE8F
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Quasithin.Vol2.Ch11SecOE8E

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3

open Matrix CFSG.CGT.Timmesfeld75 CFSG.LinearGroups CFSG.Quasithin
open scoped MatrixGroups Pointwise LinearAlgebra.Projectivization

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem mem_normalizer_of_smul_eq {h : ProjectiveSpecialLinearGroup (Fin 3) F}
    (hh : h • ppt F 0 = ppt F 0) :
    h ∈ Subgroup.normalizer ((projectiveElationSubgroup (pt F 0) : Subgroup _) : Set _) := by
  have hst := (linear_projective_elation_data (n := 3) (finrank_pt (F := F) 0)).2.2.1
  have hh' : h ∈ MulAction.stabilizer (ProjectiveSpecialLinearGroup (Fin 3) F) (ppt F 0) := hh
  have hhi : h⁻¹ ∈ MulAction.stabilizer (ProjectiveSpecialLinearGroup (Fin 3) F) (ppt F 0) :=
    inv_mem hh'
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => hst h hh' a ha, fun ha => ?_⟩
  have := hst h⁻¹ hhi _ ha
  simpa [mul_assoc] using this

omit [Finite F] [CharP F 2] in
theorem ppt_zero_ne_one : ppt F 0 ≠ ppt F 1 := by
  intro h
  have h1 := congrArg Projectivization.submodule h
  rw [Projectivization.submodule_mk'', Projectivization.submodule_mk''] at h1
  have hmem : (Pi.single 1 1 : Fin 3 → F) ∈ pt F 0 := h1 ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have := congrFun hc 1
  simp at this

theorem overgroup_elation (hF4 : 4 ≤ Nat.card F) {R : Subgroup (ProjectiveSpecialLinearGroup
    (Fin 3) F)} (hVR : projectiveElationSubgroup (pt F 0) ≤ R) :
    R ≤ Subgroup.normalizer ((projectiveElationSubgroup (pt F 0) : Subgroup _) : Set _) ∨
      (¬ Group.IsSolvable ↥R ∧
        Nat.card F ≤ (projectiveElationSubgroup (pt F 0) ⊓ solvRad R).relIndex
          (projectiveElationSubgroup (pt F 0))) := by
  set V₀ := projectiveElationSubgroup (pt F 0) with hV₀
  by_cases hfix : ∀ r ∈ R, r • ppt F 0 = ppt F 0
  · exact Or.inl fun r hr => mem_normalizer_of_smul_eq (hfix r hr)
  right
  push Not at hfix
  obtain ⟨r, hrR, hr⟩ := hfix
  have h2 := (linear_projective_action (n := 3) (K := F) (by norm_num)).2.2.2.2.2.1
  obtain ⟨h, hh0, hh1⟩ := (MulAction.is_two_pretransitive_iff.mp h2) (Ne.symm hr)
    (ppt_zero_ne_one (F := F))
  set β : MulAut (ProjectiveSpecialLinearGroup (Fin 3) F) := MulAut.conj h with hβ
  have hhN := mem_normalizer_of_smul_eq hh0
  have hVβ : V₀.map β.toMonoidHom = V₀ := A1b.conjSub_eq_iff_mem_normalizer.mpr hhN
  set R'' := R.map β.toMonoidHom with hR''
  have hV₀R : V₀ ≤ R'' := hVβ ▸ Subgroup.map_mono hVR
  set r' := h * r * h⁻¹ with hr'
  have hr'R : r' ∈ R'' := ⟨r, hrR, rfl⟩
  have hhinv : h⁻¹ • ppt F 0 = ppt F 0 := by rw [inv_smul_eq_iff, hh0]
  have hr'p : r' • ppt F 0 = ppt F 1 := by rw [hr', mul_smul, mul_smul, hhinv, hh1]
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3, F)) r'
  have hgp : piP F g • ppt F 0 = ppt F 1 := by rw [hg, hr'p]
  have hV₁ : projectiveElationSubgroup (pt F 1) = A1b.conjSub r' V₀ := by
    rw [← hg, hV₀, conjSub_projectiveElation, smul_eq_of_smul_ppt hgp]
  have hV₁R : projectiveElationSubgroup (pt F 1) ≤ R'' := by
    rw [hV₁, ← A1b.conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hr'R)]
    exact A1b.conjSub_mono r' hV₀R
  have hle := sup_le hV₀R hV₁R
  refine ⟨fun hs => not_isSolvable_of_le hF4 hle ((isSolvable_map_equiv_iff β R).mpr hs), ?_⟩
  have hc : Nat.card F ≤ (V₀ ⊓ solvRad R'').relIndex V₀ := card_le_relIndex_solvRad hF4 hle
  have h3 := relIndex_solvRad_map β V₀ R
  rw [hVβ] at h3
  rw [hR'', h3] at hc
  exact hc

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3
