module

public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

theorem actualInternalExclusion_of_raw (R : RawFrameData) (hraw : RawNoInternalTwoNode R)
    (hdict : LiteralDictionaryInput R) : ActualInternalExclusion R := by
  intro G _ _ H E D J K y hframe hDE hD9 hyD hord hK hJ hJK hC1 hI1 hrow
  obtain ⟨real⟩ := hframe
  intro hyK
  have hyE : y ∈ E := hDE hyD
  let v : R.V := real.coord (Additive.ofMul (⟨y, hyE⟩ : ↥E))
  have hy_ne : y ≠ 1 := by
    intro h
    rw [h] at hord
    simp at hord
  have hv0 : v ≠ 0 := by
    intro hv
    have hvv : real.coord (Additive.ofMul (⟨y, hyE⟩ : ↥E)) = 0 := by
      change v = 0
      exact hv
    have h0 : Additive.ofMul (⟨y, hyE⟩ : ↥E) = 0 := by
      apply real.coord.injective
      simpa using hvv
    have h1 : (⟨y, hyE⟩ : ↥E) = 1 := by
      have := congrArg Additive.toMul h0
      simpa using this
    exact hy_ne (Subtype.ext_iff.mp h1)
  let U : Submodule (ZMod 3) R.V := ggLinImage (p := 3) real.coord D
  have hzy : Subgroup.zpowers y ≤ E := Subgroup.zpowers_le.mpr hyE
  have hcent_zpow : Subgroup.centralizer (Subgroup.zpowers y : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨c, hc, hocc_c, hKc⟩ :=
    (real.occurs_iff (Subgroup.zpowers y) hzy K).mp (by simpa [hcent_zpow] using hK)
  obtain ⟨j, hj, hocc_j, hJc⟩ := (real.occurs_iff D hDE J).mp hJ
  have hgg : ∀ {P Q : Subgroup G}, E ⊓ P = E ⊓ Q →
      ggLinImage (p := 3) real.coord P = ggLinImage (p := 3) real.coord Q := by
    intro P Q hPQ
    ext w
    rw [mem_ggLinImage, mem_ggLinImage]
    have key : ∀ (P : Subgroup G),
        ((Additive.toMul (real.coord.symm w) : ↥E) : G) ∈ P ↔
        ((Additive.toMul (real.coord.symm w) : ↥E) : G) ∈ E ⊓ P := by
      intro P
      rw [Subgroup.mem_inf]
      exact ⟨fun h => ⟨(Additive.toMul (real.coord.symm w)).2, h⟩, fun h => h.2⟩
    rw [key P, key Q, hPQ]
  have hspan : ggLinImage (p := 3) real.coord (Subgroup.zpowers y) =
      Submodule.span (ZMod 3) {v} := by
    simpa [v] using (span_singleton_eq_ggLinImage (p := 3) real.coord hyE).symm
  have hcent_c : R.cent c = Submodule.span (ZMod 3) {v} := by
    rw [← real.cent_eq c hc]
    rw [← hKc]
    rw [hgg (P := Subgroup.centralizer (K : Set G)) (Q := Subgroup.zpowers y)
      (hC1.trans (inf_eq_right.mpr hzy).symm)]
    exact hspan
  have hUcard : Nat.card U = 9 := by
    change Nat.card (ggLinImage (p := 3) real.coord D) = 9
    rw [card_ggLinImage (p := 3) real.coord D, inf_eq_right.mpr hDE]
    exact hD9
  have hdim : finrank (ZMod 3) U = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := U)
    rw [hUcard, Nat.card_eq_fintype_card, ZMod.card] at h
    have h2 : (3 : ℕ) ^ 2 = 3 ^ finrank (ZMod 3) U := by
      rw [← h]; norm_num
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ)) h2).symm
  have hvU : v ∈ U := by
    change real.coord (Additive.ofMul (⟨y, hyE⟩ : ↥E)) ∈
      ggLinImage (p := 3) real.coord D
    rw [ofMul_mem_ggLinImage]
    simpa using hyD
  have hcentj_le_U : R.cent j ≤ U := by
    intro w hw
    rw [← real.cent_eq j hj] at hw
    rw [mem_ggLinImage] at hw
    change w ∈ ggLinImage (p := 3) real.coord D
    rw [mem_ggLinImage]
    rw [← hJc] at hw
    rw [Subgroup.mem_centralizer_iff] at hw
    exact hI1 _ (Additive.toMul (real.coord.symm w)).2 (fun j' hj' => (hw j' hj').symm)
  have hinside : v ∈ R.inside c := by
    rw [← real.inside_eq c hc]
    change real.coord (Additive.ofMul (⟨y, hyE⟩ : ↥E)) ∈
      ggLinImage (p := 3) real.coord (real.component c)
    rw [ofMul_mem_ggLinImage]
    rw [← hKc]
    simpa using hyK
  obtain ⟨labK, labJ, hLitK, hLitJ, hTwo⟩ := (markedRow_iff (G := G) 3 K J).mp hrow
  have hocc_c' : R.occurs (Submodule.span (ZMod 3) {v}) c := by
    rw [← hspan]; exact hocc_c
  have hlabK : labK ∈ R.equivLabels c := by
    rw [hKc] at hLitK
    exact hdict real c hc labK hLitK
  have hlabJ : labJ ∈ R.equivLabels j := by
    rw [hJc] at hLitJ
    exact hdict real j hj labJ hLitJ
  exact hraw v hv0 U hdim hvU c j hc hj hocc_c' hocc_j hcent_c hcentj_le_U hinside
    labK hlabK labJ hlabJ hTwo

theorem actualCutThreeInput_of_raw (R : RawFrameData) (hraw : CutThreeInput R)
    (hdict : LiteralDictionaryInput R) : ActualCutThreeInput R :=
  fun hcl => actualInternalExclusion_of_raw R (hraw hcl) hdict

theorem actualCutFiveInput_of_raw (R : RawFrameData) (hraw : CutFiveInput R)
    (hdict : LiteralDictionaryInput R) : ActualCutFiveInput R :=
  fun hex => actualInternalExclusion_of_raw R (hraw hex) hdict

theorem literalDictionaryInput_of_rigid (hrig : GGLabelRigidInput) (R : RawFrameData)
    (hEq : ∀ c : R.Code, R.admissible c → ∀ lab : LargeEvenLabel,
      GGLabelIso (R.label c) lab → lab ∈ R.equivLabels c) :
    LiteralDictionaryInput R := by
  intro G _ H E real c hc lab hlit
  obtain ⟨labc, hlabc, hhasc, Rc, _instRc, _Ic, _Fc, _θc, hPc⟩ :=
    largeEvenMarking_exists_hasLabel (real.marked c hc)
  obtain ⟨labl, hlabl, hhasl, Rl, _instRl, _Il, _Fl, _θl, hPl⟩ :=
    largeEvenMarking_exists_hasLabel hlit
  rw [hPc] at hlabc hhasc
  rw [hPl] at hlabl hhasl
  exact hEq c hc lab
    (hrig (R.label c) lab (real.component c ⧸ Subgroup.center (real.component c))
      hlabc hlabl hhasc hhasl)

end CFSG.StandardType.GGQ2Frame
