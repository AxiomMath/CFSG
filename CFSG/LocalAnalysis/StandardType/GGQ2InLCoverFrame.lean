module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2NbrD5Frame
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

@[expose] def InLLeafAt (R : RawFrameData) (vx z : R.V) (ℓ k : R.Code) : Prop :=
  ∃ W : GGQ2LinOn 3 R.V,
    W.toLin.parab {i | i ≠ W.a} = R.normalizerGroup ℓ ∧
    W.toLin.parab {i | i ≠ W.b} = R.normalizerGroup k ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {vx}) ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.b}, W.root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {z}) ∧
    ∃! c, c ≠ W.b ∧ W.cartan W.b c ≠ 0

@[expose] def InLLeafCases (R : RawFrameData) : Prop :=
  ∀ vx : R.V, vx ≠ 0 →
  ∀ ℓ : R.Code, R.admissible ℓ → (∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (R.label ℓ)) →
    R.occurs (Submodule.span (ZMod 3) {vx}) ℓ →
    R.cent ℓ = Submodule.span (ZMod 3) {vx} → vx ∈ R.inside ℓ →
  ∀ U : Submodule (ZMod 3) R.V, finrank (ZMod 3) U = 2 → vx ∈ U →
  ∀ j : R.Code, R.admissible j → R.occurs U j → R.cent j = U → R.inside j ≤ R.inside ℓ →
    R.normalizerGroup j ≤ R.normalizerGroup ℓ →
  ∀ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} → ∀ k : R.Code, Candidate R vx j z k →
    R.inside j ≤ R.inside k → InLLeafAt R vx z ℓ k

@[expose] def GGQ2InLCoverAtFrame (R : RawFrameData) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∈ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K → ActualFrame (ggG0 p B x L D J) Bs R →
    GGQ2LeafPair p Bs x y D L J K ∨ GGQ2SelD6 G p Bs y J K ∨ GGQ2SelDet G p Bs y J K

theorem codeL_label_q2 (hrig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {R : RawFrameData}
    (real : Realization (ggG0 3 B x L D J) Bs R) (hS : GGQTwoSetting 3 B Bs x L D J)
    {ℓ : R.Code} (hℓadm : R.admissible ℓ) (hℓcomp : real.component ℓ = L) :
    ∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (R.label ℓ) := by
  have hmark : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab = R.label ℓ) := by
    have h := real.marked ℓ hℓadm
    rw [hℓcomp] at h
    exact h
  obtain ⟨lab₂, hl₂, has₂, R₂, _, I₂, F₂, θ₂, h₂⟩ := largeEvenMarking_exists_hasLabel hmark
  obtain ⟨lab₁, hl₁, has₁, R₁, _, I₁, F₁, θ₁, h₁⟩ := largeEvenMarking_exists_hasLabel hS.2.1
  refine ⟨lab₁, h₁.1, ?_⟩
  rw [← (h₂ : lab₂ = R.label ℓ)]
  exact hrig lab₁ lab₂ _ hl₁ hl₂ has₁ has₂

theorem inLCoverAtFrame_of_leafCases (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hrig : GGLabelRigidInput) {R : RawFrameData} (hC : InLLeafCases R) :
    GGQ2InLCoverAtFrame R := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ y K hnb hF
  subst hp
  obtain ⟨real⟩ := hF
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hS.1.1.1.2.2.2.2.2.2.1.2.1
  obtain ⟨hyx, hxy, hyBs, ℓ, j, hℓadm, hℓocc, hℓcent, hℓcomp, hvxℓ, hjadm, hjocc, hjcent,
    hjcomp, hins, hnorm, hvx0, hUfin, hxU⟩ :=
    ggQ2CensusFrame_setup real hS hI1 hxBs hnb
  obtain ⟨k, hkadm, hkocc, hkcent, hkcomp, hinsJK, hcandK, hvyU, hvyx⟩ :=
    ggQ2CensusFrame_caseDCand real hLB hP hS hI1 hxBs hnb hyx hxy hyBs hjadm hjcomp
  obtain ⟨W, hWL, hWK, hfixx, hfixy, hleaf⟩ :=
    hC _ hvx0 ℓ hℓadm (codeL_label_q2 hrig real hS hℓadm hℓcomp) hℓocc hℓcent (hvxℓ.mpr hxL) _
      hUfin hxU j hjadm hjocc hjcent hins hnorm _ hvyU hvyx k hcandK hinsJK
  have hLlin : (ggAutomizer L Bs).map (ggLin (p := 3) real.coord) =
      W.toLin.parab {i | i ≠ W.a} := by
    rw [hWL, ← real.normalizer_eq ℓ hℓadm, hℓcomp]
  have hKlin : (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) =
      W.toLin.parab {i | i ≠ W.b} := by
    rw [hWK, ← real.normalizer_eq k hkadm, hkcomp]
  exact Or.inl ⟨GGQ2Lin.toModel (p := 3) (by norm_num) W.toLin real.coord hxBs hyBs hLlin hKlin
    hfixx hfixy, hleaf⟩

theorem ggQ2InLCoverInput_of_placement (catalogue : FrameKind → RawFrameData)
    (hp : PlacementInput catalogue) (h : ∀ kind, GGQ2InLCoverAtFrame (catalogue kind)) :
    GGQ2InLCoverInput := by
  intro G _ _ p B Bs x L D J hS hp3 hI1 hxL _ y K hnb
  obtain ⟨kind, hF⟩ := hp hS hp3
  exact h kind hS hp3 hI1 hxL hnb hF

theorem ggQ2InLCoverInput_of_halves (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hrig : GGLabelRigidInput) (cl ex : FrameKind → RawFrameData) (hp : PlacementInput (catalogueOf cl ex))
    (hcl : ∀ k, IsClassical k → InLLeafCases (cl k))
    (hex : ∀ k, IsExceptional k → GGQ2InLCoverAtFrame (ex k)) : GGQ2InLCoverInput := by
  refine ggQ2InLCoverInput_of_placement (catalogueOf cl ex) hp fun k => ?_
  by_cases hk : IsClassical k
  · rw [catalogueOf_classical cl ex hk]
    exact inLCoverAtFrame_of_leafCases hLB hP hrig (hcl k hk)
  · rw [catalogueOf_exceptional cl ex hk]
    exact hex k hk

end CFSG.StandardType.GGQ2Frame

end
