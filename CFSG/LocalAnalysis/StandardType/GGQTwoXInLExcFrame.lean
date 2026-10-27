module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

@[expose] def InLCommonCases (R : RawFrameData) : Prop :=
  ∀ vx : R.V, vx ≠ 0 →
  ∀ ℓ : R.Code, R.admissible ℓ →
    (∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (R.label ℓ)) →
    R.occurs (Submodule.span (ZMod 3) {vx}) ℓ →
    R.cent ℓ = Submodule.span (ZMod 3) {vx} → vx ∈ R.inside ℓ →
  ∀ U : Submodule (ZMod 3) R.V, finrank (ZMod 3) U = 2 → vx ∈ U →
  ∀ j : R.Code, R.admissible j → R.occurs U j → R.cent j = U → R.inside j ≤ R.inside ℓ →
    R.normalizerGroup j ≤ R.normalizerGroup ℓ →
  ∃ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} ∧ ∃ k : R.Code, Candidate R vx j z k ∧
    CommonWitness R vx z ℓ k

theorem xInLNbrAtFrame_of_commonCases (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hrig : GGLabelRigidInput) {R : RawFrameData} (hmov : RawInsideMoved R)
    (hC : InLCommonCases R) :
    ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
      GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∈ L → ∀ [Fact p.Prime],
      ActualFrame (ggG0 p B x L D J) Bs R →
        ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧ Nonempty (GGQTwoModel p Bs x y D L J K) := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ hF
  subst hp
  obtain ⟨real⟩ := hF
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hS.1.1.1.2.2.2.2.2.2.1.2.1
  obtain ⟨ℓ, j, hℓadm, hℓocc, hℓcent, hℓcomp, hvxℓ, hjadm, hjocc, hjcent, hjcomp, hins, hnorm,
    hvx0, hUfin, hxU⟩ := ggQ2CensusFrame_codes real hS hI1 hxBs
  obtain ⟨z, hzU, hzx, k, hcand, hW⟩ :=
    hC _ hvx0 ℓ hℓadm (codeL_label_q2 hrig real hS hℓadm hℓcomp) hℓocc hℓcent (hvxℓ.mpr hxL) _
      hUfin hxU j hjadm hjocc hjcent hins hnorm
  exact ggQ2CensusFrame_commonModel real hmov hLB hP hS hxBs hℓadm hℓcomp hjadm hjcomp hcand hzx
    hzU hW

end CFSG.StandardType.GGQ2Frame

end
