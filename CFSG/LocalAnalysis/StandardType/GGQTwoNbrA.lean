module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrAAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrAAuxBlk
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrAAuxDiag
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrAAuxMod
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrAAuxFld
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem qTwoNbr_stdComp {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)} {m : ℕ}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hm : 5 ≤ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m) :
    ∃ t : ℕ, 4 ≤ t ∧ t ≤ m - 1 ∧ 3 ∣ Nat.card J ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) .PSU t 2 1 := by
  classical
  letI := hFrameL.fieldF0
  haveI := hFrameL.finiteF0
  haveI := hFrameL.charF0
  letI := hFrameL.groupL0
  haveI := hFrameL.finiteL0
  have hF : Nat.card hFrameL.F0 = (2 ^ 1) ^ 2 := by simpa using hFrameL.hcardF0
  obtain ⟨y, hy, hyx, -, hJy⟩ := qTwoNbrA_exists_y hcfg.1.1.1 hcfg.1.1.2.1 hcfg.1.1.2.2
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hFrameL.hBsN
  have hρ : ∀ (b : ↥Bs) (l : ↥L),
      hFrameL.c (ggGamma L hN b l) = hFrameL.ρ b (hFrameL.c l) := fun b l =>
    (hFrameL.hρ_induced b l).symm ▸ rfl
  have hne := qTwoNbrA_rho_ne_one hcfg.1.1.1 hcfg.1.1.2.1 hN hFrameL.c hFrameL.hc_surj
    hFrameL.hc_ker hFrameL.ρ hρ hy hyx
  have hM := qTwoNbrA_image_isComponentOf hN hFrameL.c hFrameL.hc_surj hFrameL.hc_ker hFrameL.ρ
    hρ hy hJy
  obtain ⟨t, δ, ht, hδ, hφδ⟩ := qTwoNbrA_diag_aut hF hFrameL.πSU (hFrameL.hdiag ⟨y, hy⟩)
  set φ := hFrameL.πSU.comp (qTwoNbrRec_suEquiv hF hFrameL.m).symm.toMonoidHom with hφ
  have hφsurj : Function.Surjective φ :=
    hFrameL.hπ_surj.comp (qTwoNbrRec_suEquiv hF hFrameL.m).symm.surjective
  have hφker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 1 hFrameL.F0 hFrameL.m) := by
    intro z hz
    have h1 : (qTwoNbrRec_suEquiv hF hFrameL.m).symm z ∈ hFrameL.πSU.ker := hz
    have h2 := hFrameL.hπ_ker h1
    have h3 : z ∈ (Subgroup.center (Su hFrameL.F0 2 1 hFrameL.m)).map
        (qTwoNbrRec_suEquiv hF hFrameL.m).toMonoidHom :=
      ⟨_, h2, by simp⟩
    rwa [show (Subgroup.center (Su hFrameL.F0 2 1 hFrameL.m)).map
        (qTwoNbrRec_suEquiv hF hFrameL.m).toMonoidHom =
        Subgroup.center ↥(unitarySU 2 1 hFrameL.F0 hFrameL.m) from
      Subgroup.map_center_eq (qTwoNbrRec_suEquiv hF hFrameL.m)] at h3
  obtain ⟨S, hS4, hSm, hMS⟩ := qTwoNbrA_block_of_diag hF φ hφsurj hφker hne ht hδ hφδ hM
  obtain ⟨hLie, h3⟩ := qTwoNbrA_block_model hF φ hφker hS4 hSm
  rw [← hMS] at hLie h3
  have hJL : J ≤ L := hJy.1.trans inf_le_left
  obtain ⟨⟨e⟩, hdvd⟩ := qTwoNbrA_center_quot_of_component hJL hFrameL.c hFrameL.hc_ker hJy
  refine ⟨S.card, hS4, by omega, ?_, ?_⟩
  · exact h3.trans hdvd
  · exact LieModel.of_mulEquiv e.symm hLie

theorem qTwoNbr_le {p : ℕ} {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hpJ : p ∣ Nat.card J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K) :
    J ≤ K :=
  le_of_ggNbr hLB hcfg.1.1.1 hcfg.1.1.2.2 hpJ hnbr

theorem qTwoNbr_component {p : ℕ} {B Bs L D J : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G}
    {K : Subgroup G} (hnbr : GGNbr p B x D J y K) (hJK : J ≤ K) :
    IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
  ggIsComponentOf_inf_centralizer_nbr hcfg.1.1 hnbr hJK

theorem qTwoNbr_field
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hTCJ : GGTCJKnown) {y : G} {K : Subgroup G}
    (hnbr : GGNbr 3 B x D J y K) (hJK : J ≤ K) {t : ℕ} (ht : 4 ≤ t)
    (hJ : LieModel (↥J ⧸ Subgroup.center ↥J) .PSU t 2 1) :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) → lab.n = 1 := by
  intro lab hΛ hhas
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hInn : GGInnerDiagOn Bs K := hcfg.1.2.2.1.2 y K hnbr
  obtain ⟨labJ, hΛJ, hdvd, hhasJ⟩ :=
    qTwoNbrA_tcj_nbr hTCJ hRig hcfg.1.1 hnbr hJK hInn hΛ hhas
  have h1 : labJ.n = 1 := qTwoNbrA_labJ_n hRig ht hJ hΛJ hhasJ
  rw [h1] at hdvd
  exact Nat.dvd_one.mp hdvd

end CFSG.StandardType.QTwo

end
