module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.UniquenessCase.UCFront09h
import CFSG.LocalAnalysis.UniquenessCase.UCFront09l
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
import CFSG.Adapters.GeneralizedFitting
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.CharacterTheory.Semidihedral.LocalPrimeFailureSupport
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_le relPPrimeCore_eq_map)
open scoped commutatorElement

section Layer

variable {G : Type} [Group G]

theorem map_genFittingLayer_eq_rankThreeLayer (I : Subgroup G) :
    (genFittingLayer ↥I).map I.subtype = rankThreeLayer I := by
  rw [CFSG.Adapters.genFittingLayer_eq_foundations,
    CFSG.LocalAnalysis.ComponentInitial.layer_map_subtype, rankThreeLayer]
  simp_rw [CFSG.Assembly.isComponentOf_iff_open]

end Layer

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_I9 {M L X H : Subgroup G} (hLN : M ≤ normalizer (L : Set G))
    (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) (hX : Opp 3 X = X)
    (hXH : X ≤ H) (hO2 : pCoreOf 2 H = ⊥) (hO : CFSG.Open.relPPrimeCore 2 (I9 H) ≤ M)
    (hE : rankThreeLayer (I9 H) ≤ M) : X ≤ centralizer (I9 H : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIH : I9 H ≤ H := map_subtype_le _
  have hHI : H ≤ normalizer (I9 H : Set G) := le_normalizer_I9 H
  have hHE : H ≤ normalizer (rankThreeLayer (I9 H) : Set G) := by
    haveI : (genFittingLayer ↥(I9 H)).Characteristic :=
      CFSG.ComponentClassification.Layer.characteristic _
    rw [← map_genFittingLayer_eq_rankThreeLayer]
    exact hHI.trans (CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic _ _)
  have hPX : relPPrimeCore 2 (I9 H) ≤ centralizer (X : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 ((commutator_le_pCoreOf_of_mem_inv9'
      hLN hXL hcov hA5 ⟨hO, (not_dvd_card_relPPrimeCore_two_I9 H).2,
        hXH.trans (le_normalizer_relPPrimeCore_I9 2 H)⟩).trans
      ((CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 ((relPPrimeCore_le _).trans hIH)
        (le_normalizer_relPPrimeCore_I9 2 H)).trans hO2.le)))
  have hEX : rankThreeLayer (I9 H) ≤ centralizer (X : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 ((commutator_le_pCoreOf_of_mem_inv9'
      hLN hXL hcov hA5 ⟨hE, fun h3 => not_dvd_card_I9 H (h3.trans (card_dvd_of_le
        (CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeLayer_le _))), hXH.trans hHE⟩).trans
      ((CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2
        ((CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeLayer_le _).trans hIH) hHE).trans
        hO2.le)))
  have hO2I : CFSG.pCore 2 ↥(I9 H) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (I9 H).subtype_injective).1 (le_bot_iff.1
      ((CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hIH hHI).trans hO2.le))
  have hFX : (genFittingFStar ↥(I9 H)).map (I9 H).subtype ≤ centralizer (X : Set G) := by
    rw [genFittingFStar.eq_sup, Subgroup.map_sup]
    refine sup_le ((map_mono ?_).trans ((relPPrimeCore_eq_map Nat.prime_two _).ge.trans hPX))
      ((map_genFittingLayer_eq_rankThreeLayer _).le.trans hEX)
    have h := CFSG.GorensteinWalter.fittingSubgroup_le_sup_pCore_pPrimeCore (G := ↥(I9 H))
    rw [hO2I, bot_sup_eq] at h
    exact h
  have hIF : I9 H ≤ normalizer ((genFittingFStar ↥(I9 H)).map (I9 H).subtype : Set G) := by
    haveI : (genFittingFStar ↥(I9 H)).Characteristic :=
      CFSG.ComponentClassification.GeneralizedFitting.characteristic _
    exact le_normalizer.trans
      (CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic _ _)
  have hCF : I9 H ⊓ centralizer ((genFittingFStar ↥(I9 H)).map (I9 H).subtype : Set G) ≤
      (genFittingFStar ↥(I9 H)).map (I9 H).subtype := by
    rw [← CFSG.Semidihedral.LocalPrimeFailure.map_subtype_centralizer]
    exact map_mono (CFSG.Adapters.generalized_fitting_self_centralizing _)
  obtain ⟨D, hDX, hD⟩ := exists_card_eq_three hXL hcov hA5
  refine le_of_forall_map_conj_le hXL hcov hA5 hX hDX hD fun x hx => ?_
  have hBX : D.map (MulAut.conj x).toMonoidHom ≤ X := conj_smul_le_of_le hDX ⟨_, hx⟩
  have hBF := hBX.trans (le_centralizer_iff.1 hFX)
  have hBI := hBX.trans (hXH.trans hHI)
  have hFB := commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hBF)
  have h3 : ⁅⁅I9 H, D.map (MulAut.conj x).toMonoidHom⁆,
      (genFittingFStar ↥(I9 H)).map (I9 H).subtype⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (by rw [commutator_eq_bot_iff_le_centralizer.2 hBF, commutator_bot_left])
      (eq_bot_iff.2 ((commutator_mono (le_normalizer_iff_commutator_le_left.1 hIF) le_rfl).trans
        hFB.le))
  have hIB := (le_inf (le_normalizer_iff_commutator_le_left.1 hBI)
    (commutator_eq_bot_iff_le_centralizer.1 h3)).trans hCF
  have hc := CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq Nat.prime_three
    (IsPGroup.of_card (n := 1) (by rw [card_map_of_injective (MulAut.conj x).injective, hD,
      pow_one])) hBI (not_dvd_card_I9 H)
  refine le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 ?_)
  rw [← hc]
  exact le_bot_iff.1 ((commutator_mono hIB le_rfl).trans hFB.le)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
