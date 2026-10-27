module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructND
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructE6Diag
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructE6Levi
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingSL
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoE6
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExcStep
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj
import CFSG.LocalAnalysis.SeitzReduction.E6PilotPositionPerfectX
import CFSG.LieType.Steinberg.Adjoint.Group
import CFSG.LieType.Steinberg.Isogeny.E6
import CFSG.LieType.Steinberg.Minuscule.Datum
import CFSG.LieType.Steinberg.Minuscule.Valid
import CFSG.LieType.Chevalley.RootOps.All
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionB

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
  CFSG.SeitzReduction.E6Pilot CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule Matrix

namespace KGE6


theorem kgPiecesD_highRoot_E6 {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    KGND.KGPiecesD (innDiag K) (EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) := by
  obtain ⟨hC, hNL, hdisj, hQ⟩ :=
    KGExc.centralizer_decomp_highRoot (K := K) (Or.inl rfl)
      (show CFSG.IsQuasisimple (EPilot.perpLevi .E6 K) from isQuasisimple_a5Levi)
      (show Subgroup.center (EPilot.perpLevi .E6 K) = ⊥ from center_a5Levi_eq_bot)
  have hperfC := E6Pilot.commutator_centralizer_pinnedElt_highRoot_E6_of_one_le (K := K) hf hK
  have hLq : CFSG.Assembly.IsQuasisimple ↥(a5Levi K) :=
    ⟨isQuasisimple_a5Levi.1.commutator_eq_top, isQuasisimple_a5Levi.2.1⟩
  refine KGND.kgPiecesD_of_decomp (𝒟 := innDiag K)
    (z := EPilot.pinnedElt .E6 (highRoot .E6) (1 : K))
    (Q := EPilot.highRadical .E6 K) (L := EPilot.perpLevi .E6 K) hQ ?_ ?_ hNL ?_ ?_ hLq
    (KGND.slConjSet (slToA5Levi (K := K))) ?_ ?_
  · rw [← hC]
  · rw [← hC]
    exact Subgroup.commutator_le_self _
  · exact disjoint_iff.mp hdisj
  · rw [← hC]
    exact hperfC
  · exact KGND.largeEvenMarking_slConjSet (m := 5) (F := K) hK hf (by norm_num)
      (fun h => absurd h (by norm_num)) (slToA5Levi (K := K)) slToA5Levi_surjective
      (le_of_eq (ker_slToA5Levi (K := K)))
  · intro δ hδ hδz
    rw [mem_innDiag_iff] at hδ
    obtain ⟨g, a, rfl⟩ := hδ
    exact exists_levi_action_of_fix hδz

end KGE6

section Tag


theorem ggRootCentKGStructTag_E6 : GGRootCentKGStructTag .E6 := by
  intro G _ _ p n f ψ _ _ hadm _ hker _ _ hC _ _ r hr _ E hEN hEC _ hEinn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hπker : (e6Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center.trans
      (AutSt.ker_eq_center hker hC).symm
  obtain ⟨ψbar, hψbar_inj, hψbar_range, hcomp⟩ := KGE6.exists_factor_e6Isogeny (f := f) hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 hEC ⊢
  have hz1 : e6Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hγ' : IsRoot .E6 γ :=
    e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 _ |>.mp hγ
  have hbase : KGND.KGPiecesD (KGE6.innDiag (GaloisField 2 f))
      (xPar (rootOperatorFamily .E6) RootCentExc.e6HighRoot (1 : GaloisField 2 f)) := by
    have h2 : (2 : GaloisField 2 f) = 0 := CharTwo.two_eq_zero
    have he : xPar (rootOperatorFamily .E6) RootCentExc.e6HighRoot (1 : GaloisField 2 f) =
        EPilot.pinnedElt .E6 (highRoot .E6) (1 : GaloisField 2 f) :=
      Subtype.ext (RootCentExc.coe_xPar_eq_pinnedX h2 (rootOperatorFamily .E6)
        RootCentExc.highRootData_E6.maxHeight.1 1)
    rw [he]
    exact KGE6.kgPiecesD_highRoot_E6 hf hK
  have hinv : ∀ g z : adjointGroup .E6 (GaloisField 2 f),
      KGND.KGPiecesD (KGE6.innDiag (GaloisField 2 f)) z →
      KGND.KGPiecesD (KGE6.innDiag (GaloisField 2 f)) (g * z * g⁻¹) := by
    intro g z h
    have h' := h.map_of_mem (β := MulAut.conj g) (KGE6.conj_mem_innDiag g)
    simpa only [MulAut.conj_apply] using h'
  have hsingle : ∀ j : Fin Tag.E6.rank, KGND.KGPiecesD (KGE6.innDiag (GaloisField 2 f))
      (xPar (rootOperatorFamily .E6) (Pi.single j 1) (1 : GaloisField 2 f)) :=
    fun j => KGE6.single_E6_of_conj (P := fun z => KGND.KGPiecesD (KGE6.innDiag _) z)
      hinv (rootOperatorFamily .E6) hbase j
  have hez : e6Isogeny (GaloisField 2 f) z ∈
      rootGroup (rootOperatorFamily .E6) (GaloisField 2 f) γ := by
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup (GaloisField 2 f)).1 hz
    rw [e6Isogeny_xm (GaloisField 2 f) hγ']
    exact xPar_mem hγ' _
  have hcz : KGND.KGPiecesD (KGE6.innDiag (GaloisField 2 f))
      (e6Isogeny (GaloisField 2 f) z) := by
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup (GaloisField 2 f)).1 hz
    rw [e6Isogeny_xm (GaloisField 2 f) hγ'] at hz1 ⊢
    exact KGE6.of_mem_rootGroup_of_conj (P := fun z => KGND.KGPiecesD (KGE6.innDiag _) z)
      hinv (rootOperatorFamily .E6) hsingle hγ' (xPar_mem hγ' _) hz1
  have hcz' : KGND.KGPiecesD (KGE6.innDiag (GaloisField 2 f))
      (e6Isogeny (GaloisField 2 f) (u * z * u⁻¹)) := by
    let u' : e6Data_valid.minGroup (GaloisField 2 f) := u
    let z' : e6Data_valid.minGroup (GaloisField 2 f) := z
    change KGND.KGPiecesD (KGE6.innDiag (GaloisField 2 f))
      (e6Isogeny (GaloisField 2 f) (u' * z' * u'⁻¹))
    have h := hcz.map_of_mem (KGE6.conj_mem_innDiag (e6Isogeny (GaloisField 2 f) u'))
    have he : (MulAut.conj (e6Isogeny (GaloisField 2 f) u')) (e6Isogeny (GaloisField 2 f) z') =
        e6Isogeny (GaloisField 2 f) (u' * z' * u'⁻¹) := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    rwa [he] at h
  have hr_eq : ψ (u * z * u⁻¹) =
      ψbar (e6Isogeny (GaloisField 2 f) (u * z * u⁻¹)) := by
    let u' : e6Data_valid.minGroup (GaloisField 2 f) := u
    let z' : e6Data_valid.minGroup (GaloisField 2 f) := z
    exact (hcomp (u' * z' * u'⁻¹)).symm
  rw [hr_eq]
  have hE : E ≤ Subgroup.centralizer
      ({ψbar (e6Isogeny (GaloisField 2 f) (u * z * u⁻¹))} : Set G) := by
    simpa only [hr_eq] using hEC
  have hact : ∀ ε ∈ E, ∃ δ ∈ KGE6.innDiag (GaloisField 2 f), ∀ v,
      ε⁻¹ * ψbar v * ε = ψbar (δ v) := fun ε hε =>
    KGE6.exists_mem_innDiag_conj hker hψbar_inj hcomp (hEN hε) (hEinn ε hε)
  have hconcl := hcz' G ψbar hψbar_inj E hE hact
  rwa [hψbar_range] at hconcl

end Tag

end CFSG.StandardType
