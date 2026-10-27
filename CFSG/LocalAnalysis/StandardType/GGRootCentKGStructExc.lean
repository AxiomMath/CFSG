module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructDecomp
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeInner
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExc
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExcStep
import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootExc
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcRoots
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionPerfect
import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionPerfect
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule

namespace KGExc

private theorem largeEvenMarking_of_rawDatum_inn {X : Type} [Group X]
    (hX : CFSG.Assembly.IsQuasisimple X) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hChev : GGChevStTag lab) {Q : LargeEvenRawCont}
    (hraw : LargeEvenRawDatum lab Q)
    (hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F →
      Nonempty (X ⧸ Subgroup.center X ≃* R) ∧ LargeEvenInnSet R ⊆ I) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I) := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  refine ⟨hX.1, lab, hlab, ?_⟩
  refine largeEvenRawDatum_mono (fun R _ I F hRI => ?_) hraw
  obtain ⟨⟨e⟩, hInn⟩ := hQ R I F hRI
  exact ⟨e.symm.isSimpleGroup, nonabelian_of_mulEquiv e
    (exists_mul_ne_mul_centerQuot_of_perfect hX.1 inferInstance), e, hChev, hInn⟩

theorem largeEvenMarking_inn_of_lieModel {X : Type} [Group X]
    (hX : CFSG.Assembly.IsQuasisimple X) {t : StatedLieTag} {n f : ℕ}
    (ht : GGInnerTag t) (hM : LieModel (X ⧸ Subgroup.center X) t n 2 f) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I) := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  have hnab := exists_mul_ne_mul_centerQuot_of_perfect hX.1 inferInstance
  obtain ⟨lab, hlab, htag, -, -, -, hraw⟩ :=
    exists_label_rawDatum_of_lieModel
      (center_eq_bot_of_isSimpleGroup_of_nonabelian hnab) hM
  have hChev : GGChevStTag lab := by
    obtain ⟨tg, l, n⟩ := lab
    have hinner : GGInnerTag (markTag ⟨tg, l, n⟩) := htag ▸ ht
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl
      simp [GGInnerTag, markTag] at hinner
    · rintro rfl
      simp [GGInnerTag, markTag] at hinner
    · rintro rfl
      simp [GGInnerTag, markTag] at hinner
  refine largeEvenMarking_of_rawDatum_inn hX hlab hChev
    (largeEvenRawDatum_inn (by rw [htag]; exact ht) hraw) (fun _ _ _ _ h => h)

section PiecesE8

theorem kgPieces_highRoot_E8 {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    KGPieces (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)) := by
  obtain ⟨hC, hLQ, hdisj, hQ⟩ := centralizer_decomp_highRoot (K := K) (Or.inr (Or.inr rfl))
    E8Pilot.isQuasisimple_e7Levi E8Pilot.center_e7Levi_eq_bot
  have hLq : CFSG.Assembly.IsQuasisimple ↥(EPilot.perpLevi .E8 K) :=
    ⟨E8Pilot.isQuasisimple_e7Levi.1.commutator_eq_top,
      E8Pilot.isQuasisimple_e7Levi.2.1⟩
  refine kgPieces_of_decomp hC hQ hLQ (disjoint_iff.mp hdisj) ?_ hLq ?_
  · exact E8Pilot.commutator_centralizer_pinnedElt_highRoot_E8_of_one_le hf hK
  · have hM : LieModel (↥(E8Pilot.e7Levi K) ⧸
        Subgroup.center ↥(E8Pilot.e7Levi K)) .E7 0 2 f :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq E8Pilot.center_e7Levi_eq_bot).trans
          QuotientGroup.quotientBot).symm (E8Pilot.lieModel_e7Levi hf hK)
    exact largeEvenMarking_inn_of_lieModel hLq
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hM

end PiecesE8

section PiecesE7

theorem kgPieces_highRoot_E7 {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    KGPieces (EPilot.pinnedElt .E7 (highRoot .E7) (1 : K)) := by
  obtain ⟨hC, hLQ, hdisj, hQ⟩ := centralizer_decomp_highRoot (K := K) (Or.inr (Or.inl rfl))
    E7Pilot.isQuasisimple_perpLevi_E7 E7Pilot.center_perpLevi_E7_eq_bot
  have hLq : CFSG.Assembly.IsQuasisimple ↥(EPilot.perpLevi .E7 K) :=
    ⟨E7Pilot.isQuasisimple_perpLevi_E7.1.commutator_eq_top,
      E7Pilot.isQuasisimple_perpLevi_E7.2.1⟩
  refine kgPieces_of_decomp hC hQ hLQ (disjoint_iff.mp hdisj) ?_ hLq ?_
  · rcases Nat.lt_or_ge f 2 with h | h
    · obtain rfl : f = 1 := by omega
      exact E8Pilot.commutator_centralizer_pinnedElt_highRoot_two (Or.inr (Or.inl rfl))
        (by simpa using hK)
    · refine E7Pilot.commutator_centralizer_pinnedElt_highRoot_E7 (hq := ?_)
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
  · exact largeEvenMarking_inn_of_lieModel hLq (Or.inr (Or.inl rfl))
      (E7Pilot.lieModel_perpLevi_E7_quotient_center hK)

end PiecesE7

end KGExc

section Tags

open KGExc

theorem ggRootCentKGStructTag_E8 : GGRootCentKGStructTag .E8 := by
  intro G _ _ _ n f ψ _ _ hadm hrank hker hcomm hLie hC _ _ r hr _ E hEN hEC _ hEinn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, AutSt.ker_eq_center hker hC]
    exact center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .E8 γ := mem_adjDatum_roots.mp hγ
  have hbase : KGPieces (xPar (rootOperatorFamily .E8) (highRoot .E8)
        (1 : GaloisField 2 f)) := by
    have h2 : (2 : GaloisField 2 f) = 0 := CharTwo.two_eq_zero
    have he : xPar (rootOperatorFamily .E8) (highRoot .E8) (1 : GaloisField 2 f) =
        EPilot.pinnedElt .E8 (highRoot .E8) (1 : GaloisField 2 f) :=
      Subtype.ext (RootCentExc.coe_xPar_eq_pinnedX h2 (rootOperatorFamily .E8)
        RootCentExc.highRootData_E8.maxHeight.1 1)
    rw [he]
    exact kgPieces_highRoot_E8 hf hK
  have hcz : KGPieces z :=
    RootCentQLTyped.of_mem_rootGroup (P := KGPieces) (fun α z h => h.map α)
      (rootOperatorFamily .E8) (fun j => RootCentQLTyped.single_E8 (P := KGPieces)
        (fun α z h => h.map α) (rootOperatorFamily .E8) hbase j) hγ' hz hz1
  have hcz' : KGPieces ((MulAut.conj u) z) := hcz.map (MulAut.conj u)
  have hEψ : E ≤ ψ.range := by
    intro e he
    obtain ⟨g, hg, hcg⟩ := ggPsiDiagInnerAt_of_ggInnerTag .E8
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      G n f ψ ψ.range ⟨⟨hadm, hrank⟩, ⟨rfl, hker⟩, hcomm, hLie⟩ e (hEN he) (hEinn e he)
    exact OrdPInnerExc.mem_of_mul_mem_centralizer hC hg hcg
  exact hcz' G ψ hinj E (le_inf hEψ hEC)

theorem ggRootCentKGStructTag_E7 : GGRootCentKGStructTag .E7 := by
  intro G _ _ _ n f ψ _ _ hadm hrank hker hcomm hLie hC _ _ r hr _ E hEN hEC _ hEinn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, AutSt.ker_eq_center hker hC]
    exact E8Pilot.center_minGroup_e7_eq_bot
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  change Fin Tag.E7.rank → ℤ at γ
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  set e := E8Pilot.e7MinEquivAdjoint (GaloisField 2 f) with he
  have hz1 : e z ≠ 1 := by
    intro h
    have hz' : z = 1 := e.injective (h.trans (map_one e).symm)
    rw [hz'] at hr2
    simp at hr2
  have hγ' : IsRoot .E7 γ :=
    e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 _ |>.mp hγ
  have hbase : KGPieces (xPar (rootOperatorFamily .E7) (highRoot .E7)
        (1 : GaloisField 2 f)) := by
    have h2 : (2 : GaloisField 2 f) = 0 := CharTwo.two_eq_zero
    have he' : xPar (rootOperatorFamily .E7) (highRoot .E7) (1 : GaloisField 2 f) =
        EPilot.pinnedElt .E7 (highRoot .E7) (1 : GaloisField 2 f) :=
      Subtype.ext (RootCentExc.coe_xPar_eq_pinnedX h2 (rootOperatorFamily .E7)
        RootCentExc.highRootData_E7.maxHeight.1 1)
    rw [he']
    exact kgPieces_highRoot_E7 hf hK
  have hez : e z ∈ rootGroup (rootOperatorFamily .E7) (GaloisField 2 f) γ := by
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup (GaloisField 2 f)).1 hz
    rw [he, E8Pilot.e7MinEquivAdjoint_apply, e7Isogeny_xm]
    exact xPar_mem hγ' _
  have hcz : KGPieces (e z) :=
    RootCentQLTyped.of_mem_rootGroup (P := KGPieces) (fun α z h => h.map α)
      (rootOperatorFamily .E7) (fun j => RootCentQLTyped.single_E7 (P := KGPieces)
        (fun α z h => h.map α) (rootOperatorFamily .E7) hbase j) hγ' hez hz1
  have hcz' : KGPieces ((MulAut.conj u) z) := (KGPieces.of_mulEquiv e hcz).map
    (MulAut.conj u)
  have hEψ : E ≤ ψ.range := by
    intro e' he
    obtain ⟨g, hg, hcg⟩ := ggPsiDiagInnerAt_of_ggInnerTag .E7
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      G n f ψ ψ.range ⟨⟨hadm, hrank⟩, ⟨rfl, hker⟩, hcomm, hLie⟩ e'
      (hEN he) (hEinn e' he)
    exact OrdPInnerExc.mem_of_mul_mem_centralizer hC hg hcg
  exact hcz' G ψ hinj E (le_inf hEψ hEC)

end Tags

end CFSG.StandardType
