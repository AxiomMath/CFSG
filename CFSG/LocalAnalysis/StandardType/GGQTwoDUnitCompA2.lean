module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CanonicalPrimeComponentLift
import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263Rank
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Assembly.QuasithinDefs
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.Dihedral.DihedralFusionPrefixes
import CFSG.Foundations
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType.QTwo

open CFSG
open CFSG.ComponentClassification.CatalogueBPrimeJoin

variable {G : Type} [Group G] [Finite G]

theorem qtwoDB7_le_pLayer {H J : Subgroup G} (hJ : J ≤ CFSG.Assembly.LargeEvenPLayer 3 H) :
    J.subgroupOf H ≤ CFSG.pLayer ↥H 3 := by
  have key : CFSG.Assembly.LargeEvenPLayer 3 H ≤ (CFSG.pLayer ↥H 3).map H.subtype := by
    show sSup {L : Subgroup G | CFSG.Assembly.LargeEvenPComponent 3 H L} ≤ _
    refine sSup_le ?_
    intro L hL
    obtain ⟨hLH, hLp⟩ := (ggLargeEvenPComponent_iff 3 H L).1 hL
    rw [← Subgroup.map_subgroupOf_eq_of_le hLH]
    exact Subgroup.map_mono (le_sSup hLp)
  have h' : J.comap H.subtype ≤
      ((CFSG.pLayer ↥H 3).map H.subtype).comap H.subtype :=
    Subgroup.comap_mono (f := H.subtype) (hJ.trans key)
  rwa [Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at h'

theorem qtwoDB7_map_pLayer_le {X : Type} [Group X] [Finite X] :
    (CFSG.pLayer X 3).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤
      CFSG.pLayer (X ⧸ CFSG.pPrimeCore 3 X) 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient]
  refine (CFSG.LocalAnalysis.ComponentInitial.solvable_prime_core_ordinary_components
    (H := X ⧸ CFSG.pPrimeCore 3 X) 3 Nat.prime_three ?_).2.1
  rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := X) 3]
  infer_instance

theorem qtwoDB7_exists_pcomp {H J : Subgroup G}
    {Q : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)} (hQ : CFSG.IsComponent Q)
    (hJH : J ≤ H) (hJq : CFSG.IsQuasisimple (J.subgroupOf H))
    (h3 : 3 ∣ Nat.card (↥(J.subgroupOf H) ⧸ Subgroup.center ↥(J.subgroupOf H)))
    (hJQ : (J.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ≤ Q) :
    ∃ N : Subgroup G, CFSG.Assembly.LargeEvenPComponent 3 H N ∧ J ≤ N ∧
      (N.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) = Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  let N' := canonicalPrimeLift (X := ↥H) 3 Q
  have hN'p : CFSG.IsPComponent 3 N' :=
    ((canonical_prime_component_lift (X := ↥H) 3).1 Q hQ).1
  have hN'map : N'.map π = Q :=
    ((canonical_prime_component_lift (X := ↥H) 3).1 Q hQ).2.1
  refine ⟨N'.map H.subtype, ?_, ?_, ?_⟩
  · rw [ggLargeEvenPComponent_iff]
    refine ⟨Subgroup.map_subtype_le N', ?_⟩
    change CFSG.IsPComponent 3 ((N'.map H.subtype).comap H.subtype)
    rwa [Subgroup.comap_map_eq_self_of_injective H.subtype_injective N']
  · have hJ'le : J.subgroupOf H ≤ N' := by
      set J' := J.subgroupOf H with hJ'def
      set V := Q.comap π with hVdef
      have hJV : J' ≤ V := by
        intro x hx
        change π x ∈ Q
        exact hJQ (Subgroup.mem_map_of_mem π hx)
      have hresJ : primeResidual 3 J' = ⊤ := by
        haveI : (primeResidual 3 J').Characteristic := primeResidual_characteristic 3 J'
        rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hJq
          (N := primeResidual 3 J') inferInstance with htop | hcenter
        · exact htop
        · exfalso
          have hcop : Nat.Coprime 3 (primeResidual 3 J').index :=
            primeResidual_coprime_index 3 J'
          have hnot : ¬ 3 ∣ (primeResidual 3 J').index :=
            Nat.prime_three.coprime_iff_not_dvd.mp hcop
          apply hnot
          have hdvd : Nat.card (J' ⧸ Subgroup.center J') ∣
              Nat.card (J' ⧸ primeResidual 3 J') := by
            rw [← Subgroup.index_eq_card (H := Subgroup.center J'),
              ← Subgroup.index_eq_card (H := primeResidual 3 J')]
            exact Subgroup.index_dvd_of_le hcenter
          rw [Subgroup.index_eq_card]
          exact dvd_trans h3 hdvd
      have hinc : J'.subgroupOf V ≤ primeResidual 3 V := by
        rw [← Subgroup.inclusion_range hJV, MonoidHom.range_eq_map, ← hresJ]
        exact primeResidual_map_le 3 (Subgroup.inclusion hJV)
      calc J' = (J'.subgroupOf V).map V.subtype := by
              rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJV]
           _ ≤ (primeResidual 3 V).map V.subtype := Subgroup.map_mono hinc
           _ = N' := (closure_pElements_eq_map_primeResidual (X := ↥H) 3 V).symm
    calc J = (J.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hJH).symm
       _ ≤ N'.map H.subtype := Subgroup.map_mono hJ'le
  · change ((N'.map H.subtype).comap H.subtype).map π = Q
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective N']
    exact hN'map

theorem qtwoDB7_pcomp_unique {H N N' : Subgroup G}
    (hN : CFSG.Assembly.LargeEvenPComponent 3 H N)
    (hN' : CFSG.Assembly.LargeEvenPComponent 3 H N')
    (h : (N.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) =
      (N'.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) : N = N' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hNH, hNp⟩ := (ggLargeEvenPComponent_iff 3 H N).1 hN
  obtain ⟨hN'H, hN'p⟩ := (ggLargeEvenPComponent_iff 3 H N').1 hN'
  have hcomp : CFSG.IsComponent ((N.subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) := by
    obtain ⟨K, hK, -, hKm, -⟩ := hNp
    rwa [← hKm] at hK
  have huniq := ((canonical_prime_component_lift (X := ↥H) 3).1
    ((N.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) hcomp).2.2.2
  have hNcanon : N.subgroupOf H = canonicalPrimeLift (X := ↥H) 3
      ((N.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) :=
    huniq (N.subgroupOf H) hNp rfl
  have hN'canon : N'.subgroupOf H = canonicalPrimeLift (X := ↥H) 3
      ((N.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) :=
    huniq (N'.subgroupOf H) hN'p h.symm
  rw [← Subgroup.map_subgroupOf_eq_of_le hNH, ← Subgroup.map_subgroupOf_eq_of_le hN'H,
    hNcanon, hN'canon]

theorem qtwoDB7_components_eq {Y : Type} [Group Y] [Finite Y] {Q Q' P : Subgroup Y}
    (hQ : CFSG.IsComponent Q) (hQ' : CFSG.IsComponent Q') (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥)
    (hPQ : P ≤ Q) (hPQ' : P ≤ Q') : Q = Q' := by
  by_contra hne
  have hcomm : ⁅Q, Q'⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hQ hQ').resolve_left hne
  have hbot : ⁅P, P⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hPQ hPQ').trans_eq hcomm)
  exact hP1 (hP ▸ hbot)

theorem qtwoDB7_lift_to_G {H : Subgroup G} {E U : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEU : E ≤ Subgroup.normalizer (U : Set (↥H ⧸ CFSG.pPrimeCore 3 ↥H))) :
    ∃ E' U' : Subgroup G, U' ≠ ⊥ ∧ IsPGroup 2 U' ∧
      E' ≤ Subgroup.normalizer (U' : Set G) ∧ CFSG.Open.IsElemAbelian 3 E' ∧
      Nat.card E' = Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥H) :=
    Nat.prime_three.coprime_iff_not_dvd.mp CFSG.pPrimeCore_coprime_card
  obtain ⟨T, E₀, hT, hT2, hE₀, hE₀card, hE₀N⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T263.lift_normalizing Nat.prime_three (by norm_num)
      (CFSG.pPrimeCore 3 ↥H) hN hU hU2 hE hEU
  refine ⟨E₀.map H.subtype, T.map H.subtype, ?_, hT2.map _, ?_,
    CFSG.Open.IsElemAbelian.map hE₀ H.subtype, ?_⟩
  · intro hbot
    exact hT ((Subgroup.map_eq_bot_iff_of_injective T H.subtype_injective).1 hbot)
  · exact (Subgroup.map_mono hE₀N).trans (Subgroup.le_normalizer_map _)
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hE₀card]

theorem qtwoDB7_perfect_image {H P : Subgroup G} (hPH : P ≤ H) (hP : ⁅P, P⁆ = P)
    (h3 : 3 ∣ Nat.card P) :
    ⁅(P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)),
      (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))⁆ =
        (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ∧
    (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  have hperf : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := by
    refine (Subgroup.map_subtype_inj (H := H)).mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPH, hP]
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.map_commutator, hperf]
  · intro hbot
    have hle : P.subgroupOf H ≤ π.ker := (Subgroup.map_eq_bot_iff (P.subgroupOf H)).1 hbot
    rw [QuotientGroup.ker_mk'] at hle
    have hcard : Nat.card (P.subgroupOf H) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
    have h3' : 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥H) := by
      rw [← hcard] at h3
      exact h3.trans (Subgroup.card_dvd_of_le hle)
    exact Nat.prime_three.coprime_iff_not_dvd.mp CFSG.pPrimeCore_coprime_card h3'

end CFSG.StandardType.QTwo

end
