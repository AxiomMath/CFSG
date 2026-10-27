module

public import CFSG.RankThree.PartOne.Q1327T.ItemBasic
public import CFSG.RankThree.PartOne.Q1327T.KleinThree
public import CFSG.RankThree.PartOne.K133.Leaf2
public import CFSG.RankThree.PartOne.K133.MaxItems
import CFSG.Adapters.LinearCatalog
import CFSG.Adapters.ClassicalCatalogLinearUnitary
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.K133.Item1
public import CFSG.RankThree.PartOne.K133.KleinSL2
public import CFSG.RankThree.PartOne.K133.SylowKill
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.S11.TwoActionWiring
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem no_L2_centralizer_of_equiv {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (M : Subgroup (GL (Fin 3) K)) (e1 : X ≃* StatedProj M) {c : X}
    (hc1 : c ≠ 1) {g : ℕ} {Kb : Subgroup X} (hKc : Kb ≤ Subgroup.centralizer ({c} : Set X))
    (hKmodel : StatedClassicalModel Kb .PSL 2 2 g) : False := by
  classical
  obtain ⟨hKs, hKne⟩ := simple_nonab_of_model hKmodel
  obtain ⟨hf2, F, hF, hFin, hchar, hcardF, ⟨eK⟩⟩ := S15K.exists_mulEquiv_sl2_of_model hKmodel
  obtain ⟨V₀, hV₀el, hV₀c⟩ := exists_klein_four_sl2 (F := F) hf2 hcardF
  set K' : Subgroup (StatedProj M) := Kb.map e1.toMonoidHom with hK'
  let eKK : ↥Kb ≃* ↥K' := Subgroup.equivMapOfInjective Kb e1.toMonoidHom e1.injective
  have := hKs
  have : IsSimpleGroup ↥K' := eKK.symm.isSimpleGroup
  have hK'ne : ∃ a b : ↥K', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKne
    exact ⟨eKK a, eKK b, fun h => hab (eKK.injective (by rw [map_mul, map_mul]; exact h))⟩
  set V : Subgroup (StatedProj M) := ((V₀.map eK.symm.toMonoidHom).map Kb.subtype).map
    e1.toMonoidHom with hV
  have hVK : V ≤ K' := Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hVel : IsElementaryAbelian 2 ↥V := by
    have h1 : IsElementaryAbelian 2 ↥(V₀.map eK.symm.toMonoidHom) := by
      have := hV₀el
      exact IsElementaryAbelian.map eK.symm.toMonoidHom
    have h2' : IsElementaryAbelian 2 ↥((V₀.map eK.symm.toMonoidHom).map Kb.subtype) := by
      have := h1
      exact IsElementaryAbelian.map Kb.subtype
    have := h2'
    exact IsElementaryAbelian.map e1.toMonoidHom
  have hVc : Nat.card V = 4 := by
    rw [hV, Subgroup.card_map_of_injective e1.injective,
      Subgroup.card_map_of_injective Kb.subtype_injective,
      Subgroup.card_map_of_injective eK.symm.injective, hV₀c]
  have hcomm : ∀ k ∈ K', e1 c * k = k * e1 c := by
    intro k hk
    obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.1 hk
    have := Subgroup.mem_centralizer_singleton_iff.1 (hKc hk₀)
    show e1 c * e1 k₀ = e1 k₀ * e1 c
    rw [← map_mul, ← map_mul]
    exact congrArg e1 this.symm
  exact statedProj_three_no_klein h2 M (e1 c) (fun h => hc1 (e1.injective (by rw [h, map_one])))
    K' hK'ne V hVK hVel hVc hcomm

theorem row8U3Item_one : Row8U3Item 1 := by
  classical
  intro Q _ _ p g Ē hX h
  exfalso
  obtain ⟨c, x, K, hc1, hcp, hKc, hKmodel, hxK, hxo, hEel, hEcard⟩ := h.exists_T
  obtain ⟨q, hq2, he3, ⟨hv, ⟨e0⟩⟩ | ⟨hv, ⟨e0⟩⟩⟩ := hX
  ·
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    let Kf := GaloisField q.p q.exponent
    have e1 : (Q ⧸ Subgroup.center Q) ≃* StatedProj (StatedSL 3 Kf) :=
      (e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj 3 Kf)
    have h2 : (2 : Kf) ≠ 0 := by
      intro h0
      have := (CharP.cast_eq_zero_iff Kf q.p 2).1 (by simpa using h0)
      exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 this)
    exact no_L2_centralizer_of_equiv h2 (StatedSL 3 Kf) e1 hc1 hKc hKmodel
  ·
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have e1 := e0.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)
    have h2 : (2 : GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩)
        (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩)) ≠ 0 := by
      intro h0
      have hℓ : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p := by
        simp [ValidLieTypeIndex.characteristic]
      have := (CharP.cast_eq_zero_iff _ (ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩) 2).1
        (by simpa using h0)
      rw [hℓ] at this
      exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 this)
    exact no_L2_centralizer_of_equiv h2 _ e1 hc1 hKc hKmodel

end CFSG.RankThree.PartOne.Q1327T
