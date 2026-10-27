module

public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoClass
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.Open.StatedAPI
import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoLin
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S1469Three
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S146R3
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5S1514
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.GoldschmidtCTKFamCore
public import Certificates.Certificate8026Base
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.CTK (TwoGroupsClassTwo)
open scoped commutatorElement

section Linear

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem twoGroupsClassTwo_specialLinear_three :
    TwoGroupsClassTwo (SpecialLinearGroup (Fin 3) K) := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  refine CFSG.Quasithin.H13.CTK.TwoGroupsClassTwo.of_sylow P fun x hx y hy z hz => ?_
  rw [hP] at hx hy hz
  exact CFSG.Quasithin.H13.CTK.unitriangular3_class_two hx hy hz

theorem commutator_three_eq_one_of_isPGroup_gl {E : Subgroup (GL (Fin 3) K)}
    (hE : IsPGroup 2 E) (hSL : E ≤ StatedSL 3 K) {a b c : GL (Fin 3) K} (ha : a ∈ E)
    (hb : b ∈ E) (hc : c ∈ E) : ⁅⁅a, b⁆, c⁆ = 1 := by
  have hR : IsPGroup 2 (E.comap (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K)) :=
    hE.comap_of_injective _ SpecialLinearGroup.toGL_injective
  have hlift : ∀ w ∈ E, ∃ s : SpecialLinearGroup (Fin 3) K,
      s ∈ E.comap (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K) ∧
        SpecialLinearGroup.toGL s = w := by
    intro w hw
    have hw' : w ∈ StatedSL 3 K := hSL hw
    rw [statedSL_eq_range_toGL] at hw'
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 hw'
    exact ⟨s, by rw [Subgroup.mem_comap, hs]; exact hw, hs⟩
  obtain ⟨s, hs, rfl⟩ := hlift a ha
  obtain ⟨t, ht, rfl⟩ := hlift b hb
  obtain ⟨u, hu, rfl⟩ := hlift c hc
  rw [← map_commutatorElement, ← map_commutatorElement,
    twoGroupsClassTwo_specialLinear_three _ hR s hs t ht u hu, map_one]

theorem twoGroupsClassTwo_statedProj {H : Subgroup (GL (Fin 3) K)} (hH : H ≤ StatedSL 3 K) :
    TwoGroupsClassTwo (StatedProj H) := by
  intro P hP x hx y hy z hz
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE, hEP⟩ := CFSG.RankThree.PartTwo.Sec17.Proof176Steps.exists_isPGroup_map_eq
    ((StatedScalars (Fin 3) K).subgroupOf H) hP
  rw [← hEP] at hx hy hz
  obtain ⟨ex, hex, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨ey, hey, rfl⟩ := Subgroup.mem_map.1 hy
  obtain ⟨ez, hez, rfl⟩ := Subgroup.mem_map.1 hz
  have hmap : IsPGroup 2 (E.map H.subtype) := hE.map _
  have hle : E.map H.subtype ≤ StatedSL 3 K := fun w hw => by
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.1 hw
    exact hH e.2
  have key := commutator_three_eq_one_of_isPGroup_gl hmap hle (Subgroup.mem_map_of_mem _ hex)
    (Subgroup.mem_map_of_mem _ hey) (Subgroup.mem_map_of_mem _ hez)
  have h1 : ⁅⁅ex, ey⁆, ez⁆ = 1 := Subtype.ext (by simpa [commutatorElement_def] using key)
  rw [← map_commutatorElement, ← map_commutatorElement, h1, map_one]

end Linear

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
