module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3CtxDefs
public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.RankThree.PartOne.N143.T2LargeAll
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Amb
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Comp
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Cube
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Lem14
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Local
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Obs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Setup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {d : G}
  {K : Subgroup G}

theorem Res3Ctx.eq_one_of_noDatum
    (hND : Res3NoDatum) (h415 : Sec4.Item4_15) (hspor : SporadicModels131)
    (h41p : Sec4.Item4_1LargePrime) (h41a : Sec4.Item4_1LargeAll) (h : Res3Ctx A c L d K)
    (hT90 : ∀ x ∈ Subgroup.centralizer (A : Set G), (orderOf x).Prime →
      orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7)
    {X K' Y M T : Subgroup G} (hC : Ctx155 A X K' Y M T) {g : G}
    (hg : g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M)
    (hgZ : g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G))
    (hodd : Odd (orderOf g))
    (hCV : ∀ B : Subgroup G, IsHyperplane A B → B ≠ A ⊓ L →
      CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G) ≤
        Subgroup.centralizer ({g} : Set G)) :
    g = 1 := by
  by_contra hg1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := h.R.toSec14Std
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  have hgA : g ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hg.1
  obtain ⟨h14a, h14b, h14c⟩ := commutator_le_centralizer_of_hyperplanes hstd.isE27.1
    hstd.isE27.2 ⟨inf_le_left, by have := hstd.isE27.2; have := h.AL_card; omega⟩ h.c_mem
    (fun hc => h.c_notMem hc.2) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    (hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg.2) hgA hodd hCV
  exact Res3Q.false_of_noDatum hND
    { toRes3QBase := { toRes3QComp := h.res3QComp, toRes3QAmb := h.res3QAmb }
      fourHyp := h.sectionFourHyp_of_isQuasisimple h41p
      rank := h.localRank_lt h41a
      cube := h.cube h415 hspor
      primes := h.primes_of hT90
      toRes3QObs := h.res3QObs hC hgA hg hgZ hodd hCV hg1 h14a h14b h14c hT90 }

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
