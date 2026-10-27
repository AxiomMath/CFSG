module

import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProofTools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec16.Item163Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step163LeA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ∀ (a : G) (La : Subgroup G),
      Subgroup.zpowers a ∈ omegaA A → La ∈ lA A a → MeetsY4 A (lB A) La Y →
      Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A a →
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))) →
        La ≤ Y

variable {G : Type} [Group G] [Finite G]

theorem le_of_omegaA_eq_singleton
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (hΩ : omegaA A = {Subgroup.zpowers c})
    (h1514 : Item1514 A (lB A) c L) (hU35 : Step163U35) (h142 : Concl142 A (lB A))
    (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A)) (h1411 : Item1411_1 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) (hm : MeetsY4 A (lB A) L Y) : L ≤ Y := by
  refine le_of_forall_cover h hΩ h142 h153 hobs h1411 hY fun w hwA hwL => ?_
  have hY' : Y.map (MulAut.conj w).toMonoidHom ∈ scriptY0Star A (lB A) :=
    map_conj_mem_scriptY0Star hwA hY
  have hm' : MeetsY4 A (lB A) L (Y.map (MulAut.conj w).toMonoidHom) := by
    obtain ⟨X, hX, hXLY⟩ := hm
    refine ⟨X.map (MulAut.conj w).toMonoidHom, map_conj_mem_scriptY4 hwA hX, ?_⟩
    rw [← hwL, ← Subgroup.map_inf _ _ _ (MulAut.conj w).injective]
    exact Subgroup.map_mono hXLY
  rcases h1514 _ hY' hm' with ⟨-, hc, -⟩ | ⟨-, -, hT, -⟩ | h3
  · exact hc
  · exfalso
    have h1 := hT.1
    rw [hΩ, Set.ncard_singleton] at h1
    omega
  · exact (hU35 G A c L h _ hY' hm' h3).elim

end CFSG.RankThree.PartTwo.Sec16
