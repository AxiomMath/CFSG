module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeCoverFrame
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPerfect
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSplit
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem perfect_le_normalizer_Lf_of_three_calC
    (d : SylowThreeData G)
    (hcalC : ∀ i, d.Lf i ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC d.M)
    (hLf : Function.Injective d.Lf)
    (hM3 : CFSG.Open.pRank 3 d.M ≤ 3)
    {X : Subgroup G} (hXM : X ≤ d.M) (hXperf : Group.IsPerfect ↥X) :
    ∀ i : Fin 3, X ≤ Subgroup.normalizer (d.Lf i : Set G) := by
  classical
  have hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j := by
    intro m hm i
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.map_conj_mem_three_calC_of_pRank_le_three
      d.Lf hcalC hLf d.hrank hM3 hm i
  let ρ : ↥X →* Equiv.Perm (Fin 3) :=
    (d.permHom hLf hperm).comp (Subgroup.inclusion hXM)
  have hρ : ∀ g : ↥X, ρ g = 1 := by
    intro g
    have hfin : Finite (Set.univ : Set (Fin 3)) :=
      (Set.finite_univ : (Set.univ : Set (Fin 3)).Finite).to_subtype
    have hfix := @CFSG.RankThree.PartTwo.Sec8.Item8KFacts3.fixes_of_isPerfect
      (↥X) (Fin 3) _ ρ (⊤) (Group.IsPerfect.top_iff.mpr hXperf)
      (Set.univ) hfin (by rw [Nat.card_univ, Nat.card_fin]; norm_num)
      (fun h _ y _ => Set.mem_univ _)
    ext y
    simpa using congrArg Fin.val (hfix g (Subgroup.mem_top g) y (Set.mem_univ y))
  intro i x hx
  let xX : ↥X := ⟨x, hx⟩
  have hfix : d.permHom hLf hperm (Subgroup.inclusion hXM xX) i = i := by
    have h2 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ i) (hρ xX)
    simpa [ρ] using h2
  have hnorm : ((Subgroup.inclusion hXM xX : ↥d.M) : G) ∈
      Subgroup.normalizer (d.Lf i : Set G) :=
    (mem_normalizer_Lf_iff d hLf hperm (Subgroup.inclusion hXM xX) i).mpr hfix
  simpa using hnorm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData
