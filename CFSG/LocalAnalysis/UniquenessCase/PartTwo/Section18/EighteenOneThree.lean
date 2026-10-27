module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyEight
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bar
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASIn

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem concl18_1_3_of_no_calO {D : Data G} {V₀ V : Subgroup G} (hH : Hyp6H D.M V₀ V)
    (hV₀ : V₀ ≠ ⊥)
    (hr : ∀ n : ℕ, n < mBar D.M V₀ V hH.elemAbelian → (n : ℕ∞) < rMV D.M V)
    (h2 : Concl18_1_2 D V₀ V hH.elemAbelian) :
    Concl18_1_3 D V₀ V hH.elemAbelian := by
  have hV := hH.elemAbelian
  have hno : ∀ n, n < mBar D.M V₀ V hV → ∀ g : G, ¬ InCalO1 n D.M V₀ V g := by
    intro n hn g hg
    have hmem : conjSubgroup V g ∈ calO n D.M V₀ V := ⟨g, rfl, hg.1⟩
    rw [h2 n hn] at hmem
    exact hmem
  intro H S i j n _ hS hijn hn
  have hS' : IsSylowIn 2 S H := isSylowOf_two_iff_isSylowIn.1 hS
  rw [S17.Wi_eq_wClos i S V hV, S17.Ci_eq_cClos n S V hV]
  refine ⟨fun hE => ?_, fun hF => ?_⟩
  · have hE' : E1.InE j H := (E1.inE_subgroupOf j H).2 (inE_top_of_inEGroup j hE)
    exact (TwelveEighteen.six_thirteen_two_of_no_calO1_gen hH hV₀ (i := i) (n := j) (k := n)
      hijn.le (hr n hn) hn (hno n hn) hS' hE').symm
  · rcases TwelveEighteen.twelve_eighteen_three_of_no_calO1 hH hV₀ (i := i) (n := j) (k := n)
      hijn.le (hr n hn) hn (hno n hn) hS' hF with hN | hC
    · left
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer ((E3.wClos_le i S).trans hS'.le)).2 hN
    · right
      rwa [oUpperTwo_eq_twoResidual]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
