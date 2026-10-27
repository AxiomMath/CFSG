module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofX
public import CFSG.RankThree.PartTwo.Sec17.C174Five
public import CFSG.RankThree.PartTwo.Sec13.Item134Unconditional
public import CFSG.RankThree.PartTwo.Sec14.Ronan149Holds
public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideRank
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJYFactsOpen

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec15

theorem j2AutFixNine_holds :
    J2AutFixNine :=
  fun X _ _ hX E hE σ hσ hfix =>
    CFSG.RankThree.PartTwo.Sec17.Proof17Res3.j2_aut_eq_one_of_coprime hX hE hσ hfix

theorem j2HasE25_holds : J2HasE25 := by
  obtain ⟨x, y, -, hx, hy, hxy, hcard, -⟩ := CFSG.SectionRank.J2_sylow5_square_witness
  have hcomm : ∀ a ∈ ({x, y} : Set CFSG.Blueprint.NativeSporadic.J2),
      ∀ b ∈ ({x, y} : Set CFSG.Blueprint.NativeSporadic.J2), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl
  refine ⟨Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.J2),
    CFSG.AGLEmbedding.SPLMSide.elemAbelian_closure ?_ ?_, ?_⟩
  · intro a ha b hb _
    exact hcomm a ha b hb
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  · simpa using hcard

theorem hjThetaS14_of_item135
    (h135 : Sec13.Item135) : HJThetaS14 :=
  fun G _ _ A c L h hJ =>
    CFSG.RankThree.PartTwo.Sec17.C174.theta_eq_pCore_two_of_j2 h135 h hJ

theorem step155HostE0WRes1TypeFBarLe_hj_holds
    :
    Step155HostE0WRes1TypeFBarLe
      (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) Res1OpenType :=
  step155HostE0WRes1TypeFBarLe_hj
    CFSG.RankThree.PartTwo.Sec14.Ronan149.item149S14_holds
    CFSG.RankThree.PartTwo.Sec14.Ronan148M.concl142S14_holds
    j2AutFixNine_holds j2HasE25_holds CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15
    (hjThetaS14_of_item135 CFSG.RankThree.PartTwo.item135_holds)
    (fun _ _ _ hY => res1HJYFacts_of_res1OpenType hY)

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
