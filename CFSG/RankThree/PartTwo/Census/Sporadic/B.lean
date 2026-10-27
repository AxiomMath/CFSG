module

public import CFSG.RankThree.PartTwo.Census.Sporadic.BBridge
public import CFSG.RankThree.PartTwo.Census.Sporadic.RankFourCert
public import CFSG.Certificates.Kernel.BabyMonster.E35B

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint

theorem four_le_localRank_three_B [Finite NativeSporadic.B] :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 NativeSporadic.B := by
  obtain ⟨E, T, hE, hc, hT, hT2, hET⟩ := CFSG.KC.BM.E35Group.attained_B
  exact (by norm_num : 4 ≤ 5).trans (le_localRank_of_le_normalizer Nat.prime_three hT hT2 hE hc hET)

theorem nontrivial_B : Nontrivial NativeSporadic.B := by
  obtain ⟨-, T, -, -, hT, -⟩ := CFSG.KC.BM.E35Group.attained_B
  obtain ⟨t, -, ht1⟩ := T.bot_or_exists_ne_one.resolve_left hT
  exact ⟨⟨t, 1, ht1⟩⟩

theorem excluded433_B :
    Excluded433 (.sporadic .B) :=
  @excluded433_sporadic_of_four_le_localRank_three .B NativeSporadic.B Units.instGroup
    (fun h => @nonempty_mulEquiv_B h nontrivial_B) four_le_localRank_three_B

end CFSG.RankThree.PartTwo.Census
