module

public import CFSG.RankThree.PartTwo.Census.Sporadic.NotCharTwoFacts
public import CFSG.RankThree.PartTwo.Census.Sporadic.LyBridge
public import Certificates.Certificate8159

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem lyNC2_check :
    ∃ (t g x : NativeSporadic.Ly) (S : Subgroup NativeSporadic.Ly),
      orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 8 ∧
      g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
      ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x :=
  Certificates.certificate8159

theorem not_isCharTwoType_Ly
    [Finite NativeSporadic.Ly] :
    ¬ CFSG.Assembly.IsCharTwoType NativeSporadic.Ly :=
  not_isCharTwoType_of_nc2Facts lyNC2_check (by
    rw [show Nat.card NativeSporadic.Ly = 51765179004000000 from CFSG.Sporadic.Ly.card_Ly,
      factorization_two_of_eq (show 51765179004000000 = 2 ^ 8 * 202207730484375 by norm_num)
        (by norm_num)])

theorem excluded433_Ly :
    Excluded433 (.sporadic .Ly) :=
  @excluded433_sporadic_of_not_isCharTwoType .Ly NativeSporadic.Ly Units.instGroup
    (fun h => @nonempty_mulEquiv_Ly h) not_isCharTwoType_Ly

end CFSG.RankThree.PartTwo.Census
