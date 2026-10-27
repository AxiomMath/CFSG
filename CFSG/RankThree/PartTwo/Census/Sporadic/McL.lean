module

public import CFSG.RankThree.PartTwo.Census.Sporadic.NotCharTwoFacts
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.McL
public import Certificates.Certificate8161

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem mclNC2_check :
    ∃ (t g x : NativeSporadic.McL) (S : Subgroup NativeSporadic.McL),
      orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 7 ∧
      g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
      ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x :=
  Certificates.certificate8161

theorem not_isCharTwoType_McL
    [Finite NativeSporadic.McL] :
    ¬ CFSG.Assembly.IsCharTwoType NativeSporadic.McL :=
  not_isCharTwoType_of_nc2Facts mclNC2_check (by
    rw [show Nat.card NativeSporadic.McL = 898128000 from CFSG.Sporadic.McL.card_McL,
      factorization_two_of_eq (show 898128000 = 2 ^ 7 * 7016625 by norm_num) (by norm_num)])

theorem excluded433_McL :
    Excluded433 (.sporadic .McL) :=
  excluded433_sporadic_of_not_isCharTwoType (T := NativeSporadic.Carrier .McL)
    (fun _ => CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_McL) not_isCharTwoType_McL

end CFSG.RankThree.PartTwo.Census
