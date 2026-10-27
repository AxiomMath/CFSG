module

public import CFSG.RankThree.PartTwo.Census.Sporadic.NotCharTwoFacts
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Co3
public import Certificates.Certificate8155

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem co3NC2_check :
    ∃ (t g x : NativeSporadic.Co3) (S : Subgroup NativeSporadic.Co3),
      orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 10 ∧
      g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
      ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x :=
  Certificates.certificate8155

theorem not_isCharTwoType_Co3
    [Finite NativeSporadic.Co3] :
    ¬ CFSG.Assembly.IsCharTwoType NativeSporadic.Co3 :=
  not_isCharTwoType_of_nc2Facts co3NC2_check (by
    rw [show Nat.card NativeSporadic.Co3 = 495766656000 from CFSG.Sporadic.Co3.card_Co3,
      factorization_two_of_eq (show 495766656000 = 2 ^ 10 * 484147125 by norm_num) (by norm_num)])

theorem excluded433_Co3 :
    Excluded433 (.sporadic .Co3) :=
  excluded433_sporadic_of_not_isCharTwoType (T := NativeSporadic.Carrier .Co3)
    (fun _ => CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Co3) not_isCharTwoType_Co3

end CFSG.RankThree.PartTwo.Census
