module

public import CFSG.RankThree.PartTwo.Census.Sporadic.NotCharTwoFacts
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.ON
public import CFSG.Sporadic.ON
public import Certificates.Certificate8162

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem onNC2_check :
    ∃ (t g x : NativeSporadic.ON) (S : Subgroup NativeSporadic.ON),
      orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 9 ∧
      g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
      ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x :=
  Certificates.certificate8162

theorem not_isCharTwoType_ON
    [Finite NativeSporadic.ON] :
    ¬ CFSG.Assembly.IsCharTwoType NativeSporadic.ON :=
  not_isCharTwoType_of_nc2Facts onNC2_check (by
    rw [show Nat.card NativeSporadic.ON = 460815505920 from CFSG.Sporadic.ON.card_ON,
      factorization_two_of_eq (show 460815505920 = 2 ^ 9 * 900030285 by norm_num) (by norm_num)])

theorem excluded433_ON :
    Excluded433 (.sporadic .ONan) :=
  excluded433_sporadic_of_not_isCharTwoType (T := NativeSporadic.Carrier .ONan)
    (fun _ => CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_ON) not_isCharTwoType_ON

end CFSG.RankThree.PartTwo.Census
