module

public import CFSG.RankThree.PartTwo.Census.Sporadic.NotCharTwoFacts
public import CFSG.RankThree.PartTwo.Census.Sporadic.Centralizer
public import CFSG.Sporadic.HN.Local.Main
public import CFSG.Sporadic.Bridge.HNSurj
public import Certificates.Certificate8158

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem hnNC2_check :
    ∃ (t g x : NativeSporadic.HN) (S : Subgroup NativeSporadic.HN),
      orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 11 ∧
      g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
      (∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x) ∧
      11 ∣ Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.HN)) :=
  Certificates.certificate8158

open CFSG.Sporadic.HN.Local in
theorem card_centralizer_HN_of_eleven_dvd
    {u : NativeSporadic.HN} (hu : orderOf u = 2)
    (h11 : 11 ∣ Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.HN))) :
    Nat.card (Subgroup.centralizer ({u} : Set NativeSporadic.HN)) = 177408000 := by
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    omega
  rcases hn_involution_cover u hu2 hu1 with h | h
  · rw [← card_centralizer_of_isConj h, hn_card_centralizer_t2]
  · rw [← card_centralizer_of_isConj h, hn_card_centralizer_t4] at h11
    exact absurd h11 (by decide)

theorem not_isCharTwoType_HN
    [Finite NativeSporadic.HN] :
    ¬ CFSG.Assembly.IsCharTwoType NativeSporadic.HN :=
  not_isCharTwoType_of_nc2Facts' hnNC2_check fun u hu hq => by
    rw [card_centralizer_HN_of_eleven_dvd hu hq,
      factorization_two_of_eq (show 177408000 = 2 ^ 11 * 86625 by norm_num) (by norm_num)]

theorem excluded433_HN :
    Excluded433 (.sporadic .HN) :=
  @excluded433_sporadic_of_not_isCharTwoType .HN NativeSporadic.HN Units.instGroup
    (fun _ => CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv.map MulEquiv.symm) not_isCharTwoType_HN

end CFSG.RankThree.PartTwo.Census
