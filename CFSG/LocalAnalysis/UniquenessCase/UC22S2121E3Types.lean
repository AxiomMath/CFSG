module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3Cartan
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankNT1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC1K337
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3U3
import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2121e3_dvd_of_isL2 {X : Type} [Group X] {n p : ℕ} (hX : IsL2 X n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X) : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
  rw [StatedAPI.card_of_statedClassicalModel_psl_two_two
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX), sq,
    mul_self_tsub_one] at hpX
  rcases hp.dvd_mul.mp hpX with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
  · exact (hp.dvd_mul.mp h).symm

theorem uc22s2121e3_not_cartan_of_Sp_r847E3
    (hSE : StronglyEmbeddedFive) (hThin : PartTwo.ThinList13) (hS : Standing G) (S : Setup G)
    (hS13 : PartTwo.Setting13 (PartTwo.Three.dataOfSetup hS S))
    (hSig : UC6S846.SigmaStd (PartTwo.Three.dataOfSetup hS S))
    (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ}
    (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig) (hp5 : 5 ≤ p) {B : Subgroup G}
    (hB : F13.Case136b (PartTwo.Three.dataOfSetup hS S) p B)
    (h1 : 1 ≤ CFSG.Open.pRank p (F13.Sp S.M p)) {L : Subgroup G} (hL : L ∈ calC S.M)
    (hpL : p ∣ Nat.card (barImage S.M L)) {n : ℕ} (hn : IsPowTwo n)
    (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) :
    ¬ (p ∣ 2 ^ n - 1 ∨ (IsU3 (Bar2 L) n ∧ p ∣ 2 ^ n + 1)) := fun hpn => by
  obtain ⟨y, hyN, hy, hyc⟩ := uc22s2121e3_exists_elem_Sp hThin hS13
    ((PartTwo.Three.dataOfSetup hS S).sig_prime p hp).1 hB h1
  exact uc22s2121e3_false_of_cartan_r847E3 hSE hThin hS S hS13 hSig h847T h847S hp hp5 hB hL hn
    hX hpn y.2 hyN hy
    (hyc _ (PartTwo.s13_mem_compsP.mpr ⟨PartTwo.s13_barImage_isComponent hL, hpL⟩))

theorem uc22s2121e3_isL2_of_isU3_r847E3 (hSE : StronglyEmbeddedFive)
    (hThin : PartTwo.ThinList13) (hS : Standing G) (S : Setup G)
    (hS13 : PartTwo.Setting13 (PartTwo.Three.dataOfSetup hS S))
    (hSig : UC6S846.SigmaStd (PartTwo.Three.dataOfSetup hS S))
    (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ}
    (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig) (hp5 : 5 ≤ p) {B : Subgroup G}
    (hB : F13.Case136b (PartTwo.Three.dataOfSetup hS S) p B) {L K : Subgroup G}
    (hL : L ∈ calC S.M) (hK : K ∈ calC S.M) (hne : barImage S.M L ≠ barImage S.M K) {n m : ℕ}
    (hn : IsPowTwo n) (hU : IsU3 (Bar2 L) n) (hpn : p ∣ 2 ^ n + 1) (hm : IsPowTwo m)
    (hY : IsL2 (Bar2 K) m ∨ IsU3 (Bar2 K) m) (hpK : p ∣ Nat.card (barImage S.M K)) :
    IsL2 (Bar2 K) n := by
  obtain ⟨hpp, hp2⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  have hcart := uc22s2121e3_false_of_two_cartan_r847E3 hSE hThin hS S hS13 hSig h847T h847S hp hp5
    hB hL hK hne hn (Or.inr hU) (Or.inr ⟨hU, hpn⟩) hm hY
  obtain ⟨φ⟩ := PartTwo.s13_bar_equiv hK
  have hpK' : p ∣ Nat.card (Bar2 K) := by rwa [Nat.card_congr φ.toEquiv]
  haveI : Fact p.Prime := ⟨hpp⟩
  have hz := S15.nt1_pow_eq_neg_one hpn
  have h337 := InS3.k337_holds p hpp hp2 n m hn hm
  rcases hY with hK2 | hKU
  · rcases uc22s2121e3_dvd_of_isL2 hK2 hpp hp2 hpK' with h | h
    · exact (hcart (Or.inl h)).elim
    · rw [h337.2.1 hz (S15.nt1_pow_eq_neg_one h)]
      exact hK2
  · have hd := (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (2 * m)).mpr
      (h337.2.2.1 hz (Bar2 K) hKU hpK')
    rw [two_mul, pow_add, mul_self_tsub_one] at hd
    rcases hpp.dvd_mul.mp hd with h | h
    · exact (hcart (Or.inr ⟨hKU, h⟩)).elim
    · exact (hcart (Or.inl h)).elim

theorem uc22s2121e3_isL2_of_Sp_r847E3 (hSE : StronglyEmbeddedFive)
    (hThin : PartTwo.ThinList13) (hS : Standing G) (S : Setup G)
    (hS13 : PartTwo.Setting13 (PartTwo.Three.dataOfSetup hS S))
    (hSig : UC6S846.SigmaStd (PartTwo.Three.dataOfSetup hS S))
    (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ}
    (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig) (hp5 : 5 ≤ p) {B : Subgroup G}
    (hB : F13.Case136b (PartTwo.Three.dataOfSetup hS S) p B)
    (h1 : 1 ≤ CFSG.Open.pRank p (F13.Sp S.M p)) {L K : Subgroup G} (hL : L ∈ calC S.M)
    (hK : K ∈ calC S.M) (hne : barImage S.M L ≠ barImage S.M K)
    (hpL : p ∣ Nat.card (barImage S.M L)) (hpK : p ∣ Nat.card (barImage S.M K)) {n m : ℕ}
    (hn : IsPowTwo n) (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) (hm : IsPowTwo m)
    (hY : IsL2 (Bar2 K) m ∨ IsU3 (Bar2 K) m) : IsL2 (Bar2 L) n ∧ p ∣ 2 ^ n + 1 := by
  obtain ⟨hpp, hp2⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  have hc := uc22s2121e3_not_cartan_of_Sp_r847E3 hSE hThin hS S hS13 hSig h847T h847S hp hp5 hB h1
    hL hpL hn hX
  rcases hX with hL2 | hU
  · obtain ⟨φ⟩ := PartTwo.s13_bar_equiv hL
    rcases uc22s2121e3_dvd_of_isL2 hL2 hpp hp2 (by rwa [Nat.card_congr φ.toEquiv]) with h | h
    exacts [(hc (Or.inl h)).elim, ⟨hL2, h⟩]
  · refine (uc22s2121e3u3_false hS.rank.le (PartTwo.s13_normalSimple hThin _ hS13) hL hK hne hpp
      hp2 hn hU (fun hd => ?_) hpL hm hY hpK).elim
    rw [two_mul, pow_add, mul_self_tsub_one] at hd
    rcases hpp.dvd_mul.mp hd with h | h
    exacts [hc (Or.inr ⟨hU, h⟩), hc (Or.inl h)]

end CFSG.LocalAnalysis.UniquenessCase.UC22
