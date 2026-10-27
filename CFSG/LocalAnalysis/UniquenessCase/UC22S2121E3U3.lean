module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Layer13
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.GH74.KGroups.CoverEven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC1K337
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s2121e3u3_false (he : CFSG.Open.evenRank G ≤ 3) {D : Data G}
    (hns : PartTwo.s13_NormalSimple (Bar2 D.M)) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K) {p n m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : IsPowTwo n) (hU : IsU3 (Bar2 L) n) (h2n : ¬ p ∣ 2 ^ (2 * n) - 1)
    (hpL : p ∣ Nat.card (barImage D.M L)) (hm : IsPowTwo m)
    (hKs : IsL2 (Bar2 K) m ∨ IsU3 (Bar2 K) m) (hpK : p ∣ Nat.card (barImage D.M K)) : False := by
  have hn2 : 2 ≤ n := PartTwo.s13_two_le_of_isU3 hU
  have hp3 : p ≠ 3 := by
    rintro rfl
    apply h2n
    have h : 3 ∣ 4 ^ n - 1 := by simpa using Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := n)
    rwa [show 2 ^ (2 * n) = 4 ^ n by rw [pow_mul]; norm_num]
  obtain ⟨e₁⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even hn2 hU
  obtain ⟨φL⟩ := PartTwo.s13_bar_equiv hL
  obtain ⟨φK⟩ := PartTwo.s13_bar_equiv hK
  have hpU : p ∣ Nat.card (CFSG.Open.PSU3 2 n) := by
    rwa [← Nat.card_congr e₁.toEquiv, Nat.card_congr φL.toEquiv]
  have h3n : p ∣ 2 ^ (3 * n) + 1 := by
    rcases (CFSG.SignalizerFunctorTheorem.CatalogBridge.prime_dvd_card_psu3_iff (by omega) hp
      hp3).mp hpU with h | h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
    · exact absurd h h2n
    · exact h
  have hz3 : (2 : ZMod p) ^ (3 * n) = -1 := by
    have h0 : ((2 ^ (3 * n) + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h3n
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hz1 : (2 : ZMod p) ^ n ≠ -1 := by
    intro h
    apply h2n
    have h1 : (2 : ZMod p) ^ (2 * n) = 1 := by rw [mul_comm, pow_mul, h, neg_one_sq]
    have h0 : ((2 ^ (2 * n) - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      rw [h1, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  have hpK' : p ∣ Nat.card (Bar2 K) := by rwa [Nat.card_congr φK.toEquiv]
  have hKU : IsU3 (Bar2 K) n :=
    (InS3.k337_holds p hp hp2 n m hn hm).2.2.2.1 hz3 hz1 (Bar2 K) hKs hpK'
  obtain ⟨e₂⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even hn2 hKU
  obtain ⟨r, hr, hr2, h2r⟩ :=
    CFSG.QuasithinUnique.Vol2Native.EvenWit.exists_two_le_pRank_psu_three_even hn2
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hU)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2r
  have hrL : 2 ≤ CFSG.Open.pRank r (barImage D.M L) := by
    rw [PartTwo.s13_pRank_barImage hr hr2 (PartTwo.s13_le_of_mem_calC hL),
      ← pRank_bar2_eq_of_odd hr hr2]
    exact h2r
  have hrK : 2 ≤ CFSG.Open.pRank r (barImage D.M K) := by
    rw [PartTwo.s13_pRank_barImage hr hr2 (PartTwo.s13_le_of_mem_calC hK),
      ← pRank_bar2_eq_of_odd hr hr2,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt (e₂.trans e₁.symm)]
    exact h2r
  have hC₁ := PartTwo.s13_barImage_isComponent hL
  have hcomm := PartTwo.s13_components_commute hns (PartTwo.s13_barImage_isComponent hK) hC₁
    hne.symm
  have hdisj : barImage D.M L ⊓ barImage D.M K = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ hcomm).trans
      (PartTwo.s13_Layer13_inf_centralizer_eq_bot hns hC₁).le)
  have hsum := PartTwo.s13_pRank_sup_eq_add hr hcomm hdisj
  have hle := CFSG.SectionRank.pRank_mono hr.one_lt
    (le_top : barImage D.M L ⊔ barImage D.M K ≤ ⊤)
  rw [PartTwo.s13_pRank_bar_top hr hr2] at hle
  have hloc := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank r hr hr2 D.M
    D.maxLocal.1
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
