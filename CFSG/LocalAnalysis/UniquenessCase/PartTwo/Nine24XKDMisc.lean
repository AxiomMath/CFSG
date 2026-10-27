module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XKDDefs
import CFSG.Adapters.LieModelSimple
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Quasithin.Vol2.F134J1
import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

private theorem n924x_card_isL2 {S : Type} [Group S] {m : ℕ} (h : IsL2 S m) :
    Nat.card S = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 2 2 m :=
    h.statedClassicalModel (by decide)
  have hf : 1 ≤ m := hmodel.1.2.1
  have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).1 rfl
  have hodd : Odd (2 ^ m - 1) := by
    simpa using CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hf (n := 1) le_rfl
  have hgcd : Nat.gcd 2 (2 ^ m - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [h1]
  unfold CFSG.Open.ordA
  norm_num [Finset.Icc_self, hgcd]

private theorem n924x_four_dvd_of_dvd_four_mul {d n : ℕ} (h : d ∣ 4 * n) (h2 : ¬ d ∣ 2 * n) :
    4 ∣ d := by
  by_contra h4
  have hd2 : 2 ∣ d := by
    by_contra hodd2
    have hodd : Odd d := Nat.not_even_iff_odd.mp (by rwa [← even_iff_two_dvd] at hodd2)
    have hcop : Nat.Coprime d 4 := by
      have h2c : Nat.Coprime d 2 := Nat.coprime_comm.mpr (Nat.coprime_two_left.mpr hodd)
      simpa using h2c.pow_right 2
    have hdn : d ∣ n := hcop.dvd_of_dvd_mul_left h
    exact h2 (by simpa [mul_comm] using hdn.mul_right 2)
  obtain ⟨d', rfl⟩ := hd2
  have hd'odd : Odd d' := by
    by_contra hodd
    have h2d' : 2 ∣ d' := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    obtain ⟨k, hk⟩ := h2d'
    exact h4 ⟨k, by rw [hk]; ring⟩
  have hd'n2 : d' ∣ 2 * n := by
    have hh : 2 * d' ∣ 2 * (2 * n) := by
      have := h
      rwa [show 4 * n = 2 * (2 * n) from by ring] at this
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 hh
  have hd'n : d' ∣ n := by
    have hcop : Nat.Coprime d' 2 := Nat.coprime_comm.mpr (Nat.coprime_two_left.mpr hd'odd)
    exact hcop.dvd_of_dvd_mul_left hd'n2
  obtain ⟨j, hj⟩ := hd'n
  exact h2 ⟨j, by rw [hj]; ring⟩

theorem noL2Section_of_isCyclic {L : Type} [Group L] (hL : IsCyclic L) : NoL2Section L := by
  intro X n hn hL2
  haveI : IsCyclic L := hL
  haveI : IsCyclic X := inferInstance
  have hcyc : IsCyclic (Bar2 X) :=
    isCyclic_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 X)) (QuotientGroup.mk'_surjective _)
  haveI : IsMulCommutative (Bar2 X) := hcyc.isMulCommutative
  haveI : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have hprime : (Nat.card (Bar2 X)).Prime :=
    (Group.is_simple_iff_prime_card (α := Bar2 X)).1 inferInstance
  have hcard : Nat.card (Bar2 X) = 2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) := n924x_card_isL2 hL2
  have hdvd : 2 ^ (2 * n) ∣ Nat.card (Bar2 X) := by
    rw [hcard]; exact dvd_mul_right _ _
  have h2dvd : 2 ∣ Nat.card (Bar2 X) :=
    (Nat.pow_dvd_pow 2 (by omega : 1 ≤ 2 * n)).trans hdvd
  have hcard2 : Nat.card (Bar2 X) = 2 := by
    rcases hprime.eq_two_or_odd' with h | hodd
    · exact h
    · exact absurd (even_iff_two_dvd.mpr h2dvd) (Nat.not_even_iff_odd.mpr hodd)
  have hle : 2 ^ (2 * n) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (hcard2 ▸ hdvd)
  have hge : 16 ≤ 2 ^ (2 * n) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact absurd (le_trans hge hle) (by norm_num)

theorem noL2Section_of_isJ1 {L : Type} [Group L] [Finite L] (hL : IsSpor L .J1) :
    NoL2Section L := by
  intro X n hn hL2
  obtain ⟨e⟩ : Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) := hL
  have hcardL : Nat.card L = 175560 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Quasithin.F134.card_carrier_J1
  have hcard : Nat.card (Bar2 X) = 2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) := n924x_card_isL2 hL2
  have hdvd1 : 2 ^ (2 * n) ∣ Nat.card (Bar2 X) := by
    rw [hcard]; exact dvd_mul_right _ _
  have hdvd2 : Nat.card (Bar2 X) ∣ Nat.card X :=
    Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥X)
  have hdvd3 : Nat.card X ∣ Nat.card L := Subgroup.card_subgroup_dvd_card X
  have hdvd : 2 ^ (2 * n) ∣ 175560 := by
    rw [← hcardL]
    exact hdvd1.trans (hdvd2.trans hdvd3)
  have h16 : 2 ^ 4 ∣ 2 ^ (2 * n) := Nat.pow_dvd_pow 2 (by omega)
  exact absurd (h16.trans hdvd) (by norm_num)

theorem noL2Section_of_psl3_two_odd {L : Type} [Group L] [Finite L] {f : ℕ} (hf : Odd f)
    (hL : LieModel L .PSL 3 2 f) : NoL2Section L := by
  intro X n hn hL2
  have hcardX : Nat.card (Bar2 X) = 2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) := n924x_card_isL2 hL2
  obtain ⟨ℓ, hℓprime, hℓdvd⟩ :=
    Nat.exists_prime_and_dvd (by
      intro h
      exact (Nat.pos_iff_ne_zero.mp (by positivity : 0 < 2 ^ (2 * n))) (Nat.succ.inj h))
  have hℓne2 : ℓ ≠ 2 := by
    rintro rfl
    have hodd : Odd (2 ^ (2 * n) + 1) :=
      ((even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega : 2 * n ≠ 0)).add_one
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hℓdvd)
  have hpow : (2 : ZMod ℓ) ^ (2 * n) = -1 := by
    have hz : (((2 ^ (2 * n) + 1 : ℕ)) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hℓdvd
    push_cast at hz
    exact (add_eq_zero_iff_eq_neg).1 hz
  let d := orderOf (2 : ZMod ℓ)
  have hd4n : d ∣ 4 * n := by
    apply orderOf_dvd_of_pow_eq_one
    have h4 : (2 : ZMod ℓ) ^ (4 * n) = ((2 : ZMod ℓ) ^ (2 * n)) ^ 2 := by
      rw [show 4 * n = (2 * n) * 2 from by ring, pow_mul]
    rw [h4, hpow]
    norm_num
  have hd2n : ¬ d ∣ 2 * n := by
    intro hdiv
    have h1 : (2 : ZMod ℓ) ^ (2 * n) = 1 := (orderOf_dvd_iff_pow_eq_one).1 hdiv
    have hneg : (-1 : ZMod ℓ) = 1 := hpow.symm.trans h1
    have h2zero : (2 : ZMod ℓ) = 0 := by
      have h := congrArg (fun x : ZMod ℓ => x + 1) hneg
      rw [neg_add_cancel, one_add_one_eq_two] at h
      exact h.symm
    have hℓdvd2 : ℓ ∣ 2 := (ZMod.natCast_eq_zero_iff 2 ℓ).1 h2zero
    have hℓ2 : ℓ = 2 := le_antisymm (Nat.le_of_dvd (by norm_num) hℓdvd2) hℓprime.two_le
    exact hℓne2 hℓ2
  have h4d : 4 ∣ d := n924x_four_dvd_of_dvd_four_mul hd4n hd2n
  have hℓcardX : ℓ ∣ Nat.card (Bar2 X) := by
    rw [hcardX]
    have hx2 : ℓ ∣ (2 ^ (2 * n)) ^ 2 - 1 :=
      hℓdvd.trans (by
        have h := Nat.sq_sub_sq (2 ^ (2 * n)) 1
        simp only [one_pow] at h
        exact ⟨2 ^ (2 * n) - 1, h⟩)
    exact dvd_mul_of_dvd_right hx2 (2 ^ (2 * n))
  have hdvdL : Nat.card (Bar2 X) ∣ Nat.card L :=
    (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥X)).trans (Subgroup.card_subgroup_dvd_card X)
  have hcardL : Nat.card L = CFSG.Open.ordA 2 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).1 rfl
  have hℓord : ℓ ∣ CFSG.Open.ordA 2 (2 ^ f) := by
    rw [← hcardL]
    exact hℓcardX.trans hdvdL
  have hord_eq : CFSG.Open.ordA 2 (2 ^ f) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) / Nat.gcd 3 (2 ^ f - 1) := by
    unfold CFSG.Open.ordA
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1)]
    rw [Finset.Icc_self, Finset.prod_singleton]
  have hgN : Nat.gcd 3 (2 ^ f - 1) ∣
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
    have h1 : Nat.gcd 3 (2 ^ f - 1) ∣ 2 ^ f - 1 := Nat.gcd_dvd_right 3 _
    have h2 : 2 ^ f - 1 ∣ (2 ^ f) ^ 3 - 1 := Nat.sub_one_dvd_pow_sub_one (2 ^ f) 3
    have h3 : (2 ^ f) ^ 3 - 1 ∣ ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) := dvd_mul_left _ _
    have h4 : ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) ∣
        (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := dvd_mul_left _ _
    exact h1.trans (h2.trans (h3.trans h4))
  have hℓNg : ℓ ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) /
      Nat.gcd 3 (2 ^ f - 1) := by
    rw [hord_eq] at hℓord
    exact hℓord
  have hℓN : ℓ ∣ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
    have h1 : ℓ ∣ Nat.gcd 3 (2 ^ f - 1) *
        ((2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) / Nat.gcd 3 (2 ^ f - 1)) :=
      dvd_mul_of_dvd_right hℓNg _
    rw [Nat.mul_div_cancel' hgN] at h1
    exact h1
  have hℓAB : ℓ ∣ ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) := by
    rcases (hℓprime.dvd_mul).1 hℓN with h | h
    · exfalso
      have hℓ2f : ℓ ∣ 2 ^ f := hℓprime.dvd_of_dvd_pow h
      have hℓ2 : ℓ ∣ 2 := hℓprime.dvd_of_dvd_pow hℓ2f
      exact hℓne2 (le_antisymm (Nat.le_of_dvd (by norm_num) hℓ2) hℓprime.two_le)
    · exact h
  rcases (hℓprime.dvd_mul).1 hℓAB with h2 | h3
  · have h2f : (2 : ZMod ℓ) ^ (2 * f) = 1 := by
      have hz : (((2 ^ f) ^ 2 - 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h2
      have hp : 1 ≤ (2 ^ f) ^ 2 := by
        have : 0 < (2 ^ f) ^ 2 := by positivity
        omega
      rw [Nat.cast_sub hp] at hz
      simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hz
      have h1 : ((2 : ZMod ℓ) ^ f) ^ 2 = 1 := sub_eq_zero.mp hz
      rw [← pow_mul] at h1
      rwa [mul_comm] at h1
    have hd2f : d ∣ 2 * f := (orderOf_dvd_iff_pow_eq_one).2 h2f
    have h42f : 4 ∣ 2 * f := h4d.trans hd2f
    have h2f' : 2 ∣ f := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by simpa using h42f)
    exact (hf.ne_two_of_dvd_nat h2f') rfl
  · have h3f : (2 : ZMod ℓ) ^ (3 * f) = 1 := by
      have hz : (((2 ^ f) ^ 3 - 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h3
      have hp : 1 ≤ (2 ^ f) ^ 3 := by
        have : 0 < (2 ^ f) ^ 3 := by positivity
        omega
      rw [Nat.cast_sub hp] at hz
      simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hz
      have h1 : ((2 : ZMod ℓ) ^ f) ^ 3 = 1 := sub_eq_zero.mp hz
      rw [← pow_mul] at h1
      rwa [mul_comm] at h1
    have hd3f : d ∣ 3 * f := (orderOf_dvd_iff_pow_eq_one).2 h3f
    have h43f : 4 ∣ 3 * f := h4d.trans hd3f
    have h4f : 4 ∣ f := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 4 3) h43f
    have h2f' : 2 ∣ f := (show 2 ∣ 4 from by norm_num).trans h4f
    exact (hf.ne_two_of_dvd_nat h2f') rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
