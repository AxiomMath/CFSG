module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.L3OvDefs
import CFSG.GH74.GLS.IVK.Proofs2.Lemma18
import CFSG.Walter.PSL2Facts.Even
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open scoped MatrixGroups
open CFSG.BenderSuzuki.MatrixGroups

theorem l3OvDickson_holds : L3OvDickson := by
  intro F _ _ f hF hfodd H hHperfect hHne
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [← Nat.card_eq_fintype_card]; exact hF)
  let φ : SL(2, F) ≃* PSL2MatrixGroup F :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm
  let H' : Subgroup (PSL2MatrixGroup F) := H.map φ.toMonoidHom
  let eH : H ≃* H' := Subgroup.equivMapOfInjective H φ.toMonoidHom φ.injective
  have hH'ns : ¬ Group.IsSolvable H' := by
    intro hs
    haveI : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hHperfect
    haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hHne
    haveI := hs
    exact (Group.IsPerfect.not_isSolvable H)
      (Group.isSolvable_of_isSolvable_injective (f := eH.toMonoidHom) eH.injective)
  rcases CFSG.GH74.GLS.IVK.Proofs2.nonsolvable_cases (F := F) (p := 2) (f := f) hF H' hH'ns
    with ⟨-, h5⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  ·
    exfalso
    rcases h5 with h5 | h5
    · omega
    · have h4 : (2 ^ f) ^ 2 % 5 = 4 := by
        obtain ⟨k, rfl⟩ := hfodd
        have h : ((2 : ℕ) ^ (2 * k + 1)) ^ 2 = 4 * 16 ^ k := by
          rw [← pow_mul, show (2 * k + 1) * 2 = 4 * k + 2 by ring, pow_add, pow_mul]
          norm_num
          ring
        rw [h, Nat.mul_mod, Nat.pow_mod]
        norm_num
      have h5' : (2 ^ f) ^ 2 % 5 = 1 := by
        have h : (2 ^ f) ^ 2 % 5 = 1 % 5 := h5
        rw [Nat.mod_eq_of_lt (by norm_num : 1 < 5)] at h
        exact h
      omega
  ·
    have hoddm : Odd m := Odd.of_dvd_nat hfodd hm
    obtain ⟨k, hk⟩ := hfodd
    have hfpos : 0 < f := by omega
    have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm hfpos
    have hm0 : m ≠ 0 := by omega
    have hm1 : m ≠ 1 := by
      rintro rfl
      apply hH'ns
      haveI : Fintype (PSL2MatrixGroup (GaloisField 2 1)) :=
        Fintype.ofFinite (PSL2MatrixGroup (GaloisField 2 1))
      have h6 : Nat.card (PSL2MatrixGroup (GaloisField 2 1)) = 6 := by
        rw [CFSG.Walter.psl2_even_card (f := 1) one_ne_zero]
        norm_num
      have hpsl : Group.IsSolvable (PSL2MatrixGroup (GaloisField 2 1)) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
          (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) (by
            rw [← Nat.card_eq_fintype_card, h6]; norm_num)
      haveI := hpsl
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have hm3 : 3 ≤ m := by
      obtain ⟨j, hj⟩ := hoddm
      omega
    have hne1 : 2 ^ m - 1 ≠ 1 := by
      have h8 : 8 ≤ 2 ^ m := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
      omega
    obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd hne1
    have hoddsub : Odd (2 ^ m - 1) := by
      refine Nat.Even.sub_odd Nat.one_le_two_pow ?_ odd_one
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      rw [pow_succ]
      exact ⟨2 ^ j, by ring⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      have h1 := Nat.odd_iff.mp hoddsub
      have h0 := Nat.mod_eq_zero_of_dvd hrdvd
      omega
    have hr3 : r ≠ 3 := by
      rintro rfl
      have h2 : 2 ^ m % 3 = 2 := CFSG.two_pow_mod_three_of_odd hoddm
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have h0' : (2 ^ m - 1) % 3 = 1 := by omega
      have h0 := Nat.mod_eq_zero_of_dvd hrdvd
      omega
    have hr5 : 5 ≤ r := by
      have h2 := hrprime.two_le
      obtain ⟨j, hj⟩ := hrprime.odd_of_ne_two hr2
      omega
    have hcardH : Nat.card H = 2 ^ m * ((2 ^ m) ^ 2 - 1) :=
      calc Nat.card H = Nat.card H' := Nat.card_congr eH.toEquiv
        _ = Nat.card (PSL2MatrixGroup (GaloisField 2 m)) := Nat.card_congr e.toEquiv
        _ = 2 ^ m * ((2 ^ m) ^ 2 - 1) := CFSG.Walter.psl2_even_card hm0
    have hdvdsq : 2 ^ m - 1 ∣ (2 ^ m) ^ 2 - 1 := by
      simpa using Nat.pow_sub_one_dvd_pow_sub_one (2 ^ m) (show 1 ∣ 2 by norm_num)
    exact ⟨r, hrprime, hr5, hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hm), by
      rw [hcardH]
      exact hrdvd.trans (hdvdsq.trans (dvd_mul_left _ _))⟩
  ·
    exfalso
    obtain ⟨c, hc⟩ := hm
    obtain ⟨k, hk⟩ := hfodd
    have h2 : f = 2 * (m * c) := by rw [hc]; ring
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
