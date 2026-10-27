module

public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofSub
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

namespace KSL3Two

open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup)

theorem mod_three_eq_two_of_card {q s : ℕ} (hq : 1 ≤ q)
    (h : s * Nat.gcd 3 (q - 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) (h9 : ¬ 9 ∣ s) :
    q % 3 = 2 := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  by_contra hne
  apply h9
  have h27 : 27 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq2,
      Nat.cast_sub hq3]
    push_cast
    have key : ∀ x : ZMod 27, x.val % 3 ≠ 2 → x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) = 0 := by
      decide
    exact key _ (by rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by norm_num)]; omega)
  rw [← h] at h27
  have : 27 ∣ s * 3 := h27.trans (Nat.mul_dvd_mul_left s (Nat.gcd_dvd_left _ _))
  omega

theorem mod_three_eq_one_of_card {q s : ℕ} (hq : 1 ≤ q)
    (h : s * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) (h9 : ¬ 9 ∣ s) :
    q % 3 = 1 := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  by_contra hne
  apply h9
  have h27 : 27 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq2]
    push_cast
    have key : ∀ x : ZMod 27, x.val % 3 ≠ 1 → x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) = 0 := by
      decide
    exact key _ (by rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by norm_num)]; omega)
  rw [← h] at h27
  have : 27 ∣ s * 3 := h27.trans (Nat.mul_dvd_mul_left s (Nat.gcd_dvd_left _ _))
  omega

theorem nine_dvd_card_of_cube_two {m s : ℕ} (hq : (m ^ 3) % 3 = 2)
    (h : s * Nat.gcd 3 (m ^ 3 - 1) =
      (m ^ 3) ^ 3 * (((m ^ 3) ^ 2 - 1) * ((m ^ 3) ^ 3 - 1))) : 9 ∣ s := by
  have hm1 : 1 ≤ m ^ 3 := by omega
  have h91 : 9 ∣ m ^ 3 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    have key : ∀ x : ZMod 9, (x ^ 3).val % 3 = 2 → x ^ 3 + 1 = 0 := by decide
    apply key
    rw [← Nat.cast_pow, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by norm_num)]
    exact hq
  have hg : Nat.gcd 3 (m ^ 3 - 1) = 1 := by
    rw [← Nat.Coprime]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  rw [hg, mul_one] at h
  rw [h]
  have hsq : (m ^ 3) ^ 2 - 1 = (m ^ 3 - 1) * (m ^ 3 + 1) := by
    have : (m ^ 3) ^ 2 = (m ^ 3 - 1) * (m ^ 3 + 1) + 1 := by
      obtain ⟨k, hk⟩ : ∃ k, m ^ 3 = k + 1 := ⟨m ^ 3 - 1, by omega⟩
      rw [hk]
      simp only [Nat.add_sub_cancel]
      ring
    omega
  rw [hsq]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left h91 _) _) _

theorem nine_dvd_card_of_cube_one {m s : ℕ} (hq : (m ^ 3) % 3 = 1)
    (h : s * Nat.gcd 3 (m ^ 3 + 1) =
      (m ^ 3) ^ 3 * (((m ^ 3) ^ 2 - 1) * ((m ^ 3) ^ 3 + 1))) : 9 ∣ s := by
  have hm1 : 1 ≤ m ^ 3 := by omega
  have h91 : 9 ∣ m ^ 3 - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hm1]
    push_cast
    have key : ∀ x : ZMod 9, (x ^ 3).val % 3 = 1 → x ^ 3 - 1 = 0 := by decide
    apply key
    rw [← Nat.cast_pow, ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by norm_num)]
    exact hq
  have hg : Nat.gcd 3 (m ^ 3 + 1) = 1 := by
    rw [← Nat.Coprime]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  rw [hg, mul_one] at h
  rw [h]
  have hsq : (m ^ 3) ^ 2 - 1 = (m ^ 3 - 1) * (m ^ 3 + 1) := by
    have : (m ^ 3) ^ 2 = (m ^ 3 - 1) * (m ^ 3 + 1) + 1 := by
      obtain ⟨k, hk⟩ : ∃ k, m ^ 3 = k + 1 := ⟨m ^ 3 - 1, by omega⟩
      rw [hk]
      simp only [Nat.add_sub_cancel]
      ring
    omega
  rw [hsq]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right h91 _) _) _

theorem pow_eq_cube {r n : ℕ} (h : 3 ∣ n) : ∃ m, r ^ n = m ^ 3 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨r ^ k, by rw [← pow_mul, mul_comm]⟩

end KSL3Two

open KSL3Two
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup)

theorem ks1522OutThree : KS1522OutThree := by
  intro S _ _ r f _ hS h9 α hα3
  have hr : r.Prime := Fact.out
  suffices hinn : KFacts.IsInnerAut α by
    obtain ⟨y, hy⟩ := hinn
    exact ⟨y, fun x => by rw [← hy]; rfl⟩
  rcases hS with hL | ⟨hq2, ⟨φ⟩⟩
  ·
    obtain ⟨φ⟩ := hL
    set F := GaloisField r f with hF
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨⟨n, hn0⟩, -, hn⟩ := FiniteField.card F r
    have hcardF : Nat.card F = r ^ n := by rw [Nat.card_eq_fintype_card, hn]; rfl
    obtain ⟨ψ⟩ := KFacts.nonempty_projSL_mulEquiv 3 F
    set e : S ≃* projectiveSL 3 F := φ.trans ψ with he
    have hc := KFacts.KS14.card_projSL_three_mul_gcd F
    rw [← Nat.card_congr φ.toEquiv] at hc
    have hF1 : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    have hq2' : Nat.card F % 3 = 2 := mod_three_eq_two_of_card hF1 hc h9
    rw [← KFacts.isInnerAut_congr e]
    set β := MulAut.congr e α with hβ
    have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
    by_cases hD : β ∈ linearAutGroup 3 F
    · exact KFacts.isInnerAut_of_mem_linearAutGroup hq2' hD
    · exfalso
      obtain ⟨σ, hσ, -⟩ := KFacts.linear_order_three_field_descent le_rfl β hβ3 hD
      obtain ⟨h3n, -⟩ := KFacts.eq_frobenius_pow_of_orderOf_eq_three hr hn0 hcardF hσ
      obtain ⟨m, hm⟩ := pow_eq_cube (r := r) h3n
      rw [hcardF, hm] at hc hq2'
      exact h9 (nine_dvd_card_of_cube_two hq2' hc)
  ·
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · simp at hq2
      · exact h
    have hU : UnitaryFieldData r f (GaloisField r (2 * f)) :=
      ⟨hr, hf, GaloisField.card r (2 * f) (by omega)⟩
    obtain ⟨ψ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU hU
    set e := φ.trans ψ.symm with he
    have hc := KFacts.KS14.card_projSU_three_mul_gcd r f hf
    rw [← Nat.card_congr φ.toEquiv] at hc
    have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
    have hq1' : r ^ f % 3 = 1 := mod_three_eq_one_of_card hq1 hc h9
    rw [← KFacts.isInnerAut_congr e]
    set β := MulAut.congr e α with hβ
    have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
    by_cases hD : β ∈ (KFacts.psuConj hU).range
    · exact KFacts.isInnerAut_of_mem_psuConj_range hU hq1' hD
    · exfalso
      obtain ⟨σ, hσ, -⟩ := KFacts.unitary_order_three_field_descent hq2 β hβ3 hD
      obtain ⟨h3n, -⟩ := KFacts.eq_frobenius_pow_of_orderOf_eq_three hr (by omega) hU.card hσ
      have h3f : 3 ∣ f := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3n)
      obtain ⟨m, hm⟩ := pow_eq_cube (r := r) h3f
      rw [hm] at hc hq1'
      exact h9 (nine_dvd_card_of_cube_one hq1' hc)

theorem ks1522HessSub : KS1522HessSub := ks1522HessSub_of ks1522OutThree

end CFSG.RankThree.PartTwo.Sec15
