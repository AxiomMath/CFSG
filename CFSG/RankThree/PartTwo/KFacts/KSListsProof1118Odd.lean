module

public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.RankThree.PartTwo.KFacts.KSListsProofArith
import CFSG.RankThree.PartTwo.KFacts.KSListsProof1121
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
import CFSG.ClassicalInvolution.Orders.Basic
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec11.KSListsProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Open (ordTrialityD4 ordG2)
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem three_le_pow {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) : 3 ≤ r ^ f :=
  le_trans (by have := hr.two_le; omega) (Nat.le_self_pow (by omega) r)

theorem not_dvd_sl3_part {p x : ℕ} (hp : p.Prime) (hx : p ∣ x) (hx1 : 1 ≤ x) :
    ¬ p ∣ (x ^ 2 - 1) * (x ^ 3 - 1) ∧ ¬ p ∣ (x ^ 2 - 1) * (x ^ 3 + 1) := by
  have h2 := not_dvd_pow_sub_one (k := 2) hp hx hx1 (by norm_num)
  have h3 := not_dvd_pow_sub_one (k := 3) hp hx hx1 (by norm_num)
  have h3' := not_dvd_pow_add_one (k := 3) hp hx (by norm_num)
  exact ⟨fun h => ((Nat.Prime.dvd_mul hp).mp h).elim h2 h3,
    fun h => ((Nat.Prime.dvd_mul hp).mp h).elim h2 h3'⟩

theorem pow_twelve_le_of_dvd {r f N B : ℕ} (H : ∀ k, r ^ k ∣ N → r ^ k ≤ B)
    (h : (r ^ f) ^ 12 ∣ N) : (r ^ f) ^ 12 ≤ B := by
  rw [← pow_mul] at h ⊢
  exact H _ h

theorem false_card_psl2 {r f x : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hx : Odd x)
    (hx3 : 3 ≤ x) (h : ordTrialityD4 (r ^ f) * 2 = x * (x ^ 2 - 1)) : False := by
  have hle := pow_le_of_dvd_psl2 hr hx3 (Or.inl ⟨hx, rfl⟩) (pow_twelve_dvd_ordTrialityD4 _) h
  have := lt_psl2 (le_trans (by norm_num) (three_le_pow hr hr2 hf)) hle
  omega

theorem false_card_sl3 {r f p e g : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hp : p.Prime)
    (he1 : 1 ≤ e) (he2 : e ≤ 2) (hg : g ≤ 3)
    (h : ordTrialityD4 (r ^ f) * g = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) ∨
      ordTrialityD4 (r ^ f) * g = (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1))) :
    False := by
  have hx1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  have hx2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hpx : p ∣ p ^ e := dvd_pow_self p (by omega)
  obtain ⟨hN1, hN2⟩ := not_dvd_sl3_part hp hpx hx1
  have hdvd : (r ^ f) ^ 12 ∣ ordTrialityD4 (r ^ f) * g :=
    Dvd.dvd.mul_right (pow_twelve_dvd_ordTrialityD4 _) g
  have hQ3 := three_le_pow hr hr2 hf
  have hle3 : ordTrialityD4 (r ^ f) * g ≤ 3 * ordTrialityD4 (r ^ f) := by
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ hg
  have he3 : (p ^ e) ^ 3 = p ^ (e * 3) := by rw [pow_mul]
  rcases h with h | h
  · have hdvd' : (r ^ f) ^ 12 ∣ p ^ (e * 3) * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by
      rw [← he3, ← h]
      exact hdvd
    have hle := pow_twelve_le_of_dvd (fun k hk => pow_le_of_dvd_sl3 hr hr2 hx2 hk)
      (dvd_of_pow_twelve_dvd (a := e * 3) hr hp hf (by omega) hN1 hdvd')
    have := lt_sl3 hQ3 hle
    omega
  · have hdvd' : (r ^ f) ^ 12 ∣ p ^ (e * 3) * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
      rw [← he3, ← h]
      exact hdvd
    have hle := pow_twelve_le_of_dvd (fun k hk => pow_le_of_dvd_su3 hr hr2 hx2 hk)
      (dvd_of_pow_twelve_dvd (a := e * 3) hr hp hf (by omega) hN2 hdvd')
    have := lt_sl3 hQ3 hle
    have hmono : (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) ≤
        (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    omega

theorem false_card_g2 {r f p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hp : p.Prime)
    (h : ordG2 p = ordTrialityD4 (r ^ f)) : False := by
  have hdvd : (r ^ f) ^ 12 ∣ p ^ 6 * ((p ^ 6 - 1) * (p ^ 2 - 1)) := by
    have e : ordG2 p = p ^ 6 * ((p ^ 6 - 1) * (p ^ 2 - 1)) := by unfold ordG2; ring
    rw [← e, h]
    exact pow_twelve_dvd_ordTrialityD4 _
  have hpp : p ∣ p := dvd_rfl
  have hN : ¬ p ∣ (p ^ 6 - 1) * (p ^ 2 - 1) := fun h' =>
    ((Nat.Prime.dvd_mul hp).mp h').elim
      (not_dvd_pow_sub_one hp hpp hp.one_lt.le (by norm_num))
      (not_dvd_pow_sub_one hp hpp hp.one_lt.le (by norm_num))
  have hle := pow_twelve_le_of_dvd (fun k hk => pow_le_of_dvd_g2 hr hr2 hp.two_le hk)
    (dvd_of_pow_twelve_dvd hr hp hf (by norm_num) hN hdvd)
  have := lt_g2 (three_le_pow hr hr2 hf) hle
  omega

theorem false_card_sp4 {r f p : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hp : p.Prime)
    (h : ordTrialityD4 (r ^ f) * 2 = p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1))) : False := by
  have hdvd : (r ^ f) ^ 12 ∣ p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) :=
    h ▸ Dvd.dvd.mul_right (pow_twelve_dvd_ordTrialityD4 _) 2
  have hpp : p ∣ p := dvd_rfl
  have hN : ¬ p ∣ (p ^ 2 - 1) * (p ^ 4 - 1) := fun h' =>
    ((Nat.Prime.dvd_mul hp).mp h').elim
      (not_dvd_pow_sub_one hp hpp hp.one_lt.le (by norm_num))
      (not_dvd_pow_sub_one hp hpp hp.one_lt.le (by norm_num))
  have hle := pow_twelve_le_of_dvd (fun k hk => pow_le_of_dvd_sp4 hr hr2 hp.two_le hk)
    (dvd_of_pow_twelve_dvd hr hp hf (by norm_num) hN hdvd)
  have := lt_sp4 (three_le_pow hr hr2 hf) hle
  omega

theorem false_card_l4 {r f p g : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hp : p.Prime)
    (hg : g ≤ 4)
    (h : ordTrialityD4 (r ^ f) * g = p ^ 6 * ((p ^ 2 - 1) * (p ^ 3 - 1) * (p ^ 4 - 1)) ∨
      ordTrialityD4 (r ^ f) * g = p ^ 6 * ((p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1))) :
    False := by
  have hpp : p ∣ p := dvd_rfl
  have h2 := not_dvd_pow_sub_one (k := 2) hp hpp hp.one_lt.le (by norm_num)
  have h3 := not_dvd_pow_sub_one (k := 3) hp hpp hp.one_lt.le (by norm_num)
  have h3' := not_dvd_pow_add_one (k := 3) hp hpp (by norm_num)
  have h4 := not_dvd_pow_sub_one (k := 4) hp hpp hp.one_lt.le (by norm_num)
  have hdvd : (r ^ f) ^ 12 ∣ ordTrialityD4 (r ^ f) * g :=
    Dvd.dvd.mul_right (pow_twelve_dvd_ordTrialityD4 _) g
  have hQ3 := three_le_pow hr hr2 hf
  have hle4 : ordTrialityD4 (r ^ f) * g ≤ 4 * ordTrialityD4 (r ^ f) := by
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ hg
  rcases h with h | h
  · rw [h] at hdvd
    have hN : ¬ p ∣ (p ^ 2 - 1) * (p ^ 3 - 1) * (p ^ 4 - 1) := fun h' =>
      ((Nat.Prime.dvd_mul hp).mp h').elim
        (fun h'' => ((Nat.Prime.dvd_mul hp).mp h'').elim h2 h3) h4
    have hle := pow_twelve_le_of_dvd (fun k hk => pow_le_of_dvd_l4 hr hr2 hp.two_le hk)
      (dvd_of_pow_twelve_dvd hr hp hf (by norm_num) hN hdvd)
    have := lt_l4 hQ3 hle
    omega
  · rw [h] at hdvd
    have hN : ¬ p ∣ (p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1) := fun h' =>
      ((Nat.Prime.dvd_mul hp).mp h').elim
        (fun h'' => ((Nat.Prime.dvd_mul hp).mp h'').elim h2 h3') h4
    have hle := pow_twelve_le_of_dvd (fun k hk => pow_le_of_dvd_u4 hr hr2 hp.two_le hk)
      (dvd_of_pow_twelve_dvd hr hp hf (by norm_num) hN hdvd)
    have := lt_l4 hQ3 hle
    have hmono : p ^ 6 * ((p ^ 2 - 1) * (p ^ 3 - 1) * (p ^ 4 - 1)) ≤
        p ^ 6 * ((p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
    omega

variable {X : Type} [Group X]

theorem false_psl2_of_iso {r f p e : ℕ} [Fact p.Prime] (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hp2 : p ≠ 2) (he : 1 ≤ e) (φ : X ≃* projSL 2 (GaloisField p e))
    (hcard : Nat.card X = ordTrialityD4 (r ^ f)) : False := by
  have hp : p.Prime := Fact.out
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have h := card_projSL_two_mul (GaloisField p e)
  rw [GaloisField.card p e (by omega)] at h
  have hg : Nat.gcd 2 (p ^ e - 1) = 2 :=
    Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
  rw [hg, ← Nat.card_congr φ.toEquiv, hcard] at h
  have hx3 : 3 ≤ p ^ e := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  exact false_card_psl2 hr hr2 hf hodd hx3 h

theorem false_sl3_of_list {r f p e : ℕ} [Fact p.Prime] (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hX : Sec4.IsSLThreeEpsAt X (p ^ e) ∨ Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨
      Nonempty (X ≃* projSU 3 p e))
    (hcard : Nat.card X = ordTrialityD4 (r ^ f)) : False := by
  have hp : p.Prime := Fact.out
  rcases hX with ⟨K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · refine false_card_sl3 (g := 1) hr hr2 hf hp he1 he2 (by norm_num) (Or.inl ?_)
    rw [mul_one, ← hcard, Nat.card_congr φ.toEquiv,
      CFSG.SectionRank.OddCover.card_statedSL_three, hK]
    ring
  · have : Fintype K := Fintype.ofFinite K
    have : CharP K p := charP_of_card_eq_prime_pow (f := e * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
    refine false_card_sl3 (g := 1) hr hr2 hf hp he1 he2 (by norm_num) (Or.inr ?_)
    rw [mul_one, ← hcard, Nat.card_congr φ.toEquiv,
      CFSG.SectionRank.OddCover.card_statedSU_three hK]
    ring
  · have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv, hcard] at h
    exact false_card_sl3 hr hr2 hf hp he1 he2 (Nat.gcd_le_left _ (by norm_num)) (Or.inl h)
  · have h := KFacts.KS14.card_projSU_three_mul_gcd p e he1
    rw [← Nat.card_congr φ.toEquiv, hcard] at h
    exact false_card_sl3 hr hr2 hf hp he1 he2 (Nat.gcd_le_left _ (by norm_num)) (Or.inr h)


theorem false_three_of_list {r f p : ℕ} [Fact p.Prime] (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (hp3 : 3 < p)
    (hX : Blueprint.ChevalleyExceptionalModel X .G2 p 1 ∨
      Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
      (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
      (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1))))
    (hcard : Nat.card X = ordTrialityD4 (r ^ f)) : False := by
  have hp : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  rcases hX with hG | ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have h := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hG.2
    rw [pow_one, hcard] at h
    exact false_card_g2 hr hr2 hf hp h.symm
  · have h2 : (2 : GaloisField p 1) ≠ 0 :=
      CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp (by omega)
        (by rw [hK, pow_one])
    have h := card_projSp_two_mul (GaloisField p 1) h2
    rw [hK, ← Nat.card_congr φ.toEquiv, hcard] at h
    exact false_card_sp4 hr hr2 hf hp h
  · have h := card_projSU_four_mul p 1 le_rfl
    rw [pow_one, ← Nat.card_congr φ.toEquiv, hcard] at h
    exact false_card_l4 hr hr2 hf hp (Nat.gcd_le_left _ (by norm_num)) (Or.inr h)
  · have h := card_projSL_four_mul (GaloisField p 1)
    rw [hK, ← Nat.card_congr φ.toEquiv, hcard] at h
    exact false_card_l4 hr hr2 hf hp (Nat.gcd_le_left _ (by norm_num)) (Or.inl h)

end CFSG.RankThree.PartTwo.Sec11.KSListsProof
