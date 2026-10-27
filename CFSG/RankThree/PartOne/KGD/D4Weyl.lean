module

public import CFSG.RankThree.Chevalley.SteinbergBID4RegularCentralizer

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open scoped Matrix

@[expose] def d4Mat (e : ℕ) : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ :=
  Matrix.of fun i j => d4RootVec (d4Dig j (d4TupCode e)) i

theorem d4Mat_pow_twelve : ∀ e ∈ d4WeylTab, (d4Mat e) ^ 12 = 1 := by
  decide +kernel

theorem smul_eq_d4Mat_mulVec (w : WeylGroup Tag.D4) {e : ℕ}
    (he : ∀ i, w • (Pi.single i 1 : Fin Tag.D4.rank → ℤ) = d4RootVec (d4Dig i (d4TupCode e)))
    (v : Fin Tag.D4.rank → ℤ) : w • v = d4Mat e *ᵥ v := by
  rw [CFSG.RankThree.Chevalley.smul_eq_sum_smul_single]
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, he, smul_eq_mul, d4Mat, Matrix.mulVec,
    dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem pow_smul_eq_d4Mat_pow_mulVec (w : WeylGroup Tag.D4) {e : ℕ}
    (he : ∀ i, w • (Pi.single i 1 : Fin Tag.D4.rank → ℤ) = d4RootVec (d4Dig i (d4TupCode e)))
    (n : ℕ) (v : Fin Tag.D4.rank → ℤ) : (w ^ n) • v = (d4Mat e) ^ n *ᵥ v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, smul_eq_d4Mat_mulVec w he, ih, Matrix.mulVec_mulVec, ← pow_succ]

theorem d4_weyl_pow_twelve (w : WeylGroup Tag.D4) : w ^ 12 = 1 := by
  obtain ⟨e, he, hw⟩ := exists_mem_d4WeylTab w
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.D4.rank → ℤ) fun v => ?_
  rw [pow_smul_eq_d4Mat_pow_mulVec w hw 12 v, d4Mat_pow_twelve e he, Matrix.one_mulVec, one_smul]

theorem not_dvd_card_weylGroup_D4 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ p ∣ Nat.card (WeylGroup TwistTag.D4.tag) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := WeylGroup Tag.D4) p hdvd
  have h12 : p ∣ 12 := hg ▸ orderOf_dvd_of_pow_eq_one (d4_weyl_pow_twelve g)
  have := Nat.le_of_dvd (by norm_num) h12
  have h2 : p ∣ 2 ^ 2 * 3 := by simpa using h12
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
  · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
  · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)

end CFSG.RankThree.PartOne.KGD
