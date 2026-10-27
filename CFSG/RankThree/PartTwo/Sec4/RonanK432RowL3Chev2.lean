module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3Easy
import CFSG.RankThree.PartTwo.KFacts.K72L3Field
import CFSG.RankThree.PartTwo.KFacts.K72L3Omega
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.Models.PGL
import CFSG.Open.StatedDefs
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem two_pow_two_mul_mod_three_chev2 (m : ℕ) : 2 ^ (2 * m) % 3 = 1 := by
  rw [pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_odd_chev2 {n : ℕ} (h : n % 2 = 1) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  rw [pow_succ, Nat.mul_mod, two_pow_two_mul_mod_three_chev2 m]

theorem two_pow_mod_three_of_even_chev2 {n : ℕ} (h : n % 2 = 0) : 2 ^ n % 3 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  exact two_pow_two_mul_mod_three_chev2 m

theorem outerRow_of_three_dvd_of_fixed {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥)
    (hfix : ∀ α : MulAut S, α ^ 3 = 1 → ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut α →
      ∃ M : ℕ, (∀ T : Subgroup S, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧ 3 * M ∣ Nat.card S) :
    OuterRow S := by
  refine outerRow_of_fixed_card_dvd hZ fun σ hσ hout => ?_
  obtain ⟨M, hM, h3M⟩ := hfix σ hσ hout
  exact ⟨MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id S), M, fun x => Iff.rfl,
    hM (MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id S)) (fun t ht => ht), h3M⟩

theorem outerRow_projSL_three_two_of_three_dvd (n : ℕ) (hn : 1 ≤ n) (h3 : 3 ∣ n)
    (hmod : 2 ^ n % 3 = 2) : OuterRow (projSL 3 (GaloisField 2 n)) := by
  obtain ⟨k, rfl⟩ := h3
  have hk : 1 ≤ k := by omega
  have hX : CFSG.RankThree.PartTwo.Sec8.IsoLThreeMinusPi
      (↥(projSL 3 (GaloisField 2 (3 * k)))) 2 (3 * k) :=
    Or.inr ⟨hmod, ⟨MulEquiv.refl _⟩⟩
  exact outerRow_of_three_dvd_of_fixed
    (CFSG.RankThree.PartTwo.KFacts.center_eq_bot_of_isoLThreeMinusPi hk hX)
    fun α hα hout => (CFSG.RankThree.PartTwo.KFacts.fixedData_of_isoLThreeMinusPi hk hX α hα hout).1

theorem outerRow_projSU_two_of_three_dvd (n : ℕ) (hn : 1 ≤ n) (h3 : 3 ∣ n)
    (hmod : 2 ^ n % 3 = 1) : OuterRow (projSU 3 2 n) := by
  obtain ⟨k, rfl⟩ := h3
  have hk : 1 ≤ k := by omega
  have hX : CFSG.RankThree.PartTwo.Sec8.IsoLThreeMinusPi
      (↥(projSU 3 2 (3 * k))) 2 (3 * k) :=
    Or.inl ⟨hmod, ⟨MulEquiv.refl _⟩⟩
  exact outerRow_of_three_dvd_of_fixed
    (CFSG.RankThree.PartTwo.KFacts.center_eq_bot_of_isoLThreeMinusPi hk hX)
    fun α hα hout => (CFSG.RankThree.PartTwo.KFacts.fixedData_of_isoLThreeMinusPi hk hX α hα hout).1

theorem outerRow_projSL_three_of_not_three_dvd (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e)
    (h3 : ¬ 3 ∣ e) (hmod : p ^ e % 3 = 2) : OuterRow (projSL 3 (GaloisField p e)) := by
  apply outerRow_of_not_three_dvd_outer
  have hp : p.Prime := Fact.out
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 p e := by
    unfold CFSG.Open.StatedLieAdmissible
    refine ⟨hp, he, ?_⟩
    simp
  have hT := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm
    (MulEquiv.refl (projSL 3 (GaloisField p e)))
  have hdvd : Nat.card (Outer (projSL 3 (GaloisField p e))) ∣ 2 * e * Nat.gcd 3 (p ^ e - 1) :=
    (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) (le_refl 3) hp he hT).1
  have hg : Nat.gcd 3 (p ^ e - 1) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
  rw [hg, mul_one] at hdvd
  intro h3'
  have h3'' := h3'.trans hdvd
  omega

theorem outerRow_projSU_three_of_not_three_dvd (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e)
    (h3 : ¬ 3 ∣ e) (hmod : p ^ e % 3 = 1) : OuterRow (projSU 3 p e) := by
  apply outerRow_of_not_three_dvd_outer
  have hq : ¬ (3 = 3 ∧ p ^ e = 2) := fun h => by
    have := h.2
    omega
  have hdvd := CFSG.RankThree.PartTwo.Sec4.card_outer_projSU_dvd 3 p e he (le_refl 3) hq
  intro h3'
  have h3'' := h3'.trans hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3'' with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h' | h' <;> omega
  · omega

theorem rowOf_seven_SL3_of_odd : ∀ n : ℕ, 1 ≤ n → n % 2 = 1 →
    RowOf (projSL 3 (GaloisField 2 n)) := by
  intro n hn hodd
  have hmod : 2 ^ n % 3 = 2 := two_pow_mod_three_of_odd_chev2 hodd
  have hK : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n (by omega)]
    exact hmod
  intro S _ _ _ _ ⟨eS⟩
  refine GoodRow.of_mulEquiv eS.symm ⟨listRow_projSL_three_of_mod_two (GaloisField 2 n) hK, ?_⟩
  by_cases h3 : 3 ∣ n
  · exact outerRow_projSL_three_two_of_three_dvd n hn h3 hmod
  · exact outerRow_projSL_three_of_not_three_dvd 2 n hn h3 hmod

theorem rowOf_seven_SU3_of_even : ∀ n : ℕ, 1 ≤ n → n % 2 = 0 → RowOf (projSU 3 2 n) := by
  intro n hn heven
  have hmod : 2 ^ n % 3 = 1 := two_pow_mod_three_of_even_chev2 heven
  intro S _ _ _ _ ⟨eS⟩
  refine GoodRow.of_mulEquiv eS.symm
    ⟨listRow_projSU_three_of_mod_one 2 n (by omega) hmod, ?_⟩
  by_cases h3 : 3 ∣ n
  · exact outerRow_projSU_two_of_three_dvd n hn h3 hmod
  · exact outerRow_projSU_three_of_not_three_dvd 2 n hn h3 hmod

end CFSG.RankThree.PartTwo.Sec4.RonanK432
