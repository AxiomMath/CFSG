module

public import CFSG.RankThree.PartTwo.Sec15.F153Rest
public import CFSG.RankThree.PartTwo.Sec15.F153L3
import CFSG.Models.PGLOrders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem false_of_order_linear {q g : ℕ} (hq : 4 ≤ q) (hg : g ≤ 3)
    (h : 6048 * g = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) : False := by
  have h1 : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 15 ≤ q ^ 2 - 1 := by
    have := Nat.pow_le_pow_left hq 2
    omega
  have h3 : 63 ≤ q ^ 3 - 1 := by omega
  have h4 : 4 ^ 3 * (15 * 63) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  rw [← h] at h4
  omega

theorem false_of_order_unitary {q g : ℕ} (hq : 4 ≤ q) (hg : g ≤ 3)
    (h : 6048 * g = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) : False := by
  have h1 : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 15 ≤ q ^ 2 - 1 := by
    have := Nat.pow_le_pow_left hq 2
    omega
  have h3 : 65 ≤ q ^ 3 + 1 := by omega
  have h4 : 4 ^ 3 * (15 * 65) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  rw [← h] at h4
  omega

theorem pow_ne_three {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hp3 : p ≠ 3) : p ^ f ≠ 3 := by
  intro h
  have : p ∣ 3 := by
    rw [← h]
    exact dvd_pow_self p (by omega)
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this)

theorem false_of_isLThreeEpsAt_card_6048 {Q : Type} [Group Q] {p f : ℕ} [hp : Fact p.Prime]
    (hf : 1 ≤ f) (hp3 : p ≠ 3) (hε : IsLThreeEpsAt Q p f) (hc : Nat.card Q = 6048) : False := by
  have hq2 : 2 ≤ p ^ f := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
  have hq3 : p ^ f ≠ 3 := pow_ne_three hp.out hf hp3
  rcases hε with ⟨⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
  · have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
    have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p f)
    rw [Nat.card_congr φ.symm.toEquiv, hc, hK] at h
    rcases (by omega : p ^ f = 2 ∨ 4 ≤ p ^ f) with h2 | h4
    · rw [h2] at h
      norm_num at h
    · exact false_of_order_linear h4 (Nat.gcd_le_left _ (by norm_num)) h
  · have h := KFacts.KS14.card_projSU_three_mul_gcd p f hf
    rw [Nat.card_congr φ.symm.toEquiv, hc] at h
    exact false_of_order_unitary (by omega) (Nat.gcd_le_left _ (by norm_num)) h

theorem step153PushU33R_of_inputs
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) :
    Step153PushU33R := by
  intro G _ _ A c L hR Y hY S hS hno hFF hSY ⟨e⟩
  exfalso
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  have hc : Nat.card ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) = 6048 := by
    rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSU_three_three]
  have hdvd : 6048 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rw [← hc]
    exact Subgroup.card_quotient_dvd_card _
  have hsimple : ∀ {T : Type} [Group T], IsSimpleGroup T →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* T) → Nat.card T = 6048 := by
    intro T _ hT ⟨φ⟩
    obtain ⟨ψ⟩ := nonempty_centerQuotient_equiv_of_simple hq hT φ
    rw [← Nat.card_congr ψ.toEquiv, hc]
  rcases type153Fine_of_item148R h148 h134 h48 hR hY with hA5 | h6 | hA7 | hJ |
    ⟨p, f, hp, hf, hp3, hε⟩ | hM22 | hM12 | hA10 | hON
  · obtain ⟨φ⟩ := hA5
    rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five] at hdvd
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
  · obtain ⟨-, ⟨φ⟩⟩ := h6
    rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_six] at hc
    omega
  · obtain ⟨φ⟩ := hA7
    rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_seven] at hdvd
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
  · have h := hsimple CFSG.Sporadic.J2.isSimpleGroup_J2 hJ
    rw [KFacts.KS14.card_nativeJ2] at h
    omega
  · have hs : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := Main148.isSimpleGroup_of_isLThreeEpsAt148 hf hε
    obtain ⟨ψ⟩ := nonempty_centerQuotient_equiv_of_simple hq hs (MulEquiv.refl _)
    exact false_of_isLThreeEpsAt_card_6048 hf hp3 hε (by rw [← Nat.card_congr ψ.toEquiv, hc])
  · obtain ⟨φ⟩ := hM22
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22] at hdvd
    exact absurd hdvd (by norm_num)
  · obtain ⟨φ⟩ := hM12
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12] at hdvd
    exact absurd hdvd (by norm_num)
  · haveI : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
    have h := hsimple this hA10
    rw [card_alternatingGroup_ten] at h
    omega
  · obtain ⟨-, ⟨φ⟩⟩ := hON
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.ON.card_ON] at hc
    omega

end CFSG.RankThree.PartTwo.Sec15.F153
