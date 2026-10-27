module

public import CFSG.RankThree.PartOne.KE.SuzukiDescent
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

namespace CFSG.RankThree.PartOne.KE

theorem card_fixField_suzuki_odd {a : ℕ} {K : Type} [Field K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    ∃ b m : ℕ, a = b + (2 * b + 1) * m ∧ (2 * b + 1) * p = 2 * a + 1 ∧
      Nat.card (fixField σ) = 2 ^ (2 * b + 1) := by
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by omega : 1 ≤ 2 * a + 1) hK σ
  rw [hσ] at hdvd hcard
  obtain ⟨d, hd⟩ := hdvd
  have hdodd : Odd d := by
    have h : Odd (p * d) := by rw [← hd]; exact ⟨a, rfl⟩
    exact (Nat.odd_mul.mp h).2
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨b, hb⟩ := hdodd
  obtain ⟨m, hm⟩ := hpodd
  refine ⟨b, m, ?_, ?_, ?_⟩
  · subst hb hm
    nlinarith
  · rw [hb] at hd
    linarith
  · have h1 : (2 * a + 1) / p = d := by
      rw [hd, Nat.mul_div_cancel_left d hp.pos]
    rw [hcard, h1, hb]

end CFSG.RankThree.PartOne.KE
