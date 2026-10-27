module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgE1

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

theorem pigeon_alg {X κ ρ B S c₁ c₂ : K} (hB : B ≠ 0) (h12 : c₁ ≠ c₂)
    (e₁ : c₁ * X - κ * B = ρ * S * (B - c₁)) (e₂ : c₂ * X - κ * B = ρ * S * (B - c₂)) :
    X = κ ∧ ρ * S = -κ := by
  have hX : X = -(ρ * S) := by
    have : (c₁ - c₂) * X = (c₁ - c₂) * (-(ρ * S)) := by linear_combination e₁ - e₂
    exact mul_left_cancel₀ (sub_ne_zero.mpr h12) this
  have hρ : ρ * S = -κ := by
    have : B * (ρ * S) = B * (-κ) := by rw [hX] at e₁; linear_combination -e₁
    exact mul_left_cancel₀ hB this
  exact ⟨by rw [hX, hρ, neg_neg], hρ⟩

variable [Finite K] {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ →* Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp

variable (H : SMapHyp J q F σ h)
include H

theorem sgn_eq_one_of_q_eq_three (hq : q = 3) (y : K) : sgn J σ y = 1 := by
  classical
  by_cases hy : ∃ k : Kˣ, nrm J k = y
  · rw [sgn, dite_eq_left hy]
    set k := Classical.choose hy
    have hk : nrm J k = y := Classical.choose_spec hy
    have hy3 : y ^ 2 = 1 := by
      have hyc : J.conj y = y := by rw [← hk]; exact conj_nrm J _
      have hy0 : y ≠ 0 := by rw [← hk]; exact nrm_ne_zero J k.ne_zero
      rw [H.conj_pow, hq] at hyc
      have : y * (y ^ 2 - 1) = 0 := by linear_combination hyc
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hy0)
    have hy3' : y * y = 1 := by rw [← sq]; exact hy3
    rcases mul_self_eq_one_iff.mp hy3' with h1 | h1
    · apply H.eps_of_pow_eq_one
      rw [← H.nrm_eq_pow', hk, h1]
    · exact H.eps_eq_one_of_nrm_eq_neg_one (hk.trans h1)
  · rw [sgn, dite_eq_right hy]

theorem exists_fixed_ne (hq5 : 5 ≤ q) :
    ∃ x : K, x ≠ 0 ∧ J.conj x = x ∧ x ≠ 1 ∧ x ≠ -1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hog : orderOf g = q * q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units, ← Nat.card_eq_fintype_card, H.card, sq]
  refine ⟨nrm J g, nrm_ne_zero J g.ne_zero, conj_nrm J _, ?_⟩
  have hsq : ¬ (nrm J g) ^ 2 = 1 := by
    intro e
    rw [H.nrm_eq_pow', ← pow_mul] at e
    have e' : g ^ ((q + 1) * 2) = 1 := Units.ext (by simpa using e)
    have hle := orderOf_le_of_pow_eq_one (by omega) e'
    rw [hog] at hle
    have : 5 * q ≤ q * q := Nat.mul_le_mul_right q hq5
    omega
  constructor
  · intro e; exact hsq (by rw [e, one_pow])
  · intro e; exact hsq (by rw [e, neg_one_sq])

theorem sign_prod_sq (a b c d : K) :
    sgn J σ a * sgn J σ b * sgn J σ c * sgn J σ d = 1 ∨
      sgn J σ a * sgn J σ b * sgn J σ c * sgn J σ d = -1 := by
  rcases H.sgn_sq a with ea | ea <;> rcases H.sgn_sq b with eb | eb <;>
    rcases H.sgn_sq c with ec | ec <;> rcases H.sgn_sq d with ed | ed <;>
    simp [ea, eb, ec, ed]

theorem emm_eq {κ : K} (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 →
      (F z).1.1 = 0 ∧ (F z).1.2 = κ / z.1.2)
    (hκ0 : κ ≠ 0) (hκc : J.conj κ = κ) {c₀ : K} (hc₀0 : c₀ ≠ 0)
    (hgam : ∀ b : K, b + J.conj b ≠ 0 → gam J F b = c₀ * sgn J σ (nn J b) / J.conj b)
    {c₁ : K} (hc₁0 : c₁ ≠ 0) (hc₁ : J.conj c₁ = -c₁) {w : Coord J} (hw : w.1.1 ≠ 0) :
    emm J F w.1.2 = κ / w.1.2 ∧ ∀ c : K, c ≠ 0 → J.conj c = -c →
      c₀ * (c₁ * theta h c₁ hc₁) * (sgn J σ (nn J (w.1.2 + c)) *
        sgn J σ (nn J (κ / c + emm J F w.1.2)) * sgn J σ (nn J w.1.2) *
        sgn J σ (c₁ / c)) = -κ := by
  set ρ := c₀ * (c₁ * theta h c₁ hc₁) with hρdef
  set S : K → K := fun c => sgn J σ (nn J (w.1.2 + c)) *
    sgn J σ (nn J (κ / c + emm J F w.1.2)) * sgn J σ (nn J w.1.2) * sgn J σ (c₁ / c) with hS
  have hb : w.1.2 + J.conj w.1.2 ≠ 0 := tr_ne_zero_of_fst hw
  have hb0 : w.1.2 ≠ 0 := by intro e; apply hb; rw [e, map_zero, add_zero]
  have hB0 : J.conj w.1.2 ≠ 0 := (map_ne_zero J.conj).2 hb0
  set X := J.conj (emm J F w.1.2) * J.conj w.1.2 with hXdef
  have hE : ∀ c : K, c ≠ 0 → J.conj c = -c →
      c * X - κ * J.conj w.1.2 = ρ * S c * (J.conj w.1.2 - c) := by
    intro c hc0 hc
    have := H.E1 hκF hκc hc₀0 hgam hc₁0 hc₁ hw hc0 hc
    rw [hXdef, hρdef, hS]
    linear_combination this
  have hSsq : ∀ c, S c = 1 ∨ S c = -1 := fun c => H.sign_prod_sq _ _ _ _
  have hneg : J.conj (-c₁) = -(-c₁) := by rw [map_neg, hc₁]
  have hc₁n : c₁ ≠ -c₁ := by
    intro e; apply hc₁0
    have : (2 : K) * c₁ = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_left H.two_ne_zero'
  obtain ⟨d₁, d₂, hd₁0, hd₁, hd₂0, hd₂, hd12, hS12⟩ : ∃ d₁ d₂ : K, d₁ ≠ 0 ∧ J.conj d₁ = -d₁ ∧
      d₂ ≠ 0 ∧ J.conj d₂ = -d₂ ∧ d₁ ≠ d₂ ∧ S d₁ = S d₂ := by
    rcases (show q = 3 ∨ 5 ≤ q by have := H.q_ge; obtain ⟨m, hm⟩ := H.q_odd; omega) with
      hq3 | hq5
    · refine ⟨c₁, -c₁, hc₁0, hc₁, neg_ne_zero.mpr hc₁0, hneg, hc₁n, ?_⟩
      simp only [hS, H.sgn_eq_one_of_q_eq_three hq3]
    · obtain ⟨x, hx0, hxc, hx1, hxn1⟩ := H.exists_fixed_ne hq5
      have hxc₁ : J.conj (x * c₁) = -(x * c₁) := by rw [map_mul, hxc, hc₁]; ring
      have hxc₁0 : x * c₁ ≠ 0 := mul_ne_zero hx0 hc₁0
      have h13 : c₁ ≠ x * c₁ := by
        intro e; apply hx1
        have : (x - 1) * c₁ = 0 := by linear_combination -e
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc₁0)
      have h23 : -c₁ ≠ x * c₁ := by
        intro e; apply hxn1
        have : (x + 1) * c₁ = 0 := by linear_combination -e
        have := (mul_eq_zero.mp this).resolve_right hc₁0
        linear_combination this
      by_cases e12 : S c₁ = S (-c₁)
      · exact ⟨c₁, -c₁, hc₁0, hc₁, neg_ne_zero.mpr hc₁0, hneg, hc₁n, e12⟩
      by_cases e13 : S c₁ = S (x * c₁)
      · exact ⟨c₁, x * c₁, hc₁0, hc₁, hxc₁0, hxc₁, h13, e13⟩
      refine ⟨-c₁, x * c₁, neg_ne_zero.mpr hc₁0, hneg, hxc₁0, hxc₁, h23, ?_⟩
      rcases hSsq c₁ with a1 | a1 <;> rcases hSsq (-c₁) with a2 | a2 <;>
        rcases hSsq (x * c₁) with a3 | a3 <;> simp_all
  have e₁ := hE d₁ hd₁0 hd₁
  have e₂ := hE d₂ hd₂0 hd₂
  rw [hS12] at e₁
  obtain ⟨hX, hρS⟩ := pigeon_alg hB0 hd12 e₁ e₂
  refine ⟨?_, ?_⟩
  ·
    have h1 : J.conj (emm J F w.1.2 * w.1.2) = κ := by rw [map_mul]; exact hX
    have h2 : emm J F w.1.2 * w.1.2 = κ := by
      have := congrArg J.conj h1; rwa [conj_conj, hκc] at this
    field_simp
    exact h2
  · intro c hc0 hc
    change ρ * S c = -κ
    rcases hSsq c with ec | ec <;> rcases hSsq d₂ with ed | ed
    · rw [ec, ← ed]; exact hρS
    ·
      exfalso
      have hρ : ρ = κ := by rw [ed] at hρS; linear_combination -hρS
      have e3 := hE c hc0 hc
      rw [hX, ec, hρ] at e3
      have : (2 * κ) * c = (2 * κ) * J.conj w.1.2 := by linear_combination e3
      have hcB := mul_left_cancel₀ (mul_ne_zero H.two_ne_zero' hκ0) this
      apply hb
      have : J.conj (J.conj w.1.2) = -J.conj w.1.2 := by rw [← hcB]; exact hc
      rw [conj_conj] at this
      linear_combination this
    · exfalso
      have hρ : ρ = -κ := by rw [ed] at hρS; linear_combination hρS
      have e3 := hE c hc0 hc
      rw [hX, ec, hρ] at e3
      have : (2 * κ) * c = (2 * κ) * J.conj w.1.2 := by linear_combination e3
      have hcB := mul_left_cancel₀ (mul_ne_zero H.two_ne_zero' hκ0) this
      apply hb
      have : J.conj (J.conj w.1.2) = -J.conj w.1.2 := by rw [← hcB]; exact hc
      rw [conj_conj] at this
      linear_combination this
    · rw [ec, ← ed]; exact hρS

end SMapHyp

end CFSG.UnitaryThreeRecognition.WeylAlg
