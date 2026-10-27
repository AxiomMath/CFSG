module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique

variable {H : Type*} [Group H]

@[expose] def kl (v w : H) : Fin 4 → H := ![1, v, w, v * w]

section Klein

variable {v w : H} (hv : v * v = 1) (hw : w * w = 1) (hc : v * w = w * v)

include hv hw hc

theorem kl_mul (i j : Fin 4) : ∃ k : Fin 4, kl v w i * kl v w j = kl v w k := by
  have e1 : v * (v * w) = w := by rw [← mul_assoc, hv, one_mul]
  have e2 : w * (v * w) = v := by rw [← mul_assoc, ← hc, mul_assoc, hw, mul_one]
  have e3 : v * w * v = w := by rw [hc, mul_assoc, hv, mul_one]
  have e4 : v * w * w = v := by rw [mul_assoc, hw, mul_one]
  have e5 : v * w * (v * w) = 1 := by rw [mul_assoc, e2, hv]
  fin_cases i <;> fin_cases j
  · exact ⟨0, by simp [kl]⟩
  · exact ⟨1, by simp [kl]⟩
  · exact ⟨2, by simp [kl]⟩
  · exact ⟨3, by simp [kl]⟩
  · exact ⟨1, by simp [kl]⟩
  · exact ⟨0, by simp [kl, hv]⟩
  · exact ⟨3, by simp [kl]⟩
  · exact ⟨2, by simp [kl, e1]⟩
  · exact ⟨2, by simp [kl]⟩
  · exact ⟨3, by simp [kl, hc]⟩
  · exact ⟨0, by simp [kl, hw]⟩
  · exact ⟨1, by simp [kl, e2]⟩
  · exact ⟨3, by simp [kl]⟩
  · exact ⟨2, by simp [kl, e3]⟩
  · exact ⟨1, by simp [kl, e4]⟩
  · exact ⟨0, by simp [kl, e5]⟩

theorem kl_inv (i : Fin 4) : (kl v w i)⁻¹ = kl v w i := by
  have e2 : w * (v * w) = v := by rw [← mul_assoc, ← hc, mul_assoc, hw, mul_one]
  have e5 : v * w * (v * w) = 1 := by rw [mul_assoc, e2, hv]
  fin_cases i
  · simp [kl]
  · simpa [kl] using inv_eq_of_mul_eq_one_right hv
  · simpa [kl] using inv_eq_of_mul_eq_one_right hw
  · simpa [kl] using inv_eq_of_mul_eq_one_right e5

@[expose] def klQ (Q : Subgroup H) (hQ : Q.Normal) : Subgroup H where
  carrier := {x | ∃ i : Fin 4, ∃ q ∈ Q, x = kl v w i * q}
  mul_mem' := by
    rintro x y ⟨i, q, hq, rfl⟩ ⟨j, q', hq', rfl⟩
    obtain ⟨k, hk⟩ := kl_mul hv hw hc i j
    refine ⟨k, (kl v w j)⁻¹ * q * (kl v w j) * q', Q.mul_mem ?_ hq', ?_⟩
    · have := hQ.conj_mem q hq (kl v w j)⁻¹
      simpa using this
    · rw [← hk]
      group
  one_mem' := ⟨0, 1, Q.one_mem, by simp [kl]⟩
  inv_mem' := by
    rintro x ⟨i, q, hq, rfl⟩
    refine ⟨i, kl v w i * q⁻¹ * (kl v w i)⁻¹, hQ.conj_mem _ (Q.inv_mem hq) _, ?_⟩
    have hi := kl_inv hv hw hc i
    have hii : kl v w i * kl v w i = 1 := by
      have := mul_inv_cancel (kl v w i)
      rwa [hi] at this
    rw [mul_inv_rev, hi]
    calc q⁻¹ * kl v w i = (kl v w i * kl v w i) * q⁻¹ * kl v w i := by rw [hii, one_mul]
      _ = kl v w i * (kl v w i * q⁻¹ * kl v w i) := by group

theorem kl_mul_mem_Q {Q : Subgroup H} (hvQ : v ∉ Q) (hwQ : w ∉ Q) (hvwQ : v * w ∉ Q)
    (i j : Fin 4) (h : kl v w i * kl v w j ∈ Q) : i = j := by
  have e1 : v * (v * w) = w := by rw [← mul_assoc, hv, one_mul]
  have e2 : w * (v * w) = v := by rw [← mul_assoc, ← hc, mul_assoc, hw, mul_one]
  have e3 : v * w * v = w := by rw [hc, mul_assoc, hv, mul_one]
  have e4 : v * w * w = v := by rw [mul_assoc, hw, mul_one]
  have q1 : v * (v * w) ∉ Q := by rw [e1]; exact hwQ
  have q2 : w * v ∉ Q := by rw [← hc]; exact hvwQ
  have q3 : w * (v * w) ∉ Q := by rw [e2]; exact hvQ
  have q4 : v * w * v ∉ Q := by rw [e3]; exact hwQ
  have q5 : v * w * w ∉ Q := by rw [e4]; exact hvQ
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (exfalso; simp [kl] at h; exact absurd h (by assumption))

theorem card_klQ {Q : Subgroup H} (hQ : Q.Normal) (hvQ : v ∉ Q) (hwQ : w ∉ Q)
    (hvwQ : v * w ∉ Q) : Nat.card (klQ hv hw hc Q hQ) = 4 * Nat.card Q := by
  have hbij : Function.Bijective (fun p : Fin 4 × Q =>
      (⟨kl v w p.1 * p.2, ⟨p.1, p.2, p.2.2, rfl⟩⟩ : klQ hv hw hc Q hQ)) := by
    constructor
    · rintro ⟨i, q⟩ ⟨j, q'⟩ h
      have h1 : kl v w i * q = kl v w j * q' := congrArg Subtype.val h
      have h2 : (kl v w j)⁻¹ * kl v w i = q' * (q : H)⁻¹ := by
        calc (kl v w j)⁻¹ * kl v w i = (kl v w j)⁻¹ * (kl v w i * q) * (q : H)⁻¹ := by group
          _ = (kl v w j)⁻¹ * (kl v w j * q') * (q : H)⁻¹ := by rw [h1]
          _ = q' * (q : H)⁻¹ := by group
      rw [kl_inv hv hw hc j] at h2
      have hji : j = i := kl_mul_mem_Q hv hw hc hvQ hwQ hvwQ j i
        (h2 ▸ Q.mul_mem q'.2 (Q.inv_mem q.2))
      subst hji
      have : (q : H) = q' := mul_left_cancel h1
      rw [Subtype.ext this]
    · rintro ⟨x, i, q, hq, rfl⟩
      exact ⟨(i, ⟨q, hq⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end Klein

theorem klein_le_of_a4 [Finite H] {Q : Subgroup H} (hQ : Q.Normal) (hQp : IsPGroup 2 Q)
    (hQcard : twoPart (⊤ : Subgroup H) ≤ 4 * Nat.card Q)
    (hself : ∀ S : Subgroup H, IsSylowTwoOf S ⊤ → Subgroup.normalizer (S : Set H) ≤ S)
    {v b : H} (hv : v * v = 1) (hb : b * b * b = 1) (hvw : b * v * b⁻¹ ≠ v)
    (hcomm : v * (b * v * b⁻¹) = (b * v * b⁻¹) * v)
    (hrel : b * (b * v * b⁻¹) * b⁻¹ = v * (b * v * b⁻¹)) : v ∈ Q := by
  set w := b * v * b⁻¹ with hwdef
  have hw : w * w = 1 := by
    calc w * w = b * (v * v) * b⁻¹ := by rw [hwdef]; group
      _ = 1 := by rw [hv]; group
  have hc : v * w = w * v := hcomm
  have hbw : b * w * b⁻¹ = v * w := hrel
  have hbvw : b * (v * w) * b⁻¹ = v := by
    calc b * (v * w) * b⁻¹ = (b * v * b⁻¹) * (b * w * b⁻¹) := by group
      _ = w * (v * w) := by rw [← hwdef, hbw]
      _ = v := by rw [← mul_assoc, ← hc, mul_assoc, hw, mul_one]
  by_contra hvQ
  have hwQ : w ∉ Q := fun h => hvQ (by
    have e : b⁻¹ * w * b⁻¹⁻¹ = v := by rw [hwdef]; group
    rw [← e]
    exact hQ.conj_mem w h b⁻¹)
  have hvwQ : v * w ∉ Q := fun h => hvQ (by
    rw [← hbvw]
    exact hQ.conj_mem (v * w) h b)
  have hb_kl : ∀ i : Fin 4, ∃ k : Fin 4, b * kl v w i * b⁻¹ = kl v w k := by
    intro i
    fin_cases i
    · exact ⟨0, by simp [kl]⟩
    · exact ⟨2, by simp [kl, hwdef]⟩
    · exact ⟨3, by simpa [kl] using hbw⟩
    · exact ⟨1, by simpa [kl] using hbvw⟩
  have hbi_kl : ∀ i : Fin 4, ∃ k : Fin 4, b⁻¹ * kl v w i * b = kl v w k := by
    intro i
    fin_cases i
    · exact ⟨0, by simp [kl]⟩
    · refine ⟨3, ?_⟩
      have := congrArg (fun x => b⁻¹ * x * b) hbvw
      show b⁻¹ * v * b = v * w
      simpa [mul_assoc] using this.symm
    · refine ⟨1, ?_⟩
      show b⁻¹ * w * b = v
      rw [hwdef]
      group
    · refine ⟨2, ?_⟩
      have := congrArg (fun x => b⁻¹ * x * b) hbw
      show b⁻¹ * (v * w) * b = w
      simpa [mul_assoc] using this.symm
  let S := klQ hv hw hc Q hQ
  have hScard : Nat.card S = 4 * Nat.card Q := card_klQ hv hw hc hQ hvQ hwQ hvwQ
  have hSp : IsPGroup 2 S := by
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    exact IsPGroup.of_card (n := k + 2) (by rw [hScard, hk]; ring)
  have hSsyl : IsSylowTwoOf S ⊤ := isSylowTwoOf_of_card_eq le_top hSp
    (le_antisymm (card_le_twoPart le_top hSp) (hScard ▸ hQcard))
  have hconj : ∀ x ∈ S, b * x * b⁻¹ ∈ S := by
    rintro x ⟨i, q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hb_kl i
    exact ⟨k, b * q * b⁻¹, hQ.conj_mem q hq b, by rw [← hk]; group⟩
  have hconj' : ∀ x ∈ S, b⁻¹ * x * b ∈ S := by
    rintro x ⟨i, q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hbi_kl i
    exact ⟨k, b⁻¹ * q * b, by simpa using hQ.conj_mem q hq b⁻¹, by rw [← hk]; group⟩
  have hbN : b ∈ Subgroup.normalizer (S : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hconj x, fun hx => by simpa [mul_assoc] using hconj' _ hx⟩
  have hbS : b ∈ S := hself S hSsyl hbN
  have hb1 : b ≠ 1 := fun h => hvw (by rw [hwdef, h]; simp)
  have hb3 : b ^ 3 = 1 := by rw [pow_succ, pow_two]; exact hb
  have hord : orderOf b = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hb3 hb1
  have hdvd : orderOf (⟨b, hbS⟩ : S) ∣ Nat.card S := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  rw [hScard, hk] at hdvd
  have h3 : 3 ∣ 2 ^ (k + 2) := by
    have : 4 * 2 ^ k = 2 ^ (k + 2) := by ring
    rwa [this] at hdvd
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3)
  omega

end CFSG.Quasithin.H13.F431.U42Aut
