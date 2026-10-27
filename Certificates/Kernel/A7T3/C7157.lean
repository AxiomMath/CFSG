module

public import Certificates.Data.A7T3
public import Certificates.Kernel.A7T3.Chk7157
public import CFSG.Certificates.Kernel.Misc.A7NatSound

public section

namespace CertificateChecks.KernelA7T3

open Equiv CFSG.KD.A7T3K CFSG.KC.LQT.P CFSG.KC.Ord CFSG.KD.A7Nat CFSG.KC.A7Nat

theorem t0_codes : A7T3.T0l.map code = t0C := by
  simp only [A7T3.T0l, A7T3.ga, A7T3.gb, List.map_cons, List.map_nil, ← code_mul h7, ← code_swap,
    ← code_one]
  decide +kernel

theorem small_facts : A7T3.mulT0 ∧ A7T3.invT0 ∧ A7T3.T0l.Nodup ∧ A7T3.evenT0 := by
  have h := ch7157_small
  rw [smallK, andB_iff, ← t0_codes, allL_map] at h
  obtain ⟨-, hm, hi, hn⟩ := grp_of rfl h.1
  exact ⟨hm, hi, hn, fun a ha => (even_code h7 a).1 (h.2 a ha)⟩

theorem permT0_of {σ : Perm (Fin 7)} (hp : A7T3.permT0 σ) :
    ∀ t ∈ A7T3.T0l, ∃ u ∈ A7T3.T0l, t * σ = u ∨ t * σ = σ * u ∨ t * σ = σ * σ * u := by
  intro t ht
  obtain ⟨j, t', ht', e⟩ := hp t ht
  have hj := j.isLt
  have hj' : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 := by omega
  rcases hj' with hj' | hj' | hj' <;> rw [hj'] at e
  · exact ⟨t', ht', Or.inl (by rw [e, pow_zero, one_mul])⟩
  · exact ⟨t', ht', Or.inr (Or.inl (by rw [e, pow_one]))⟩
  · exact ⟨t', ht', Or.inr (Or.inr (by rw [e, pow_two]))⟩

theorem cond_of (σ : Perm (Fin 7)) (h : condK (A7T3.T0l.map code) (code σ) = true) :
    A7T3.cond σ := by
  simp only [condK, permT0K, letB_eq, code_mul h7, code_one, impB_iff, andB_iff, orB_iff,
    beq_iff, code_eq_iff h7, allL_map, anyL_map] at h
  intro _ h9
  have e9 : σ ^ 9 = σ * (σ * σ) * (σ * (σ * σ) * (σ * (σ * σ))) := by
    rw [← pow_three, ← pow_three, ← pow_mul]
  rw [e9] at h9
  obtain ⟨h3, hq⟩ := h h9
  have hinv : σ⁻¹ = σ * σ := inv_eq_of_mul_eq_one_right h3
  refine ⟨by rw [pow_three, h3], fun hp => ?_⟩
  obtain ⟨t, ht, e⟩ := hq (permT0_of hp)
  exact ⟨t, ht, by rw [e, hinv, mul_inv_cancel_right]⟩

theorem stmt_true : A7T3.stmt := by
  obtain ⟨hm, hi, hn, he⟩ := small_facts
  refine ⟨hm, hi, hn, he, fun σ => cond_of σ ?_⟩
  have h := ch7157_all
  rw [allK, ← t0_codes, allP_iff] at h
  exact h σ

end CertificateChecks.KernelA7T3

end
