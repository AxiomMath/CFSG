module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem Kl1_four : ∀ l ∈ Kl1L, l = idL ∨ l = dL ∨ l = a1L ∨ l = comp a1L dL := by decide +kernel

theorem Alt1_dec : ∀ l ∈ Alt1L, ∃ k ∈ Kl1L, ∃ i ∈ [0, 1, 2], l = comp k (powL b1L i) := by
  decide +kernel

theorem a1_facts : a1L ≠ idL ∧ a1L ≠ dL ∧ a1L ∈ Kl1L := by decide +kernel

@[expose] noncomputable def aA : Ah := Classical.choose (exists_elt_Kl1 (l := a1L) a1_facts.2.2)

theorem aA_mem_Kl1h : aA ∈ Kl1h :=
  (Classical.choose_spec (exists_elt_Kl1 (l := a1L) a1_facts.2.2)).1

theorem repL_aA : RepL a1L (aA : P45) :=
  (Classical.choose_spec (exists_elt_Kl1 (l := a1L) a1_facts.2.2)).2

@[expose] noncomputable def b1A : Ah := Classical.choose (exists_elt_Alt1 (l := b1L) b1_check.1)

theorem b1A_mem_Alt1h : b1A ∈ Alt1h :=
  (Classical.choose_spec (exists_elt_Alt1 (l := b1L) b1_check.1)).1

theorem repL_b1A : RepL b1L (b1A : P45) :=
  (Classical.choose_spec (exists_elt_Alt1 (l := b1L) b1_check.1)).2

theorem b1A_cube : b1A ^ 3 = 1 := pow_three_of_repL repL_b1A b1_check.2.2.1

theorem b1A_inv : b1A⁻¹ = b1A * b1A := by
  have h : b1A * (b1A * b1A) = 1 := by
    have := b1A_cube
    simpa [pow_succ, mul_assoc] using this
  exact inv_eq_of_mul_eq_one_right h

theorem repL_b1A_inv : RepL (comp b1L b1L) ((b1A⁻¹ : Ah) : P45) := by
  rw [b1A_inv]
  exact repL_mul repL_b1A repL_b1A

theorem b1A_conj_Kl1h {v : Ah} (hv : v ∈ Kl1h) : b1A * v * b1A⁻¹ ∈ Kl1h := by
  obtain ⟨l, hl, hr⟩ := hv
  refine ⟨comp (comp b1L l) (comp b1L b1L), b1_check.2.2.2.2.1 l hl, ?_⟩
  exact repL_mul (repL_mul repL_b1A hr) repL_b1A_inv

theorem mem_Kl1h_four {k : Ah} (hk : k ∈ Kl1h) :
    k = 1 ∨ k = dA ∨ k = aA ∨ k = aA * dA := by
  obtain ⟨l, hl, hr⟩ := hk
  rcases Kl1_four l hl with h | h | h | h
  · left
    have hrl : RepL idL (k : P45) := by rw [← h]; exact hr
    exact Subtype.ext (eq_of_repL hrl (repL_one 45))
  · right; left
    have hrl : RepL dL (k : P45) := by rw [← h]; exact hr
    exact Subtype.ext (eq_of_repL hrl repL_dA)
  · right; right; left
    have hrl : RepL a1L (k : P45) := by rw [← h]; exact hr
    exact Subtype.ext (eq_of_repL hrl repL_aA)
  · right; right; right
    have hrl : RepL (comp a1L dL) (k : P45) := by rw [← h]; exact hr
    exact Subtype.ext (eq_of_repL hrl (repL_mul repL_aA repL_dA))

theorem mem_Alt1h_dec {p : Ah} (hp : p ∈ Alt1h) :
    ∃ k ∈ Kl1h, ∃ i : ℕ, i < 3 ∧ p = k * b1A ^ i := by
  obtain ⟨l, hl, hr⟩ := hp
  obtain ⟨kL, hk, i, hi, hli⟩ := Alt1_dec l hl
  obtain ⟨κ, hκ, hκr⟩ := exists_elt_Kl1 hk
  have hi3 : i < 3 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    omega
  refine ⟨κ, hκ, i, hi3, ?_⟩
  have h1 : RepL l ((κ : P45) * ((b1A ^ i : Ah) : P45)) := by
    rw [hli]
    exact repL_mul hκr (repL_powL repL_b1A i)
  exact Subtype.ext (eq_of_repL hr h1)

theorem Alt1_inner_elt {q : Ah} (hq : q ∈ Alt1h)
    (h : ∀ v ∈ Kl1h, q * v = (b1A * v * b1A⁻¹) * q) : ∃ w ∈ Kl1h, q = w * b1A * w := by
  obtain ⟨lq, hlq, hrq⟩ := hq
  have key : ∀ v ∈ Kl1L, comp lq v = comp (comp (comp b1L v) (comp b1L b1L)) lq := by
    intro v hv
    obtain ⟨κ, hκ, hκr⟩ := exists_elt_Kl1 hv
    have h1 : RepL (comp lq v) ((q * κ : Ah) : P45) := repL_mul hrq hκr
    have h2 : RepL (comp (comp (comp b1L v) (comp b1L b1L)) lq)
        (((b1A * κ * b1A⁻¹) * q : Ah) : P45) :=
      repL_mul (repL_mul (repL_mul repL_b1A hκr) repL_b1A_inv) hrq
    rw [← h κ hκ] at h2
    exact repL_unique h1 h2
  obtain ⟨w, hw, hlw⟩ := Alt1_inner lq hlq key
  obtain ⟨ω, hω, hωr⟩ := exists_elt_Kl1 hw
  refine ⟨ω, hω, ?_⟩
  have h1 : RepL lq ((ω : P45) * (b1A : P45) * (ω : P45)) := by
    rw [hlw]
    exact repL_mul (repL_mul hωr repL_b1A) hωr
  exact Subtype.ext (eq_of_repL hrq h1)

theorem Uh_comm_b1 {u : Ah} (hu : u ∈ Uh) (hc : u * b1A = b1A * u) : u = 1 := by
  obtain ⟨l, hl, hr⟩ := hu
  have h1 : comp l b1L = comp b1L l := comp_comm_of_comm (v := b1A) repL_b1A hr hc
  have h2 := CU_b1 l hl h1
  have hrl : RepL idL (u : P45) := by rw [← h2]; exact hr
  exact Subtype.ext (eq_of_repL hrl (repL_one 45))

end CFSG.Quasithin.H13.F431.U42Aut
