module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgSetup

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

theorem coord_ext {z w : Coord J} (h1 : z.1.1 = w.1.1) (h2 : z.1.2 = w.1.2) : z = w :=
  Subtype.ext (Prod.ext h1 h2)

theorem torus_fst (k : Kˣ) (z : Coord J) :
    (hermitianTorusAction J k z).1.1 = z.1.1 * k * (J.conj (k : K))⁻¹ ^ 2 :=
  congrArg Prod.fst (torusAction_val J k z)

theorem torus_snd (k : Kˣ) (z : Coord J) :
    (hermitianTorusAction J k z).1.2 = z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹ :=
  congrArg Prod.snd (torusAction_val J k z)

theorem mul_fst (z w : Coord J) : (z * w).1.1 = z.1.1 + w.1.1 := rfl

theorem mul_snd (z w : Coord J) : (z * w).1.2 = z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 := rfl

theorem inv_fst (z : Coord J) : (z⁻¹).1.1 = -z.1.1 := rfl

theorem inv_snd (z : Coord J) : (z⁻¹).1.2 = J.conj z.1.2 := rfl

theorem coord_rel (z : Coord J) : z.1.2 + J.conj z.1.2 + z.1.1 * J.conj z.1.1 = 0 := z.2

theorem conj_snd_of_fst_eq_zero {z : Coord J} (hz : z.1.1 = 0) : J.conj z.1.2 = -z.1.2 := by
  have := coord_rel z
  rw [hz, zero_mul, add_zero] at this
  linear_combination this

variable [Finite K] {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ →* Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp

variable (H : SMapHyp J q F σ h)
include H

theorem conj_sigma_mul (k : Kˣ) : J.conj (σ k : K) * k = (σ k : K) * J.conj k := by
  rcases H.sigma_eq k with e | e
  · have e' := congrArg J.conj e
    rw [map_mul, conj_conj, map_one] at e'
    rw [e, e']
  · have e' := congrArg J.conj e
    rw [map_mul, conj_conj, map_neg, map_one] at e'
    rw [e, e']

theorem nrm_sigma (k : Kˣ) : nrm J (σ k) = (nrm J k)⁻¹ := by
  have hsq : ((σ k : K) * J.conj k) * ((σ k : K) * J.conj k) = 1 := by
    rcases H.sigma_eq k with e | e <;> rw [e] <;> ring
  rw [nrm_def, nrm_def]
  apply eq_inv_of_mul_eq_one_left
  calc (σ k : K) * J.conj (σ k : K) * ((k : K) * J.conj k) =
      (σ k : K) * (J.conj (σ k : K) * k) * J.conj k := by ring
    _ = 1 := by rw [H.conj_sigma_mul k]; linear_combination hsq

theorem exists_trace_zero : ∃ c : K, c ≠ 0 ∧ J.conj c = -c := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hq := H.q_ge
  have hog : orderOf g = q * q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units, ← Nat.card_eq_fintype_card, H.card, sq]
  have hne : J.conj (g : K) ≠ g := by
    intro e
    rw [H.conj_pow] at e
    have h1 : g ^ (q - 1) = 1 := by
      apply Units.ext
      have h2 : (g : K) ^ (q - 1) * g = g := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), e]
      simpa using (mul_eq_right₀ g.ne_zero).mp h2
    have h3 := orderOf_le_of_pow_eq_one (by omega) h1
    rw [hog] at h3
    have : q ≤ q * q - q := by
      have : 3 * q ≤ q * q := Nat.mul_le_mul_right q hq
      omega
    omega
  refine ⟨(g : K) - J.conj g, sub_ne_zero.mpr (Ne.symm hne), ?_⟩
  rw [map_sub, conj_conj]; ring

theorem exists_F_center : ∃ κ : K, κ ≠ 0 ∧ J.conj κ = κ ∧
    ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 → (F z).1.1 = 0 ∧ (F z).1.2 = κ / z.1.2 := by
  obtain ⟨c₁, hc₁, hcc₁⟩ := H.exists_trace_zero
  let z₁ : Coord J := ⟨(0, c₁), by simp [hcc₁]⟩
  have hz₁ : z₁ ≠ 1 := fun e => hc₁ (congrArg (fun w : Coord J => w.1.2) e)
  have hF₁ : (F z₁).1.1 = 0 := H.F_Z z₁ hz₁ rfl
  set M₁ := (F z₁).1.2 with hM₁def
  have hM₁ : M₁ ≠ 0 := coord_snd_ne_zero J (H.F_ne z₁ hz₁)
  have hcM₁ : J.conj M₁ = -M₁ := conj_snd_of_fst_eq_zero hF₁
  refine ⟨M₁ * c₁, mul_ne_zero hM₁ hc₁, by rw [map_mul, hcM₁, hcc₁]; ring, ?_⟩
  intro z hz hz0
  refine ⟨H.F_Z z hz hz0, ?_⟩
  set c := z.1.2 with hcdef
  have hc : c ≠ 0 := coord_snd_ne_zero J hz
  have hcc : J.conj c = -c := conj_snd_of_fst_eq_zero hz0
  have hx : c₁ / c ≠ 0 := div_ne_zero hc₁ hc
  have hxc : J.conj (c₁ / c) = c₁ / c := by rw [map_div₀, hcc₁, hcc, neg_div_neg_eq]
  obtain ⟨k, hk⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hx hxc
  have hk' : (k : K) * J.conj (k : K) = c₁ / c := hk
  have hkz : hermitianTorusAction J k z₁ = z := by
    apply coord_ext
    · rw [torus_fst]; simp [z₁, hz0]
    · rw [torus_snd]
      change c₁ * (J.conj (k : K))⁻¹ * (k : K)⁻¹ = c
      rw [mul_assoc, ← mul_inv, mul_comm (J.conj _), hk']
      field_simp
  rw [← hkz, H.F_torus k z₁ hz₁, torus_snd, ← hM₁def]
  have hn : (σ k : K) * J.conj (σ k : K) = (c₁ / c)⁻¹ := by
    have := H.nrm_sigma k
    rw [nrm_def, nrm_def, hk'] at this
    exact this
  rw [mul_assoc, ← mul_inv, mul_comm (J.conj _), hn, inv_inv, mul_div_assoc]

end SMapHyp

end CFSG.UnitaryThreeRecognition.WeylAlg
