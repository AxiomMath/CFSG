module

public import CFSG.Timmesfeld.Transvection.ModelRadical

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank

variable {n : ℕ} {F : Type} [Field F]

open CFSG.LieType.Universal.Symplectic in
theorem tim79a_spMat_inj {x y : StatedSp n F}
    (h : SpExtras.mat n F x = SpExtras.mat n F y) : x = y :=
  SpExtras.mat_injective h

theorem tim79a_spNil_mul_spNil_self (v : Fin n ⊕ Fin n → F) : spNil v * spNil v = 0 := by
  rw [spNil_mul_spNil, spForm_self, zero_smul]

theorem tim79a_spNil_mul_spNil_mul (v w : Fin n ⊕ Fin n → F) :
    spNil v * spNil w * spNil v = (spForm v w * spForm w v) • spNil v := by
  refine Matrix.ext_iff_mulVec.2 fun x => ?_
  simp only [← mulVec_mulVec, smul_mulVec, spNil_mulVec, spForm_smul_right', smul_smul]
  congr 1
  ring

theorem tim79a_spNil_ne_zero {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) : spNil a ≠ 0 := by
  intro h
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero ha
  have h1 : spNil a *ᵥ y = 0 := by rw [h, zero_mulVec]
  rw [spNil_mulVec] at h1
  exact ha ((smul_eq_zero.1 h1).resolve_left hy)

theorem tim79a_cube_of_involutions {R : Type*} [Monoid R] {A B : R} (hA : A * A = 1)
    (hB : B * B = 1) (hABA : A * B * A = B * A * B) : (A * B) ^ 3 = 1 := by
  rw [pow_three]
  calc A * B * (A * B * (A * B)) = A * B * A * (B * A * B) := by simp only [mul_assoc]
    _ = A * B * A * (A * B * A) := by rw [← hABA]
    _ = A * (B * (A * A * (B * A))) := by simp only [mul_assoc]
    _ = A * (B * (B * A)) := by rw [hA, one_mul]
    _ = A * (B * B * A) := by simp only [mul_assoc]
    _ = A * A := by rw [hB, one_mul]
    _ = 1 := hA

theorem tim79a_braid_of_relations {R : Type*} [Ring R] (h2 : ∀ x : R, x + x = 0) {u v : R}
    (hu2 : u * u = 0) (hv2 : v * v = 0) (huvu : u * v * u = u) (hvuv : v * u * v = v) :
    ((1 + u) * (1 + v)) ^ 3 = 1 := by
  have hAA : (1 + u) * (1 + u) = 1 := by
    calc (1 + u) * (1 + u) = 1 + (u + u) + u * u := by noncomm_ring
      _ = 1 := by simp only [h2 u, hu2, add_zero]
  have hBB : (1 + v) * (1 + v) = 1 := by
    calc (1 + v) * (1 + v) = 1 + (v + v) + v * v := by noncomm_ring
      _ = 1 := by simp only [h2 v, hv2, add_zero]
  refine tim79a_cube_of_involutions hAA hBB ?_
  have e1 : (1 + u) * (1 + v) * (1 + u) = 1 + u + v + u * v + u + u * u + v * u + u * v * u := by
    noncomm_ring
  have e2 : (1 + v) * (1 + u) * (1 + v) = 1 + v + u + v * u + v + v * v + u * v + v * u * v := by
    noncomm_ring
  rw [e1, e2, hu2, hv2, huvu, hvuv]
  calc 1 + u + v + u * v + u + 0 + v * u + u
      = (1 + v + u + v * u + v + 0 + u * v + v) + (u + u) - (v + v) := by abel
    _ = 1 + v + u + v * u + v + 0 + u * v + v := by
      simp only [h2 u, h2 v, add_zero, sub_zero]

theorem tim79a_eq_zero_of_eq_one {R : Type*} [Ring R] {u v : R} (hu2 : u * u = 0)
    (huvu : u * v * u = u) (h : (1 + u) * (1 + v) = 1) : u = 0 := by
  have e : (1 + u) * (1 + v) = 1 + (u + v + u * v) := by noncomm_ring
  rw [e] at h
  have h1 : u + v + u * v = 0 := add_left_cancel (h.trans (add_zero (1 : R)).symm)
  have e2 : u * (u + v + u * v) * u = u * u * u + u * v * u + u * u * v * u := by
    noncomm_ring
  have h3 : u * (u + v + u * v) * u = 0 := by rw [h1, mul_zero, zero_mul]
  rw [e2, hu2, huvu] at h3
  simpa using h3

theorem tim79a_braid_key [CharP F 2] {a a' : Fin n ⊕ Fin n → F} {s r : F} (ha : a ≠ 0)
    (hB : spForm a a' ≠ 0) (hs : s ≠ 0) (hr : r * (s * spForm a a' * spForm a a') = 1) :
    (spTrans a s * spTrans a' r) ^ 3 = 1 ∧ spTrans a s * spTrans a' r ≠ 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hadd : ∀ X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F, X + X = 0 := by
    intro X
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hβ : spForm a' a = -spForm a a' := spForm_comm a a'
  have hu2 : (s • spNil a) * (s • spNil a) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, tim79a_spNil_mul_spNil_self, smul_zero, smul_zero]
  have hv2 : (r • spNil a') * (r • spNil a') = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, tim79a_spNil_mul_spNil_self, smul_zero, smul_zero]
  have hc1 : s * (r * s) * (spForm a a' * spForm a' a) = s := by
    rw [hβ]
    linear_combination (-s) * hr + (-s) * h2
  have hc2 : r * (s * r) * (spForm a' a * spForm a a') = r := by
    rw [hβ]
    linear_combination (-r) * hr + (-r) * h2
  have huvu : (s • spNil a) * (r • spNil a') * (s • spNil a) = s • spNil a := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [tim79a_spNil_mul_spNil_mul, smul_smul, hc1]
  have hvuv : (r • spNil a') * (s • spNil a) * (r • spNil a') = r • spNil a' := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [tim79a_spNil_mul_spNil_mul, smul_smul, hc2]
  refine ⟨tim79a_braid_of_relations hadd hu2 hv2 huvu hvuv, fun h => ?_⟩
  exact tim79a_spNil_ne_zero ha
    ((smul_eq_zero.1 (tim79a_eq_zero_of_eq_one hu2 huvu h)).resolve_left hs)

theorem spOppMeetModel_holds :
    ∀ (n : ℕ) (F : Type) [Field F] (a a' : Fin n ⊕ Fin n → F)
      (T T' : Subgroup (StatedSp n F)), IsTransGroup a T → IsTransGroup a' T' →
      spForm a a' ≠ 0 → T' ⊓ Subgroup.normalizer (T : Set (StatedSp n F)) = ⊥ := by
  intro n F _ a a' T T' hT hT' hB
  rw [eq_bot_iff]
  rintro g ⟨hgT', hgN⟩
  have ha : a ≠ 0 := by
    rintro rfl
    exact hB (by simp [spForm])
  have hgL : g ∈ spLine a := by
    rw [← normalizer_eq_spLine ha hT]
    exact hgN
  obtain ⟨μ, -, hμ⟩ := hgL
  obtain ⟨c, hc⟩ := (hT'.1 g).1 hgT'
  have hcomb : a + (c * spForm a' a) • a' = μ • a := by
    have h1 := spTrans_mulVec a' a c
    rw [← hc, hμ] at h1
    exact h1.symm
  have h3 : spForm a (a + (c * spForm a' a) • a') = spForm a (μ • a) := by
    rw [hcomb]
  simp only [spForm_add_right, spForm_smul_right', spForm_self, mul_zero, zero_add] at h3
  have hs : spForm a' a ≠ 0 := by
    rw [spForm_comm]
    exact neg_ne_zero.2 hB
  have hc0 : c = 0 := by
    rcases mul_eq_zero.1 h3 with h4 | h4
    · rcases mul_eq_zero.1 h4 with h5 | h5
      · exact h5
      · exact absurd h5 hs
    · exact absurd h4 hB
  rw [Subgroup.mem_bot]
  apply tim79a_spMat_inj
  rw [hc, hc0, spTrans_zero, map_one]

theorem spBraidModel_holds :
    ∀ (n : ℕ) (F : Type) [Field F] [CharP F 2] (a a' : Fin n ⊕ Fin n → F)
      (T T' : Subgroup (StatedSp n F)), IsTransGroup a T → IsTransGroup a' T' →
      spForm a a' ≠ 0 → ∀ t ∈ T, t ≠ 1 → ∃ t' ∈ T', orderOf (t * t') = 3 := by
  intro n F _ _ a a' T T' hT hT' hB t ht ht1
  obtain ⟨s, hs⟩ := (hT.1 t).1 ht
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply ht1
    apply tim79a_spMat_inj
    rw [hs, spTrans_zero, map_one]
  have ha : a ≠ 0 := by
    rintro rfl
    exact hB (by simp [spForm])
  have hne : s * spForm a a' * spForm a a' ≠ 0 := mul_ne_zero (mul_ne_zero hs0 hB) hB
  obtain ⟨t₀, ht₀⟩ := hT'.2 (s * spForm a a' * spForm a a')⁻¹
  refine ⟨t₀, (hT'.1 t₀).2 ⟨_, ht₀⟩, ?_⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr : (s * spForm a a' * spForm a a')⁻¹ * (s * spForm a a' * spForm a a') = 1 :=
    inv_mul_cancel₀ hne
  obtain ⟨hcube, hne1⟩ := tim79a_braid_key ha hB hs0 hr
  have hpow : (t * t₀) ^ 3 = 1 := by
    apply tim79a_spMat_inj
    rw [map_pow, map_mul, map_one, hs, ht₀]
    exact hcube
  have hprod : t * t₀ ≠ 1 := by
    intro h
    apply hne1
    rw [← hs, ← ht₀, ← map_mul, h, map_one]
  exact orderOf_eq_prime hpow hprod

end CFSG.RankThree.GF2n.Tim79a
