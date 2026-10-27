module

public import CFSG.RankThree.GF2n.Smith81.S81A5Basic
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TotallySplit
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix

@[expose] def IsTransvec (K : Type*) [Field K] {n : ℕ} (g : GL (Fin n) K) : Prop :=
  ((g : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1) = 0 ∧
    Matrix.rank ((g : Matrix (Fin n) (Fin n) K) - 1) = 1

@[expose] noncomputable def transvGL (K : Type*) [Field K] (i j : Fin 6) (hij : i ≠ j) (c : K) :
    GL (Fin 6) K :=
  Matrix.SpecialLinearGroup.toGL
    (Matrix.TransvectionStruct.toSpecialLinearGroup
      (⟨i, j, hij, c⟩ : Matrix.TransvectionStruct (Fin 6) K))

variable {K : Type*} [Field K]

theorem transvGL_val (i j : Fin 6) (hij : i ≠ j) (c : K) :
    (transvGL K i j hij c : Matrix (Fin 6) (Fin 6) K) = Matrix.transvection i j c := rfl

theorem sq_eq_one_of_sub_one_sq [CharP K 2] {n : Type*} [Fintype n] [DecidableEq n]
    {t : Matrix n n K} (h : (t - 1) * (t - 1) = 0) : t * t = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs : ∀ x : Matrix n n K, x + x = 0 := fun x => by
    rw [← two_smul K x, h2, zero_smul]
  have key : t * t - 1 = (t - 1) * (t - 1) + (t + t) - (1 + 1) := by noncomm_ring
  rw [h, hs t, hs 1, add_zero, sub_zero] at key
  exact sub_eq_zero.mp key

theorem fe3_vecMulVec_mul {n : ℕ} (a f b g : Fin n → K) :
    vecMulVec a f * vecMulVec b g = (f ⬝ᵥ b) • vecMulVec a g := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]

theorem exists_vecMulVec_of_rank_eq_one {n : ℕ} {M : Matrix (Fin n) (Fin n) K} (h : M.rank = 1) :
    ∃ a f : Fin n → K, M = vecMulVec a f := by
  rw [Matrix.rank_eq_finrank_span_cols] at h
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 h
  have hcol : ∀ j : Fin n, ∃ c : K, c • (v : Fin n → K) = M.col j := fun j => by
    obtain ⟨c, hc⟩ := hv ⟨M.col j, Submodule.subset_span ⟨j, rfl⟩⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose f hf using hcol
  refine ⟨(v : Fin n → K), f, ?_⟩
  ext i j
  have h1 := congrFun (hf j) i
  rw [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at h1
  rw [vecMulVec_apply, ← h1, mul_comm]

theorem IsTransvec.exists {n : ℕ} {g : GL (Fin n) K} (hg : IsTransvec K g) :
    ∃ a f : Fin n → K, a ≠ 0 ∧ f ≠ 0 ∧ f ⬝ᵥ a = 0 ∧
      (g : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec a f := by
  obtain ⟨hsq, hrk⟩ := hg
  obtain ⟨a, f, hN⟩ := exists_vecMulVec_of_rank_eq_one hrk
  rw [hN] at hsq hrk
  have hne : vecMulVec a f ≠ 0 := by
    intro h0
    rw [h0, Matrix.rank_zero] at hrk
    exact zero_ne_one hrk
  have ha : a ≠ 0 := by
    rintro rfl
    exact hne (Matrix.zero_vecMulVec f)
  have hf : f ≠ 0 := by
    rintro rfl
    exact hne (Matrix.vecMulVec_zero a)
  have hfa : f ⬝ᵥ a = 0 := by
    rw [fe3_vecMulVec_mul] at hsq
    rcases smul_eq_zero.1 hsq with h0 | h0
    · exact h0
    · exact absurd h0 hne
  refine ⟨a, f, ha, hf, hfa, ?_⟩
  rw [← hN]
  abel

theorem one_add_mul_one_add_sub_one (a b f g : Fin 6 → K) :
    (1 + vecMulVec a f) * (1 + vecMulVec b g) - 1 =
      vecMulVec a f + vecMulVec b g + (f ⬝ᵥ b) • vecMulVec a g := by
  simp only [add_mul, mul_add, one_mul, mul_one, fe3_vecMulVec_mul]
  abel

theorem unipotent_cube_zero (a b f g : Fin 6 → K) (hfa : f ⬝ᵥ a = 0) (hgb : g ⬝ᵥ b = 0)
    (h : (f ⬝ᵥ b) * (g ⬝ᵥ a) = 0) :
    ((vecMulVec a f + vecMulVec b g + (f ⬝ᵥ b) • vecMulVec a g) ^ 3 : Matrix (Fin 6) (Fin 6) K) = 0 := by
  rw [pow_three]
  rcases mul_eq_zero.1 h with hα | hβ
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
      fe3_vecMulVec_mul, hfa, hgb, hα, zero_smul, smul_zero, zero_add, add_zero, mul_zero,
      zero_mul]
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
      fe3_vecMulVec_mul, hfa, hgb, hβ, zero_smul, smul_zero, zero_add, add_zero, mul_zero,
      zero_mul]

theorem fe3_pairing_ne_zero [CharP K 2] {x y : GL (Fin 6) K} {a b f g : Fin 6 → K}
    (hx : (x : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f)
    (hy : (y : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec b g)
    (hfa : f ⬝ᵥ a = 0) (hgb : g ⬝ᵥ b = 0) (hodd : Odd (orderOf (x * y))) (hne : x * y ≠ 1) :
    f ⬝ᵥ b ≠ 0 ∧ g ⬝ᵥ a ≠ 0 := by
  have hprod : (f ⬝ᵥ b) * (g ⬝ᵥ a) ≠ 0 := by
    intro h0
    have hu3 := unipotent_cube_zero a b f g hfa hgb h0
    set u : Matrix (Fin 6) (Fin 6) K := vecMulVec a f + vecMulVec b g + (f ⬝ᵥ b) • vecMulVec a g
      with hu
    have hxy : ((x * y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 + u := by
      rw [Units.val_mul, hx, hy, hu, ← one_add_mul_one_add_sub_one a b f g]
      abel
    have hu4 : u ^ (2 ^ 2) = 0 := pow_eq_zero_of_le (by norm_num) hu3
    have h4 : ((x * y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ (2 ^ 2) = 1 := by
      rw [hxy, add_pow_char_pow_of_commute 2 2 (Commute.one_left u), one_pow, hu4, add_zero]
    have hpow : (x * y) ^ (2 ^ 2) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact h4
    obtain ⟨i, -, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow)
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [pow_zero] at hoi
      exact hne (orderOf_eq_one_iff.1 hoi)
    · rw [hoi] at hodd
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [pow_succ] at hodd
      obtain ⟨t, ht⟩ := hodd
      omega
  exact ⟨fun h0 => hprod (by rw [h0, zero_mul]), fun h0 => hprod (by rw [h0, mul_zero])⟩

theorem linearIndependent_pair {a b f : Fin 6 → K} (ha : a ≠ 0) (hfa : f ⬝ᵥ a = 0)
    (hfb : f ⬝ᵥ b ≠ 0) : LinearIndependent K ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : t * (f ⬝ᵥ b) = 0 := by
    have h2 : f ⬝ᵥ (s • a + t • b) = 0 := by rw [hst, dotProduct_zero]
    simpa [dotProduct_add, dotProduct_smul, hfa] using h2
  have ht : t = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hfb
  subst ht
  refine ⟨?_, rfl⟩
  have h3 : s • a = 0 := by simpa using hst
  rcases smul_eq_zero.mp h3 with h | h
  · exact h
  · exact absurd h ha

theorem exists_det_one_mulVec_two {a b : Fin 6 → K} (h : LinearIndependent K ![a, b]) :
    ∃ s : Matrix (Fin 6) (Fin 6) K, s.det = 1 ∧ s.mulVec a = e K 0 ∧ s.mulVec b = e K 1 := by
  have he : LinearIndependent K ![e K 0, e K 1] := by
    refine linearIndependent_pair (f := e K 1) ?_ ?_ ?_
    · intro h0
      have h00 := congrFun h0 0
      simp [e] at h00
    · simp [e, single_one_dotProduct, Pi.single_apply]
    · simp [e, single_one_dotProduct]
  obtain ⟨g, hg, hgv⟩ := exists_sl_of_linearIndependent (by norm_num : (2 : ℕ) < 6) h he
  exact ⟨g, hg, hgv 0, hgv 1⟩

theorem conj_one_add_vecMulVec (c : GL (Fin 6) K) (a f : Fin 6 → K) :
    (c : Matrix (Fin 6) (Fin 6) K) * (1 + vecMulVec a f) * ((c⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + vecMulVec ((c : Matrix (Fin 6) (Fin 6) K).mulVec a)
        (f ᵥ* ((c⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := by
  have hc : (c : Matrix (Fin 6) (Fin 6) K) * ((c⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 :=
    Units.mul_inv c
  rw [mul_add, add_mul, mul_one, hc, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

theorem transvection_zero_one_eq (α : K) :
    Matrix.transvection (0 : Fin 6) 1 α = 1 + vecMulVec (e K 0) (fun j => if j = 1 then α else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, Matrix.vecMulVec, e, Pi.single_apply]

theorem transvection_one_zero_eq (β : K) :
    Matrix.transvection (1 : Fin 6) 0 β = 1 + vecMulVec (e K 1) (fun j => if j = 0 then β else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, Matrix.vecMulVec, e, Pi.single_apply]

theorem fe3_vecMulVec_mulVec (u v x : Fin 6 → K) : (vecMulVec u v).mulVec x = (v ⬝ᵥ x) • u := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem fe3_mulVec_unipotent (u w x : Fin 6 → K) :
    (1 + vecMulVec (e K 0) u + vecMulVec (e K 1) w : Matrix (Fin 6) (Fin 6) K).mulVec x =
      x + (u ⬝ᵥ x) • e K 0 + (w ⬝ᵥ x) • e K 1 := by
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, fe3_vecMulVec_mulVec,
    fe3_vecMulVec_mulVec]

theorem fe3_unipotent_det (u w : Fin 6 → K) (hu0 : u 0 = 0) (hu1 : u 1 = 0) (hw0 : w 0 = 0)
    (hw1 : w 1 = 0) :
    (1 + vecMulVec (e K 0) u + vecMulVec (e K 1) w : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [Fin.prod_univ_six, Matrix.one_apply, Matrix.vecMulVec, e, Pi.single_apply, hu0, hu1, hw0, hw1]
  · intro i j hji
    revert hji
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, Matrix.vecMulVec, e, Pi.single_apply, hu0, hu1, hw0, hw1]

theorem exists_unipotent_normalizer {f₁ g₁ : Fin 6 → K} {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hf0 : f₁ 0 = 0) (hf1 : f₁ 1 = α) (hg0 : g₁ 0 = β) (hg1 : g₁ 1 = 0) :
    ∃ S : Matrix (Fin 6) (Fin 6) K, S.det = 1 ∧ S.mulVec (e K 0) = e K 0 ∧ S.mulVec (e K 1) = e K 1 ∧
      ∀ j : Fin 6, 2 ≤ j.val → f₁ ⬝ᵥ S.mulVec (e K j) = 0 ∧ g₁ ⬝ᵥ S.mulVec (e K j) = 0 := by
  obtain ⟨u, hu0, hu1, hu⟩ : ∃ u : Fin 6 → K, u 0 = 0 ∧ u 1 = 0 ∧
      ∀ j : Fin 6, 2 ≤ j.val → u j = -(g₁ j / β) :=
    ⟨fun j => if 2 ≤ j.val then -(g₁ j / β) else 0, by simp, by simp, fun j hj => by simp [hj]⟩
  obtain ⟨w, hw0, hw1, hw⟩ : ∃ w : Fin 6 → K, w 0 = 0 ∧ w 1 = 0 ∧
      ∀ j : Fin 6, 2 ≤ j.val → w j = -(f₁ j / α) :=
    ⟨fun j => if 2 ≤ j.val then -(f₁ j / α) else 0, by simp, by simp, fun j hj => by simp [hj]⟩
  refine ⟨1 + vecMulVec (e K 0) u + vecMulVec (e K 1) w, fe3_unipotent_det u w hu0 hu1 hw0 hw1,
    ?_, ?_, ?_⟩
  · rw [fe3_mulVec_unipotent]
    simp [e, hu0, hw0]
  · rw [fe3_mulVec_unipotent]
    simp [e, hu1, hw1]
  · intro j hj
    rw [fe3_mulVec_unipotent]
    constructor
    · simp [e, dotProduct_add, dotProduct_smul, dotProduct_single_one, hu j hj, hw j hj, hf0, hf1, hα]
    · simp [e, dotProduct_add, dotProduct_smul, dotProduct_single_one, hu j hj, hw j hj, hg0, hg1, hβ]

theorem fe3_vecMul_apply_e (M : Matrix (Fin 6) (Fin 6) K) (f : Fin 6 → K) (j : Fin 6) :
    (f ᵥ* M) j = f ⬝ᵥ (M *ᵥ e K j) := by
  rw [Matrix.dotProduct_mulVec]
  simp [e]

theorem fe3_conj_explicit {a b f g : Fin 6 → K} (ha : a ≠ 0) (hfa : f ⬝ᵥ a = 0) (hgb : g ⬝ᵥ b = 0)
    (hα : f ⬝ᵥ b ≠ 0) (hβ : g ⬝ᵥ a ≠ 0) :
    ∃ c : GL (Fin 6) K, (c : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      (c : Matrix (Fin 6) (Fin 6) K) * (1 + vecMulVec a f) *
          ((c⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Matrix.transvection 0 1 (f ⬝ᵥ b) ∧
      (c : Matrix (Fin 6) (Fin 6) K) * (1 + vecMulVec b g) *
          ((c⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Matrix.transvection 1 0 (g ⬝ᵥ a) := by
  obtain ⟨s, hsdet, hsa, hsb⟩ := exists_det_one_mulVec_two (linearIndependent_pair ha hfa hα)
  have hsu : IsUnit s.det := by rw [hsdet]; exact isUnit_one
  have hsinv : s⁻¹ * s = 1 := Matrix.nonsing_inv_mul s hsu
  have hsinvdet : s⁻¹.det = 1 := by simp [Matrix.det_nonsing_inv, hsdet]
  have hsi0 : s⁻¹ *ᵥ e K 0 = a := by rw [← hsa, Matrix.mulVec_mulVec, hsinv, Matrix.one_mulVec]
  have hsi1 : s⁻¹ *ᵥ e K 1 = b := by rw [← hsb, Matrix.mulVec_mulVec, hsinv, Matrix.one_mulVec]
  have hf0 : (f ᵥ* s⁻¹) 0 = 0 := by rw [fe3_vecMul_apply_e, hsi0, hfa]
  have hf1 : (f ᵥ* s⁻¹) 1 = f ⬝ᵥ b := by rw [fe3_vecMul_apply_e, hsi1]
  have hg0 : (g ᵥ* s⁻¹) 0 = g ⬝ᵥ a := by rw [fe3_vecMul_apply_e, hsi0]
  have hg1 : (g ᵥ* s⁻¹) 1 = 0 := by rw [fe3_vecMul_apply_e, hsi1, hgb]
  obtain ⟨S, hSdet, hSe0, hSe1, hS⟩ := exists_unipotent_normalizer hα hβ hf0 hf1 hg0 hg1
  have hPdet : (s⁻¹ * S).det = 1 := by rw [Matrix.det_mul, hsinvdet, hSdet, one_mul]
  obtain ⟨P, hPval⟩ : ∃ P : GL (Fin 6) K, (P : Matrix (Fin 6) (Fin 6) K) = s⁻¹ * S :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (s⁻¹ * S) (by rw [hPdet]; exact one_ne_zero),
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _⟩
  have hPe0 : (P : Matrix (Fin 6) (Fin 6) K) *ᵥ e K 0 = a := by
    rw [hPval, ← Matrix.mulVec_mulVec, hSe0, hsi0]
  have hPe1 : (P : Matrix (Fin 6) (Fin 6) K) *ᵥ e K 1 = b := by
    rw [hPval, ← Matrix.mulVec_mulVec, hSe1, hsi1]
  have hPj : ∀ j : Fin 6, 2 ≤ j.val →
      f ⬝ᵥ ((P : Matrix (Fin 6) (Fin 6) K) *ᵥ e K j) = 0 ∧
        g ⬝ᵥ ((P : Matrix (Fin 6) (Fin 6) K) *ᵥ e K j) = 0 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hS j hj
    rw [hPval, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec f, Matrix.dotProduct_mulVec g]
    exact ⟨h1, h2⟩
  refine ⟨P⁻¹, ?_, ?_, ?_⟩
  · have h : ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det *
        (P : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    rw [hPval, hPdet, mul_one] at h
    exact h
  · have hc_e0 : ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ a = e K 0 := by
      rw [← hPe0, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have hfP : f ᵥ* (P : Matrix (Fin 6) (Fin 6) K) = fun j => if j = 1 then f ⬝ᵥ b else 0 := by
      funext j
      rw [fe3_vecMul_apply_e]
      by_cases hj0 : j = 0
      · subst hj0
        simp [hPe0, hfa]
      · by_cases hj1 : j = 1
        · subst hj1
          simp [hPe1]
        · have hj2 : 2 ≤ j.val := by
            have h0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
            have h1 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
            omega
          rw [(hPj j hj2).1, if_neg hj1]
    rw [conj_one_add_vecMulVec, inv_inv, hc_e0, hfP, transvection_zero_one_eq]
  · have hc_e1 : ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ b = e K 1 := by
      rw [← hPe1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have hgP : g ᵥ* (P : Matrix (Fin 6) (Fin 6) K) = fun j => if j = 0 then g ⬝ᵥ a else 0 := by
      funext j
      rw [fe3_vecMul_apply_e]
      by_cases hj0 : j = 0
      · subst hj0
        simp [hPe0]
      · by_cases hj1 : j = 1
        · subst hj1
          simp [hPe1, hgb]
        · have hj2 : 2 ≤ j.val := by
            have h0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
            have h1 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
            omega
          rw [(hPj j hj2).2, if_neg hj0]
    rw [conj_one_add_vecMulVec, inv_inv, hc_e1, hgP, transvection_one_zero_eq]

theorem fe3_conj [CharP K 2] {x y : GL (Fin 6) K} (hx : IsTransvec K x) (hy : IsTransvec K y)
    (hodd : Odd (orderOf (x * y))) (hne : x * y ≠ 1) :
    ∃ (c : GL (Fin 6) K) (α β : K), (c : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ α ≠ 0 ∧ β ≠ 0 ∧
      c * x * c⁻¹ = transvGL K 0 1 (by decide) α ∧ c * y * c⁻¹ = transvGL K 1 0 (by decide) β := by
  obtain ⟨a, f, ha, -, hfa, hxa⟩ := IsTransvec.exists hx
  obtain ⟨b, g, hb, -, hgb, hyb⟩ := IsTransvec.exists hy
  obtain ⟨hα, hβ⟩ := fe3_pairing_ne_zero hxa hyb hfa hgb hodd hne
  obtain ⟨c, hdet, hc1, hc2⟩ := fe3_conj_explicit ha hfa hgb hα hβ
  refine ⟨c, f ⬝ᵥ b, g ⬝ᵥ a, hdet, hα, hβ, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, hxa, transvGL_val]
    exact hc1
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, hyb, transvGL_val]
    exact hc2

end CFSG.RankThree.GF2n.Smith81.A5Cube
