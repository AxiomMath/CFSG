module

public import CFSG.Quasithin.Background.SmithB45U3Desc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aRankT
public import CFSG.Quasithin.Background.SmithB45SzDesc

public section

namespace CFSG.Quasithin.B45U3

open CFSG.QuasithinUnique.Setup.X7a
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply MatIso fixedSub)
open scoped MatrixGroups Matrix

section RankGen

variable {F : Type} [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem dim_le_two_mul_rank_of_tt (τ : ι → Bool × Bool) (e : ι → ℕ) {p : ι}
    (hp : τ p = (true, true)) :
    ∏ i, locDim (τ i).1 (τ i).2 ≤
      2 * (tensorRepGen (F := F) k τ e (up3 (0 : F) 0 1) - 1).rank := by
  have hprod : ∏ i, locDim (τ i).1 (τ i).2 =
      8 * ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ p, hp]
    rfl
  rw [hprod, tensorRepGen_rank_split k τ e p (true, true) hp]
  have hRR' : tensorRepGen (F := F) k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j)
      (up3 (0 : F) 0 1) *
      tensorRepGen (F := F) k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j)
        (up3 (0 : F) 0 1)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hcardα : Fintype.card (∀ j : {j : ι // j ≠ p}, Fin (locDim (τ j).1 (τ j).2)) =
      ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 := by
    simp [Fintype.card_pi]
  have key : ({1, 2, 5, 7} : Finset (Fin 8)).card *
      Fintype.card (∀ j : {j : ι // j ≠ p}, Fin (locDim (τ j).1 (τ j).2)) ≤
      (Matrix.kroneckerMap (· * ·) (tensorRepGen (F := F) k
        (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) (up3 (0 : F) 0 1))
        (locRep (F := F) k (true, true).1 (true, true).2 (e p) (up3 (0 : F) 0 1)) - 1).rank :=
    rank_kron_free (tensorRepGen (F := F) k
      (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) (up3 (0 : F) 0 1)) _ hRR'
      (adjRep (F := F) k (e p) (up3 (0 : F) 0 1)) ({1, 2, 5, 7} : Finset (Fin 8)) (by
        rw [adjRep_tr0]
        exact adjT0_free k)
  have e2 : ({1, 2, 5, 7} : Finset (Fin 8)).card = 4 := by decide
  rw [e2, hcardα] at key
  omega

theorem rank_tensorRepGen_involution (τ : ι → Bool × Bool) (e : ι → ℕ) {t : SL(3, F)}
    (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    (tensorRepGen (F := F) k τ e t - 1).rank =
      (tensorRepGen (F := F) k τ e (up3 (0 : F) 0 1) - 1).rank := by
  obtain ⟨g, hg⟩ := exists_conj_transvection t ht1 ht2
  set T := tensorRepGen (F := F) k τ e with hT
  have e1 : T (up3 (0 : F) 0 1) - 1 = T g⁻¹ * (T t - 1) * T g := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← map_mul, ← map_mul, ← map_mul,
      inv_mul_cancel, map_one, ← hg]
  have hu1 : IsUnit (T g⁻¹).det := by
    refine IsUnit.of_mul_eq_one (T g).det ?_
    rw [← Matrix.det_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.det_one]
  have hu2 : IsUnit (T g).det := by
    refine IsUnit.of_mul_eq_one (T g⁻¹).det ?_
    rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one]
  rw [e1, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu2,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu1]

end RankGen

theorem four_mul_add_one_le_three_pow {r : ℕ} (hr : 2 ≤ r) : 4 * r + 1 ≤ 3 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    rw [pow_succ]
    omega

theorem four_mul_le_pow_mul_pow {r m : ℕ} (hm : 1 ≤ m) : 4 * (r + 2 * m) ≤ 3 ^ r * 8 ^ m := by
  have h1 : r + 1 ≤ 3 ^ r := by
    induction r with
    | zero => norm_num
    | succ r ih =>
      rw [pow_succ]
      omega
  have h2 : 8 * m ≤ 8 ^ m := by
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      rw [pow_succ]
      omega
  calc 4 * (r + 2 * m) ≤ (r + 1) * (8 * m) := by nlinarith
    _ ≤ 3 ^ r * 8 ^ m := Nat.mul_le_mul h1 h2

theorem eq_one_zero_of_small {s d r m R : ℕ} (hs : 1 ≤ s)
    (hC : 2 * s ≤ (r + 2 * m) * d) (hne : r + 2 * m ≠ 0) (hR1 : 3 ^ r * 8 ^ m ≤ 2 * R + 1)
    (hR2 : 1 ≤ m → 3 ^ r * 8 ^ m ≤ 2 * R) (hsmall : d * R ≤ 3 * s) : r = 1 ∧ m = 0 := by
  have hR : r + 2 * m ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h2R : 2 * (r + 2 * m) ≤ R := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have hr : 2 ≤ r := by omega
        have := four_mul_add_one_le_three_pow hr
        simp only [pow_zero, mul_one] at hR1
        omega
      · have := four_mul_le_pow_mul_pow (r := r) hm
        have := hR2 hm
        omega
    have h3 : 2 * ((r + 2 * m) * d) ≤ d * R := by nlinarith
    omega
  omega

section Small

variable {K : Type} [Field K] [Finite K] [CharP K 2] {s : ℕ}
variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) (suJ K s) W} [Fact ρ.IsIrreducible]

open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing matRepE)

theorem u3_finrank_eq_three_of_small (hK : Nat.card K = (2 ^ s) ^ 2) (hnt : ∃ g, ρ g ≠ 1)
    {t : suJ K s} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hsmall : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 3 * s) :
    Module.finrank (EndRing ρ) W = 3 := by
  classical
  have hs := one_le_s hK
  obtain ⟨d, hd1, hDcard, hdesc⟩ := u3_descent hK hnt
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιK, ιD, a, b', hab, ⟨Φ⟩, hmod, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing ρ) W)
  let _ : Algebra K E := ιK.toAlgebra
  have hdisp := B45Sz.finrank_range_eq_gen hDcard (Module.finBasis (EndRing ρ) W) ιD
    (TJ (K := K) E a b') Φ hdimW t
  have ht1' : (t : SL(3, K)) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht2' : (t : SL(3, K)) * t = 1 := congrArg Subtype.val ht2
  have hrank := rank_tensorRepGen_involution (F := K) E (fun i : Fin s => (a i, b' i))
    (fun i => (i : ℕ)) ht1' ht2'
  have hTt : TJ (K := K) E a b' t =
      tensorRepGen (F := K) E (fun i : Fin s => (a i, b' i)) (fun i => (i : ℕ)) t := rfl
  set R := (TJ (K := K) E a b' t - 1).rank with hRdef
  have hR1 : Fintype.card (TIdx s a b') ≤ 2 * R + 1 := by
    rw [card_TIdx, hRdef, hTt, hrank]
    exact dim_le_two_mul_rank_add_one (F := K) E (Fintype.card (Fin s)) rfl
      (fun i : Fin s => (a i, b' i)) (fun i => (i : ℕ))
  have hR2 : 1 ≤ cntH a b' → Fintype.card (TIdx s a b') ≤ 2 * R := by
    intro hm
    obtain ⟨p, hp⟩ : ∃ p, a p = true ∧ b' p = true := by
      by_contra hc
      push Not at hc
      have : cntH a b' = 0 := by
        rw [cntH, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ h
        exact absurd h.2 (by simpa using hc i h.1)
      omega
    rw [card_TIdx, hRdef, hTt, hrank]
    exact dim_le_two_mul_rank_of_tt (F := K) E (fun i : Fin s => (a i, b' i))
      (fun i => (i : ℕ)) (p := p) (by show (a p, b' p) = (true, true); rw [hp.1, hp.2])
  rw [card_TIdx_eq] at hR1 hR2
  have hC := two_mul_le_card_mul hs hd1 (letJ_subset a b') (letJ_nonempty hab) (by
    rw [sum_letJ, show 2 ^ (2 * s) = (2 ^ s) ^ 2 by rw [← pow_mul, mul_comm]]
    exact hmod)
  rw [card_letJ] at hC
  have hne : cntS a b' + 2 * cntH a b' ≠ 0 := by
    rw [← card_letJ]
    exact (Finset.card_pos.mpr (letJ_nonempty hab)).ne'
  have hsmall' : d * R ≤ 3 * s := hdisp ▸ hsmall
  obtain ⟨hr, hm⟩ := eq_one_zero_of_small hs hC hne hR1 hR2 hsmall'
  rw [hdimW, card_TIdx_eq, hr, hm]
  norm_num

end Small

end CFSG.Quasithin.B45U3
