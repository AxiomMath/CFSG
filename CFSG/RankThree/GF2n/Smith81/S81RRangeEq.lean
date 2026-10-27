module

public import CFSG.RankThree.GF2n.Smith81.S81NModel1
public import CFSG.RankThree.GF2n.Smith81.S81RFrame
public import CFSG.RankThree.GF2n.Smith81.S81A5Root

open CFSG.RankThree.GF2n.Smith81.A5Cube
open scoped Matrix
open exteriorPower Matrix

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type*} [Field K]

private theorem eqsmul_isTransvec_conj {n : ℕ} {c g : GL (Fin n) K} (hg : IsTransvec K g) :
    IsTransvec K (c⁻¹ * g * c) := by
  obtain ⟨hsq, hrk⟩ := hg
  have hcc : ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (c : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul c
  have hcc' : (c : Matrix (Fin n) (Fin n) K) *
      ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := Units.mul_inv c
  have hsub : ((c⁻¹ * g * c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
      ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((g : Matrix (Fin n) (Fin n) K) - 1) *
        (c : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, hcc]
  refine ⟨?_, ?_⟩
  · rw [hsub]
    calc _ = ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (((g : Matrix (Fin n) (Fin n) K) - 1) * ((c : Matrix (Fin n) (Fin n) K) *
            ((c⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((g : Matrix (Fin n) (Fin n) K) - 1)) * (c : Matrix (Fin n) (Fin n) K) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hcc', mul_one, hsq]; simp
  · rw [hsub, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units c),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units c⁻¹)]
    exact hrk

private theorem eqsmul_rho_one : rho K (1 : GL (Fin 6) K) = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

private theorem eqsmul_rho_mul_apply (g h : GL (Fin 6) K) (ξ : Cube K) :
    rho K (g * h) ξ = rho K g (rho K h ξ) := by
  rw [rho, map_mul, Module.End.mul_apply]

private theorem eqsmul_rho_inv_cancel (c : GL (Fin 6) K) (η : Cube K) :
    rho K c⁻¹ (rho K c η) = η := by
  rw [← eqsmul_rho_mul_apply, inv_mul_cancel, eqsmul_rho_one, Module.End.one_apply]

private theorem eqsmul_rho_mul_inv (c : GL (Fin 6) K) (η : Cube K) :
    rho K c (rho K c⁻¹ η) = η := by
  rw [← eqsmul_rho_mul_apply, mul_inv_cancel, eqsmul_rho_one, Module.End.one_apply]

private theorem eqsmul_rho_conj_apply (c x : GL (Fin 6) K) (η : Cube K) :
    rho K (c * x * c⁻¹) (rho K c η) = rho K c (rho K x η) := by
  rw [eqsmul_rho_mul_apply, eqsmul_rho_inv_cancel, eqsmul_rho_mul_apply]

private theorem eqsmul_rho_sub_one_conj (c x : GL (Fin 6) K) (η : Cube K) :
    rho K c ((rho K x - 1) η) = (rho K (c * x * c⁻¹) - 1) (rho K c η) := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, eqsmul_rho_conj_apply]

private def eqsmul_R1 (η : Cube K) : Prop :=
  cfm K η 7 = 0 ∧ cfm K η 11 = 0 ∧ cfm K η 19 = 0 ∧ cfm K η 35 = 0 ∧ cfm K η 14 = 0 ∧
    cfm K η 22 = 0 ∧ cfm K η 38 = 0 ∧ cfm K η 26 = 0 ∧ cfm K η 42 = 0 ∧ cfm K η 50 = 0 ∧
    cfm K η 28 = 0 ∧ cfm K η 44 = 0 ∧ cfm K η 52 = 0 ∧ cfm K η 56 = 0

private theorem eqsmul_R1_of_mem_range [CharP K 2] {η : Cube K}
    (h : η ∈ LinearMap.range (rho K (tInv1 K) - 1)) : eqsmul_R1 η := by
  rw [(ker_range_eq1 (K := K)).2] at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    unfold eqsmul_R1
    fin_cases k <;> simp (config := {decide := true}) [ranG1, cfm_ub_mask]
  | zero =>
    unfold eqsmul_R1
    simp [cfm_zero]
  | add x y _ _ hx hy =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hx
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := hy
    unfold eqsmul_R1
    simp [cfm_add, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
      b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14]
  | smul c x _ hx =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hx
    unfold eqsmul_R1
    simp [cfm_smul, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]

private theorem eqsmul_R1_cfm {η : Cube K} (h : eqsmul_R1 η) (N : ℕ)
    (hN : N ∈ [7, 11, 19, 35, 14, 22, 38, 26, 42, 50, 28, 44, 52, 56]) :
    cfm K η N = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  simp at hN
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

private theorem eqsmul_mset_all : ∀ l p r : Fin 6, l ≠ p → l ≠ r → p ≠ r →
    mset (2 ^ (l : ℕ) + 2 ^ (p : ℕ) + 2 ^ (r : ℕ)) = {l, p, r} := by
  decide +kernel

private theorem eqsmul_cfm_ιMulti [CharP K 2] (v : Fin 3 → Fin 6 → K) {l p r : Fin 6}
    (hlp : l ≠ p) (hlr : l ≠ r) (hpr : p ≠ r) :
    cfm K (ιMulti K 3 v) (2 ^ (l : ℕ) + 2 ^ (p : ℕ) + 2 ^ (r : ℕ)) = minor3 v l p r := by
  have hmset : mset (2 ^ (l : ℕ) + 2 ^ (p : ℕ) + 2 ^ (r : ℕ)) = {l, p, r} :=
    eqsmul_mset_all l p r hlp hlr hpr
  have hcard : ({l, p, r} : Finset (Fin 6)).card = 3 :=
    Finset.card_eq_three.mpr ⟨l, p, r, hlp, hlr, hpr, rfl⟩
  have hI : cfm K (ιMulti K 3 v) (2 ^ (l : ℕ) + 2 ^ (p : ℕ) + 2 ^ (r : ℕ)) =
      coord K (ιMulti K 3 v) (tripleSet l p r hlp hlr hpr) := by
    unfold cfm cf
    rw [hmset, dif_pos hcard]
    rfl
  rw [hI]
  rcases coord_ιMulti_triple v (I := tripleSet l p r hlp hlr hpr) rfl hlp hlr hpr with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

private theorem eqsmul_coeff [CharP K 2] {y : GL (Fin 6) K} {a f : Fin 6 → K}
    (hy : (y : Matrix (Fin 6) (Fin 6) K) = 1 + Matrix.vecMulVec a f) (m l p r : Fin 6)
    (hlp : l ≠ p) (hlr : l ≠ r) (hpr : p ≠ r) (hml : m ≠ l) (hmp : m ≠ p) (hmr : m ≠ r) :
    cfm K ((rho K y - 1) (ιMulti K 3 ![e K m, e K p, e K r]))
      (2 ^ (l : ℕ) + 2 ^ (p : ℕ) + 2 ^ (r : ℕ)) = f m * a l := by
  have hdot : ∀ i : Fin 6, f ⬝ᵥ e K i = f i := fun i => by simp [e, dotProduct_single]
  rw [LinearMap.sub_apply, Module.End.one_apply, rho_sub_one_ιMulti hy, hdot m, hdot p, hdot r,
    cfm_add, cfm_add, cfm_smul, cfm_smul, cfm_smul, eqsmul_cfm_ιMulti _ hlp hlr hpr,
    eqsmul_cfm_ιMulti _ hlp hlr hpr, eqsmul_cfm_ιMulti _ hlp hlr hpr]
  simp [minor3, Matrix.det_fin_three, e, Pi.single_apply, hlp, hlr, hpr, hlp.symm, hlr.symm,
    hpr.symm, hml, hmp, hmr, hml.symm, hmp.symm, hmr.symm]

private theorem eqsmul_mask_bad : ∀ l p r : Fin 6, l ≠ p → l ≠ r → p ≠ r →
    ¬ ((l = 0 ∨ p = 0 ∨ r = 0) ∧ l ≠ 1 ∧ p ≠ 1 ∧ r ≠ 1) →
    2 ^ (l : ℕ) + 2 ^ (p : ℕ) + 2 ^ (r : ℕ) ∈
      [7, 11, 19, 35, 14, 22, 38, 26, 42, 50, 28, 44, 52, 56] := by
  decide +kernel

private theorem eqsmul_off_diag [CharP K 2] {y : GL (Fin 6) K} {a f : Fin 6 → K}
    (hy : (y : Matrix (Fin 6) (Fin 6) K) = 1 + Matrix.vecMulVec a f)
    (hIn : ∀ ξ : Cube K, eqsmul_R1 ((rho K y - 1) ξ)) (m l p r : Fin 6)
    (h : l ≠ p ∧ l ≠ r ∧ p ≠ r ∧ m ≠ l ∧ m ≠ p ∧ m ≠ r ∧
      ¬ ((l = 0 ∨ p = 0 ∨ r = 0) ∧ l ≠ 1 ∧ p ≠ 1 ∧ r ≠ 1)) :
    f m * a l = 0 := by
  obtain ⟨hlp, hlr, hpr, hml, hmp, hmr, hbad⟩ := h
  rw [← eqsmul_coeff hy m l p r hlp hlr hpr hml hmp hmr]
  exact eqsmul_R1_cfm (hIn _) _ (eqsmul_mask_bad l p r hlp hlr hpr hbad)

private theorem eqsmul_tInv1_coe [CharP K 2] :
    ((tInv1 K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + Matrix.vecMulVec (Pi.single 0 1) (Pi.single 1 1) := by
  rw [tInv1, transvGL_val, Matrix.transvection]
  congr 1
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.vecMulVec, Matrix.single_apply, Pi.single_apply]

private theorem eqsmul_tInv1_sub_one [CharP K 2] :
    ((tInv1 K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) - 1 =
      Matrix.vecMulVec (e K 0) (e K 1) := by
  rw [eqsmul_tInv1_coe, add_sub_cancel_left]

theorem eq_smul_tInv1_of_range_le [CharP K 2] {y : GL (Fin 6) K} (hy : IsTransvec K y)
    (hR : LinearMap.range (rho K y - 1) ≤ LinearMap.range (rho K (tInv1 K) - 1)) :
    ∃ s : K, s ≠ 0 ∧
      (y : Matrix (Fin 6) (Fin 6) K) - 1 = s • ((tInv1 K : Matrix (Fin 6) (Fin 6) K) - 1) := by
  obtain ⟨a, f, ha0, hf0, hfa, hyM⟩ := IsTransvec.exists hy
  have hIn : ∀ ξ : Cube K, eqsmul_R1 ((rho K y - 1) ξ) := fun ξ =>
    eqsmul_R1_of_mem_range (hR (LinearMap.mem_range_self _ ξ))
  have OD : ∀ m l : Fin 6, m ≠ l → ¬ (m = 1 ∧ l = 0) → f m * a l = 0 := by
    intro m l hml hne
    fin_cases m <;> fin_cases l <;>
      first
        | exact (hml rfl).elim
        | exact (hne (by decide)).elim
        | exact eqsmul_off_diag hyM hIn _ _ 0 1 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 0 2 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 0 3 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 0 4 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 0 5 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 1 0 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 1 2 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 1 3 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 1 4 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 1 5 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 2 0 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 2 1 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 2 3 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 2 4 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 2 5 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 3 0 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 3 1 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 3 2 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 3 4 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 3 5 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 4 0 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 4 1 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 4 2 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 4 3 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 4 5 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 5 0 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 5 1 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 5 2 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 5 3 (by decide)
        | exact eqsmul_off_diag hyM hIn _ _ 5 4 (by decide)
  by_cases hA : ∃ m₀ : Fin 6, m₀ ≠ 1 ∧ f m₀ ≠ 0
  · exfalso
    obtain ⟨m₀, hm₀1, hm₀f⟩ := hA
    have hbz : ∀ l : Fin 6, l ≠ m₀ → a l = 0 := by
      intro l hl
      exact (mul_eq_zero.mp (OD m₀ l (Ne.symm hl) (fun h => hm₀1 h.1))).resolve_left hm₀f
    have hdot : f ⬝ᵥ a = f m₀ * a m₀ := by
      rw [dotProduct, Finset.sum_eq_single m₀]
      · intro j _ hj
        rw [hbz j hj, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ m₀) h
    have ham : a m₀ = 0 := by
      rw [hdot] at hfa
      exact (mul_eq_zero.mp hfa).resolve_left hm₀f
    apply ha0
    funext j
    by_cases hj : j = m₀
    · subst hj
      exact ham
    · exact hbz j hj
  · push Not at hA
    have hf1 : f 1 ≠ 0 := by
      intro h1
      apply hf0
      funext j
      by_cases hj : j = 1
      · subst hj
        exact h1
      · exact hA j hj
    have hdot : f ⬝ᵥ a = f 1 * a 1 := by
      rw [dotProduct, Finset.sum_eq_single (1 : Fin 6)]
      · intro j _ hj
        rw [hA j hj, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ (1 : Fin 6)) h
    have ha1 : a 1 = 0 := by
      rw [hdot] at hfa
      exact (mul_eq_zero.mp hfa).resolve_left hf1
    have hal : ∀ l : Fin 6, l ≠ 0 → a l = 0 := by
      intro l hl
      by_cases hl1 : l = 1
      · subst hl1
        exact ha1
      · exact (mul_eq_zero.mp (OD 1 l (Ne.symm hl1) (fun h => hl h.2))).resolve_left hf1
    have ha00 : a 0 ≠ 0 := by
      intro h0
      apply ha0
      funext j
      by_cases hj : j = 0
      · subst hj
        exact h0
      · exact hal j hj
    obtain ⟨β, hβ⟩ : ∃ β : K, β = a 0 := ⟨_, rfl⟩
    obtain ⟨γ, hγ⟩ : ∃ γ : K, γ = f 1 := ⟨_, rfl⟩
    have hav : a = β • e K 0 := by
      funext j
      by_cases hj : j = 0
      · subst hj
        simp [hβ, e]
      · simp [e, Pi.single_apply, hj, hal j hj]
    have hfv : f = γ • e K 1 := by
      funext j
      by_cases hj : j = 1
      · subst hj
        simp [hγ, e]
      · simp [e, Pi.single_apply, hj, hA j hj]
    refine ⟨β * γ, mul_ne_zero (by rw [hβ]; exact ha00) (by rw [hγ]; exact hf1), ?_⟩
    rw [hyM, add_sub_cancel_left, eqsmul_tInv1_sub_one, hav, hfv]
    ext i j
    simp [Matrix.vecMulVec, e, Pi.single_apply] <;> ring

private theorem eqsmul_conj_sub_one {P Q X Y T : Matrix (Fin 6) (Fin 6) K} {s : K}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hX : P * X * Q = T)
    (hY : P * Y * Q - 1 = s • (T - 1)) : Y - 1 = s • (X - 1) := by
  have key : ∀ M : Matrix (Fin 6) (Fin 6) K, Q * (P * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hX' : X = Q * T * P := by
    rw [← hX]
    simp only [Matrix.mul_assoc, hQP, Matrix.mul_one, key]
  have hY' : Y - 1 = Q * (P * Y * Q - 1) * P := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, hQP, key]
  rw [hY', hY, hX']
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_assoc, hQP, key]

theorem eq_smul_of_range_eq [Finite K] [CharP K 2] {x y : GL (Fin 6) K} (hx : IsTransvec K x)
    (hy : IsTransvec K y)
    (h : LinearMap.range (rho K x - 1) = LinearMap.range (rho K y - 1)) :
    ∃ s : K, s ≠ 0 ∧ (y : Matrix (Fin 6) (Fin 6) K) - 1 = s • ((x : Matrix (Fin 6) (Fin 6) K) - 1) := by
  obtain ⟨c, -, hc⟩ := exists_conj_tInv1 hx
  have hyc : IsTransvec K (c * y * c⁻¹) := by
    simpa only [inv_inv] using eqsmul_isTransvec_conj (c := c⁻¹) hy
  have hR : LinearMap.range (rho K (c * y * c⁻¹) - 1) ≤
      LinearMap.range (rho K (tInv1 K) - 1) := by
    rintro _ ⟨ξ, rfl⟩
    have hmem : (rho K y - 1) (rho K c⁻¹ ξ) ∈ LinearMap.range (rho K x - 1) := by
      rw [h]
      exact LinearMap.mem_range_self _ _
    obtain ⟨η, hη⟩ := LinearMap.mem_range.mp hmem
    refine LinearMap.mem_range.mpr ⟨rho K c η, ?_⟩
    rw [← hc, ← eqsmul_rho_sub_one_conj c x η, hη, eqsmul_rho_sub_one_conj c y (rho K c⁻¹ ξ),
      eqsmul_rho_mul_inv]
  obtain ⟨s, hs, hsM⟩ := eq_smul_tInv1_of_range_le hyc hR
  refine ⟨s, hs, ?_⟩
  have hPQ : (c : Matrix (Fin 6) (Fin 6) K) *
      ((c⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 :=
    Units.mul_inv c
  have hQP : ((c⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (c : Matrix (Fin 6) (Fin 6) K) = 1 :=
    Units.inv_mul c
  have hX : (c : Matrix (Fin 6) (Fin 6) K) * (x : Matrix (Fin 6) (Fin 6) K) *
      ((c⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((tInv1 K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    simpa only [Units.val_mul] using congrArg Units.val hc
  have hY : (c : Matrix (Fin 6) (Fin 6) K) * (y : Matrix (Fin 6) (Fin 6) K) *
      ((c⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) - 1 =
      s • (((tInv1 K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) - 1) := by
    simpa only [Units.val_mul] using hsM
  exact eqsmul_conj_sub_one hPQ hQP hX hY

end CFSG.RankThree.GF2n.Smith81.A5Cube
