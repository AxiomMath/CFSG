module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoCoord
public import CFSG.HardMathSupport.Seitz.Proving.SL2PrimeOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K] [Finite K]

private theorem s16g_det_pairMat {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) K) : (pairMat a b g).det = g.det := by
  let U : Matrix ι (Fin 2) K := Matrix.of fun x c =>
    if c = 0 then (if x = a then (1 : K) else 0) else (if x = b then (1 : K) else 0)
  let V : Matrix (Fin 2) ι K := Matrix.of fun c y =>
    if c = 0 then (if y = a then g 0 0 - 1 else if y = b then g 0 1 else 0)
    else (if y = a then g 1 0 else if y = b then g 1 1 - 1 else 0)
  have hUV : pairMat a b g = U * V + 1 := by
    ext x y
    rw [Matrix.add_apply, mul_apply, Fin.sum_univ_two]
    by_cases hxa : x = a
    · rw [hxa]
      by_cases hya : y = a
      · rw [hya]; simp [U, V, pairMat, hab, Ne.symm hab, sub_add_cancel]
      by_cases hyb : y = b
      · rw [hyb]; simp [U, V, pairMat, hab, Ne.symm hab]
      · simp [U, V, pairMat, hya, hyb, Ne.symm hya, Ne.symm hyb, hab, Ne.symm hab]
    by_cases hxb : x = b
    · rw [hxb]
      by_cases hya : y = a
      · rw [hya]; simp [U, V, pairMat, hab, Ne.symm hab]
      by_cases hyb : y = b
      · rw [hyb]; simp [U, V, pairMat, hab, Ne.symm hab, sub_add_cancel]
      · simp [U, V, pairMat, hya, hyb, Ne.symm hya, Ne.symm hyb, hab, Ne.symm hab]
    · simp [U, V, pairMat, hxa, hxb, Ne.symm hxa, Ne.symm hxb, hab, Ne.symm hab]
  have hVU : g = V * U + 1 := by
    ext i j
    rw [Matrix.add_apply, mul_apply,
      Fintype.sum_eq_add a b hab (fun z hz => by simp [U, hz.1, hz.2])]
    fin_cases i <;> fin_cases j <;> simp [U, V, hab, Ne.symm hab, sub_add_cancel]
  rw [hUV, det_mul_add_one_comm U V, ← hVU]

theorem s16g_pairGL_mem_statedSL {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : pairGL hab g ∈ StatedSL n K := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff, coe_pairGL, s16g_det_pairMat hab]
  exact g.2

theorem s16g_exists_units_orderOf {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])

private theorem s16g_sl2Diag_injective : Function.Injective (sl2Diag (k := K)) := by
  intro a b h
  have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  exact Units.ext (by simpa [coe_sl2Diag] using h')

theorem s16g_pairGL_sl2Diag_commute {ι : Type} [Fintype ι] [DecidableEq ι] {a b c : ι}
    (hab : a ≠ b) (hbc : b ≠ c) (ζ : Kˣ) :
    Commute (pairGL hab (sl2Diag ζ)) (pairGL hbc (sl2Diag ζ)) := by
  apply Units.ext
  simp only [Units.val_mul, coe_pairGL, coe_sl2Diag, pairMat_diag hab, pairMat_diag hbc]
  exact (Matrix.commute_diagonal _ _).eq

theorem s16g_pairGL_sl2Diag_not_mem {ι : Type} [Fintype ι] [DecidableEq ι] {a b c : ι}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {ζ : Kˣ} (hζ : ζ ≠ 1) :
    pairGL hbc (sl2Diag ζ) ∉ Subgroup.zpowers (pairGL hab (sl2Diag ζ)) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  rw [← map_zpow] at hk
  have hmat : ((pairGL hab ((sl2Diag ζ) ^ k) : GL ι K) : Matrix ι ι K) c c =
      ((pairGL hbc (sl2Diag ζ) : GL ι K) : Matrix ι ι K) c c :=
    congrArg (fun M : Matrix ι ι K => M c c)
      (congrArg (fun x : GL ι K => (x : Matrix ι ι K)) hk)
  simp only [coe_pairGL] at hmat
  have hL : (pairMat a b (((sl2Diag ζ) ^ k : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) c c = 1 := by
    rw [pairMat_apply_of_ne (x := c) hac.symm hbc.symm _ c]
    simp
  have hR : (pairMat b c ((sl2Diag ζ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) c c = ((ζ⁻¹ : Kˣ) : K) := by
    rw [(pairMat_apply_pair hbc _).2.2.2]
    simp [coe_sl2Diag]
  rw [hL, hR] at hmat
  have h1 : (ζ⁻¹ : Kˣ) = 1 := Units.ext (by simpa using hmat.symm)
  exact hζ (inv_eq_one.mp h1)

private theorem s16g_fin_ne {n i j : ℕ} (hi : i < n) (hj : j < n) (h : i ≠ j) :
    (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun e => h (Fin.mk.inj_iff.1 e)

private theorem s16g_single_ne_zero {ι : Type} [DecidableEq ι] (i : ι) :
    (Pi.single i 1 : ι → K) ≠ 0 := fun h => by
  have h1 := congrFun h i
  simp at h1

theorem s16g_fixNc_statedSL_blocks {n : ℕ} (hn : 5 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K ^ 2 - 1) : FixNc (StatedSL n K) p := by
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hp hpK
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact hp.one_lt.ne hg
  have h01 := s16g_fin_ne (n := n) (i := 0) (j := 1) (by omega) (by omega) (by omega)
  have h23 := s16g_fin_ne (n := n) (i := 2) (j := 3) (by omega) (by omega) (by omega)
  have h02 := s16g_fin_ne (n := n) (i := 0) (j := 2) (by omega) (by omega) (by omega)
  have h03 := s16g_fin_ne (n := n) (i := 0) (j := 3) (by omega) (by omega) (by omega)
  have h12 := s16g_fin_ne (n := n) (i := 1) (j := 2) (by omega) (by omega) (by omega)
  have h13 := s16g_fin_ne (n := n) (i := 1) (j := 3) (by omega) (by omega) (by omega)
  have h04 := s16g_fin_ne (n := n) (i := 0) (j := 4) (by omega) (by omega) (by omega)
  have h14 := s16g_fin_ne (n := n) (i := 1) (j := 4) (by omega) (by omega) (by omega)
  have h24 := s16g_fin_ne (n := n) (i := 2) (j := 4) (by omega) (by omega) (by omega)
  have h34 := s16g_fin_ne (n := n) (i := 3) (j := 4) (by omega) (by omega) (by omega)
  refine s16g_fixNc_of_fixed_pair (StatedSL n K) hp
    (fun x y hx hy => CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq (by omega) hx hy)
    (s16g_pairGL_mem_statedSL h01 g) (s16g_pairGL_mem_statedSL h23 g)
    (s16g_pairGL_commute h01 h23 h02 h03 h12 h13 g g)
    ((orderOf_injective _ (s16g_pairGL_injective h01) g).trans hg)
    ((orderOf_injective _ (s16g_pairGL_injective h23) g).trans hg) ?_
    (s16g_single_ne_zero (⟨4, by omega⟩ : Fin n))
    (s16g_pairGL_mulVec_single h01 h04.symm h14.symm g)
    (s16g_pairGL_mulVec_single h23 h24.symm h34.symm g)
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  rw [← map_zpow] at hk
  exact hg1 (s16g_pairGL_eq_pairGL_disjoint h23 h01 h02.symm h12.symm h03.symm h13.symm hk.symm)

theorem s16g_fixNc_statedSL_torus {n : ℕ} (hn : 4 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) : FixNc (StatedSL n K) p := by
  obtain ⟨ζ, hζ⟩ := s16g_exists_units_orderOf hp hpK
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hord : orderOf (sl2Diag ζ : Matrix.SpecialLinearGroup (Fin 2) K) = p := by
    rw [orderOf_injective sl2Diag s16g_sl2Diag_injective ζ, hζ]
  have h01 := s16g_fin_ne (n := n) (i := 0) (j := 1) (by omega) (by omega) (by omega)
  have h12 := s16g_fin_ne (n := n) (i := 1) (j := 2) (by omega) (by omega) (by omega)
  have h02 := s16g_fin_ne (n := n) (i := 0) (j := 2) (by omega) (by omega) (by omega)
  have h03 := s16g_fin_ne (n := n) (i := 0) (j := 3) (by omega) (by omega) (by omega)
  have h13 := s16g_fin_ne (n := n) (i := 1) (j := 3) (by omega) (by omega) (by omega)
  have h23 := s16g_fin_ne (n := n) (i := 2) (j := 3) (by omega) (by omega) (by omega)
  exact s16g_fixNc_of_fixed_pair (StatedSL n K) hp
    (fun x y hx hy => CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq (by omega) hx hy)
    (s16g_pairGL_mem_statedSL h01 _) (s16g_pairGL_mem_statedSL h12 _)
    (s16g_pairGL_sl2Diag_commute h01 h12 ζ)
    ((orderOf_injective _ (s16g_pairGL_injective h01) _).trans hord)
    ((orderOf_injective _ (s16g_pairGL_injective h12) _).trans hord)
    (s16g_pairGL_sl2Diag_not_mem h01 h12 h02 hζ1)
    (s16g_single_ne_zero (⟨3, by omega⟩ : Fin n))
    (s16g_pairGL_mulVec_single h01 h03.symm h13.symm _)
    (s16g_pairGL_mulVec_single h12 h13.symm h23.symm _)

theorem s16g_fixOrd_statedSL {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K ^ 2 - 1) : FixOrd (StatedSL n K) p := by
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hp hpK
  have h01 := s16g_fin_ne (n := n) (i := 0) (j := 1) (by omega) (by omega) (by omega)
  have h02 := s16g_fin_ne (n := n) (i := 0) (j := 2) (by omega) (by omega) (by omega)
  have h12 := s16g_fin_ne (n := n) (i := 1) (j := 2) (by omega) (by omega) (by omega)
  exact s16g_fixOrd_of_fixed_vector (StatedSL n K)
    (fun x y hx hy => CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq (by omega) hx hy)
    (s16g_pairGL_mem_statedSL h01 g) ((orderOf_injective _ (s16g_pairGL_injective h01) g).trans hg)
    (s16g_single_ne_zero (⟨2, by omega⟩ : Fin n))
    (s16g_pairGL_mulVec_single h01 h02.symm h12.symm g)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
