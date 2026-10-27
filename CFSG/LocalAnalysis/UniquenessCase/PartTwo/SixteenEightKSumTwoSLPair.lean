module

public import CFSG.CGT.T75E.LinTwoTrans
public import CFSG.Open.StatedZModTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoCoord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K]

private theorem s16k_charP_two (hK : Nat.card K = 2) : CharP K 2 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype K := Fintype.ofFinite K
  haveI := ringChar.charP K
  obtain ⟨m, hp', hm⟩ := FiniteField.card K (ringChar K)
  have hm2 : (2 : ℕ) = ringChar K ^ (m : ℕ) := by
    rw [← Nat.card_eq_fintype_card, hK] at hm
    exact hm
  have hdvd : 2 ∣ ringChar K ^ (m : ℕ) := by rw [← hm2]
  have h2 : 2 = ringChar K :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp').mp (Nat.prime_two.dvd_of_dvd_pow hdvd)
  rw [h2]
  infer_instance

private def s16k_e {n : ℕ} (i : Fin n) : Fin n → K := Pi.single i 1

private theorem s16k_e_ne_zero {n : ℕ} (i : Fin n) : s16k_e (K := K) i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [s16k_e] at this

private def s16k_Rmat : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 1]

private theorem s16k_Rmat_symm : (s16k_Rmat (K := K))ᵀ = s16k_Rmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s16k_Rmat]

private theorem s16k_Rmat_det [CharP K 2] : (s16k_Rmat (K := K)).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [s16k_Rmat, CharTwo.neg_eq]

private def s16k_R [CharP K 2] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨s16k_Rmat, s16k_Rmat_det⟩

private theorem s16k_R_pow_three [CharP K 2] : (s16k_R (K := K)) ^ 3 = 1 := by
  apply Subtype.ext
  change (s16k_Rmat : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1
  have h2 : (s16k_Rmat : Matrix (Fin 2) (Fin 2) K) ^ 2 = !![1, 1; 1, 0] := by
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s16k_Rmat, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s16k_Rmat, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

private theorem s16k_R_ne_one [CharP K 2] : (s16k_R (K := K)) ≠ 1 := by
  intro h
  have h01 : (s16k_Rmat : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have := congrFun (congrFun (congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h) 0) 1
    simpa [s16k_R, Matrix.SpecialLinearGroup.coe_one] using this
  simp [s16k_Rmat] at h01

private theorem s16k_orderOf_R [CharP K 2] : orderOf (s16k_R (K := K)) = 3 :=
  orderOf_eq_prime s16k_R_pow_three s16k_R_ne_one

private theorem s16k_pairGL_R_symm {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ι}
    [CharP K 2] (hab : a ≠ b) :
    (((pairGL hab (s16k_R (K := K)) : GL ι K) : Matrix ι ι K))ᵀ =
      ((pairGL hab (s16k_R (K := K)) : GL ι K) : Matrix ι ι K) := by
  rw [coe_pairGL, pairMat_transpose hab]
  congr 1
  exact s16k_Rmat_symm

private noncomputable def s16k_toΓ {n : ℕ} (g : Matrix.SpecialLinearGroup (Fin n) K) :
    ↥(StatedSL n K) :=
  ⟨Matrix.SpecialLinearGroup.toGL g,
    CFSG.Open.StatedAPI.mem_statedSL_of_det (A := (g : GL (Fin n) K)) (by simpa using g.2)⟩

private theorem s16k_fin_ne {n i j : ℕ} (hi : i < n) (hj : j < n) (h : i ≠ j) :
    (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun hh => h (Fin.ext_iff.mp hh)

private theorem s16k_exists_E (hK : Nat.card K = 2) {n : ℕ} (hn : 6 ≤ n) :
    ∃ E : Subgroup (GL (Fin n) K),
      E ≤ StatedSL n K ∧ Nat.card E = 3 ^ 2 ∧ (∀ x : GL (Fin n) K, x ∈ E → x ^ 3 = 1) ∧
      (∀ e : GL (Fin n) K, e ∈ E → (e : Matrix (Fin n) (Fin n) K) *ᵥ
        s16k_e (⟨0, by omega⟩ : Fin n) = s16k_e (⟨0, by omega⟩ : Fin n)) ∧
      (∀ e : GL (Fin n) K, e ∈ E → (e : Matrix (Fin n) (Fin n) K) *ᵥ
        s16k_e (⟨5, by omega⟩ : Fin n) = s16k_e (⟨5, by omega⟩ : Fin n)) ∧
      (∀ e : GL (Fin n) K, e ∈ E →
        Matrix.GeneralLinearGroup.inverseTranspose e ∈ E) := by
  haveI : CharP K 2 := s16k_charP_two hK
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ :=
    s16k_fin_ne (by omega) (by omega) (by decide)
  have h34 : (⟨3, by omega⟩ : Fin n) ≠ ⟨4, by omega⟩ :=
    s16k_fin_ne (by omega) (by omega) (by decide)
  have h13 : (⟨1, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ :=
    s16k_fin_ne (by omega) (by omega) (by decide)
  have h14 : (⟨1, by omega⟩ : Fin n) ≠ ⟨4, by omega⟩ :=
    s16k_fin_ne (by omega) (by omega) (by decide)
  have h23 : (⟨2, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ :=
    s16k_fin_ne (by omega) (by omega) (by decide)
  have h24 : (⟨2, by omega⟩ : Fin n) ≠ ⟨4, by omega⟩ :=
    s16k_fin_ne (by omega) (by omega) (by decide)
  let x : GL (Fin n) K := pairGL h12 (s16k_R (K := K))
  let y : GL (Fin n) K := pairGL h34 (s16k_R (K := K))
  let E : Subgroup (GL (Fin n) K) := Subgroup.zpowers x ⊔ Subgroup.zpowers y
  have hxy : Commute x y := s16g_pairGL_commute h12 h34 h13 h14 h23 h24 _ _
  have hx3 : orderOf x = 3 :=
    (orderOf_injective _ (s16g_pairGL_injective h12) (s16k_R (K := K))).trans s16k_orderOf_R
  have hy3 : orderOf y = 3 :=
    (orderOf_injective _ (s16g_pairGL_injective h34) (s16k_R (K := K))).trans s16k_orderOf_R
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← map_zpow] at hk
    exact s16k_R_ne_one
      (s16g_pairGL_eq_pairGL_disjoint h34 h12 h13.symm h23.symm h14.symm h24.symm hk.symm)
  obtain ⟨hcard, hexp⟩ := s16g_card_pair_subgroup Nat.prime_three hxy hx3 hy3 hyx
  have hEfix0 : ∀ e : GL (Fin n) K, e ∈ E → (e : Matrix (Fin n) (Fin n) K) *ᵥ
      s16k_e (⟨0, by omega⟩ : Fin n) = s16k_e (⟨0, by omega⟩ : Fin n) :=
    s16g_fixed_of_pair
      (s16g_pairGL_mulVec_single h12 (Fin.ne_of_val_ne (by decide : (0 : ℕ) ≠ 1))
        (Fin.ne_of_val_ne (by decide : (0 : ℕ) ≠ 2)) _)
      (s16g_pairGL_mulVec_single h34 (Fin.ne_of_val_ne (by decide : (0 : ℕ) ≠ 3))
        (Fin.ne_of_val_ne (by decide : (0 : ℕ) ≠ 4)) _)
  have hEfix5 : ∀ e : GL (Fin n) K, e ∈ E → (e : Matrix (Fin n) (Fin n) K) *ᵥ
      s16k_e (⟨5, by omega⟩ : Fin n) = s16k_e (⟨5, by omega⟩ : Fin n) :=
    s16g_fixed_of_pair
      (s16g_pairGL_mulVec_single h12 (Fin.ne_of_val_ne (by decide : (5 : ℕ) ≠ 1))
        (Fin.ne_of_val_ne (by decide : (5 : ℕ) ≠ 2)) _)
      (s16g_pairGL_mulVec_single h34 (Fin.ne_of_val_ne (by decide : (5 : ℕ) ≠ 3))
        (Fin.ne_of_val_ne (by decide : (5 : ℕ) ≠ 4)) _)
  have hxsymm : (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ =
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := s16k_pairGL_R_symm h12
  have hysymm : (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := s16k_pairGL_R_symm h34
  have hxmap : Matrix.GeneralLinearGroup.inverseTranspose x = x⁻¹ := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, Matrix.GeneralLinearGroup.coe_inv]
    rw [Matrix.transpose_nonsing_inv, hxsymm]
  have hymap : Matrix.GeneralLinearGroup.inverseTranspose y = y⁻¹ := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, Matrix.GeneralLinearGroup.coe_inv]
    rw [Matrix.transpose_nonsing_inv, hysymm]
  have hmapE : E.map (Matrix.GeneralLinearGroup.inverseTranspose (n := Fin n) (A := K)).toMonoidHom
      = E := by
    change (Subgroup.zpowers x ⊔ Subgroup.zpowers y).map
      (Matrix.GeneralLinearGroup.inverseTranspose (n := Fin n) (A := K)).toMonoidHom = E
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    change Subgroup.zpowers (Matrix.GeneralLinearGroup.inverseTranspose x) ⊔
      Subgroup.zpowers (Matrix.GeneralLinearGroup.inverseTranspose y) = E
    rw [hxmap, hymap, Subgroup.zpowers_inv, Subgroup.zpowers_inv]
  refine ⟨E, ?_, hcard, hexp, hEfix0, hEfix5, ?_⟩
  · rw [CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK n]
    exact le_top
  · intro e he
    rw [← hmapE]
    exact Subgroup.mem_map.mpr ⟨e, he, rfl⟩

private theorem s16k_dot_single {n : ℕ} (i : Fin n) (v : Fin n → K) :
    dotProduct (s16k_e (K := K) i) v = v i := by
  rw [dotProduct, Finset.sum_eq_single i]
  · simp [s16k_e]
  · intro b _ hb
    simp [s16k_e, Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem s16k_conj_mulVec_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (A b : GL ι K) (x : ι → K) :
    (((A * b * A⁻¹ : GL ι K) : Matrix ι ι K)) *ᵥ x =
      (A : Matrix ι ι K) *ᵥ ((b : Matrix ι ι K) *ᵥ
        (((A⁻¹ : GL ι K)) : Matrix ι ι K) *ᵥ x) := by
  rw [Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private theorem s16k_conj_sub [Finite K] {n : ℕ} (E : Subgroup (GL (Fin n) K))
    (hEΓ : E ≤ StatedSL n K)
    (hcard : Nat.card E = 3 ^ 2) (hexp : ∀ x ∈ E, x ^ 3 = 1) (c : ↥(StatedSL n K)) :
    ∃ B : Subgroup ↥(StatedSL n K), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧
      (∀ z ∈ B, ∃ e ∈ E,
        (z : GL (Fin n) K) = ((c : GL (Fin n) K))⁻¹ * e * (((c : GL (Fin n) K))⁻¹)⁻¹) := by
  let cG : GL (Fin n) K := (c : GL (Fin n) K)
  let B' : Subgroup (GL (Fin n) K) := E.map (MulAut.conj (cG)⁻¹).toMonoidHom
  have hB'Γ : B' ≤ StatedSL n K := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hz
    change MulAut.conj (cG)⁻¹ e ∈ StatedSL n K
    rw [MulAut.conj_apply]
    exact (StatedSL n K).mul_mem ((StatedSL n K).mul_mem ((StatedSL n K).inv_mem c.2)
      (hEΓ he)) c.2
  let B : Subgroup ↥(StatedSL n K) := B'.subgroupOf (StatedSL n K)
  have hcardB : Nat.card ↥B = 3 ^ 2 := by
    have h1 : Nat.card ↥B = Nat.card ↥B' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'Γ).toEquiv
    have h2 : Nat.card ↥B' = Nat.card ↥E :=
      (Nat.card_congr (Subgroup.equivMapOfInjective E (MulAut.conj (cG)⁻¹).toMonoidHom
        (MulAut.conj (cG)⁻¹).injective).toEquiv).symm
    rw [h1, h2, hcard]
  have hpowB : ∀ z : ↥B, z ^ 3 = 1 := by
    intro z
    obtain ⟨e, he, hez⟩ := Subgroup.mem_map.mp ((Subgroup.mem_subgroupOf).mp z.property)
    have he3 : (e : GL (Fin n) K) ^ 3 = 1 := hexp e he
    have hz3 : (((z : ↥(StatedSL n K)) : GL (Fin n) K)) ^ 3 = 1 := by
      rw [← hez, ← map_pow, he3, map_one]
    exact Subtype.ext (Subtype.ext (by simpa using hz3))
  refine ⟨B, IsPGroup.of_card hcardB, ?_, ?_⟩
  · intro hcyc
    obtain ⟨z, hz⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
    have hz3 : z ^ 3 = 1 := hpowB z
    have hdvd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    rw [hz, hcardB] at hdvd
    have hle : 3 ^ 2 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    norm_num at hle
  · intro z hz
    obtain ⟨e, he, hez⟩ := Subgroup.mem_map.mp ((Subgroup.mem_subgroupOf).mp hz)
    refine ⟨e, he, ?_⟩
    have h1 : (((MulAut.conj (cG)⁻¹) e : GL (Fin n) K)) = (cG)⁻¹ * e * (cG)⁻¹⁻¹ := by
      rw [MulAut.conj_apply]
    rw [hez.symm]
    exact h1

private theorem s16k_conj_fix_two [Finite K] {n : ℕ} (E : Subgroup (GL (Fin n) K))
    (hEΓ : E ≤ StatedSL n K) (hcard : Nat.card E = 3 ^ 2) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (c : ↥(StatedSL n K)) {u w x y : Fin n → K} (hcu : (c : GL (Fin n) K) *ᵥ x = u)
    (hcw : (c : GL (Fin n) K) *ᵥ y = w)
    (hEu : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) *ᵥ u = u)
    (hEw : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) *ᵥ w = w) :
    ∃ B : Subgroup ↥(StatedSL n K), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
      (g : GL (Fin n) K) *ᵥ x = x ∧ (g : GL (Fin n) K) *ᵥ y = y := by
  obtain ⟨B, hBp, hBcyc, hBrep⟩ := s16k_conj_sub E hEΓ hcard hexp c
  refine ⟨B, hBp, hBcyc, ?_⟩
  intro g hg
  obtain ⟨e, he, hge⟩ := hBrep g hg
  constructor
  · have hfix : ((c : GL (Fin n) K)⁻¹ * e * ((c : GL (Fin n) K)⁻¹)⁻¹ :
        GL (Fin n) K) *ᵥ x = x := by
      rw [s16k_conj_mulVec_eq, inv_inv, hcu, hEu e he]
      rw [← hcu, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hge]; exact hfix
  · have hfix : ((c : GL (Fin n) K)⁻¹ * e * ((c : GL (Fin n) K)⁻¹)⁻¹ :
        GL (Fin n) K) *ᵥ y = y := by
      rw [s16k_conj_mulVec_eq, inv_inv, hcw, hEw e he]
      rw [← hcw, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hge]; exact hfix

private theorem s16k_conj_fix_dual [Finite K] {n : ℕ} (E : Subgroup (GL (Fin n) K))
    (hEΓ : E ≤ StatedSL n K) (hcard : Nat.card E = 3 ^ 2) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hσE : ∀ e ∈ E, Matrix.GeneralLinearGroup.inverseTranspose e ∈ E)
    (c : ↥(StatedSL n K)) {u x y : Fin n → K} (hcu : (c : GL (Fin n) K) *ᵥ x = u)
    (hEu : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) *ᵥ u = u)
    (hEz : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) *ᵥ
        ((Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y =
      ((Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) :
    ∃ B : Subgroup ↥(StatedSL n K), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
      (g : GL (Fin n) K) *ᵥ x = x ∧
        ((((g⁻¹ : ↥(StatedSL n K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ y = y) := by
  obtain ⟨B, hBp, hBcyc, hBrep⟩ := s16k_conj_sub E hEΓ hcard hexp c
  refine ⟨B, hBp, hBcyc, ?_⟩
  intro g hg
  obtain ⟨e, he, hge⟩ := hBrep g hg
  constructor
  · have hfix : ((c : GL (Fin n) K)⁻¹ * e * ((c : GL (Fin n) K)⁻¹)⁻¹ :
        GL (Fin n) K) *ᵥ x = x := by
      rw [s16k_conj_mulVec_eq, inv_inv, hcu, hEu e he]
      rw [← hcu, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hge]; exact hfix
  · have hσg : Matrix.GeneralLinearGroup.inverseTranspose (g : GL (Fin n) K) =
        (Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K))⁻¹ *
          Matrix.GeneralLinearGroup.inverseTranspose e *
          ((Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K))⁻¹)⁻¹ := by
      rw [hge]
      simp only [map_mul, map_inv]
    have hdual : (Matrix.GeneralLinearGroup.inverseTranspose (g : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ y = y := by
      rw [hσg, s16k_conj_mulVec_eq]
      rw [show ((Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K))⁻¹)⁻¹ =
          Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) from inv_inv _]
      rw [hEz (Matrix.GeneralLinearGroup.inverseTranspose e) (hσE e he)]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul,
        show (Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K))⁻¹ *
            Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) = 1 from
          inv_mul_cancel (Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K)),
        Units.val_one, Matrix.one_mulVec]
    rw [show ((((g⁻¹ : ↥(StatedSL n K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ =
        (Matrix.GeneralLinearGroup.inverseTranspose (g : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) from by
      rw [Matrix.GeneralLinearGroup.coe_inverseTranspose]
      congr 1]
    exact hdual

private theorem s16k_eq_zero_or_one (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype K := Fintype.ofFinite K
  have h2 : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  have : ({0, 1} : Finset K) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (zero_ne_one), h2]
  have hmem : x ∈ ({0, 1} : Finset K) := by rw [this]; exact Finset.mem_univ x
  simpa using hmem

private theorem s16k_tvSL_row {n : ℕ} (v φ : Fin n → K) (h : dotProduct φ v = 0)
    (i : Fin n) (h0 : v i = 0) :
    (((CFSG.CGT.Timmesfeld75.tvSL v φ h : Matrix (Fin n) (Fin n) K))ᵀ) *ᵥ
      s16k_e i = s16k_e i := by
  rw [show s16k_e (K := K) i = (Pi.single i (1 : K) : Fin n → K) from rfl,
    Matrix.mulVec_single_one]
  ext k
  rw [Matrix.col_apply, Matrix.transpose_apply, CFSG.CGT.Timmesfeld75.coe_tvSL,
    Matrix.add_apply, Matrix.vecMulVec_apply, h0, zero_mul, add_zero]
  simp [Pi.single_apply, Matrix.one_apply, eq_comm]

private theorem s16k_E_fix_span {n : ℕ} {E : Subgroup (GL (Fin n) K)} (i j : Fin n)
    (h0 : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) *ᵥ s16k_e (K := K) i = s16k_e (K := K) i)
    (h5 : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) *ᵥ s16k_e (K := K) j = s16k_e (K := K) j) :
    ∀ e ∈ E, ∀ a b : K, (e : Matrix (Fin n) (Fin n) K) *ᵥ
      (a • s16k_e (K := K) i + b • s16k_e (K := K) j) =
      a • s16k_e (K := K) i + b • s16k_e (K := K) j := by
  intro e he a b
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h0 e he, h5 e he]

private theorem s16k_tvSL_col {n : ℕ} (v φ : Fin n → K) (h : dotProduct φ v = 0)
    (i : Fin n) (h0 : φ i = 0) :
    ((CFSG.CGT.Timmesfeld75.tvSL v φ h : Matrix (Fin n) (Fin n) K)) *ᵥ s16k_e i = s16k_e i := by
  rw [show s16k_e (K := K) i = (Pi.single i (1 : K) : Fin n → K) from rfl,
    CFSG.CGT.Timmesfeld75.coe_tvSL, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_single_one]
  ext k
  simp [Pi.add_apply, Matrix.col_apply, Matrix.vecMulVec_apply, h0]

private theorem s16k_inv_mulVec_of_mulVec {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (hA : IsUnit A.det) {v : Fin n → K} (h : A *ᵥ v = v) : A⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul (A := A) hA, Matrix.one_mulVec]

private theorem s16k_move_to_pair (hK : Nat.card K = 2) {n : ℕ} (hn : 6 ≤ n) (β : Fin n → K) :
    ∃ (M : Matrix.SpecialLinearGroup (Fin n) K) (a b : K),
      ((M : Matrix (Fin n) (Fin n) K) *ᵥ β = a • s16k_e (K := K) (⟨0, by omega⟩ : Fin n) +
        b • s16k_e (K := K) (⟨5, by omega⟩ : Fin n)) ∧
      (((M : Matrix (Fin n) (Fin n) K)ᵀ) *ᵥ s16k_e (K := K) (⟨0, by omega⟩ : Fin n) =
        s16k_e (K := K) (⟨0, by omega⟩ : Fin n)) ∧
      ((M : Matrix (Fin n) (Fin n) K) *ᵥ s16k_e (K := K) (⟨0, by omega⟩ : Fin n) =
        s16k_e (K := K) (⟨0, by omega⟩ : Fin n)) := by
  haveI : CharP K 2 := s16k_charP_two hK
  classical
  by_cases hβspan : ∀ j : Fin n, j ≠ (⟨0, by omega⟩ : Fin n) →
      j ≠ (⟨5, by omega⟩ : Fin n) → β j = 0
  · refine ⟨1, β (⟨0, by omega⟩ : Fin n), β (⟨5, by omega⟩ : Fin n), ?_, by simp, by simp⟩
    funext j
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    simp only [Pi.add_apply, Pi.smul_apply, s16k_e, Pi.single_apply]
    by_cases hj0 : j = (⟨0, by omega⟩ : Fin n)
    · subst hj0; simp
    · by_cases hj5 : j = (⟨5, by omega⟩ : Fin n)
      · subst hj5; simp [hj0]
      · rw [hβspan j hj0 hj5]; simp [hj0, hj5]
  · rw [not_forall] at hβspan
    obtain ⟨j, hjspan⟩ := hβspan
    rw [not_imp] at hjspan
    obtain ⟨hj0, hjspan⟩ := hjspan
    rw [not_imp] at hjspan
    obtain ⟨hj5, hj⟩ := hjspan
    have hjval : β j = 1 := by
      rcases s16k_eq_zero_or_one hK (β j) with h | h
      · exact absurd h hj
      · exact h
    set η : Fin n → K := β - β (⟨0, by omega⟩ : Fin n) • s16k_e (K := K) (⟨0, by omega⟩ : Fin n)
      with hη
    have hη0 : η (⟨0, by omega⟩ : Fin n) = 0 := by
      simp [hη, Pi.sub_apply, s16k_e]
    have hβdec : β = β (⟨0, by omega⟩ : Fin n) • s16k_e (K := K) (⟨0, by omega⟩ : Fin n) + η := by
      rw [hη]; abel
    have hηj : η j = 1 := by
      simp [hη, Pi.sub_apply, s16k_e, hj0, hjval]
    by_cases hβ5 : β (⟨5, by omega⟩ : Fin n) = 1
    · have hη5 : η (⟨5, by omega⟩ : Fin n) = 1 := by
        rw [hη]
        simp [Pi.sub_apply, s16k_e, Pi.single_eq_of_ne (by decide : (5 : ℕ) ≠ 0), hβ5]
      have hφβ : dotProduct (s16k_e (K := K) (⟨5, by omega⟩ : Fin n)) β = 1 := by
        rw [s16k_dot_single, hβ5]
      have hφη : dotProduct (s16k_e (K := K) (⟨5, by omega⟩ : Fin n)) η = 1 := by
        rw [s16k_dot_single, hη5]
      have hφe5 : dotProduct (s16k_e (K := K) (⟨5, by omega⟩ : Fin n))
          (s16k_e (K := K) (⟨5, by omega⟩ : Fin n)) = 1 := by
        rw [s16k_dot_single]; simp [s16k_e]
      have hdot : dotProduct (s16k_e (K := K) (⟨5, by omega⟩ : Fin n))
          (s16k_e (K := K) (⟨5, by omega⟩ : Fin n) - η) = 0 := by
        rw [dotProduct_sub, hφe5, hφη]; ring
      refine ⟨CFSG.CGT.Timmesfeld75.tvSL
        (s16k_e (K := K) (⟨5, by omega⟩ : Fin n) - η)
        (s16k_e (K := K) (⟨5, by omega⟩ : Fin n)) hdot,
        β (⟨0, by omega⟩ : Fin n), 1, ?_, ?_, ?_⟩
      · rw [CFSG.CGT.T75E.tvSL_mulVec, hφβ, one_smul]
        funext k
        by_cases hk0 : k = (⟨0, by omega⟩ : Fin n)
        · subst hk0
          simp [Pi.add_apply, Pi.sub_apply, s16k_e, Pi.single_apply, hη0]
        · by_cases hk5 : k = (⟨5, by omega⟩ : Fin n)
          · subst hk5
            simp [Pi.add_apply, Pi.sub_apply, s16k_e, Pi.single_apply, hk0, hβ5, hη5]
          · simp [Pi.add_apply, Pi.sub_apply, s16k_e, Pi.single_apply, hη, hk0, hk5]
      · exact s16k_tvSL_row _ _ hdot (⟨0, by omega⟩) (by simp [Pi.sub_apply, hη0, s16k_e])
      · exact s16k_tvSL_col _ _ hdot (⟨0, by omega⟩) (by simp [s16k_e])
    · have hβ50 : β (⟨5, by omega⟩ : Fin n) = 0 := by
        rcases s16k_eq_zero_or_one hK (β (⟨5, by omega⟩ : Fin n)) with h | h
        · exact h
        · exact absurd h hβ5
      have hη5 : η (⟨5, by omega⟩ : Fin n) = 0 := by
        simp [hη, Pi.sub_apply, s16k_e, hβ50]
      have hφβ : dotProduct (s16k_e (K := K) (⟨5, by omega⟩ : Fin n) + s16k_e j) β = 1 := by
        rw [add_dotProduct, s16k_dot_single, s16k_dot_single, hβ50, hjval]
        ring
      have hφη : dotProduct (s16k_e (K := K) (⟨5, by omega⟩ : Fin n) + s16k_e j) η = 1 := by
        rw [add_dotProduct, s16k_dot_single, s16k_dot_single, hη5, hηj]
        ring
      have hφe5 : dotProduct (s16k_e (K := K) (⟨5, by omega⟩ : Fin n) + s16k_e j)
          (s16k_e (K := K) (⟨5, by omega⟩ : Fin n)) = 1 := by
        rw [add_dotProduct, s16k_dot_single, s16k_dot_single]
        simp [s16k_e, hj5]
      have hdot : dotProduct (s16k_e (K := K) (⟨5, by omega⟩ : Fin n) + s16k_e j)
          (s16k_e (K := K) (⟨5, by omega⟩ : Fin n) - η) = 0 := by
        rw [dotProduct_sub, hφe5, hφη]; ring
      refine ⟨CFSG.CGT.Timmesfeld75.tvSL
        (s16k_e (K := K) (⟨5, by omega⟩ : Fin n) - η)
        (s16k_e (K := K) (⟨5, by omega⟩ : Fin n) + s16k_e j) hdot,
        β (⟨0, by omega⟩ : Fin n), 1, ?_, ?_, ?_⟩
      · rw [CFSG.CGT.T75E.tvSL_mulVec, hφβ, one_smul]
        funext k
        by_cases hk0 : k = (⟨0, by omega⟩ : Fin n)
        · subst hk0
          simp [Pi.add_apply, Pi.sub_apply, s16k_e, Pi.single_apply, hη0]
        · by_cases hk5 : k = (⟨5, by omega⟩ : Fin n)
          · subst hk5
            simp [Pi.add_apply, Pi.sub_apply, s16k_e, Pi.single_apply, hk0, hβ50, hη5]
          · simp [Pi.add_apply, Pi.sub_apply, s16k_e, Pi.single_apply, hη, hk0, hk5]
      · exact s16k_tvSL_row _ _ hdot (⟨0, by omega⟩) (by simp [Pi.sub_apply, hη0, s16k_e])
      · exact s16k_tvSL_col _ _ hdot (⟨0, by omega⟩) (by simp [s16k_e, hj0])

private theorem s16k_nat_pair_of_ne_zero (hK : Nat.card K = 2) {n : ℕ} (hn : 6 ≤ n)
    (a b : Multiplicative (Fin n → K)) (hab : a ≠ 1 ∨ b ≠ 1) :
    ∃ B : Subgroup ↥(StatedSL n K), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
        natAct (StatedSL n K) g a = a ∧ natAct (StatedSL n K) g b = b := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨E, hEΓ, hcard, hexp, hfix0, hfix5, hσE⟩ := s16k_exists_E hK hn
  have h2n : 2 ≤ n := by omega
  by_cases ha : Multiplicative.toAdd a ≠ 0
  · obtain ⟨g, hg, hga⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq h2n ha
      (s16k_e_ne_zero (K := K) (⟨0, by omega⟩ : Fin n))
    let gΓ : ↥(StatedSL n K) := ⟨g, hg⟩
    obtain ⟨M, p, q, hMβ, hMrow, hMcol⟩ := s16k_move_to_pair hK hn
      (g *ᵥ Multiplicative.toAdd b)
    let c : ↥(StatedSL n K) := s16k_toΓ M * gΓ
    have hcu : (c : GL (Fin n) K) *ᵥ Multiplicative.toAdd a =
        s16k_e (K := K) (⟨0, by omega⟩ : Fin n) := by
      change ((((M : GL (Fin n) K) * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ
        Multiplicative.toAdd a = _
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hga]
      exact hMcol
    have hcw : (c : GL (Fin n) K) *ᵥ Multiplicative.toAdd b =
        p • s16k_e (K := K) (⟨0, by omega⟩ : Fin n) +
          q • s16k_e (K := K) (⟨5, by omega⟩ : Fin n) := by
      change ((((M : GL (Fin n) K) * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ
        Multiplicative.toAdd b = _
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      simpa using hMβ
    have hEu : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) *ᵥ
        s16k_e (K := K) (⟨0, by omega⟩ : Fin n) =
        s16k_e (K := K) (⟨0, by omega⟩ : Fin n) := hfix0
    have hEw : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) *ᵥ
        (p • s16k_e (K := K) (⟨0, by omega⟩ : Fin n) +
          q • s16k_e (K := K) (⟨5, by omega⟩ : Fin n)) =
        p • s16k_e (K := K) (⟨0, by omega⟩ : Fin n) +
          q • s16k_e (K := K) (⟨5, by omega⟩ : Fin n) := by
      intro e he
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hfix0 e he, hfix5 e he]
    obtain ⟨B, hBp, hBc, hBfix⟩ := s16k_conj_fix_two E hEΓ hcard hexp c hcu hcw hEu hEw
    exact ⟨B, hBp, hBc, fun g hg => ⟨by rw [natAct, (hBfix g hg).1, ofAdd_toAdd],
      by rw [natAct, (hBfix g hg).2, ofAdd_toAdd]⟩⟩
  · have ha0 : Multiplicative.toAdd a = 0 := not_not.mp ha
    have hb : Multiplicative.toAdd b ≠ 0 := by
      intro hb0
      rcases hab with h | h
      · exact h ((toAdd_eq_zero).mp ha0)
      · exact h ((toAdd_eq_zero).mp hb0)
    obtain ⟨c, hc, hcb⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq h2n hb
      (s16k_e_ne_zero (K := K) (⟨0, by omega⟩ : Fin n))
    let cΓ : ↥(StatedSL n K) := ⟨c, hc⟩
    have hcu : ((cΓ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        Multiplicative.toAdd a = 0 := by
      rw [ha0]
      exact Matrix.mulVec_zero _
    have hcw : (cΓ : GL (Fin n) K) *ᵥ Multiplicative.toAdd b =
        s16k_e (K := K) (⟨0, by omega⟩ : Fin n) := hcb
    obtain ⟨B, hBp, hBc, hBfix⟩ := s16k_conj_fix_two E hEΓ hcard hexp cΓ hcu hcw
      (fun e _ => Matrix.mulVec_zero _) hfix0
    exact ⟨B, hBp, hBc, fun g hg => ⟨by rw [natAct, (hBfix g hg).1, ofAdd_toAdd],
      by rw [natAct, (hBfix g hg).2, ofAdd_toAdd]⟩⟩

private theorem s16k_dual_pair_of_ne_zero (hK : Nat.card K = 2) {n : ℕ} (hn : 6 ≤ n)
    (a b : Multiplicative (Fin n → K)) (hab : a ≠ 1 ∨ b ≠ 1) :
    ∃ B : Subgroup ↥(StatedSL n K), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
        natAct (StatedSL n K) g a = a ∧ dualNatAct (StatedSL n K) g b = b := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨E, hEΓ, hcard, hexp, hfix0, hfix5, hσE⟩ := s16k_exists_E hK hn
  have h2n : 2 ≤ n := by omega
  by_cases ha : Multiplicative.toAdd a ≠ 0
  · obtain ⟨g, hg, hga⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq h2n ha
      (s16k_e_ne_zero (K := K) (⟨0, by omega⟩ : Fin n))
    let gΓ : ↥(StatedSL n K) := ⟨g, hg⟩
    let β : Fin n → K :=
      ((Matrix.GeneralLinearGroup.inverseTranspose (gΓ : GL (Fin n) K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd b
    obtain ⟨M, p, q, hMβ, hMrow, hMcol⟩ := s16k_move_to_pair hK hn β
    let MΓ : ↥(StatedSL n K) := s16k_toΓ M
    have hdet : IsUnit (((MΓ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det) := by
      change IsUnit ((M : Matrix (Fin n) (Fin n) K).det)
      rw [M.2]; exact isUnit_one
    let N : ↥(StatedSL n K) :=
      ⟨Matrix.GeneralLinearGroup.inverseTranspose (MΓ : GL (Fin n) K), by
        have htop : StatedSL n K = (⊤ : Subgroup (GL (Fin n) K)) :=
          CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK n
        simpa only [htop] using Subgroup.mem_top
          (Matrix.GeneralLinearGroup.inverseTranspose (MΓ : GL (Fin n) K))⟩
    let c : ↥(StatedSL n K) := N * gΓ
    have hN0 : (N : GL (Fin n) K) *ᵥ s16k_e (K := K) (⟨0, by omega⟩ : Fin n) =
        s16k_e (K := K) (⟨0, by omega⟩ : Fin n) := by
      have h1 : (((M : Matrix (Fin n) (Fin n) K)ᵀ)⁻¹) *ᵥ
          s16k_e (K := K) (⟨0, by omega⟩ : Fin n) =
          s16k_e (K := K) (⟨0, by omega⟩ : Fin n) :=
        s16k_inv_mulVec_of_mulVec (by rw [Matrix.det_transpose]; exact hdet) hMrow
      change ((((Matrix.GeneralLinearGroup.inverseTranspose (MΓ : GL (Fin n) K) : GL (Fin n) K)) :
        Matrix (Fin n) (Fin n) K)) *ᵥ s16k_e (K := K) (⟨0, by omega⟩ : Fin n) = _
      rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, Matrix.GeneralLinearGroup.coe_inv,
        Matrix.transpose_nonsing_inv]
      exact h1
    have hcu : (c : GL (Fin n) K) *ᵥ Multiplicative.toAdd a =
        s16k_e (K := K) (⟨0, by omega⟩ : Fin n) := by
      change ((((N : GL (Fin n) K) * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ
        Multiplicative.toAdd a = _
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hga, hN0]
    have hEz : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) *ᵥ
        ((Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd b =
        ((Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd b := by
      intro e he
      have hz : (Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) :
          GL (Fin n) K) *ᵥ Multiplicative.toAdd b =
          p • s16k_e (K := K) (⟨0, by omega⟩ : Fin n) +
            q • s16k_e (K := K) (⟨5, by omega⟩ : Fin n) := by
        have hσc : Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) =
            (s16k_toΓ M : GL (Fin n) K) *
              Matrix.GeneralLinearGroup.inverseTranspose (gΓ : GL (Fin n) K) := by
          change Matrix.GeneralLinearGroup.inverseTranspose
            (Matrix.GeneralLinearGroup.inverseTranspose (MΓ : GL (Fin n) K) *
              (gΓ : GL (Fin n) K)) = _
          rw [map_mul, Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
        rw [hσc, Units.val_mul, ← Matrix.mulVec_mulVec]
        change ((s16k_toΓ M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((Matrix.GeneralLinearGroup.inverseTranspose (gΓ : GL (Fin n) K) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd b) = _
        rw [show ((s16k_toΓ M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            (M : Matrix (Fin n) (Fin n) K) from rfl,
          show ((Matrix.GeneralLinearGroup.inverseTranspose (gΓ : GL (Fin n) K) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd b = β from rfl]
        exact hMβ
      rw [hz]
      exact s16k_E_fix_span (⟨0, by omega⟩ : Fin n) (⟨5, by omega⟩ : Fin n)
        hfix0 hfix5 e he p q
    obtain ⟨B, hBp, hBc, hBfix⟩ := s16k_conj_fix_dual E hEΓ hcard hexp hσE c hcu
      (fun e he => hfix0 e he) hEz
    refine ⟨B, hBp, hBc, fun g hg => ⟨by rw [natAct, (hBfix g hg).1, ofAdd_toAdd], ?_⟩⟩
    rw [dualNatAct, (hBfix g hg).2, ofAdd_toAdd]
  · have ha0 : Multiplicative.toAdd a = 0 := not_not.mp ha
    have hb : Multiplicative.toAdd b ≠ 0 := by
      intro hb0
      rcases hab with h | h
      · exact h ((toAdd_eq_zero).mp ha0)
      · exact h ((toAdd_eq_zero).mp hb0)
    obtain ⟨N, hN, hNb⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq h2n hb
      (s16k_e_ne_zero (K := K) (⟨0, by omega⟩ : Fin n))
    let c : ↥(StatedSL n K) :=
      ⟨Matrix.GeneralLinearGroup.inverseTranspose N,
        (CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK n).symm ▸ Subgroup.mem_top _⟩
    have hcu : ((c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        Multiplicative.toAdd a = 0 := by
      rw [ha0]
      exact Matrix.mulVec_zero _
    have hEz : ∀ e ∈ E, (e : Matrix (Fin n) (Fin n) K) *ᵥ
        ((Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd b =
        ((Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Multiplicative.toAdd b := by
      intro e he
      have hz : (Matrix.GeneralLinearGroup.inverseTranspose (c : GL (Fin n) K) :
          GL (Fin n) K) *ᵥ Multiplicative.toAdd b =
          s16k_e (K := K) (⟨0, by omega⟩ : Fin n) := by
        change (((Matrix.GeneralLinearGroup.inverseTranspose
          (Matrix.GeneralLinearGroup.inverseTranspose N : GL (Fin n) K) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K)) *ᵥ Multiplicative.toAdd b = _
        rw [Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
        exact hNb
      rw [hz]
      exact hfix0 e he
    obtain ⟨B, hBp, hBc, hBfix⟩ := s16k_conj_fix_dual E hEΓ hcard hexp hσE c hcu
      (fun e _ => Matrix.mulVec_zero _) hEz
    refine ⟨B, hBp, hBc, fun g hg => ⟨by rw [natAct, (hBfix g hg).1, ofAdd_toAdd], ?_⟩⟩
    rw [dualNatAct, (hBfix g hg).2, ofAdd_toAdd]

theorem s16k_sl_pair_fix {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (hn : 6 ≤ n) (a b : Multiplicative (Fin n → K)) (hab : a ≠ 1 ∨ b ≠ 1) :
    (∃ B : Subgroup ↥(StatedSL n K), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
        natAct (StatedSL n K) g a = a ∧ natAct (StatedSL n K) g b = b) ∧
      (∃ B : Subgroup ↥(StatedSL n K), IsPGroup 3 B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
        natAct (StatedSL n K) g a = a ∧ dualNatAct (StatedSL n K) g b = b) :=
  ⟨s16k_nat_pair_of_ne_zero hK hn a b hab, s16k_dual_pair_of_ne_zero hK hn a b hab⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
