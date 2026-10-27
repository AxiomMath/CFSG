module

public import CFSG.LocalAnalysis.StandardType.GGTPWeightDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open Multiplicative

private lemma ggTP_three_dvd_sq_sub_one {q : ℕ} (h3 : 3 ∣ q + 1) : 3 ∣ q ^ 2 - 1 := by
  have hq : 0 < q := by
    by_contra h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    rw [hq0] at h3
    norm_num at h3
  have hqneg : (q : ZMod 3) = -1 := by
    have h : ((q + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).2 h3
    push_cast at h
    simpa using (eq_neg_of_add_eq_zero_left h)
  have hsq : ((q ^ 2 : ℕ) : ZMod 3) = 1 := by
    rw [Nat.cast_pow, hqneg]
    decide
  have hsub : ((q ^ 2 - 1 : ℕ) : ZMod 3) = 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow 2 q hq), hsq]
    decide
  exact (ZMod.natCast_eq_zero_iff _ 3).1 hsub

private def ggTP_diagGL {K : Type} [Field K] (a : Fin 6 → Kˣ) : GL (Fin 6) K :=
  ⟨Matrix.diagonal fun i => (a i : K),
   Matrix.diagonal fun i => ((a i)⁻¹ : K),
   by
     rw [Matrix.diagonal_mul_diagonal]
     ext i j
     by_cases h : i = j
     · subst h; simp
     · simp [h],
   by
     rw [Matrix.diagonal_mul_diagonal]
     ext i j
     by_cases h : i = j
     · subst h; simp
     · simp [h]⟩

private def ggTP_permGL {K : Type} [Field K] (σ : Equiv.Perm (Fin 6)) : GL (Fin 6) K :=
  ⟨σ.permMatrix K, (σ⁻¹).permMatrix K,
   by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
   by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

private lemma ggTP_permGL_conj_diagGL {K : Type} [Field K] (σ : Equiv.Perm (Fin 6))
    (a : Fin 6 → Kˣ) :
    ggTP_permGL σ * ggTP_diagGL a * (ggTP_permGL σ)⁻¹ = ggTP_diagGL (a ∘ σ) := by
  apply Units.ext
  change σ.permMatrix K * Matrix.diagonal (fun i => (a i : K)) * (σ⁻¹).permMatrix K =
    Matrix.diagonal fun i => (a (σ i) : K)
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext k l
  simp only [Matrix.submatrix_apply, id, Matrix.diagonal_apply, Equiv.Perm.inv_def,
    Equiv.symm_symm, EmbeddingLike.apply_eq_iff_eq]

private lemma ggTP_pow_mul {K : Type} [Field K] (ω : Kˣ) (hω3 : orderOf ω = 3)
    (a b : Multiplicative (ZMod 3)) :
    ω ^ (a * b).toAdd.val = ω ^ a.toAdd.val * ω ^ b.toAdd.val := by
  have hcast : (((a * b).toAdd).val : ZMod 3) =
      ((a.toAdd.val + b.toAdd.val : ℕ) : ZMod 3) := by
    rw [ZMod.natCast_zmod_val, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      toAdd_mul]
  have hmod : (a * b).toAdd.val ≡ a.toAdd.val + b.toAdd.val [MOD 3] :=
    (ZMod.natCast_eq_natCast_iff _ _ 3).1 hcast
  have hmod' : (a * b).toAdd.val ≡ a.toAdd.val + b.toAdd.val [MOD orderOf ω] := by
    rwa [hω3]
  rw [pow_eq_pow_iff_modEq.mpr hmod', pow_add]

private lemma ggTP_prod_sum (x : GGTPTorus) :
    ((∑ i, (x.1 i).toAdd.val : ℕ) : ZMod 3) = 0 := by
  have h := congrArg toAdd x.2
  rw [toAdd_prod, toAdd_one] at h
  have hcast : ((∑ i, (x.1 i).toAdd.val : ℕ) : ZMod 3) = ∑ i, (x.1 i).toAdd := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ZMod.natCast_zmod_val _
  rw [hcast]
  exact h

private lemma ggTP_dvd_sum (x : GGTPTorus) : 3 ∣ ∑ i, (x.1 i).toAdd.val :=
  (ZMod.natCast_eq_zero_iff _ 3).1 (ggTP_prod_sum x)

private lemma ggTP_diag_det {K : Type} [Field K] (ω : Kˣ) (hω3 : orderOf ω = 3)
    (x : GGTPTorus) :
    ((ggTP_diagGL (fun i => ω ^ (x.1 i).toAdd.val) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K).det = 1 := by
  have hprod : ∏ i, ω ^ (x.1 i).toAdd.val = 1 := by
    rw [Finset.prod_pow_eq_pow_sum]
    rw [← orderOf_dvd_iff_pow_eq_one]
    rw [hω3]
    exact ggTP_dvd_sum x
  change (Matrix.diagonal (fun i => ((ω ^ (x.1 i).toAdd.val : Kˣ) : K))).det = 1
  rw [Matrix.det_diagonal, ← Units.coe_prod, hprod, Units.val_one]

private lemma ggTP_diag_unitary {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0) (ω : Kˣ)
    (hω3 : orderOf ω = 3)
    (hωq1 : ω ^ (q + 1) = 1) (x : GGTPTorus) :
    ((((ggTP_diagGL (fun i => ω ^ (x.1 i).toAdd.val) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K).map (· ^ q)).transpose) *
      ((ggTP_diagGL (fun i => ω ^ (x.1 i).toAdd.val) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = 1 := by
  change (((Matrix.diagonal (fun i => ((ω ^ (x.1 i).toAdd.val : Kˣ) : K))).map (· ^ q)).transpose) *
    Matrix.diagonal (fun i => ((ω ^ (x.1 i).toAdd.val : Kˣ) : K)) = 1
  rw [Matrix.diagonal_map (by simp [hq]), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← pow_succ]
  have hai : (ω ^ (x.1 i).toAdd.val : Kˣ) ^ (q + 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hωq1, one_pow]
  rw [← Units.val_pow_eq_pow_val, hai, Units.val_one]

private lemma ggTP_diag_mem_SU {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0) (ω : Kˣ)
    (hω3 : orderOf ω = 3)
    (hωq1 : ω ^ (q + 1) = 1) (x : GGTPTorus) :
    ggTP_diagGL (fun i => ω ^ (x.1 i).toAdd.val) ∈
      LargeEvenSUGroup (Fin 6) K q := by
  rw [LargeEvenSUGroup]
  apply Subgroup.subset_closure
  exact ⟨ggTP_diag_det ω hω3 x, ggTP_diag_unitary hq ω hω3 hωq1 x⟩

private lemma ggTP_perm_det {K : Type} [Field K] [CharP K 2] (σ : Equiv.Perm (Fin 6)) :
    ((ggTP_permGL σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  change (σ.permMatrix K).det = 1
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h]; simp
  · rw [h]
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hneg : (-1 : K) = 1 := by
      have hh := congrArg (fun x : K => x - 1) h2
      norm_num at hh
      exact hh.symm
    simpa using hneg

private lemma ggTP_perm_unitary {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0)
    (σ : Equiv.Perm (Fin 6)) :
    ((((ggTP_permGL σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map (· ^ q)).transpose) *
      ((ggTP_permGL σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
  change (((σ.permMatrix K).map (· ^ q)).transpose) * (σ.permMatrix K) = 1
  have hmap : (σ.permMatrix K).map (· ^ q) = σ.permMatrix K := by
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp [hq]
  rw [hmap, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]

private lemma ggTP_perm_mem_SU {K : Type} [Field K] [CharP K 2] {q : ℕ} (hq : q ≠ 0)
    (σ : Equiv.Perm (Fin 6)) :
    ggTP_permGL σ ∈ LargeEvenSUGroup (Fin 6) K q := by
  rw [LargeEvenSUGroup]
  apply Subgroup.subset_closure
  exact ⟨ggTP_perm_det σ, ggTP_perm_unitary hq σ⟩

private lemma ggTP_diag_mem_scalars_iff {K : Type} [Field K] (ω : Kˣ)
    (hω3 : orderOf ω = 3)
    (x : GGTPTorus) :
    ggTP_diagGL (fun i => ω ^ (x.1 i).toAdd.val) ∈ LargeEvenScalars (Fin 6) K ↔
      x.1 ∈ GGTPTorusConst := by
  constructor
  · intro h
    have h' : ggTP_diagGL (fun i => ω ^ (x.1 i).toAdd.val) ∈
        (Matrix.GeneralLinearGroup.scalar (Fin 6) : Kˣ →* GL (Fin 6) K).range := by
      simpa [LargeEvenScalars, CFSG.Open.StatedScalars] using h
    rw [MonoidHom.mem_range] at h'
    obtain ⟨c, hc⟩ := h'
    have hentry : ∀ i, ((ω ^ (x.1 i).toAdd.val : Kˣ) : K) = (c : K) := by
      intro i
      have := congrArg (fun A : GL (Fin 6) K =>
        ((A : Matrix (Fin 6) (Fin 6) K) i i)) hc
      simpa [ggTP_diagGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
        using this.symm
    intro i j
    have hpow : ω ^ (x.1 i).toAdd.val = ω ^ (x.1 j).toAdd.val := by
      apply Units.ext
      exact (hentry i).trans (hentry j).symm
    have hmod := (pow_eq_pow_iff_modEq).1 hpow
    rw [hω3] at hmod
    have hv := Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt _) (ZMod.val_lt _)
    calc
      x.1 i = ofAdd ((x.1 i).toAdd.val : ZMod 3) := by
        rw [ZMod.natCast_zmod_val, ofAdd_toAdd]
      _ = ofAdd ((x.1 j).toAdd.val : ZMod 3) := by rw [hv]
      _ = x.1 j := by rw [ZMod.natCast_zmod_val, ofAdd_toAdd]
  · intro hx
    have h' : ggTP_diagGL (fun i => ω ^ (x.1 i).toAdd.val) ∈
        (Matrix.GeneralLinearGroup.scalar (Fin 6) : Kˣ →* GL (Fin 6) K).range := by
      rw [MonoidHom.mem_range]
      refine ⟨ω ^ (x.1 0).toAdd.val, ?_⟩
      apply Units.ext
      change Matrix.diagonal (fun _ : Fin 6 => ((ω ^ (x.1 0).toAdd.val : Kˣ) : K)) =
        Matrix.diagonal fun i => ((ω ^ (x.1 i).toAdd.val : Kˣ) : K)
      congr 1
      funext i
      have hxi : x.1 i = x.1 0 := hx i 0
      rw [hxi]
    simpa [LargeEvenScalars, CFSG.Open.StatedScalars] using h'

private def ggTP_Dhom {K : Type} [Field K] (ω : Kˣ) (hω3 : orderOf ω = 3) :
    GGTPTorus →* GL (Fin 6) K where
  toFun x := ggTP_diagGL (fun i => ω ^ (x.1 i).toAdd.val)
  map_one' := by
    apply Units.ext
    change Matrix.diagonal (fun i => ((ω ^ (((1 : GGTPTorus).1 i)).toAdd.val : Kˣ) : K)) = 1
    simp [ggTP_diagGL, Matrix.diagonal_one]
  map_mul' x y := by
    apply Units.ext
    change Matrix.diagonal (fun i => ((ω ^ ((x * y).1 i).toAdd.val : Kˣ) : K)) =
      Matrix.diagonal (fun i => ((ω ^ (x.1 i).toAdd.val : Kˣ) : K)) *
        Matrix.diagonal (fun i => ((ω ^ (y.1 i).toAdd.val : Kˣ) : K))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact congrArg (fun u : Kˣ => (u : K)) (ggTP_pow_mul ω hω3 (x.1 i) (y.1 i))

theorem ggTPTorus_PSU6 {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) :
    ∃ (δ : GGTPTorus →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K q))
      (w : Equiv.Perm (Fin 6) → LargeEvenProj (LargeEvenSUGroup (Fin 6) K q)),
      (∀ x : GGTPTorus, δ x = 1 ↔ (x : Fin 6 → Multiplicative (ZMod 3)) ∈ GGTPTorusConst) ∧
        ∀ (σ : Equiv.Perm (Fin 6)) (x : GGTPTorus), w σ * δ x * (w σ)⁻¹ = δ (ggTPPermAct σ x) := by
  have hq : q ≠ 0 := by
    intro hq0
    rw [hq0] at h3
    norm_num at h3
  have hcard : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact ggTP_three_dvd_sq_sub_one h3
  have hunits : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hcard
  obtain ⟨ω, hω3⟩ := exists_prime_orderOf_dvd_card' 3 hunits
  have hωq1 : ω ^ (q + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hω3]
    exact h3
  let DH : GGTPTorus →* ↥(LargeEvenSUGroup (Fin 6) K q) :=
    (ggTP_Dhom ω hω3).codRestrict _ (fun x => ggTP_diag_mem_SU hq ω hω3 hωq1 x)
  let δ : GGTPTorus →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K q) :=
    (LargeEvenProjMk _).comp DH
  let w : Equiv.Perm (Fin 6) → LargeEvenProj (LargeEvenSUGroup (Fin 6) K q) :=
    fun σ => LargeEvenProjMk _ ⟨ggTP_permGL (σ⁻¹), ggTP_perm_mem_SU hq (σ⁻¹)⟩
  refine ⟨δ, w, ?_, ?_⟩
  · intro x
    change LargeEvenProjMk _ (DH x) = 1 ↔ x.1 ∈ GGTPTorusConst
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    change ggTP_diagGL (fun i => ω ^ (x.1 i).toAdd.val) ∈ LargeEvenScalars (Fin 6) K ↔
      x.1 ∈ GGTPTorusConst
    exact ggTP_diag_mem_scalars_iff ω hω3 x
  · intro σ x
    change LargeEvenProjMk _ ⟨ggTP_permGL (σ⁻¹), ggTP_perm_mem_SU hq (σ⁻¹)⟩ *
        LargeEvenProjMk _ (DH x) *
        (LargeEvenProjMk _ ⟨ggTP_permGL (σ⁻¹), ggTP_perm_mem_SU hq (σ⁻¹)⟩)⁻¹ =
      LargeEvenProjMk _ (DH (ggTPPermAct σ x))
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    change ggTP_permGL (σ⁻¹) * ggTP_diagGL (fun i => ω ^ (x.1 i).toAdd.val) *
        (ggTP_permGL (σ⁻¹))⁻¹ =
      ggTP_diagGL (fun i => ω ^ ((ggTPPermAct σ x).1 i).toAdd.val)
    rw [ggTP_permGL_conj_diagGL]
    apply congrArg ggTP_diagGL
    funext i
    simp [ggTPPermAct]

end CFSG.StandardType

end
