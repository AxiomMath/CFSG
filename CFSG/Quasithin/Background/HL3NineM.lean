module

public import CFSG.Quasithin.Background.FixVZPowers
public import CFSG.Quasithin.Background.HL3NineNorm
public import CFSG.Quasithin.Background.HSL3Alpha
public import CFSG.CGT.Timmesfeld75.SLTransvection

public section

namespace CFSG.Quasithin

namespace H

namespace L3Nine

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix SU3 Tri CFSG.LocalAnalysis.ComponentInitial
open Module

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem card_fixV_conj {W : Type*} [CommGroup W] (g t : MulAut W) :
    Nat.card ↥(fixV (Subgroup.zpowers (g * t * g⁻¹))) = Nat.card ↥(fixV (Subgroup.zpowers t)) :=
  CFSG.Quasithin.card_fixV_zpowers_conj g t

theorem fix_trGL_entries (hK : Nat.card K = (2 ^ n) ^ 2) {X : HMod n K}
    (hX : rhoT hK (trGL (0 : Fin 3) 2 (by decide) 1) X = X) :
    mat X 2 1 = 0 ∧ mat X 2 2 = 0 ∧ mat X 1 2 = 0 ∧ bar n (mat X 0 2) = mat X 0 2 := by
  have e : ∀ i j : Fin 3, mat (rhoT hK (trGL (0 : Fin 3) 2 (by decide) 1) X) i j = mat X i j :=
    fun i j => by rw [hX]
  simp only [mat_rhoT, tw, coe_trGL, Matrix.mul_apply, Fin.sum_univ_three, transpose_apply,
    conjM, map_apply] at e
  have h01 := e 0 1
  have h02 := e 0 2
  have h10 := e 1 0
  have h00 := e 0 0
  simp [transvection] at h01 h02 h10 h00
  refine ⟨h01, h02, h10, ?_⟩
  rw [herm_apply X 2 0]
  have h1 : mat X 2 0 + mat X 0 2 = 0 := by
    rw [h02, add_zero] at h00
    linear_combination h00
  rw [← CharTwo.neg_eq (mat X 0 2)]
  exact eq_neg_of_add_eq_zero_left h1

theorem card_fixV_trGL_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card ↥(fixV (Subgroup.zpowers (rhoT hK (trGL (0 : Fin 3) 2 (by decide) (1 : K))))) ≤
      2 ^ (6 * n) := by
  classical
  let Fq := {b : K // bar n b = b}
  let f : ↥(fixV (Subgroup.zpowers (rhoT hK (trGL (0 : Fin 3) 2 (by decide) (1 : K))))) →
      Fq × Fq × K × Fq := fun X =>
    (⟨mat (X : HMod n K) 0 0, herm_apply _ 0 0⟩, ⟨mat (X : HMod n K) 1 1, herm_apply _ 1 1⟩,
      mat (X : HMod n K) 0 1,
      ⟨mat (X : HMod n K) 0 2, (fix_trGL_entries hK (mem_fixV_zpowers_iff.mp X.2)).2.2.2⟩)
  have hf : Function.Injective f := by
    intro X Y h
    have h00 : mat (X : HMod n K) 0 0 = mat (Y : HMod n K) 0 0 := congrArg (fun p => p.1.1) h
    have h11 : mat (X : HMod n K) 1 1 = mat (Y : HMod n K) 1 1 :=
      congrArg (fun p => p.2.1.1) h
    have h01 : mat (X : HMod n K) 0 1 = mat (Y : HMod n K) 0 1 :=
      congrArg (fun p => p.2.2.1) h
    have h02 : mat (X : HMod n K) 0 2 = mat (Y : HMod n K) 0 2 :=
      congrArg (fun p => p.2.2.2.1) h
    obtain ⟨x21, x22, x12, -⟩ := fix_trGL_entries hK (mem_fixV_zpowers_iff.mp X.2)
    obtain ⟨y21, y22, y12, -⟩ := fix_trGL_entries hK (mem_fixV_zpowers_iff.mp Y.2)
    apply Subtype.ext
    apply mat_injective
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h02
    · change mat (X : HMod n K) 1 0 = mat (Y : HMod n K) 1 0
      rw [← herm_apply (X : HMod n K) 1 0, ← herm_apply (Y : HMod n K) 1 0, h01]
    · exact h11
    · change mat (X : HMod n K) 1 2 = mat (Y : HMod n K) 1 2
      rw [x12, y12]
    · change mat (X : HMod n K) 2 0 = mat (Y : HMod n K) 2 0
      rw [← herm_apply (X : HMod n K) 2 0, ← herm_apply (Y : HMod n K) 2 0, h02]
    · change mat (X : HMod n K) 2 1 = mat (Y : HMod n K) 2 1
      rw [x21, y21]
    · change mat (X : HMod n K) 2 2 = mat (Y : HMod n K) 2 2
      rw [x22, y22]
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod] at hle
  change _ ≤ Nat.card Fq * (Nat.card Fq * (Nat.card K * Nat.card Fq)) at hle
  rw [card_fixed hn hK, hK] at hle
  calc _ ≤ 2 ^ n * (2 ^ n * ((2 ^ n) ^ 2 * 2 ^ n)) := hle
    _ = 2 ^ (5 * n) := by ring
    _ ≤ 2 ^ (6 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)

omit [Finite K] in
theorem card_fixed_vec [Finite K] {A : Matrix (Fin 3) (Fin 3) K} (hA : A * A = 1) (hA1 : A ≠ 1) :
    Nat.card {w : Fin 3 → K // A *ᵥ w = w} = Nat.card K ^ 2 := by
  classical
  set f := Matrix.toLin' (A - 1) with hf
  have hker : ∀ w, w ∈ LinearMap.ker f ↔ A *ᵥ w = w := by
    intro w
    rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_eq_zero]
  have hsq : (A - 1) * (A - 1) = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (A - 1) * (A - 1) = A * A - 2 • A + 1 := by
      rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, mul_one, two_smul]
      abel
    rw [this, hA, two_smul, ← two_smul K A, h2, zero_smul, sub_zero,
      ← two_smul K (1 : Matrix _ _ K)]
    rw [h2, zero_smul]
  have hrange : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hf, ← Matrix.toLin'_mul, hsq, map_zero,
      LinearMap.zero_apply]
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hsum
  have hle := Submodule.finrank_mono hrange
  have hpos : 0 < Module.finrank K (LinearMap.range f) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
    intro h0
    apply hA1
    have : A - 1 = 0 := by
      rw [← Matrix.toLin'.injective.eq_iff, map_zero]
      exact h0
    exact sub_eq_zero.mp this
  have h2 : Module.finrank K (LinearMap.ker f) = 2 := by omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun w => (hker w).symm)]
  change Nat.card ↥(LinearMap.ker f) = _
  rw [Module.natCard_eq_pow_finrank (K := K), h2]

omit [Finite K] in
theorem eq_one_of_sq_eq_one {x : K} (h : x * x = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (x - 1) * (x - 1) = 0 := by linear_combination h + (1 - x) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)

open CFSG.CGT.Timmesfeld75 in
theorem exists_conj_eq_transvection {u : SpecialLinearGroup (Fin 3) K} (hu : u * u = 1)
    (hu1 : u ≠ 1) :
    ∃ W : SpecialLinearGroup (Fin 3) K,
      W * u * W⁻¹ = SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) 1 := by
  have hcard : ∀ v : SpecialLinearGroup (Fin 3) K, v * v = 1 → v ≠ 1 →
      Nat.card {w : Fin 3 → K // (v : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w} =
        Nat.card K ^ (3 - 1) := by
    intro v hv hv1
    refine card_fixed_vec (A := (v : Matrix (Fin 3) (Fin 3) K)) ?_ ?_
    · rw [← Matrix.SpecialLinearGroup.coe_mul, hv, Matrix.SpecialLinearGroup.coe_one]
    · intro h
      exact hv1 (Subtype.ext h)
  have ht2 := transvection_mul_self (by decide : (0 : Fin 3) ≠ 2) (1 : K)
  have ht1 : SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) (1 : K) ≠ 1 := by
    intro h
    have := congrArg (fun v : SpecialLinearGroup (Fin 3) K => (v : Matrix (Fin 3) (Fin 3) K) 0 2) h
    simp [Matrix.SpecialLinearGroup.transvection_coe] at this
  exact exists_conj_of_isTransvection (isTransvection_of_card_fixed hu hu1 (hcard u hu hu1))
    (isTransvection_of_card_fixed ht2 ht1 (hcard _ ht2 ht1))

theorem exists_sq_eq_one (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {A : GL (Fin 3) K}
    (h : rhoT hK A * rhoT hK A = 1) :
    ∃ A' : GL (Fin 3) K, rhoT hK A' = rhoT hK A ∧ A' * A' = 1 := by
  rw [← map_mul] at h
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h
  have hdd : d * bar n d = 1 := by
    have h1 := congrArg (fun Y : HMod n K => mat Y 0 0) (congrArg (fun f => f (e00 hK)) h)
    simp only [MulAut.one_apply, mat_rhoT, hd, tw, mat_pt, rk1_apply] at h1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, conjM, Matrix.smul_apply, rk1_apply] using h1
  have hd0 : d ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hdd
    exact zero_ne_one hdd
  have hdq : d ^ (2 ^ n + 1) = 1 := by
    rw [pow_succ, ← bar_apply, mul_comm]
    exact hdd
  set ν := d ^ (2 ^ (n - 1) + 1) with hν
  have hν0 : ν ≠ 0 := pow_ne_zero _ hd0
  have h2n : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hn]
  have hνsq : ν * ν = d := by
    rw [← pow_two, hν, ← pow_mul]
    have e : (2 ^ (n - 1) + 1) * 2 = (2 ^ n + 1) + 1 := by omega
    rw [e, pow_succ, hdq, one_mul]
  have hνbar : ν * bar n ν = 1 := by
    rw [bar_apply, ← pow_succ', hν, ← pow_mul, mul_comm, pow_mul, hdq, one_pow]
  let u : Kˣ := Units.mk0 ν hν0
  have hs : rhoT hK (scalGL u) = 1 := MulEquiv.ext fun X => mat_injective (by
    rw [mat_rhoT_scalGL]
    change (ν * bar n ν) • mat X = mat X
    rw [hνbar, one_smul])
  refine ⟨(scalGL u)⁻¹ * A, by rw [map_mul, map_inv, hs, inv_one, one_mul], ?_⟩
  apply Units.ext
  have hsi : (((scalGL u)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ν⁻¹ • 1 := by
    have e : (scalGL u)⁻¹ = scalGL u⁻¹ :=
      (map_inv (Matrix.GeneralLinearGroup.scalar (Fin 3)) u).symm
    rw [e, coe_scalGL]
    rfl
  have hAA : (A : Matrix (Fin 3) (Fin 3) K) * A = d • 1 := by
    rw [← Units.val_mul]
    exact hd
  rw [Units.val_mul, Units.val_mul, Units.val_one, hsi, Matrix.smul_mul, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAA, smul_smul, ← hνsq]
  rw [show ν⁻¹ * ν⁻¹ * (ν * ν) = 1 by field_simp, one_smul]

theorem card_fixV_le_of_rhoT (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {A : GL (Fin 3) K}
    (h2 : rhoT hK A * rhoT hK A = 1) (h1 : rhoT hK A ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers (rhoT hK A))) ≤ 2 ^ (6 * n) := by
  obtain ⟨A', hA', hA'2⟩ := exists_sq_eq_one hn hK h2
  have hdet : (A' : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    apply eq_one_of_sq_eq_one
    rw [← Matrix.det_mul, ← Units.val_mul, hA'2, Units.val_one, Matrix.det_one]
  let u : SpecialLinearGroup (Fin 3) K := ⟨A', hdet⟩
  have hu : u * u = 1 := by
    apply Subtype.ext
    change (A' : Matrix (Fin 3) (Fin 3) K) * A' = 1
    rw [← Units.val_mul, hA'2, Units.val_one]
  have hu1 : u ≠ 1 := by
    intro h
    apply h1
    have e : A' = 1 := Units.ext (congrArg (fun v : SpecialLinearGroup (Fin 3) K =>
      (v : Matrix (Fin 3) (Fin 3) K)) h)
    rw [← hA', e, map_one]
  obtain ⟨W, hW⟩ := exists_conj_eq_transvection hu hu1
  have e : rhoT hK A = (rho hK W)⁻¹ * rhoT hK (trGL (0 : Fin 3) 2 (by decide) 1) *
      ((rho hK W)⁻¹)⁻¹ := by
    have e1 : rhoT hK A' = rho hK u := (rho_mk hK hdet).symm
    rw [← hA', e1, ← rho_transvection, ← hW, map_mul, map_mul, map_inv]
    group
  rw [e, card_fixV_conj]
  exact card_fixV_trGL_le hn hK

theorem card_sym {R : Type*} [Finite R] :
    Nat.card {Z : Matrix (Fin 3) (Fin 3) R // Zᵀ = Z} = Nat.card R ^ 6 := by
  classical
  let e : {Z : Matrix (Fin 3) (Fin 3) R // Zᵀ = Z} ≃ R × R × R × R × R × R :=
    { toFun := fun Z => (Z.1 0 0, Z.1 1 1, Z.1 2 2, Z.1 0 1, Z.1 0 2, Z.1 1 2)
      invFun := fun p => ⟨!![p.1, p.2.2.2.1, p.2.2.2.2.1; p.2.2.2.1, p.2.1, p.2.2.2.2.2;
          p.2.2.2.2.1, p.2.2.2.2.2, p.2.2.1], by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl⟩
      left_inv := fun Z => by
        apply Subtype.ext
        have h := Z.2
        ext i j
        fin_cases i <;> fin_cases j <;> first
          | rfl
          | exact (congrFun (congrFun h _ ) _)
      right_inv := fun p => rfl }
  rw [Nat.card_congr e]
  simp only [Nat.card_prod]
  ring

theorem card_fixV_le_of_twisted (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : GL (Fin 3) K}
    (h2 : (rhoT hK A * fldAut (bar n)) * (rhoT hK A * fldAut (bar n)) = 1) :
    Nat.card ↥(fixV (Subgroup.zpowers (rhoT hK A * fldAut (bar n)))) ≤ 2 ^ (6 * n) := by
  classical
  have hbar2 : (bar n : K ≃+* K) * bar n = 1 := by
    ext x
    change bar n (bar n x) = x
    exact bar_bar hK x
  have h3 : rhoT hK (A * mapGL (bar n) A) = 1 := by
    rw [map_mul]
    calc rhoT hK A * rhoT hK (mapGL (bar n) A) =
        rhoT hK A * rhoT hK (mapGL (bar n) A) * fldAut ((bar n : K ≃+* K) * bar n) := by
          rw [hbar2, fldAut_one, mul_one]
      _ = (rhoT hK A * fldAut (bar n)) * (rhoT hK A * fldAut (bar n)) := by
          rw [fldAut_mul, mul_assoc (rhoT hK A) (fldAut (bar n)), ← mul_assoc (fldAut (bar n)),
            fldAut_mul_rhoT]
          group
      _ = 1 := h2
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h3
  have hd' : (A : Matrix (Fin 3) (Fin 3) K) * conjM n (A : Matrix (Fin 3) (Fin 3) K) = d • 1 := by
    rw [← hd, Units.val_mul, coe_mapGL]
    rfl
  have hdd : d * bar n d = 1 := by
    have h1 := congrArg (fun Y : HMod n K => mat Y 0 0) (congrArg (fun f => f (e00 hK)) h3)
    simp only [MulAut.one_apply, mat_rhoT, hd, tw, mat_pt, rk1_apply] at h1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, conjM, Matrix.smul_apply, rk1_apply] using h1
  have hAi : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcA : conjM n (A : Matrix (Fin 3) (Fin 3) K) = d • ((A⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) := by
    calc conjM n (A : Matrix (Fin 3) (Fin 3) K) =
        (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A) * conjM n (A : Matrix _ _ K) := by
          rw [hAi, Matrix.one_mul]
      _ = ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (d • 1) := by
          rw [Matrix.mul_assoc, hd']
      _ = _ := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hdb : bar n d = d := by
    have h1 : conjM n ((A : Matrix (Fin 3) (Fin 3) K) * conjM n (A : Matrix (Fin 3) (Fin 3) K)) =
        conjM n (A : Matrix (Fin 3) (Fin 3) K) * A := by
      rw [conjM_mul, conjM_conjM hK]
    rw [hd', hcA, Matrix.smul_mul, hAi] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa [conjM] using h2
  have hd1 : d = 1 := eq_one_of_sq_eq_one (by rw [hdb] at hdd; exact hdd)
  rw [hd1, one_smul] at hcA
  have hsym : ∀ X : HMod n K, (rhoT hK A * fldAut (bar n) : MulAut (HMod n K)) X = X →
      (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * mat X)ᵀ =
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * mat X := by
    intro X hX
    have h := congrArg mat hX
    rw [MulAut.mul_apply, mat_rhoT, mat_fldAut] at h
    have hc : (mat X).map (bar n) = (mat X)ᵀ := by
      have := congrArg Matrix.transpose (herm_mat X)
      rwa [transpose_transpose] at this
    rw [tw, hc, hcA] at h
    rw [transpose_mul]
    calc (mat X)ᵀ * (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ =
        (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A) * (mat X)ᵀ *
          (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ := by rw [hAi, Matrix.one_mul]
      _ = ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((A : Matrix (Fin 3) (Fin 3) K) * (mat X)ᵀ *
            (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * mat X := by rw [h]
  obtain ⟨z, hz⟩ := exists_bar_ne hn hK
  set C := fixV (Subgroup.zpowers (rhoT hK A * fldAut (bar n))) with hC
  let F : ↥C × ↥C → {Z : Matrix (Fin 3) (Fin 3) K // Zᵀ = Z} := fun p =>
    ⟨((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (mat (p.1 : HMod n K) + z • mat (p.2 : HMod n K)), by
      rw [Matrix.mul_add, Matrix.transpose_add, Matrix.mul_smul, Matrix.transpose_smul,
        hsym _ (mem_fixV_zpowers_iff.mp p.1.2), hsym _ (mem_fixV_zpowers_iff.mp p.2.2)]⟩
  have hherm : ∀ X Y : HMod n K, (conjM n (mat X - mat Y))ᵀ = mat X - mat Y := by
    intro X Y
    have e : conjM n (mat X - mat Y) = conjM n (mat X) - conjM n (mat Y) := by
      ext i j
      simp [conjM]
    rw [e, transpose_sub, herm_mat, herm_mat]
  have hF : Function.Injective F := by
    rintro ⟨X, Y⟩ ⟨X', Y'⟩ h
    have h1 : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (mat (X : HMod n K) + z • mat (Y : HMod n K)) =
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (mat (X' : HMod n K) + z • mat (Y' : HMod n K)) := congrArg Subtype.val h
    have h2 : mat (X : HMod n K) + z • mat (Y : HMod n K) =
        mat (X' : HMod n K) + z • mat (Y' : HMod n K) := by
      have := congrArg (fun M => (A : Matrix (Fin 3) (Fin 3) K) * M) h1
      simp only [← Matrix.mul_assoc] at this
      rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.one_mul] at this
    have h3 : mat (X : HMod n K) - mat (X' : HMod n K) =
        z • (mat (Y' : HMod n K) - mat (Y : HMod n K)) := by
      rw [smul_sub]
      linear_combination (norm := abel_nf) h2
    have hY : mat (Y' : HMod n K) - mat (Y : HMod n K) = 0 := by
      set H := mat (Y' : HMod n K) - mat (Y : HMod n K) with hHdef
      have hH := hherm Y' Y
      have hzH := hherm X X'
      rw [h3] at hzH
      have e : conjM n (z • H) = bar n z • conjM n H := by
        ext i j
        simp [conjM]
      rw [e, Matrix.transpose_smul, hH] at hzH
      have : (bar n z - z) • H = 0 := by rw [sub_smul, hzH, sub_self]
      exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hz)
    have hYY : (Y : HMod n K) = Y' := mat_injective (sub_eq_zero.mp hY).symm
    have hXX : (X : HMod n K) = X' := mat_injective (by
      rw [hY, smul_zero] at h3
      exact sub_eq_zero.mp h3)
    exact Prod.ext (Subtype.ext hXX) (Subtype.ext hYY)
  have hle := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, card_sym, hK] at hle
  have h12 : ((2 ^ n) ^ 2) ^ 6 = 2 ^ (6 * n) * 2 ^ (6 * n) := by ring
  rw [h12] at hle
  exact Nat.mul_self_le_mul_self_iff.mp hle

theorem card_fixV_le_of_involution (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {t : MulAut (HMod n K)} (ht : t ∈ norm hK) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ 2 ^ (6 * n) := by
  obtain ⟨A, rfl | rfl⟩ := exists_of_involution hn hK ht ht2
  · exact card_fixV_le_of_rhoT hn hK ht2 ht1
  · exact card_fixV_le_of_twisted hn hK ht2

theorem le_mParam (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (HMod n K))} (hXN : X ≤ norm hK) : 3 * n ≤ E3.mParam X := by
  classical
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  have hV : Nat.card (HMod n K) = 2 ^ (9 * n) := card_HMod hn hK
  unfold E3.mParam
  split_ifs with hev
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.mp hev)
    refine le_csInf ⟨_, (t : MulAut (HMod n K)), t.2,
      (Subgroup.orderOf_coe t).trans ht, rfl⟩ ?_
    rintro k ⟨s, hsX, hs2, rfl⟩
    have hss : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hs2, sq] at h
      exact h
    have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs2; omega
    have hq := card_fixV_le_of_involution hn hK (hXN hsX) hss hs1
    refine SL3Pair.le_rkIdx_of_card_mul_le hV _ ?_
    calc Nat.card ↥(fixV (Subgroup.zpowers s)) * 2 ^ (3 * n) ≤
          2 ^ (6 * n) * 2 ^ (3 * n) := Nat.mul_le_mul_right _ hq
      _ = 2 ^ (9 * n) := by
          rw [← pow_add]
          congr 1
          ring
  · rw [rk, hV]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [padicValNat.prime_pow]
    omega

end L3Nine

theorem H42_L3Nine_mParam {V : Type*} [CommGroup V] [Finite V] {L M : Subgroup (MulAut V)}
    {n : ℕ} (hn : 1 ≤ n) (hL : BinaryNineTensor L ⊤ ⊥ n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) : 3 * n ≤ E3.mParam M := by
  obtain ⟨K, _, _, _, hK, hreal⟩ := hL
  have hK' : Nat.card K = (2 ^ n) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨e, -, h2⟩ := L3Nine.exists_transport hK' hreal hLM hMN
  rw [← mParam_map_congrHom e]
  exact L3Nine.le_mParam hn hK' h2

end H

end CFSG.Quasithin
