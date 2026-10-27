module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3CoreA
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists

section CoreB

variable {F : Type} [Field F] [Finite F] {S : Subgroup (GL (Fin 3) F)}
  {Bl : Subgroup (GL (Fin 2) F)} {p : ℕ} {G : Type*} [Group G] {ψ : ↥S →* G}

private theorem blk_entry22_L3coreB (X : GL (Fin 2) F) :
    ((blk X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 =
      ((X : Matrix (Fin 2) (Fin 2) F).det)⁻¹ := by
  rw [coe_blk]
  simp [blkMat]

private theorem eq_one_of_conj_scalar_L3coreB {X : GL (Fin 2) F}
    (hX : Matrix.GeneralLinearGroup.det X = 1) (q : GL (Fin 3) F) {c : Fˣ}
    (h : q * blk X * q⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) c) : X = 1 := by
  have hbX : blk X = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    have e : blk X = q⁻¹ * (q * blk X * q⁻¹) * q := by group
    rw [e, h, mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc,
      inv_mul_cancel, one_mul]
  have hXm : (X : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hX, Units.val_one]
  have h22 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 2 2) hbX
  simp only [blk_entry22_L3coreB, hXm, inv_one, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h22
  have hc : c = 1 := Units.ext (by simpa using h22.symm)
  apply blk_injective
  rw [hbX, hc, map_one, map_one]

private theorem five_ne_zero_L3coreB (hS : L3Shape F S Bl p) (hp : 5 < p) : (5 : F) ≠ 0 := by
  haveI : CharP F p := hS.charP
  intro h
  have h' : ((5 : ℕ) : F) = 0 := by exact_mod_cast h
  have hd : p ∣ 5 := (CharP.cast_eq_zero_iff F p 5).mp h'
  have hle := Nat.le_of_dvd (by norm_num) hd
  omega

private theorem two_ne_zero_L3coreB (hS : L3Shape F S Bl p) (hp : 5 < p) : (2 : F) ≠ 0 := by
  haveI : CharP F p := hS.charP
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h'
  have hle := Nat.le_of_dvd (by norm_num) hd
  omega

private theorem ker_central_L3coreB (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) :
    ψ.ker ≤ Subgroup.center S :=
  fun z hz => CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center S (hker hz)

private theorem ker_cube_L3coreB (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) : ∀ z ∈ ψ.ker, z ^ 3 = 1 := by
  intro z hz
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp (hker hz))
  have hdet : Matrix.GeneralLinearGroup.det (z : GL (Fin 3) F) = 1 := by
    apply Units.ext
    rw [Units.val_one, Matrix.GeneralLinearGroup.val_det_apply]
    exact hS.det_one _ z.2
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  apply Subtype.ext
  show (z : GL (Fin 3) F) ^ 3 = 1
  rw [← hc, ← map_pow, hdet, map_one]

private theorem det_sl2_L3coreB {b : GL (Fin 2) F} (hb : b ∈ sl2Of Bl) :
    Matrix.GeneralLinearGroup.det b = 1 :=
  MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hb).2

private theorem sq_one_of_orderOf_two_L3coreB {H : Type*} [Group H] {x : H}
    (hx : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← hx, pow_orderOf_eq_one]

private theorem coe_ne_one_of_orderOf_L3coreB {x : ↥S} (hx : orderOf (ψ x) = 2) :
    (x : GL (Fin 3) F) ≠ 1 := by
  intro h
  have h1 : x = 1 := Subtype.ext h
  rw [h1, map_one, orderOf_one] at hx
  norm_num at hx

private theorem coe_sq_one_L3coreB {x : ↥S} (hx : x * x = 1) :
    (x : GL (Fin 3) F) * x = 1 := by
  have := congrArg Subtype.val hx
  simpa using this

private theorem poly5_L3coreB {M : Matrix (Fin 2) (Fin 2) F} (h5 : (5 : F) ≠ 0)
    (hdet : M.det = 1) (hM5 : M ^ 5 = 1) (hM1 : M ≠ 1) :
    ∑ k ∈ Finset.range 5, M ^ k = 0 := by
  have hCH : M * M = (M 0 0 + M 1 1) • M - M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.one_apply] <;> ring
  have hgeom : (M - 1) * ∑ k ∈ Finset.range 5, M ^ k = 0 := by
    rw [mul_geom_sum, hM5, sub_self]
  by_cases hd : (M - 1).det = 0
  · exfalso
    have htr : M 0 0 + M 1 1 = 2 := by
      have e : (M - 1).det = (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 := by
        simp [Matrix.det_fin_two] <;> ring
      have hd' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := (Matrix.det_fin_two M).symm.trans hdet
      rw [e] at hd
      linear_combination (-1 : F) * hd + hd'
    have hMM : M * M = (2 : F) • M - (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hCH, htr, hdet, one_smul]
    have hNN : (M - 1) * (M - 1) = 0 := by
      calc (M - 1) * (M - 1) = M * M - M - M + 1 := by noncomm_ring
        _ = (2 : F) • M - 1 - M - M + 1 := by rw [hMM]
        _ = 0 := by module
    have h1 : (M - 1) * M = M - 1 := by
      have h := hNN
      rw [mul_sub, mul_one] at h
      exact sub_eq_zero.mp h
    have hpow : ∀ k : ℕ, M ^ k = 1 + (k : F) • (M - 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ih, add_mul, one_mul, smul_mul_assoc, h1]
        push_cast
        module
    have hX : ((5 : ℕ) : F) • (M - 1) = 0 := by
      have h := hpow 5
      rw [hM5] at h
      exact add_left_cancel (h.symm.trans (add_zero (1 : Matrix (Fin 2) (Fin 2) F)).symm)
    simp only [Nat.cast_ofNat] at hX
    have hM1' : M - 1 = 0 := by
      have h := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => (5 : F)⁻¹ • X) hX
      simpa [smul_smul, inv_mul_cancel₀ h5] using h
    exact hM1 (sub_eq_zero.mp hM1')
  · have hunit : IsUnit (M - 1) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
    exact (IsUnit.mul_right_eq_zero hunit).mp hgeom

private theorem pow_blk_L3coreB (X : GL (Fin 2) F)
    (hdet : (X : Matrix (Fin 2) (Fin 2) F).det = 1) (k : ℕ) :
    ((blk X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k =
      blkMat ((X : Matrix (Fin 2) (Fin 2) F) ^ k) 1 := by
  have hb : ((blk X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blkMat (X : Matrix (Fin 2) (Fin 2) F) 1 := by
    rw [coe_blk, hdet, inv_one]
  induction k with
  | zero => rw [pow_zero, pow_zero, blkMat_one]
  | succ k ih =>
    rw [pow_succ ((blk X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) k,
      pow_succ (X : Matrix (Fin 2) (Fin 2) F) k, ih, hb, blkMat_mul, mul_one]

private theorem sum_pow_blk_L3coreB (X : GL (Fin 2) F)
    (hdet : (X : Matrix (Fin 2) (Fin 2) F).det = 1) :
    ∑ k ∈ Finset.range 5, ((blk X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k =
      blkMat (∑ k ∈ Finset.range 5, (X : Matrix (Fin 2) (Fin 2) F) ^ k) 5 := by
  simp only [pow_blk_L3coreB X hdet]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat, Matrix.sum_apply]

private theorem key_L3coreB {g yl wt : ↥S} {X : GL (Fin 2) F} (h5 : (5 : F) ≠ 0)
    (hX : X ∈ sl2Of Bl) (hX5 : X ^ 5 = 1) (hX1 : X ≠ 1)
    (hw : (wt : GL (Fin 3) F) = (g : GL (Fin 3) F) * negDiag3 F * (g : GL (Fin 3) F)⁻¹)
    (hy : (yl : GL (Fin 3) F) = (g : GL (Fin 3) F) * blk X * (g : GL (Fin 3) F)⁻¹) :
    (5 : F) • ((wt : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (2 : F) • (∑ k ∈ Finset.range 5, ((yl : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k) -
        (5 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have hdet : (X : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_sl2_L3coreB hX, Units.val_one]
  have hM5 : (X : Matrix (Fin 2) (Fin 2) F) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hX5, Units.val_one]
  have hM1 : (X : Matrix (Fin 2) (Fin 2) F) ≠ 1 := fun h => hX1 (Units.ext h)
  have hsum0 : ∑ k ∈ Finset.range 5, (X : Matrix (Fin 2) (Fin 2) F) ^ k = 0 :=
    poly5_L3coreB h5 hdet hM5 hM1
  have hpow : ∀ k : ℕ, ((yl : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((blk X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k *
        (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro k
    have hyk : (yl : GL (Fin 3) F) ^ k =
        (g : GL (Fin 3) F) * (blk X : GL (Fin 3) F) ^ k * (g : GL (Fin 3) F)⁻¹ := by
      rw [hy, conj_pow]
    have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) hyk
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have hsumY : ∑ k ∈ Finset.range 5, ((yl : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (∑ k ∈ Finset.range 5, ((blk X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k) *
        (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    simp only [hpow, Finset.mul_sum, Finset.sum_mul]
  have hGG : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hN : (5 : F) • ((negDiag3 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (2 : F) • blkMat (0 : Matrix (Fin 2) (Fin 2) F) 5 -
        (5 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [coe_negDiag3]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blkMat, Matrix.diagonal_apply, Matrix.one_apply] <;> norm_num
  rw [hw, Units.val_mul, Units.val_mul, hsumY, sum_pow_blk_L3coreB X hdet, hsum0]
  calc (5 : F) • (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((negDiag3 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
      = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((5 : F) • ((negDiag3 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
          (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((2 : F) • blkMat (0 : Matrix (Fin 2) (Fin 2) F) 5 -
            (5 : F) • (1 : Matrix (Fin 3) (Fin 3) F)) *
          (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        rw [hN]
    _ = (2 : F) • (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          blkMat (0 : Matrix (Fin 2) (Fin 2) F) 5 *
          (((g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) -
          (5 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one]
        rw [hGG]

private theorem levi_data_L3coreB (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) {g a : ↥S} {X : GL (Fin 2) F}
    (hX : X ∈ sl2Of Bl)
    (ha : (a : GL (Fin 3) F) = (g : GL (Fin 3) F) * blk X * (g : GL (Fin 3) F)⁻¹)
    (ha5 : ψ (a ^ 5) = 1) (ha1 : ψ a ≠ 1) : X ^ 5 = 1 ∧ X ≠ 1 ∧ a ^ 5 = 1 := by
  have hk : a ^ 5 ∈ ψ.ker := ha5
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp (hker hk))
  have e5 : ((a ^ 5 : ↥S) : GL (Fin 3) F) =
      (g : GL (Fin 3) F) * blk (X ^ 5) * (g : GL (Fin 3) F)⁻¹ := by
    rw [show ((a ^ 5 : ↥S) : GL (Fin 3) F) = (a : GL (Fin 3) F) ^ 5 from rfl, ha, conj_pow,
      map_pow]
  have hG : (g : GL (Fin 3) F) * blk (X ^ 5) * (g : GL (Fin 3) F)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := e5.symm.trans hc.symm
  have hdet5 : Matrix.GeneralLinearGroup.det (X ^ 5) = 1 := by
    rw [map_pow, det_sl2_L3coreB hX, one_pow]
  have hX5 : X ^ 5 = 1 := eq_one_of_conj_scalar_L3coreB hdet5 _ hG
  refine ⟨hX5, ?_, ?_⟩
  · intro h1
    apply ha1
    have ha1' : a = 1 := Subtype.ext (by rw [ha, h1]; simp)
    rw [ha1', map_one]
  · apply Subtype.ext
    rw [e5, hX5]
    simp

private theorem involution_form_L3coreB (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) {u : G} (hu : u ∈ ψ.range)
    (hu2 : orderOf u = 2) : ∃ g : ↥S, ψ (g * ⟨negDiag3 F, hS.neg_mem⟩ * g⁻¹) = u := by
  obtain ⟨a, ha, rfl⟩ := lift_involution_L3 (ker_cube_L3coreB hS hker) hu
    (sq_one_of_orderOf_two_L3coreB hu2)
  obtain ⟨q, hq, hqa⟩ := hS.conj (a : GL (Fin 3) F) a.2 (coe_sq_one_L3coreB ha)
    (coe_ne_one_of_orderOf_L3coreB hu2)
  refine ⟨⟨q, hq⟩, congrArg ψ (Subtype.ext ?_)⟩
  show q * negDiag3 F * q⁻¹ = (a : GL (Fin 3) F)
  rw [← hqa]
  group

private theorem lift_formula_L3coreB (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) (h5 : (5 : F) ≠ 0)
    {y : G} (hy5 : orderOf y = 5) {yl : ↥S} (hyl5 : yl ^ 5 = 1) (hyly : ψ yl = y)
    {u : G} (hu : u ∈ ψ.range) (hu2 : orderOf u = 2) (hyu : y ∈ leviOfL3 ψ.range u) :
    ∃ w : ↥S, ψ w = u ∧ (5 : F) • ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (2 : F) • (∑ k ∈ Finset.range 5, ((yl : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ k) -
        (5 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy5
    norm_num at hy5
  obtain ⟨g, hg⟩ := involution_form_L3coreB hS hker hu hu2
  rw [← hg] at hyu
  obtain ⟨X, hX, a, ha, hay⟩ := hS.exists_of_mem_levi hker hyu
  have ha5 : ψ (a ^ 5) = 1 := by rw [map_pow, hay, hy5']
  have ha1 : ψ a ≠ 1 := by rw [hay]; exact hy1
  obtain ⟨hX5, hX1, ha5'⟩ := levi_data_L3coreB hS hker hX ha ha5 ha1
  have hayl : a = yl := lift_five_unique_L3 (ker_central_L3coreB hker) (ker_cube_L3coreB hS hker)
    (hay.trans hyly.symm) ha5' hyl5
  rw [hayl] at ha
  have hw : ((g * ⟨negDiag3 F, hS.neg_mem⟩ * g⁻¹ : ↥S) : GL (Fin 3) F) =
      (g : GL (Fin 3) F) * negDiag3 F * (g : GL (Fin 3) F)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨_, hg, ?_⟩
  exact key_L3coreB h5 hX hX5 hX1 hw ha

theorem L3Shape.uniq (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) (hp : 5 < p) :
    ∀ y ∈ ψ.range, orderOf y = 5 → ∀ u ∈ ψ.range, ∀ v ∈ ψ.range, orderOf u = 2 →
      orderOf v = 2 → Commute u y → Commute v y → y ∈ leviOfL3 ψ.range u →
        y ∈ leviOfL3 ψ.range v → u = v := by
  intro y hy hy5 u hu v hv hu2 hv2 _ _ hyu hyv
  have h5 : (5 : F) ≠ 0 := five_ne_zero_L3coreB hS hp
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  obtain ⟨yl, hyl5, hyly⟩ := lift_five_L3 (ker_cube_L3coreB hS hker) hy hy5'
  obtain ⟨wu, hwu, hwuM⟩ := lift_formula_L3coreB hS hker h5 hy5 hyl5 hyly hu hu2 hyu
  obtain ⟨wv, hwv, hwvM⟩ := lift_formula_L3coreB hS hker h5 hy5 hyl5 hyly hv hv2 hyv
  have hM : ((wu : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((wv : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have h := congrArg (fun X : Matrix (Fin 3) (Fin 3) F => (5 : F)⁻¹ • X)
      (hwuM.trans hwvM.symm)
    simpa [smul_smul, inv_mul_cancel₀ h5] using h
  have hw : wu = wv := Subtype.ext (Units.ext hM)
  rw [← hwu, ← hwv, hw]

theorem L3Shape.invert (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S) (hp : 5 < p) :
    ∀ y ∈ ψ.range, ∀ z ∈ ψ.range, orderOf y = 5 → orderOf z = 2 → y ∈ leviOfL3 ψ.range z →
      ∃ t ∈ ψ.range, orderOf t = 2 ∧ t * y * t⁻¹ = y⁻¹ := by
  intro y hy z hz hy5 hz2 hyz
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy5
    norm_num at hy5
  obtain ⟨g, hg⟩ := involution_form_L3coreB hS hker hz hz2
  rw [← hg] at hyz
  obtain ⟨X, hX, a, ha, hay⟩ := hS.exists_of_mem_levi hker hyz
  have ha5 : ψ (a ^ 5) = 1 := by rw [map_pow, hay, hy5']
  have ha1 : ψ a ≠ 1 := by rw [hay]; exact hy1
  obtain ⟨hX5, hX1, -⟩ := levi_data_L3coreB hS hker hX ha ha5 ha1
  obtain ⟨R, hR, hRR, hdetR, hRXR⟩ := hS.exists_inverter hp X hX hX5 hX1
  have hRdet : (R : Matrix (Fin 2) (Fin 2) F).det = -1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdetR, Units.val_neg, Units.val_one]
  obtain ⟨r, hr⟩ : ∃ r : ↥S, (r : GL (Fin 3) F) =
      (g : GL (Fin 3) F) * blk R * (g : GL (Fin 3) F)⁻¹ :=
    ⟨g * ⟨blk R, hS.blk_mem R hR⟩ * g⁻¹, by simp only [Subgroup.coe_mul, Subgroup.coe_inv]⟩
  have hBB : blk R * blk R = 1 := by rw [← map_mul, hRR, map_one]
  have hrr : r * r = 1 := by
    refine Subtype.ext ?_
    show (r : GL (Fin 3) F) * (r : GL (Fin 3) F) = 1
    rw [hr]
    calc (g : GL (Fin 3) F) * blk R * (g : GL (Fin 3) F)⁻¹ *
          ((g : GL (Fin 3) F) * blk R * (g : GL (Fin 3) F)⁻¹)
        = (g : GL (Fin 3) F) * (blk R * blk R) * (g : GL (Fin 3) F)⁻¹ := by group
      _ = 1 := by rw [hBB]; group
  have hψr1 : ψ r ≠ 1 := by
    intro h1
    have hk : r ∈ ψ.ker := h1
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp (hker hk))
    have hcr : Matrix.GeneralLinearGroup.scalar (Fin 3) c =
        (g : GL (Fin 3) F) * blk R * (g : GL (Fin 3) F)⁻¹ := hc.trans hr
    have hblk : blk R = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
      have e : blk R = (g : GL (Fin 3) F)⁻¹ *
          ((g : GL (Fin 3) F) * blk R * (g : GL (Fin 3) F)⁻¹) * (g : GL (Fin 3) F) := by
        group
      rw [e, ← hcr, mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc,
        inv_mul_cancel, one_mul]
    have h22 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) 2 2) hblk
    simp only [blk_entry22_L3coreB, hRdet, inv_neg, inv_one, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h22
    have hdetb : Matrix.GeneralLinearGroup.det (blk R) = 1 :=
      Units.ext (by rw [Units.val_one, Matrix.GeneralLinearGroup.val_det_apply]; exact det_blk R)
    rw [hblk, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdetb
    have h3 : (c : F) ^ 3 = 1 := by
      have := congrArg Units.val hdetb
      simpa using this
    rw [← h22] at h3
    have h2 : (2 : F) = 0 := by linear_combination -h3
    exact two_ne_zero_L3coreB hS hp h2
  have hsq : ψ r ^ 2 = 1 := by rw [← map_pow, sq, hrr, map_one]
  have hord : orderOf (ψ r) = 2 := orderOf_eq_prime hsq hψr1
  have hrar : r * a * r⁻¹ = a⁻¹ := by
    refine Subtype.ext ?_
    show (r : GL (Fin 3) F) * (a : GL (Fin 3) F) * (r : GL (Fin 3) F)⁻¹ = (a : GL (Fin 3) F)⁻¹
    rw [hr, ha]
    have hc : blk R * blk X * (blk R)⁻¹ = (blk X)⁻¹ := by
      rw [← map_inv blk R, ← map_mul, ← map_mul, hRXR, map_inv]
    calc (g : GL (Fin 3) F) * blk R * (g : GL (Fin 3) F)⁻¹ *
          ((g : GL (Fin 3) F) * blk X * (g : GL (Fin 3) F)⁻¹) *
          ((g : GL (Fin 3) F) * blk R * (g : GL (Fin 3) F)⁻¹)⁻¹
        = (g : GL (Fin 3) F) * (blk R * blk X * (blk R)⁻¹) * (g : GL (Fin 3) F)⁻¹ := by
          group
      _ = (g : GL (Fin 3) F) * (blk X)⁻¹ * (g : GL (Fin 3) F)⁻¹ := by rw [hc]
      _ = ((g : GL (Fin 3) F) * blk X * (g : GL (Fin 3) F)⁻¹)⁻¹ := by group
  refine ⟨ψ r, MonoidHom.mem_range.mpr ⟨r, rfl⟩, hord, ?_⟩
  rw [← hay, ← map_inv ψ r, ← map_mul, ← map_mul, hrar, map_inv]

theorem L3Shape.factB (hS : L3Shape F S Bl p)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf S)
    (hfb : ∀ v : G, v * v = 1 →
      (∀ A : ↥S, (A : GL (Fin 3) F) ∈ sl2BlockL3 Bl → v * ψ A = ψ A * v) →
        v = 1 ∨ ∃ A : ↥S, (A : GL (Fin 3) F) = negDiag3 F ∧ v = ψ A) :
    ∀ u ∈ ψ.range, orderOf u = 2 → ∀ v : G, v * v = 1 →
      v ∈ Subgroup.centralizer (leviOfL3 ψ.range u : Set G) → v = 1 ∨ v = u := by
  intro u hu hu2 v hv hvC
  obtain ⟨g, hg⟩ := involution_form_L3coreB hS hker hu hu2
  obtain ⟨v', hv'⟩ : ∃ v' : G, v' = (ψ g)⁻¹ * v * ψ g := ⟨_, rfl⟩
  have hv'v' : v' * v' = 1 := by
    rw [hv']
    calc (ψ g)⁻¹ * v * ψ g * ((ψ g)⁻¹ * v * ψ g) = (ψ g)⁻¹ * (v * v) * ψ g := by group
      _ = 1 := by rw [hv, mul_one, inv_mul_cancel]
  have hcomm : ∀ A : ↥S, (A : GL (Fin 3) F) ∈ sl2BlockL3 Bl → v' * ψ A = ψ A * v' := by
    intro A hA
    obtain ⟨b, hb, hbA⟩ :=
      Subgroup.mem_map.mp (show (A : GL (Fin 3) F) ∈ (sl2Of Bl).map blk from hA)
    have ha : ((g * A * g⁻¹ : ↥S) : GL (Fin 3) F) =
        (g : GL (Fin 3) F) * blk b * (g : GL (Fin 3) F)⁻¹ := by
      show (g : GL (Fin 3) F) * (A : GL (Fin 3) F) * (g : GL (Fin 3) F)⁻¹ = _
      rw [← hbA]
    have hmem := hS.mem_levi_of_exists hker hb ha
    rw [hg] at hmem
    have hc := Subgroup.mem_centralizer_iff.mp hvC _ hmem
    rw [map_mul, map_mul, map_inv] at hc
    rw [hv']
    calc (ψ g)⁻¹ * v * ψ g * ψ A = (ψ g)⁻¹ * (v * (ψ g * ψ A * (ψ g)⁻¹)) * ψ g := by group
      _ = (ψ g)⁻¹ * (ψ g * ψ A * (ψ g)⁻¹ * v) * ψ g := by rw [hc]
      _ = ψ A * ((ψ g)⁻¹ * v * ψ g) := by group
  rcases hfb v' hv'v' hcomm with h1 | ⟨A₀, hA₀, hv'A₀⟩
  · left
    calc v = ψ g * v' * (ψ g)⁻¹ := by rw [hv']; group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  · right
    have hA₀e : A₀ = ⟨negDiag3 F, hS.neg_mem⟩ := Subtype.ext hA₀
    calc v = ψ g * v' * (ψ g)⁻¹ := by rw [hv']; group
      _ = ψ g * ψ A₀ * (ψ g)⁻¹ := by rw [hv'A₀]
      _ = ψ (g * A₀ * g⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = ψ (g * ⟨negDiag3 F, hS.neg_mem⟩ * g⁻¹) := by rw [hA₀e]
      _ = u := hg

end CoreB

end CFSG.Quasithin.H13
