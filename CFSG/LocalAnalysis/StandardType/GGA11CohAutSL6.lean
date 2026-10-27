module

public import CFSG.LocalAnalysis.StandardType.GGA11CohDefs
public import CFSG.Quasithin.EmptyFaithful.R3c14Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.R3c12Syl
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S146yBorel
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.Quasithin.EmptyFaithful.S153D43
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

private abbrev F2Z : Type := ZMod 2

private def OmZ : Matrix (Fin 3) (Fin 3) F2Z := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

private def T6matZ (b : Fin 2) : Matrix (Fin 6) (Fin 6) F2Z :=
  Matrix.of fun a c =>
    if a.val / 3 = b.val ∧ c.val / 3 = b.val
    then OmZ ⟨a.val % 3, Nat.mod_lt _ (by norm_num)⟩ ⟨c.val % 3, Nat.mod_lt _ (by norm_num)⟩
    else if a = c then 1 else 0

private theorem T6matZ_det (b : Fin 2) : (T6matZ b).det = 1 := by
  fin_cases b <;> decide +kernel

private def T6Z (b : Fin 2) : Matrix.SpecialLinearGroup (Fin 6) F2Z :=
  ⟨T6matZ b, T6matZ_det b⟩

private def e6 : Fin 3 ⊕ Fin 3 ≃ Fin 6 where
  toFun := Sum.elim (Fin.castLE (by omega : 3 ≤ 6)) (Fin.natAdd 3)
  invFun := fun i => if h : i.val < 3 then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - 3, by omega⟩
  left_inv := by rintro (i | i) <;> simp [Fin.ext_iff] <;> omega
  right_inv := by
    intro i
    by_cases h : i.val < 3
    · simp [h, Fin.ext_iff]
    · simp [h, Fin.ext_iff]; omega

private theorem T6matZ0_block :
    (T6matZ 0).submatrix e6 e6 = fromBlocks OmZ 0 0 (1 : Matrix (Fin 3) (Fin 3) F2Z) := by
  decide +kernel

private theorem T6matZ1_block :
    (T6matZ 1).submatrix e6 e6 = fromBlocks (1 : Matrix (Fin 3) (Fin 3) F2Z) 0 0 OmZ := by
  decide +kernel

private theorem cancel_left_OmZ {B : Matrix (Fin 3) (Fin 3) F2Z} (h : (OmZ - 1) * B = 0) : B = 0 := by
  have h' := congrArg (fun X => (OmZ ^ 4) * X) h
  rw [mul_zero] at h'
  rwa [← mul_assoc, show OmZ ^ 4 * (OmZ - 1) = 1 by decide +kernel, one_mul] at h'

private theorem T6matZ_centralizer_blocks (A : Matrix (Fin 6) (Fin 6) F2Z)
    (h0 : A * T6matZ 0 = T6matZ 0 * A) (h1 : A * T6matZ 1 = T6matZ 1 * A) :
    (A.submatrix e6 e6).toBlocks₁₂ = 0 ∧ (A.submatrix e6 e6).toBlocks₂₁ = 0 ∧
    (A.submatrix e6 e6).toBlocks₁₁ * OmZ = OmZ * (A.submatrix e6 e6).toBlocks₁₁ ∧
    (A.submatrix e6 e6).toBlocks₂₂ * OmZ = OmZ * (A.submatrix e6 e6).toBlocks₂₂ := by
  have h0' : (A.submatrix e6 e6) * ((T6matZ 0).submatrix e6 e6) =
      ((T6matZ 0).submatrix e6 e6) * (A.submatrix e6 e6) := by
    rw [submatrix_mul_equiv, submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix e6 e6) h0
  rw [T6matZ0_block, ← fromBlocks_toBlocks (A.submatrix e6 e6)] at h0'
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h0'
  obtain ⟨h11, h12, h21, h22⟩ := h0'
  have h12z : (A.submatrix e6 e6).toBlocks₁₂ = 0 := by
    have h12' : (A.submatrix e6 e6).toBlocks₁₂ = OmZ * (A.submatrix e6 e6).toBlocks₁₂ := by
      simpa using h12
    have hB : (OmZ - 1) * (A.submatrix e6 e6).toBlocks₁₂ = 0 := by
      rw [sub_mul, one_mul, sub_eq_zero]; exact h12'.symm
    exact cancel_left_OmZ hB
  have h21z : (A.submatrix e6 e6).toBlocks₂₁ = 0 := by
    have h21' : (A.submatrix e6 e6).toBlocks₂₁ * OmZ = (A.submatrix e6 e6).toBlocks₂₁ := by
      simpa using h21
    have hB : (A.submatrix e6 e6).toBlocks₂₁ * (OmZ - 1) = 0 := by
      rw [mul_sub, mul_one, sub_eq_zero]; exact h21'
    have h' := congrArg (fun X => X * (OmZ ^ 4)) hB
    rw [zero_mul] at h'
    rwa [mul_assoc, show (OmZ - 1) * OmZ ^ 4 = 1 by decide +kernel, mul_one] at h'
  have h11c : (A.submatrix e6 e6).toBlocks₁₁ * OmZ = OmZ * (A.submatrix e6 e6).toBlocks₁₁ := by
    simpa using h11
  refine ⟨h12z, h21z, h11c, ?_⟩
  have h1' : (A.submatrix e6 e6) * ((T6matZ 1).submatrix e6 e6) =
      ((T6matZ 1).submatrix e6 e6) * (A.submatrix e6 e6) := by
    rw [submatrix_mul_equiv, submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix e6 e6) h1
  rw [T6matZ1_block, ← fromBlocks_toBlocks (A.submatrix e6 e6)] at h1'
  rw [h12z, h21z] at h1'
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h1'
  obtain ⟨k11, k12, k21, k22⟩ := h1'
  simpa using k22

private theorem centralizer3_OmZ (P : Matrix (Fin 3) (Fin 3) F2Z) (hc : P * OmZ = OmZ * P)
    (hu : IsUnit P) : ∃ k : ℕ, P = OmZ ^ k := by
  have h : ∀ Q : Matrix (Fin 3) (Fin 3) F2Z, Q * OmZ = OmZ * Q →
      Q = 0 ∨ ∃ k : Fin 7, Q = OmZ ^ (k : ℕ) := by decide +kernel
  rcases h P hc with h0 | ⟨k, hk⟩
  · exact absurd h0 hu.ne_zero
  · exact ⟨k, hk⟩

private theorem submatrix_pow_T6matZ0 (a : ℕ) :
    (T6matZ 0 ^ a).submatrix e6 e6 = ((T6matZ 0).submatrix e6 e6) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_succ, submatrix_mul (T6matZ 0 ^ a) (T6matZ 0) e6 e6 e6 e6.bijective, ih]

private theorem submatrix_pow_T6matZ1 (b : ℕ) :
    (T6matZ 1 ^ b).submatrix e6 e6 = ((T6matZ 1).submatrix e6 e6) ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, pow_succ, submatrix_mul (T6matZ 1 ^ b) (T6matZ 1) e6 e6 e6 e6.bijective, ih]

private theorem fromBlocks_OmZ_pow (a b : ℕ) :
    (fromBlocks (OmZ ^ a) 0 0 (1 : Matrix (Fin 3) (Fin 3) F2Z)) *
      (fromBlocks (1 : Matrix (Fin 3) (Fin 3) F2Z) 0 0 (OmZ ^ b)) =
      fromBlocks (OmZ ^ a) 0 0 (OmZ ^ b) := by
  rw [fromBlocks_multiply]
  simp

private theorem inner6_zmod (A : Matrix (Fin 6) (Fin 6) F2Z)
    (h0 : A * T6matZ 0 = T6matZ 0 * A) (h1 : A * T6matZ 1 = T6matZ 1 * A)
    (hA : IsUnit A) :
    ∃ a b : ℕ, A = T6matZ 0 ^ a * T6matZ 1 ^ b := by
  obtain ⟨h12z, h21z, h11c, h22c⟩ := T6matZ_centralizer_blocks A h0 h1
  have hA' : IsUnit (A.submatrix e6 e6) := by
    obtain ⟨B, hB⟩ := isUnit_iff_exists_inv.mp hA
    exact isUnit_iff_exists_inv.mpr ⟨B.submatrix e6 e6, by
      rw [← submatrix_mul A B e6 e6 e6 e6.bijective, hB, submatrix_one_equiv e6]⟩
  have hA'eq : A.submatrix e6 e6 =
      fromBlocks (A.submatrix e6 e6).toBlocks₁₁ 0 0 (A.submatrix e6 e6).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (A.submatrix e6 e6)]
    rw [h12z, h21z]
  have hunit11 : IsUnit (A.submatrix e6 e6).toBlocks₁₁ := by
    rw [hA'eq] at hA'
    rw [Matrix.isUnit_iff_isUnit_det] at hA' ⊢
    rw [Matrix.det_fromBlocks_zero₂₁] at hA'
    exact ((Commute.all _ _).isUnit_mul_iff.mp hA').1
  have hunit22 : IsUnit (A.submatrix e6 e6).toBlocks₂₂ := by
    rw [hA'eq] at hA'
    rw [Matrix.isUnit_iff_isUnit_det] at hA' ⊢
    rw [Matrix.det_fromBlocks_zero₂₁] at hA'
    exact ((Commute.all _ _).isUnit_mul_iff.mp hA').2
  obtain ⟨a, ha⟩ := centralizer3_OmZ _ h11c hunit11
  obtain ⟨b, hb⟩ := centralizer3_OmZ _ h22c hunit22
  refine ⟨a, b, ?_⟩
  have hsubinj : Function.Injective (fun M : Matrix (Fin 6) (Fin 6) F2Z => M.submatrix e6 e6) := by
    intro M N hMN
    simpa using congrArg (fun X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F2Z =>
      X.submatrix e6.symm e6.symm) hMN
  apply hsubinj
  show A.submatrix e6 e6 = (T6matZ 0 ^ a * T6matZ 1 ^ b).submatrix e6 e6
  rw [submatrix_mul (T6matZ 0 ^ a) (T6matZ 1 ^ b) e6 e6 e6 e6.bijective,
    submatrix_pow_T6matZ0, submatrix_pow_T6matZ1, T6matZ0_block, T6matZ1_block,
    fromBlocks_diagonal_pow, fromBlocks_diagonal_pow, one_pow, one_pow, fromBlocks_OmZ_pow,
    hA'eq, ha, hb]

private theorem autSL6_zmod (α : MulAut (Matrix.SpecialLinearGroup (Fin 6) F2Z))
    (hα0 : α (T6Z 0) = T6Z 0) (hα1 : α (T6Z 1) = T6Z 1) :
    ∃ a b : ℕ, ∀ g : Matrix.SpecialLinearGroup (Fin 6) F2Z,
      α g = (T6Z 0 ^ a * T6Z 1 ^ b) * g * (T6Z 0 ^ a * T6Z 1 ^ b)⁻¹ := by
  obtain ⟨h, ε, hε, hα⟩ := CFSG.Quasithin.R3c14.aut_form_sl (n := 6) (by norm_num) α
  interval_cases ε
  · have hα' : α = MulAut.conj h := by simpa using hα
    have hh0 : h * T6Z 0 = T6Z 0 * h := by
      have hh := hα0; rw [hα', MulAut.conj_apply] at hh
      calc h * T6Z 0 = (h * T6Z 0 * h⁻¹) * h := by group
        _ = T6Z 0 * h := by rw [hh]
    have hh1 : h * T6Z 1 = T6Z 1 * h := by
      have hh := hα1; rw [hα', MulAut.conj_apply] at hh
      calc h * T6Z 1 = (h * T6Z 1 * h⁻¹) * h := by group
        _ = T6Z 1 * h := by rw [hh]
    have hunit : IsUnit (h : Matrix (Fin 6) (Fin 6) F2Z) := by
      refine ⟨⟨(h : Matrix (Fin 6) (Fin 6) F2Z),
        ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 6) F2Z) : Matrix (Fin 6) (Fin 6) F2Z),
        ?_, ?_⟩, rfl⟩
      · simp only [Matrix.SpecialLinearGroup.coe_inv]
        rw [Matrix.mul_adjugate, show (h : Matrix (Fin 6) (Fin 6) F2Z).det = 1 from h.2, one_smul]
      · simp only [Matrix.SpecialLinearGroup.coe_inv]
        rw [Matrix.adjugate_mul, show (h : Matrix (Fin 6) (Fin 6) F2Z).det = 1 from h.2, one_smul]
    have hh0m : (h : Matrix (Fin 6) (Fin 6) F2Z) * T6matZ 0 =
        T6matZ 0 * (h : Matrix (Fin 6) (Fin 6) F2Z) := by
      have hh := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 6) F2Z =>
        (x : Matrix (Fin 6) (Fin 6) F2Z)) hh0
      change (h : Matrix (Fin 6) (Fin 6) F2Z) * T6matZ 0 =
        T6matZ 0 * (h : Matrix (Fin 6) (Fin 6) F2Z) at hh
      exact hh
    have hh1m : (h : Matrix (Fin 6) (Fin 6) F2Z) * T6matZ 1 =
        T6matZ 1 * (h : Matrix (Fin 6) (Fin 6) F2Z) := by
      have hh := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 6) F2Z =>
        (x : Matrix (Fin 6) (Fin 6) F2Z)) hh1
      change (h : Matrix (Fin 6) (Fin 6) F2Z) * T6matZ 1 =
        T6matZ 1 * (h : Matrix (Fin 6) (Fin 6) F2Z) at hh
      exact hh
    obtain ⟨a, b, hab⟩ := inner6_zmod (h : Matrix (Fin 6) (Fin 6) F2Z) hh0m hh1m hunit
    refine ⟨a, b, ?_⟩
    have hh : h = T6Z 0 ^ a * T6Z 1 ^ b := by
      apply Subtype.ext
      rw [hab, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
        Matrix.SpecialLinearGroup.coe_pow]
      rfl
    intro g
    rw [hα', MulAut.conj_apply, hh]
  · exfalso
    have hα' : α = MulAut.conj h * CFSG.Quasithin.R3c14.dlt 6 := by simpa using hα
    have h1 : MulAut.conj h (CFSG.Quasithin.R3c14.dlt 6 (T6Z 0)) = T6Z 0 := by
      have hh := hα0; rw [hα', MulAut.mul_apply] at hh; exact hh
    have htrace := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 6) F2Z =>
      ((x : Matrix (Fin 6) (Fin 6) F2Z)).trace) h1
    rw [MulAut.conj_apply] at htrace
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv] at htrace
    rw [Matrix.trace_mul_cycle] at htrace
    rw [Matrix.adjugate_mul,
      show (h : Matrix (Fin 6) (Fin 6) F2Z).det = 1 from h.2, one_smul, Matrix.one_mul] at htrace
    have hdlt : ((CFSG.Quasithin.R3c14.dlt 6 (T6Z 0) : Matrix.SpecialLinearGroup (Fin 6) F2Z) :
        Matrix (Fin 6) (Fin 6) F2Z) = (T6matZ 0).adjugateᵀ := rfl
    rw [hdlt, Matrix.trace_transpose] at htrace
    have hzero : (T6matZ 0).adjugate.trace = 0 := by decide +kernel
    have hone : (T6matZ 0).trace = 1 := by decide +kernel
    rw [hzero] at htrace
    change 0 = (T6matZ 0).trace at htrace
    rw [hone] at htrace
    exact zero_ne_one htrace

private noncomputable def e2 : F2 ≃+* F2Z := (GaloisField.equivZmodP (p := 2)).toRingEquiv

private noncomputable def SL6iso : SL 6 ≃* Matrix.SpecialLinearGroup (Fin 6) F2Z :=
  MulEquiv.ofBijective (Matrix.SpecialLinearGroup.map e2.toRingHom) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 6) F2Z =>
        (z : Matrix (Fin 6) (Fin 6) F2Z)) hxy
      change e2.toRingHom.mapMatrix (x : Matrix (Fin 6) (Fin 6) F2) =
        e2.toRingHom.mapMatrix (y : Matrix (Fin 6) (Fin 6) F2) at h
      exact e2.toRingHom.mapMatrix.injective h
    · intro y
      refine ⟨Matrix.SpecialLinearGroup.map e2.symm.toRingHom y, ?_⟩
      apply Subtype.ext
      change e2.toRingHom.mapMatrix
        (e2.symm.toRingHom.mapMatrix (y : Matrix (Fin 6) (Fin 6) F2Z)) =
        (y : Matrix (Fin 6) (Fin 6) F2Z)
      ext i j
      simp)

private theorem SL6iso_T6 (b : Fin 2) : SL6iso (T6 b) = T6Z b := by
  apply Subtype.ext
  change e2.toRingHom.mapMatrix (T6mat b) = T6matZ b
  ext i j
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [T6mat, T6matZ, Om, OmZ, e2]

theorem a11AutSL6Input_holds :
    ∀ α : MulAut (SL 6), α (T6 0) = T6 0 → α (T6 1) = T6 1 →
      ∃ a b : ℕ, ∀ g : SL 6, α g = (T6 0 ^ a * T6 1 ^ b) * g * (T6 0 ^ a * T6 1 ^ b)⁻¹ := by
  intro α hα0 hα1
  set β : MulAut (Matrix.SpecialLinearGroup (Fin 6) F2Z) := MulAut.congr SL6iso α with hβ
  have hβ0 : β (T6Z 0) = T6Z 0 := by
    rw [hβ]
    change SL6iso (α (SL6iso.symm (T6Z 0))) = T6Z 0
    have hs : SL6iso.symm (T6Z 0) = T6 0 := by
      rw [← SL6iso_T6 0, MulEquiv.symm_apply_apply]
    rw [hs, hα0, SL6iso_T6 0]
  have hβ1 : β (T6Z 1) = T6Z 1 := by
    rw [hβ]
    change SL6iso (α (SL6iso.symm (T6Z 1))) = T6Z 1
    have hs : SL6iso.symm (T6Z 1) = T6 1 := by
      rw [← SL6iso_T6 1, MulEquiv.symm_apply_apply]
    rw [hs, hα1, SL6iso_T6 1]
  obtain ⟨a, b, hab⟩ := autSL6_zmod β hβ0 hβ1
  refine ⟨a, b, ?_⟩
  intro g
  apply SL6iso.injective
  have h1 : SL6iso (α g) = β (SL6iso g) := by
    rw [hβ]
    simp [MulAut.congr_apply, MulEquiv.symm_apply_apply]
  rw [h1, hab (SL6iso g)]
  simp only [map_mul, map_inv, map_pow, SL6iso_T6]

end CFSG.StandardType.A11

end
