module

public import CFSG.RankThree.Classical.UnitaryPairedRoot
public import CFSG.RankThree.Classical.EvenSurvivingScalarRank

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover
open scoped commutatorElement Matrix

section General

variable {Y X : Type*} [Group Y] [Group X]

theorem commutatorElement_pow_right_of_mem_center {z x : Y} (h : ⁅z, x⁆ ∈ Subgroup.center Y)
    (n : ℕ) : ⁅z, x ^ n⁆ = ⁅z, x⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, commutatorElement_mul_right_of_mem_center h, ih, pow_succ]

theorem exists_involution_elemAbelian [Finite Y] (φ : Y →* X) (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center Y) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {U : Subgroup X} {k : ℕ} (hU : IsElemAbelian p U) (hUcard : Nat.card U = p ^ k)
    (hcomm : ∀ x ∈ U.comap φ, ∀ y ∈ U.comap φ, x * y = y * x)
    {s : X} (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) (hsU : ∀ u ∈ U, s * u = u * s) :
    ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ V : Subgroup Y, V ≤ Subgroup.centralizer {z} ∧
      IsElemAbelian p V ∧ Nat.card V = p ^ k := by
  set Y₀ := U.comap φ
  have hc₀ : ∀ a b : Y₀, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  let pw : Y₀ →* Y₀ :=
    { toFun := fun y => y ^ p
      map_one' := one_pow p
      map_mul' := fun a b => (Commute.mul_pow (hc₀ a b) p) }
  let ψ : Y₀ →* U := (φ.comp Y₀.subtype).codRestrict U fun y => y.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨u, hu⟩
    obtain ⟨y, rfl⟩ := hφ u
    exact ⟨⟨y, hu⟩, rfl⟩
  have hrange : pw.range ≤ ψ.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change φ ((y : Y) ^ p) = 1
    rw [map_pow]
    exact hU.2 _ y.2
  have h1 : Nat.card Y₀ = Nat.card pw.range * Nat.card pw.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange pw).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have h2 : Nat.card Y₀ = Nat.card U * Nat.card ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have h3 : Nat.card pw.range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hrange
  have hpos : 0 < Nat.card pw.range := Nat.card_pos
  have hΩ : p ^ k ≤ Nat.card pw.ker := by
    rw [← hUcard]
    by_contra hlt
    push Not at hlt
    have := Nat.mul_lt_mul_of_lt_of_le' hlt h3 hpos
    rw [mul_comm (Nat.card pw.ker), ← h1, ← h2] at this
    exact lt_irrefl _ this
  have hpgrp : IsPGroup p pw.ker := fun y => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (MonoidHom.mem_ker.mp y.2)⟩
  obtain ⟨m, hm⟩ := hpgrp.exists_card_eq
  have hkm : k ≤ m := by
    rw [hm] at hΩ
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hΩ
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime p (n := k)
    (by rw [hm]; exact pow_dvd_pow p hkm)
  set V : Subgroup Y := (W.map pw.ker.subtype).map Y₀.subtype
  have hVmem : ∀ x ∈ V, x ∈ Y₀ ∧ x ^ p = 1 := by
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    refine ⟨(w : Y₀).2, ?_⟩
    have := MonoidHom.mem_ker.mp w.2
    exact congrArg Subtype.val this
  have hVcard : Nat.card V = p ^ k := by
    rw [Subgroup.card_map_of_injective Y₀.subtype_injective,
      Subgroup.card_map_of_injective pw.ker.subtype_injective, hW]
  set Wz := (Subgroup.zpowers s).comap φ
  have hsord : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  let ψz : Wz →* Subgroup.zpowers s := (φ.comp Wz.subtype).codRestrict _ fun y => y.2
  have hψz : Function.Surjective ψz := by
    rintro ⟨u, hu⟩
    obtain ⟨y, rfl⟩ := hφ u
    exact ⟨⟨y, hu⟩, rfl⟩
  have h2dvd : 2 ∣ Nat.card Wz := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψz.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψz hψz).toEquiv,
      Nat.card_zpowers, hsord]
    exact dvd_mul_right 2 _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hz2 : (z : Y) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z : Y) ≠ 1 := by
    intro h0
    have : z = 1 := Subtype.ext h0
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzU : ∀ u ∈ U, φ z * u = u * φ z := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp z.2
    intro u hu
    rw [← hj]
    exact ((Commute.zpow_left (hsU u hu) j)).eq
  refine ⟨z, hz2, hz1, V, fun x hx => ?_,
    ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => (hVmem x hx).2⟩, hVcard⟩
  ·
    obtain ⟨hxY₀, hxp⟩ := hVmem x hx
    have hc : ⁅(z : Y), x⁆ ∈ Subgroup.center Y := hZ (by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hzU _ hxY₀)
    have hsq : ⁅(z : Y), x⁆ ^ 2 = 1 := by
      rw [pow_two, ← commutatorElement_mul_left_of_mem_center hc, ← pow_two, hz2,
        commutatorElement_one_left]
    have hpw : ⁅(z : Y), x⁆ ^ p = 1 := by
      rw [← commutatorElement_pow_right_of_mem_center hc, hxp, commutatorElement_one_right]
    have hone : ⁅(z : Y), x⁆ = 1 := by
      have hg : ⁅(z : Y), x⁆ ^ Nat.gcd 2 p = 1 := pow_gcd_eq_one.mpr ⟨hsq, hpw⟩
      rwa [(Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2), pow_one] at hg
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  · exact hcomm _ (hVmem a a.2).1 _ (hVmem b b.2).1

end General

section Frames

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem exists_norm_eq_neg_one : ∃ α : K, h.norm α = -1 := by
  obtain ⟨α, hα⟩ := h.normHom_surjective (-1 : h.fixedField)
  refine ⟨α, ?_⟩
  have := congrArg Subtype.val hα
  rw [UnitaryFieldData.coe_normHom] at this
  rw [this]
  rfl

theorem hadj_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (c : K) :
    hadj h (c • (1 : Matrix ι ι K)) = h.bar c • (1 : Matrix ι ι K) := by
  ext i j
  simp [hadj, Matrix.one_apply, apply_ite h.bar, eq_comm]

@[expose] noncomputable def hypBlock (r : ℕ) (α : K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  Matrix.fromBlocks 1 ((2 : K)⁻¹ • 1) (α • 1) ((-(α / 2)) • 1)

theorem hadj_hypBlock_mul (h2 : (2 : K) ≠ 0) {α : K} (hα : h.norm α = -1) (r : ℕ) :
    hadj h (hypBlock r α) * hypBlock r α = hypGram2 r K := by
  have hα' : α * h.bar α = -1 := hα
  have hb2 : h.bar (2 : K)⁻¹ = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  have hb3 : h.bar (-(α / 2)) = -(h.bar α / 2) := by rw [map_neg, map_div₀, map_ofNat]
  have h2' : (2 : K) * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2
  rw [hypBlock, hadj_fromBlocks, hadj_one, hadj_smul_one, hadj_smul_one, hadj_smul_one, hb2, hb3,
    Matrix.fromBlocks_multiply, hypGram2]
  congr 1 <;> ext i j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.zero_apply, smul_eq_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] <;>
    split_ifs <;>
    first
      | rfl
      | ring1
      | linear_combination hα'
      | linear_combination -hα'
      | linear_combination (-(2 : K)⁻¹) * hα' + h2'
      | linear_combination (2 : K)⁻¹ * hα' - h2'
      | linear_combination ((2 : K)⁻¹) ^ 2 * hα'

theorem hadj_submatrix {ι ι' : Type*} [Fintype ι] {n : ℕ} (A : Matrix ι ι' K) (e : Fin n ≃ ι) :
    hadj h (A.submatrix e id) = (hadj h A).submatrix id e := by
  ext i j
  rfl

theorem exists_evenFrame (h2 : (2 : K) ≠ 0) {n r : ℕ} (hn : 2 * r ≤ n) :
    ∃ P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin (n - 2 * r)) K,
      (P.map h.bar)ᵀ * P = Matrix.fromBlocks (Matrix.fromBlocks 0 1 1 0) 0 0 1 := by
  obtain ⟨α, hα⟩ := exists_norm_eq_neg_one h
  have e : Fin n ≃ (Fin r ⊕ Fin r) ⊕ Fin (n - 2 * r) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_sum]; omega)
  set P₀ : Matrix ((Fin r ⊕ Fin r) ⊕ Fin (n - 2 * r)) ((Fin r ⊕ Fin r) ⊕ Fin (n - 2 * r)) K :=
    Matrix.fromBlocks (hypBlock r α) 0 0 1
  refine ⟨P₀.submatrix e id, ?_⟩
  change hadj h (P₀.submatrix e id) * P₀.submatrix e id = _
  rw [hadj_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, hadj_fromBlocks,
    hadj_zero, hadj_zero, hadj_one, Matrix.fromBlocks_multiply, hadj_hypBlock_mul h h2 hα]
  simp [hypGram2]

theorem exists_fourFrame (h2 : (2 : K) ≠ 0) :
    ∃ P : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) K, (P.map h.bar)ᵀ * P = Matrix.fromBlocks 0 1 1 0 := by
  obtain ⟨α, hα⟩ := exists_norm_eq_neg_one h
  have e : Fin 4 ≃ Fin 2 ⊕ Fin 2 := Fintype.equivOfCardEq (by simp)
  refine ⟨(hypBlock 2 α).submatrix e id, ?_⟩
  change hadj h ((hypBlock 2 α).submatrix e id) * (hypBlock 2 α).submatrix e id = _
  rw [hadj_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    hadj_hypBlock_mul h h2 hα]
  rfl

end Frames

section EvenInvolution

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem hadj_neg {l m : Type*} (A : Matrix l m K) : hadj h (-A) = -hadj h A := by
  ext i j
  simp [hadj]

@[expose] def summandNeg (r m : ℕ) (K : Type) [Field K] :
    Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K :=
  Matrix.fromBlocks (-1) 0 0 1

variable {r m : ℕ}

theorem summandNeg_mul_self : summandNeg r m K * summandNeg r m K = 1 := by
  rw [summandNeg, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_neg, neg_neg, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add,
    neg_zero]
  exact Matrix.fromBlocks_one

theorem summandNeg_isometry :
    hadj h (summandNeg r m K) * frameGram r m K * summandNeg r m K = frameGram r m K := by
  simp only [summandNeg, frameGram, hadj_fromBlocks, hadj_neg, hadj_zero, hadj_one,
    Matrix.fromBlocks_multiply, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, neg_neg, neg_zero]

theorem det_summandNeg : (summandNeg r m K).det = 1 := by
  rw [summandNeg, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg, Matrix.det_one, Matrix.det_one,
    mul_one, mul_one, Fintype.card_sum, Fintype.card_fin, Even.neg_one_pow ⟨r, rfl⟩]

theorem summandNeg_mul_frameMat (B : Matrix (Fin r) (Fin r) K) :
    summandNeg r m K * frameMat m B = frameMat m B * summandNeg r m K := by
  simp [summandNeg, frameMat, Matrix.fromBlocks_multiply]

theorem summandNeg_ne_smul_one (h2 : (2 : K) ≠ 0) (hr : 1 ≤ r) (hm : 1 ≤ m) (c : K) :
    summandNeg r m K ≠ c • 1 := by
  intro hc
  have e1 := congrFun (congrFun hc (Sum.inl (Sum.inl ⟨0, hr⟩))) (Sum.inl (Sum.inl ⟨0, hr⟩))
  have e2 := congrFun (congrFun hc (Sum.inr ⟨0, hm⟩)) (Sum.inr ⟨0, hm⟩)
  simp [summandNeg] at e1 e2
  apply h2
  linear_combination e2 - e1

variable {n : ℕ} {P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) K}
  (hP : hadj h P * P = frameGram r m K) (hnm : 2 * r + m = n)

@[expose] noncomputable def evenInvolution : unitaryPSU h n :=
  unitaryProj h n (frameSU h hP hnm (summandNeg r m K) (summandNeg_isometry h) det_summandNeg)

theorem frameSU_summandNeg_sq :
    frameSU h hP hnm (summandNeg r m K) (summandNeg_isometry h) det_summandNeg ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [pow_two, Subgroup.coe_mul, Units.val_mul, coe_frameSU, frameConj_mul h hP,
    summandNeg_mul_self, frameConj_one h hP hnm, Subgroup.coe_one, Units.val_one]

theorem evenInvolution_sq : evenInvolution h hP hnm ^ 2 = 1 := by
  rw [evenInvolution, ← map_pow, frameSU_summandNeg_sq, map_one]

theorem evenInvolution_ne_one (h2 : (2 : K) ≠ 0) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    evenInvolution h hP hnm ≠ 1 := by
  intro h1
  have hmem : frameSU h hP hnm (summandNeg r m K) (summandNeg_isometry h) det_summandNeg ∈
      unitaryScalars h n := by
    rw [← ker_unitaryProj]
    exact h1
  obtain ⟨c, -, -, hc⟩ := hmem
  refine summandNeg_ne_smul_one h2 hr hm (c : K) (eq_smul_of_frameConj_eq_scalar h hP ?_)
  rw [← coe_frameSU h hP hnm _ (summandNeg_isometry h) det_summandNeg, hc,
    Matrix.GeneralLinearGroup.coe_scalar]

theorem evenInvolution_comm {u : unitaryPSU h n} (hu : u ∈ frameUnipotent h P) :
    evenInvolution h hP hnm * u = u * evenInvolution h hP hnm := by
  rw [frameUnipotent_eq_range h hP hnm] at hu
  obtain ⟨B, rfl⟩ := hu
  have hSU : frameSU h hP hnm (summandNeg r m K) (summandNeg_isometry h) det_summandNeg *
      frameSUHom h hP hnm B = frameSUHom h hP hnm B *
        frameSU h hP hnm (summandNeg r m K) (summandNeg_isometry h) det_summandNeg := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_frameSUHom,
      coe_frameSU, frameConj_mul h hP, frameConj_mul h hP, summandNeg_mul_frameMat]
  rw [evenInvolution, frameUnipotentHom, MonoidHom.comp_apply, ← map_mul, ← map_mul, hSU]

end EvenInvolution

section FourInvolution

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem bar_neg_one_units : h.bar ((-1 : Kˣ) : K) = ((-1 : Kˣ) : K) := by
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

theorem bar_one_units : h.bar ((1 : Kˣ) : K) = ((1 : Kˣ) : K) := by
  rw [Units.val_one, map_one]

theorem torusGL_neg_one_mul_self :
    (torusGL ![(-1 : Kˣ), 1] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (torusGL ![(-1 : Kˣ), 1] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
  have hd : ∀ i, ((![(-1 : Kˣ), 1] i : Kˣ) : K) * ((![(-1 : Kˣ), 1] i : Kˣ) : K) = 1 := by
    intro i
    fin_cases i <;> simp
  have hd' : ∀ i, (((![(-1 : Kˣ), 1] i)⁻¹ : Kˣ) : K) * (((![(-1 : Kˣ), 1] i)⁻¹ : Kˣ) : K) = 1 := by
    intro i
    fin_cases i <;> simp
  rw [coe_torusGL, Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  simp only [hd, hd', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.diagonal_one,
    Matrix.fromBlocks_one]

variable {P : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) K} (hP : hadj h P * P = hypGram2 2 K)

@[expose] noncomputable def fourInvolution : unitaryPSU h 4 :=
  unitaryProj h 4 (pairedTorusSU h hP (bar_neg_one_units h) (bar_one_units h))

theorem pairedTorusSU_neg_one_sq :
    pairedTorusSU h hP (bar_neg_one_units h) (bar_one_units h) ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [pow_two, Subgroup.coe_mul, Units.val_mul, pairedTorusSU, coe_gSU,
    gConj_mul h (hypGram2_mul_self 2) hP, torusGL_neg_one_mul_self,
    gConj_one h (hypGram2_mul_self 2) hP card_two_sum_two, Subgroup.coe_one, Units.val_one]

theorem fourInvolution_sq : fourInvolution h hP ^ 2 = 1 := by
  rw [fourInvolution, ← map_pow, pairedTorusSU_neg_one_sq, map_one]

theorem fourInvolution_ne_one (h2 : (2 : K) ≠ 0) : fourInvolution h hP ≠ 1 := by
  intro h1
  have hmem : pairedTorusSU h hP (bar_neg_one_units h) (bar_one_units h) ∈
      unitaryScalars h 4 := by
    rw [← ker_unitaryProj]
    exact h1
  obtain ⟨c, -, -, hc⟩ := hmem
  have hcoe : ((pairedTorusSU h hP (bar_neg_one_units h) (bar_one_units h) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = gConj h (hypGram2 2 K) P
        (torusGL ![(-1 : Kˣ), 1] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := rfl
  have hT := eq_smul_of_gConj_eq_scalar h (hypGram2_mul_self 2) hP
    (T := (torusGL ![(-1 : Kˣ), 1] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (c := (c : K))
    (by rw [← hcoe, hc, Matrix.GeneralLinearGroup.coe_scalar])
  have e1 := congrFun (congrFun hT (Sum.inl 0)) (Sum.inl 0)
  have e2 := congrFun (congrFun hT (Sum.inl 1)) (Sum.inl 1)
  simp [coe_torusGL] at e1 e2
  apply h2
  linear_combination e2 - e1

theorem fourInvolution_comm {η : K} (hη : h.bar η = -η) {u : unitaryPSU h 4}
    (hu : u ∈ pairedRoot h P η) : fourInvolution h hP * u = u * fourInvolution h hP := by
  rw [pairedRoot_eq_range h hP hη] at hu
  obtain ⟨v, rfl⟩ := hu
  rw [← mul_inv_eq_iff_eq_mul]
  obtain ⟨w, rfl⟩ : ∃ w, Multiplicative.ofAdd w = v := ⟨v.toAdd, rfl⟩
  exact pairedRootHom_conj' h hP hη (bar_neg_one_units h) (bar_one_units h) (by simp) (by simp)

end FourInvolution

section Main

variable {p f : ℕ} {K : Type} [Field K]

theorem two_ne_zero_of_three_lt (h : UnitaryFieldData p f K) (hp3 : 3 < p) : (2 : K) ≠ 0 := by
  have : CharP K p := h.charP
  intro h0
  have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem exists_even_witness {Y : Type*} [Group Y] [Finite Y] (h : UnitaryFieldData p f K)
    (hp3 : 3 < p) {n : ℕ} (φ : Y →* unitaryPSU h n) (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center Y) {r : ℕ} (hr : 1 ≤ r) (hn : 2 * r < n) :
    ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ V : Subgroup Y, V ≤ Subgroup.centralizer {z} ∧
      IsElemAbelian p V ∧ Nat.card V = p ^ (f * r ^ 2) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have h2 := two_ne_zero_of_three_lt h hp3
  obtain ⟨P, hP⟩ := exists_evenFrame h h2 (n := n) (r := r) hn.le
  have hP' : hadj h P * P = frameGram r (n - 2 * r) K := hP
  have hnm : 2 * r + (n - 2 * r) = n := by omega
  obtain ⟨hU, hUcard⟩ := unitary_even_summand_unipotent h hn P hP
  exact exists_involution_elemAbelian φ hφ hZ (by omega) hU hUcard
    (unitary_even_summand_unipotent_preimage_comm h hp3 hn P hP φ hφ hZ)
    (evenInvolution_ne_one h hP' hnm h2 hr (by omega)) (evenInvolution_sq h hP' hnm)
    (fun _ hu => evenInvolution_comm h hP' hnm hu)

theorem exists_four_witness {Y : Type*} [Group Y] [Finite Y] (h : UnitaryFieldData p f K)
    (hp3 : 3 < p) (φ : Y →* unitaryPSU h 4) (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center Y) :
    ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ V : Subgroup Y, V ≤ Subgroup.centralizer {z} ∧
      IsElemAbelian p V ∧ Nat.card V = p ^ (2 * f) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have h2 := two_ne_zero_of_three_lt h hp3
  obtain ⟨P, hP⟩ := exists_fourFrame h h2
  have hP' : hadj h P * P = hypGram2 2 K := hP
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hη0 : c - h.bar c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hη : h.bar (c - h.bar c) = -(c - h.bar c) := by rw [map_sub, h.bar_bar, neg_sub]
  obtain ⟨hU, hUcard⟩ := unitary_four_paired_root h P hP hη0 hη
  exact exists_involution_elemAbelian φ hφ hZ (by omega) hU hUcard
    (unitary_four_paired_root_preimage_comm h hp3 P hP hη0 hη φ hφ hZ)
    (fourInvolution_ne_one h hP' h2) (fourInvolution_sq h hP')
    (fun _ hu => fourInvolution_comm h hP' hη hu)

theorem le_localRank_of_witness {G : Type*} [Group G] [Finite G] {Y : Subgroup G} {p k : ℕ}
    (hp : 1 < p) (hw : ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ V : Subgroup Y,
      V ≤ Subgroup.centralizer {z} ∧ IsElemAbelian p V ∧ Nat.card V = p ^ k) :
    k ≤ localRank p G := by
  obtain ⟨z, hz2, hz1, V, hVz, hV, hVcard⟩ := hw
  refine le_localRank_of_injective hp (A := V) (fun a b => hV.1.is_comm.comm a b)
    (fun a => Subtype.ext (by rw [Subgroup.coe_pow]; exact hV.2 _ a.2)) hVcard
    (Y.subtype.comp V.subtype) (Y.subtype_injective.comp V.subtype_injective) (u := (z : G))
    (fun h0 => hz1 (Subtype.ext h0)) (by rw [← Subgroup.coe_pow, hz2, Subgroup.coe_one])
    (fun a => ?_)
  have := Subgroup.mem_centralizer_iff.mp (hVz a.2) z (Set.mem_singleton z)
  exact congrArg Subtype.val this.symm

theorem unitary_defining_prime_central_cover_two_local_rank_witness {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) (h : UnitaryFieldData p f K) (hp3 : 3 < p) {n : ℕ}
    (_hn : 3 ≤ n) (φ : Y →* unitaryPSU h n) (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center Y) :
    (∀ r : ℕ, 1 ≤ r → 2 * r < n → ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ V : Subgroup Y,
      V ≤ Subgroup.centralizer {z} ∧ IsElemAbelian p V ∧ Nat.card V = p ^ (f * r ^ 2)) ∧
    (n = 4 → ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ V : Subgroup Y,
      V ≤ Subgroup.centralizer {z} ∧ IsElemAbelian p V ∧ Nat.card V = p ^ (2 * f)) ∧
    (∀ r : ℕ, 1 ≤ r → 2 * r < n → f * r ^ 2 ≤ localRank p G) ∧
    (n = 4 → 2 * f ≤ localRank p G) := by
  have hwe : ∀ r : ℕ, 1 ≤ r → 2 * r < n → ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ V : Subgroup Y,
      V ≤ Subgroup.centralizer {z} ∧ IsElemAbelian p V ∧ Nat.card V = p ^ (f * r ^ 2) :=
    fun r hr hrn => exists_even_witness h hp3 φ hφ hZ hr hrn
  have hwf : n = 4 → ∃ z : Y, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ V : Subgroup Y,
      V ≤ Subgroup.centralizer {z} ∧ IsElemAbelian p V ∧ Nat.card V = p ^ (2 * f) := by
    rintro rfl
    exact exists_four_witness h hp3 φ hφ hZ
  exact ⟨hwe, hwf, fun r hr hrn => le_localRank_of_witness (by omega) (hwe r hr hrn),
    fun h4 => le_localRank_of_witness (by omega) (hwf h4)⟩

end Main

end CFSG.RankThree.Classical
