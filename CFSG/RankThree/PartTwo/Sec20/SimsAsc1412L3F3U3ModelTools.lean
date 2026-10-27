module

public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite
import Mathlib.Algebra.CharP.CharAndCard

public section

namespace CFSG.RankThree.PartTwo.Sec20.F3U3Model

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External
open scoped MatrixGroups LinearAlgebra.Projectivization Matrix

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

variable {p : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ 2)
  (hfix : Nat.card {x : K // J.conj x = x} = p)

include hK in
theorem charP_of_card_sq : CharP K p := by
  letI : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])

include hK in
theorem two_ne_zero_of_card_sq (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  haveI := charP_of_card_sq hK
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

include hJ hK hfix in
theorem factorization_card_psu :
    (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)).factorization p = 3 := by
  have hp : p.Prime := Fact.out
  have hcard := card_psu J hJ p hK hfix
  set d := Nat.gcd (p + 1) 3 with hd
  have hdvd : d ∣ (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) := by
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    exact (Nat.gcd_dvd_left (p + 1) 3).trans
      (by simpa using Odd.nat_add_dvd_pow_add_pow p 1 (by decide : Odd 3))
  have hN : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) * d =
      (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) := by
    rw [hcard]
    exact Nat.div_mul_cancel hdvd
  have hn0 : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ≠ 0 := Nat.card_pos.ne'
  have h3 : p ^ 3 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
    rw [← card_rootGroup J hJ p hK hfix]
    exact Subgroup.card_subgroup_dvd_card _
  have h4 : ¬ p ^ 4 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
    intro h
    have h' : p ^ 4 ∣ (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) := hN ▸ Dvd.dvd.mul_right h d
    have h'' : p ^ 3 * p ∣ p ^ 3 * ((p ^ 3 + 1) * (p ^ 2 - 1)) := by
      convert h' using 1 <;> ring
    have hpd : p ∣ (p ^ 3 + 1) * (p ^ 2 - 1) :=
      (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos 3)).mp h''
    rcases hp.dvd_mul.mp hpd with h1 | h1
    · have : p ∣ 1 := (Nat.dvd_add_right (dvd_pow_self p (by norm_num))).mp h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · have h2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
      have h5 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h2 h1
      have h6 : p ^ 2 - (p ^ 2 - 1) = 1 := by
        have := Nat.one_le_pow 2 p hp.pos
        omega
      rw [h6] at h5
      exact hp.one_lt.ne' (Nat.dvd_one.mp h5)
  have h3' := (hp.pow_dvd_iff_le_factorization hn0).mp h3
  have h4' : ¬ 4 ≤ (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)).factorization p :=
    fun h => h4 ((hp.pow_dvd_iff_le_factorization hn0).mpr h)
  omega

theorem coord_zpow_fst (z : Coord J) (s : ℤ) :
    ((z ^ s : Coord J) : K × K).1 = (s : K) * z.1.1 := by
  let π : Coord J →* Multiplicative K :=
    { toFun := fun w => Multiplicative.ofAdd w.1.1
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have h : π (z ^ s) = π z ^ s := map_zpow π z s
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_zpow] at h'
  change (z ^ s).1.1 = s • z.1.1 at h'
  rw [h', zsmul_eq_mul]

include hK hfix in
theorem exists_norm_one_pow_six_ne_one (hp7 : 7 ≤ p) :
    ∃ k : Kˣ, (k : K) * J.conj (k : K) = 1 ∧ (k : K) ^ 6 ≠ 1 := by
  let : IsCyclic Kˣ := inferInstance
  have hcardUnits : Nat.card Kˣ = p ^ 2 - 1 := by rw [Nat.card_units, hK]
  have hfactor : p ^ 2 - 1 = (p - 1) * (p + 1) := by simpa [mul_comm] using Nat.sq_sub_sq p 1
  have hdq1 : p + 1 ∣ p ^ 2 - 1 := by
    rw [hfactor]
    exact dvd_mul_left (p + 1) (p - 1)
  have hroots : Nat.card (rootsOfUnity (p + 1) K) = p + 1 := by
    rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, hcardUnits, Nat.gcd_eq_right hdq1]
  have hsix : 6 < Nat.card (rootsOfUnity (p + 1) K) := by
    rw [hroots]
    omega
  let : IsCyclic (rootsOfUnity (p + 1) K) := inferInstance
  obtain ⟨k0, hk6⟩ := exists_pow_ne_one_of_isCyclic (G := rootsOfUnity (p + 1) K)
    (by decide : (6 : ℕ) ≠ 0) hsix
  have hkq : (k0 : Kˣ) ^ (p + 1) = 1 := (mem_rootsOfUnity (p + 1) (k0 : Kˣ)).mp k0.property
  refine ⟨(k0 : Kˣ), ?_, ?_⟩
  · rw [huppert_II_10_4_conj_eq_frobenius J p hK hfix, ← pow_succ']
    simpa using congrArg Units.val hkq
  · intro h
    apply hk6
    apply Subtype.ext
    apply Units.ext
    simpa using h

structure IotaData (J : HermitianForm 3 K) (q : ℕ) where
  e : ZMod q →+* K
  ζ : K
  ζ_ne : ζ ≠ 0
  conj_ζ : J.conj ζ = -ζ
  conj_e : ∀ c, J.conj (e c) = e c

namespace IotaData

variable {J} {q : ℕ}

@[expose] noncomputable def mat (D : IotaData J q) (X : SL(2, ZMod q)) : Matrix (Fin 3) (Fin 3) K :=
  !![D.e (X.1 0 0), 0, D.e (X.1 0 1) * D.ζ⁻¹; 0, 1, 0; D.e (X.1 1 0) * D.ζ, 0, D.e (X.1 1 1)]

theorem mat_mul (D : IotaData J q) (X Y : SL(2, ZMod q)) :
    D.mat (X * Y) = (D.mat X : Matrix (Fin 3) (Fin 3) K) * D.mat Y := by
  have h := D.ζ_ne
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.coe_mul,
      Fin.sum_univ_two] <;> field_simp

theorem mat_one (D : IotaData J q) : D.mat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat]

theorem mat_det (D : IotaData J q) (X : SL(2, ZMod q)) : (D.mat X).det = 1 := by
  have h := X.2
  rw [Matrix.det_fin_two] at h
  have h' : D.e (X.1 0 0) * D.e (X.1 1 1) - D.e (X.1 0 1) * D.e (X.1 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, h, map_one]
  have hz := D.ζ_ne
  rw [Matrix.det_fin_three]
  simp [mat]
  field_simp
  linear_combination h'

theorem mat_unitary (D : IotaData J q) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (X : SL(2, ZMod q)) :
    J.conjTranspose (D.mat X) * J.form * D.mat X = J.form := by
  have h := X.2
  rw [Matrix.det_fin_two] at h
  have h' : D.e (X.1 0 0) * D.e (X.1 1 1) - D.e (X.1 0 1) * D.e (X.1 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, h, map_one]
  have hz := D.ζ_ne
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hJ, mat, map_mul,
      map_inv₀, D.conj_e, D.conj_ζ]
  all_goals first
    | ring1
    | (field_simp; linear_combination h')
    | (field_simp; linear_combination D.ζ * h')

@[expose] noncomputable def iotaGL (D : IotaData J q) (X : SL(2, ZMod q)) : GL (Fin 3) K :=
  ⟨D.mat X, D.mat X⁻¹, by rw [← mat_mul, mul_inv_cancel, mat_one],
    by rw [← mat_mul, inv_mul_cancel, mat_one]⟩

theorem coe_iotaGL (D : IotaData J q) (X : SL(2, ZMod q)) :
    ((iotaGL D X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = D.mat X :=
  rfl

@[expose] noncomputable def iotaSU (D : IotaData J q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) : SL(2, ZMod q) →* J.specialSubgroup where
  toFun X := ⟨iotaGL D X, (J.mem_specialSubgroup_iff _).mpr
    ⟨mat_unitary D hJ X, Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact mat_det D X)⟩⟩
  map_one' := Subtype.ext (Units.ext (mat_one D))
  map_mul' X Y := Subtype.ext (Units.ext (mat_mul D X Y))

@[expose] noncomputable def iota (D : IotaData J q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    SL(2, ZMod q) →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup).comp (iotaSU D hJ)

theorem coe_iota (D : IotaData J q) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (X : SL(2, ZMod q)) :
    ((iota D hJ X : ProjectiveSpecialUnitaryMatrixGroup J) : Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk (iotaGL D X) :=
  rfl

end IotaData

@[expose] def upperSL {R : Type*} [CommRing R] (c : R) : SL(2, R) :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lowerSL {R : Type*} [CommRing R] (c : R) : SL(2, R) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem coe_upperSL {R : Type*} [CommRing R] (c : R) :
    (upperSL c : Matrix (Fin 2) (Fin 2) R) = !![1, c; 0, 1] :=
  rfl

@[simp] theorem coe_lowerSL {R : Type*} [CommRing R] (c : R) :
    (lowerSL c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] :=
  rfl

@[expose] def wSL (R : Type*) [CommRing R] : SL(2, R) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

@[simp] theorem coe_wSL (R : Type*) [CommRing R] :
    (wSL R : Matrix (Fin 2) (Fin 2) R) = !![0, -1; 1, 0] :=
  rfl

theorem mem_of_upper_lower {F : Type*} [Field F] (S : Subgroup SL(2, F))
    (hU : ∀ c, upperSL c ∈ S) (hL : ∀ c, lowerSL c ∈ S) (M : SL(2, F)) : M ∈ S := by
  have hne : ∀ M : SL(2, F), (M : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → M ∈ S := by
    intro M hc
    obtain ⟨a, b, c, d, hm⟩ : ∃ a b c d : F, (M : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
      ⟨_, _, _, _, Matrix.eta_fin_two _⟩
    have hdet := M.2
    rw [hm, Matrix.det_fin_two_of] at hdet
    rw [hm] at hc
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one] at hc
    have hM : M = upperSL ((a - 1) / c) * lowerSL c * upperSL ((d - 1) / c) := by
      ext i j
      rw [hm]
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp <;> first | ring1 | linear_combination -hdet
    rw [hM]
    exact mul_mem (mul_mem (hU _) (hL _)) (hU _)
  by_cases hc : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hdet := M.2
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    have ha : (M : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have h1 : lowerSL 1 * M ∈ S := hne _ (by
      simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc] using ha)
    have h2 : M = (lowerSL (1 : F))⁻¹ * (lowerSL 1 * M) := by group
    rw [h2]
    exact mul_mem (inv_mem (hL 1)) h1
  · exact hne M hc

include hK hfix in
theorem nonempty_iotaData : Nonempty (IotaData J p) := by
  haveI := charP_of_card_sq hK
  let e : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hconj_e : ∀ c, J.conj (e c) = e c := fun c => by
    have h : (J.conj : K ≃+* K).toRingHom.comp e = e := RingHom.ext_zmod _ _
    exact congrArg (fun f => f c) h
  obtain ⟨ξ, hξ⟩ : ∃ ξ : K, J.conj ξ ≠ ξ := by
    by_contra h
    push Not at h
    have hcard : Nat.card {x : K // J.conj x = x} = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv h)
    rw [hfix, hK] at hcard
    have hp : p.Prime := Fact.out
    nlinarith [hp.two_le]
  exact ⟨⟨e, ξ - J.conj ξ, sub_ne_zero.mpr (Ne.symm hξ), by rw [map_sub, J.conj_involutive]; ring,
    hconj_e⟩⟩

include hfix in
theorem IotaData.exists_eq_e (D : IotaData J p) {x : K} (hx : J.conj x = x) :
    ∃ c : ZMod p, D.e c = x := by
  have hinj : Function.Injective
      (fun c : ZMod p => (⟨D.e c, D.conj_e c⟩ : {x : K // J.conj x = x})) :=
    fun a b h => D.e.injective (congrArg Subtype.val h)
  have hcard : Nat.card {x : K // J.conj x = x} ≤ Nat.card (ZMod p) := by
    rw [hfix, Nat.card_zmod]
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨x, hx⟩
  exact ⟨c, congrArg Subtype.val hc⟩

namespace IotaData

variable {J}

@[expose] noncomputable def zUpper (D : IotaData J p) (s : ZMod p) : Coord J :=
  ⟨(0, D.e s * D.ζ⁻¹), by
    have := D.ζ_ne
    simp [map_mul, map_inv₀, D.conj_e, D.conj_ζ]⟩

@[expose] noncomputable def zLower (D : IotaData J p) (s : ZMod p) : Coord J :=
  ⟨(0, D.e s * D.ζ), by simp [map_mul, D.conj_e, D.conj_ζ]⟩

theorem iota_upper (D : IotaData J p) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (s : ZMod p) : iota D hJ (upperSL s) = root J hJ (D.zUpper s) := by
  apply Subtype.ext
  rw [coe_iota, coe_root]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change D.mat (upperSL s) i j = hermitianUnipotentMatrix J (D.zUpper s) i j
  fin_cases i <;> fin_cases j <;> simp [mat, zUpper, hermitianUnipotentMatrix]

theorem iota_lower (D : IotaData J p) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (s : ZMod p) :
    iota D hJ (lowerSL s) = weyl J hJ * root J hJ (D.zLower s) * weyl J hJ := by
  apply Subtype.ext
  rw [coe_iota, Subgroup.coe_mul, Subgroup.coe_mul, coe_weyl, coe_root, ← map_mul, ← map_mul]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change D.mat (lowerSL s) i j = ((hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) *
    hermitianUnipotentMatrix J (D.zLower s) * (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K)) i j
  fin_cases i <;> fin_cases j <;>
    simp [mat, zLower, hermitianUnipotentMatrix, hermitianWeylMatrix, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem iota_injective (D : IotaData J p) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (iota D hJ) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  have h1 : Matrix.ProjGenLinGroup.mk (iotaGL D X) = 1 := congrArg Subtype.val hX
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h1
  obtain ⟨c, hc⟩ := h1
  have hz := D.ζ_ne
  have e00 := congrFun (congrFun hc 0) 0
  have e02 := congrFun (congrFun hc 0) 2
  have e11 := congrFun (congrFun hc 1) 1
  have e20 := congrFun (congrFun hc 2) 0
  have e22 := congrFun (congrFun hc 2) 2
  simp [coe_iotaGL, mat, Matrix.scalar_apply] at e00 e02 e11 e20 e22
  have h01 : (X : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := e02.resolve_right hz
  have h10 : (X : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := e20.resolve_right hz
  have h00 : (X : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 :=
    D.e.injective (by rw [← e00, e11, map_one])
  have h11 : (X : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 :=
    D.e.injective (by rw [← e22, e11, map_one])
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

include hfix in
theorem exists_coords (D : IotaData J p) (h2 : (2 : K) ≠ 0) (t : K) :
    ∃ a b : ZMod p, t = D.e a + D.ζ * D.e b := by
  have hz := D.ζ_ne
  have ha : J.conj ((t + J.conj t) / 2) = (t + J.conj t) / 2 := by
    rw [map_div₀, map_add, J.conj_involutive, map_ofNat]
    ring
  have hb : J.conj ((t - J.conj t) / (2 * D.ζ)) = (t - J.conj t) / (2 * D.ζ) := by
    rw [map_div₀, map_sub, map_mul, J.conj_involutive, D.conj_ζ]
    simp only [map_ofNat]
    field_simp
    ring
  obtain ⟨a, ha'⟩ := IotaData.exists_eq_e J hfix D ha
  obtain ⟨b, hb'⟩ := IotaData.exists_eq_e J hfix D hb
  refine ⟨a, b, ?_⟩
  rw [ha', hb']
  field_simp
  ring

end IotaData

include hJ hK hfix in
theorem subgroupMap_mk_injective (hp3 : p % 3 = 1) :
    Function.Injective (Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup) := by
  rw [injective_iff_map_eq_one]
  intro M hM
  have h1 : Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) = 1 := congrArg Subtype.val hM
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h1
  obtain ⟨c, hc⟩ := h1
  have hspec := (J.mem_specialSubgroup_iff _).mp M.2
  have hcc : J.conj c * c = 1 := by
    have h := congrArg (fun A => A 0 2) hspec.1
    simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, ← hc, hJ,
      Matrix.scalar_apply] at h
    exact h
  have hc3 : c ^ 3 = 1 := by
    have h := congrArg Units.val hspec.2
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hc] at h
    simpa [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three, pow_succ] using h
  have hcp : c ^ (p + 1) = 1 := by
    rw [pow_succ', ← huppert_II_10_4_conj_eq_frobenius J p hK hfix c, mul_comm]
    exact hcc
  obtain ⟨m, hm⟩ : ∃ m, p = 3 * m + 1 := ⟨p / 3, by omega⟩
  have hc2 : c ^ 2 = 1 := by
    rw [show p + 1 = 3 * m + 2 by omega, pow_add, pow_mul, hc3, one_pow, one_mul] at hcp
    exact hcp
  have hc1 : c = 1 := by
    have h3 : c ^ 3 = c := by
      calc c ^ 3 = c ^ 2 * c := by ring
        _ = c := by rw [hc2, one_mul]
    rw [← h3, hc3]
  apply Subtype.ext
  apply Units.ext
  rw [← hc, hc1, map_one]
  rfl

include hJ hK hfix in
theorem exists_lift (hp3 : p % 3 = 1) :
    ∃ L : ProjectiveSpecialUnitaryMatrixGroup J →* GL (Fin 3) K,
      (∀ g, L g ∈ J.specialSubgroup) ∧
        ∀ g, Matrix.ProjGenLinGroup.mk (L g) = (g : Matrix.ProjGenLinGroup (Fin 3) K) := by
  let e : J.specialSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    MulEquiv.ofBijective (Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup)
      ⟨subgroupMap_mk_injective J hJ hK hfix hp3, MonoidHom.subgroupMap_surjective _ _⟩
  refine ⟨J.specialSubgroup.subtype.comp e.symm.toMonoidHom, fun g => (e.symm g).2, fun g => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply g)

theorem block_form_aux (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {M N : Matrix (Fin 3) (Fin 3) K} (hMN : M * N = 1)
    (hunit : J.conjTranspose M * J.form * M = J.form) (hN10 : N 1 0 = 0) (hN12 : N 1 2 = 0) :
    M 0 1 = 0 ∧ M 2 1 = 0 := by
  have h : J.conjTranspose M * J.form = J.form * N := by
    calc J.conjTranspose M * J.form = J.conjTranspose M * J.form * (M * N) := by
          rw [hMN, Matrix.mul_one]
      _ = (J.conjTranspose M * J.form * M) * N := by simp only [Matrix.mul_assoc]
      _ = J.form * N := by rw [hunit]
  have h10 := congrFun (congrFun h 1) 0
  have h12 := congrFun (congrFun h 1) 2
  simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hJ, hN10,
    hN12] at h10 h12
  exact ⟨h12, h10⟩

theorem eq_diag_of_involution {T : Matrix (Fin 3) (Fin 3) K} (h2 : (2 : K) ≠ 0)
    (h01 : T 0 1 = 0) (h10 : T 1 0 = 0) (h12 : T 1 2 = 0) (h21 : T 2 1 = 0) (h11 : T 1 1 = 1)
    (hdet : T.det = 1) (hsq : T * T = 1) (hne : T ≠ 1) :
    T = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := by
  have hdet' : T 0 0 * T 2 2 - T 0 2 * T 2 0 = 1 := by
    rw [Matrix.det_fin_three] at hdet
    simp only [h01, h10, h12, h21, h11] at hdet
    linear_combination hdet
  have e00 := congrFun (congrFun hsq 0) 0
  have e02 := congrFun (congrFun hsq 0) 2
  have e20 := congrFun (congrFun hsq 2) 0
  have e22 := congrFun (congrFun hsq 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h10, h12, h21, h11] at e00 e02 e20 e22
  have hT : ∀ x : K, T 0 0 = x → T 2 2 = x → T 0 2 = 0 → T 2 0 = 0 →
      T = !![x, 0, 0; 0, 1, 0; 0, 0, x] := by
    intro x h00 h22 h02 h20
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h22, h02, h20, h01, h10, h12, h21, h11]
  rcases eq_or_ne (T 0 0 + T 2 2) 0 with hs | hs
  · exfalso
    apply h2
    linear_combination (-1 : K) * e00 + (-1 : K) * hdet' + T 0 0 * hs
  · have hb0 : T 0 2 = 0 := by
      have : (T 0 0 + T 2 2) * T 0 2 = 0 := by linear_combination e02
      exact (mul_eq_zero.mp this).resolve_left hs
    have hc0 : T 2 0 = 0 := by
      have : (T 0 0 + T 2 2) * T 2 0 = 0 := by linear_combination e20
      exact (mul_eq_zero.mp this).resolve_left hs
    have haa : T 0 0 * T 0 0 = 1 := by
      rw [hb0] at e00
      linear_combination e00
    have had : T 0 0 * T 2 2 = 1 := by
      rw [hb0] at hdet'
      linear_combination hdet'
    have ha0 : T 0 0 ≠ 0 := fun h => by
      rw [h] at haa
      simp at haa
    have hda : T 2 2 = T 0 0 := by
      apply mul_left_cancel₀ ha0
      rw [had, haa]
    have hsq1 : (T 0 0 - 1) * (T 0 0 + 1) = 0 := by linear_combination haa
    rcases mul_eq_zero.mp hsq1 with h | h
    · exfalso
      apply hne
      have h1 : T 0 0 = 1 := by linear_combination h
      rw [hT 1 h1 (hda.trans h1) hb0 hc0, Matrix.one_fin_three]
    · have h1 : T 0 0 = -1 := by linear_combination h
      exact hT (-1) h1 (hda.trans h1) hb0 hc0

end CFSG.RankThree.PartTwo.Sec20.F3U3Model
