module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102SylOddTorus
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102SylOddSylow
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix CFSG.Open CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.ClassicalEven

variable {f : ℕ} {K : Type} [Field K]

section

variable [CharP K 2]

private def u4G (lam : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 1, 0, 0; 1, lam, 0, 0; 0, 0, 1, 1; 0, 0, 1, lam]

private def u4Ginv (lam : K) : Matrix (Fin 4) (Fin 4) K :=
  (lam + 1)⁻¹ • !![lam, 1, 0, 0; 1, 1, 0, 0; 0, 0, lam, 1; 0, 0, 1, 1]

private def u4J (lam : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1 + lam, 0, 0; 1 + lam⁻¹, 0, 0, 0; 0, 0, 0, 1 + lam; 0, 0, 1 + lam⁻¹, 0]

omit [CharP K 2] in
private theorem u4G_transpose (lam : K) : (u4G lam)ᵀ = u4G lam := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4G]

private theorem u4G_mul_u4Ginv (lam : K) (hlam : lam + 1 ≠ 0) : u4G lam * u4Ginv lam = 1 := by
  have hself : ∀ x : K, x + x = 0 := fun x => by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination (x : K) * h2
  have hdiag : lam * (lam + 1)⁻¹ + (lam + 1)⁻¹ = 1 := by
    rw [show lam * (lam + 1)⁻¹ + (lam + 1)⁻¹ = (lam + 1) * (lam + 1)⁻¹ by ring,
      mul_inv_cancel₀ hlam]
  have hdiag' : (lam + 1)⁻¹ + lam * (lam + 1)⁻¹ = 1 := by
    rw [add_comm]; exact hdiag
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u4G, u4Ginv, Matrix.mul_apply, Fin.sum_univ_four, hself, hdiag, hdiag',
      mul_comm, mul_left_comm]

private theorem u4Ginv_mul_u4G (lam : K) (hlam : lam + 1 ≠ 0) : u4Ginv lam * u4G lam = 1 := by
  have hself : ∀ x : K, x + x = 0 := fun x => by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination (x : K) * h2
  have hdiag : lam * (lam + 1)⁻¹ + (lam + 1)⁻¹ = 1 := by
    rw [show lam * (lam + 1)⁻¹ + (lam + 1)⁻¹ = (lam + 1) * (lam + 1)⁻¹ by ring,
      mul_inv_cancel₀ hlam]
  have hdiag' : (lam + 1)⁻¹ + lam * (lam + 1)⁻¹ = 1 := by
    rw [add_comm]; exact hdiag
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u4G, u4Ginv, Matrix.mul_apply, Fin.sum_univ_four, hself, hdiag, hdiag',
      mul_comm, mul_left_comm]

private noncomputable def u4GL (lam : K) (hlam : lam + 1 ≠ 0) : GL (Fin 4) K :=
  ⟨u4G lam, u4Ginv lam, u4G_mul_u4Ginv lam hlam, u4Ginv_mul_u4G lam hlam⟩

private theorem coe_u4GL (lam : K) (hlam : lam + 1 ≠ 0) :
    ((u4GL lam hlam : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = u4G lam := rfl

omit [CharP K 2] in
private theorem u4G_map_bar (h : UnitaryFieldData 2 f K) {lam : K} (hlamq : h.bar lam = lam⁻¹) :
    (u4G lam).map h.bar = u4G lam⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u4G, hlamq]

private theorem u4G_map_bar_mul (h : UnitaryFieldData 2 f K) {lam : K}
    (hlamq : h.bar lam = lam⁻¹) (hlam0 : lam ≠ 0) :
    ((u4G lam).map h.bar)ᵀ * u4G lam = u4J lam := by
  rw [← Matrix.transpose_map, u4G_transpose, u4G_map_bar h hlamq]
  have hself : ∀ x : K, x + x = 0 := fun x => by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination (x : K) * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u4G, u4J, Matrix.mul_apply, Fin.sum_univ_four, hself, hlam0, mul_comm]

omit [CharP K 2] in
private theorem transpose_torusDiag (v : Fin 4 → Kˣ) :
    ((torusDiag v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ =
      (torusDiag v : GL (Fin 4) K) := by
  rw [coe_torusDiag]
  exact Matrix.diagonal_transpose _

omit [CharP K 2] in
private theorem torusDiag_map_bar (h : UnitaryFieldData 2 f K) {v : Fin 4 → Kˣ}
    (hv : ∀ i, h.bar ((v i : K)) = (v i : K)) :
    ((torusDiag v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar =
      ((torusDiag v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  rw [coe_torusDiag, Matrix.diagonal_map (map_zero h.bar)]
  congr 1
  funext i
  exact hv i

omit [CharP K 2] in
private theorem torusDiag_mul_J_mul (lam : K) (v : Fin 4 → Kˣ)
    (hv0 : (v 0 : K) * (v 1 : K) = 1) (hv1 : (v 1 : K) * (v 0 : K) = 1)
    (hv2 : (v 2 : K) * (v 3 : K) = 1) (hv3 : (v 3 : K) * (v 2 : K) = 1) :
    ((torusDiag v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * u4J lam *
      ((torusDiag v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = u4J lam := by
  rw [coe_torusDiag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u4J, Matrix.mul_apply, Fin.sum_univ_four, hv0, hv1, hv2, hv3, mul_comm, mul_assoc]

private theorem u4M_unitary (h : UnitaryFieldData 2 f K) {lam : K} (hlam : lam + 1 ≠ 0)
    (hlamq : h.bar lam = lam⁻¹) (hlam0 : lam ≠ 0) {v : Fin 4 → Kˣ}
    (hv : ∀ i, h.bar ((v i : K)) = (v i : K))
    (hv0 : (v 0 : K) * (v 1 : K) = 1) (hv1 : (v 1 : K) * (v 0 : K) = 1)
    (hv2 : (v 2 : K) * (v 3 : K) = 1) (hv3 : (v 3 : K) * (v 2 : K) = 1) :
    ((((u4G lam * (torusDiag v : Matrix (Fin 4) (Fin 4) K) * u4Ginv lam).map h.bar)ᵀ) *
      (u4G lam * (torusDiag v : Matrix (Fin 4) (Fin 4) K) * u4Ginv lam)) = 1 := by
  set G := u4G lam
  set Gi := u4Ginv lam
  set D := (torusDiag v : Matrix (Fin 4) (Fin 4) K)
  have hGG : G * Gi = 1 := u4G_mul_u4Ginv lam hlam
  have hDmap : D.map h.bar = D := torusDiag_map_bar h hv
  have hJ : (G.map h.bar)ᵀ * G = u4J lam := u4G_map_bar_mul h hlamq hlam0
  have hDJD : D * u4J lam * D = u4J lam := torusDiag_mul_J_mul lam v hv0 hv1 hv2 hv3
  have hDtr : Dᵀ = D := transpose_torusDiag v
  have hMmap : (G * D * Gi).map h.bar = (G.map h.bar) * D * (Gi.map h.bar) := by
    rw [Matrix.map_mul, Matrix.map_mul, hDmap]
  have hGiG : (Gi.map h.bar)ᵀ * (G.map h.bar)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hGG,
      Matrix.map_one (⇑h.bar) (map_zero h.bar) (map_one h.bar), Matrix.transpose_one]
  calc
    (((G * D * Gi).map h.bar)ᵀ * (G * D * Gi))
        = ((G.map h.bar) * D * (Gi.map h.bar))ᵀ * (G * D * Gi) := by rw [hMmap]
    _ = (Gi.map h.bar)ᵀ * Dᵀ * (G.map h.bar)ᵀ * (G * D * Gi) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul]; noncomm_ring
    _ = (Gi.map h.bar)ᵀ * (D * ((G.map h.bar)ᵀ * G) * D) * Gi := by
          rw [hDtr]; noncomm_ring
    _ = (Gi.map h.bar)ᵀ * (D * u4J lam * D) * Gi := by rw [hJ]
    _ = (Gi.map h.bar)ᵀ * u4J lam * Gi := by rw [hDJD]
    _ = (Gi.map h.bar)ᵀ * ((G.map h.bar)ᵀ * G) * Gi := by rw [hJ]
    _ = ((Gi.map h.bar)ᵀ * (G.map h.bar)ᵀ) * (G * Gi) := by noncomm_ring
    _ = 1 := by rw [hGiG, hGG, one_mul]

omit [CharP K 2] in
private theorem bar_eq_self_rootsOfUnity (h : UnitaryFieldData 2 f K) {c : ℕ}
    (hc : 3 ^ c ∣ 2 ^ f - 1) (a : rootsOfUnity (3 ^ c) K) :
    h.bar ((a : Kˣ) : K) = ((a : Kˣ) : K) := by
  have ha : ((a : Kˣ) : K) ^ (3 ^ c) = 1 := by
    have h1 := (mem_rootsOfUnity (3 ^ c) (a : Kˣ)).mp a.2
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    simpa [Units.val_pow_eq_pow_val] using h2
  obtain ⟨t, ht⟩ := hc
  have hq1 : 2 ^ f = 3 ^ c * t + 1 := by
    have hle : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by norm_num)
    omega
  rw [h.bar_apply, hq1, pow_succ, pow_mul, ha, one_pow, one_mul]

omit [CharP K 2] in
private theorem bar_inv_rootsOfUnity (h : UnitaryFieldData 2 f K) {c : ℕ}
    (hc : 3 ^ c ∣ 2 ^ f - 1) (a : rootsOfUnity (3 ^ c) K) :
    h.bar (((a : Kˣ) : K)⁻¹) = (((a : Kˣ) : K))⁻¹ := by
  rw [map_inv₀, bar_eq_self_rootsOfUnity h hc a]

private noncomputable def u4Dhom (c : ℕ) :
    (rootsOfUnity (3 ^ c) K × rootsOfUnity (3 ^ c) K) →* (Fin 4 → Kˣ) where
  toFun x := ![(x.1 : Kˣ), (x.1 : Kˣ)⁻¹, (x.2 : Kˣ), (x.2 : Kˣ)⁻¹]
  map_one' := by funext i; fin_cases i <;> simp
  map_mul' := by
    intro x y
    funext i
    fin_cases i <;> simp [mul_comm]

private noncomputable def u4Mhom {c : ℕ} (lam : K) (hlam : lam + 1 ≠ 0) :
    (rootsOfUnity (3 ^ c) K × rootsOfUnity (3 ^ c) K) →* GL (Fin 4) K where
  toFun x := u4GL lam hlam * torusDiag (u4Dhom c x) * (u4GL lam hlam)⁻¹
  map_one' := by simp
  map_mul' := by
    intro x y
    simp only [map_mul]
    group

private theorem coe_u4Mhom {c : ℕ} (lam : K) (hlam : lam + 1 ≠ 0)
    (x : rootsOfUnity (3 ^ c) K × rootsOfUnity (3 ^ c) K) :
    ((u4Mhom lam hlam x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      u4G lam * (torusDiag (u4Dhom c x) : Matrix (Fin 4) (Fin 4) K) * u4Ginv lam := rfl

private theorem det_u4M {c : ℕ} (lam : K) (hlam : lam + 1 ≠ 0)
    (x : rootsOfUnity (3 ^ c) K × rootsOfUnity (3 ^ c) K) :
    ((u4Mhom lam hlam x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [coe_u4Mhom]
  have hD : (torusDiag (u4Dhom c x) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [CFSG.SectionRank.ClassicalEven.det_torusDiag]
    have hprod : (∏ i, u4Dhom c x i) = 1 := by
      rw [Fin.prod_univ_four]
      simp [u4Dhom]
    rw [hprod, Units.val_one]
  rw [Matrix.det_mul, Matrix.det_mul, hD, mul_one]
  have hdet : (u4Ginv lam).det * (u4G lam).det = 1 := by
    rw [← Matrix.det_mul, u4Ginv_mul_u4G lam hlam, Matrix.det_one]
  rw [mul_comm]
  exact hdet

private theorem mem_u4Mhom_SU (h : UnitaryFieldData 2 f K) {c : ℕ}
    (hc : 3 ^ c ∣ 2 ^ f - 1) {lam : K} (hlam : lam + 1 ≠ 0)
    (hlamq : h.bar lam = lam⁻¹) (hlam0 : lam ≠ 0)
    (x : rootsOfUnity (3 ^ c) K × rootsOfUnity (3 ^ c) K) :
    u4Mhom lam hlam x ∈ StatedSU 4 (2 ^ f) K := by
  refine Subgroup.subset_closure ⟨det_u4M lam hlam x, ?_⟩
  rw [coe_u4Mhom]
  refine u4M_unitary h hlam hlamq hlam0 ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [u4Dhom, bar_eq_self_rootsOfUnity h hc, bar_inv_rootsOfUnity h hc]
  · simp [u4Dhom]
  · simp [u4Dhom]
  · simp [u4Dhom]
  · simp [u4Dhom]

omit [CharP K 2] in
private theorem u4M_apply_zero_one (lam : K) (v : Fin 4 → Kˣ) :
    (u4G lam * (torusDiag v : Matrix (Fin 4) (Fin 4) K) * u4Ginv lam) 0 1 =
      (lam + 1)⁻¹ * ((v 0 : K) + (v 1 : K)) := by
  rw [CFSG.SectionRank.ClassicalEven.coe_torusDiag]
  simp [u4G, u4Ginv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul_diagonal]
  ring

omit [CharP K 2] in
private theorem u4M_apply_two_three (lam : K) (v : Fin 4 → Kˣ) :
    (u4G lam * (torusDiag v : Matrix (Fin 4) (Fin 4) K) * u4Ginv lam) 2 3 =
      (lam + 1)⁻¹ * ((v 2 : K) + (v 3 : K)) := by
  rw [CFSG.SectionRank.ClassicalEven.coe_torusDiag]
  simp [u4G, u4Ginv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul_diagonal]
  ring

private theorem eq_one_of_add_inv_eq_zero {a : Kˣ} (h : (a : K) + (a : K)⁻¹ = 0) : a = 1 := by
  have ha0 : (a : K) ≠ 0 := Units.ne_zero a
  have hmul : (a : K) * ((a : K) + (a : K)⁻¹) = 0 := by rw [h, mul_zero]
  rw [mul_add, mul_inv_cancel₀ ha0] at hmul
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hx2 : (a : K) ^ 2 = 1 := by
    linear_combination hmul - h2
  have hzero : ((a : K) - 1) ^ 2 = 0 := by
    rw [sub_pow_char, hx2, one_pow, sub_self]
  have hzero' : ((a : K) - 1) * ((a : K) - 1) = 0 := by rwa [pow_two] at hzero
  exact Units.ext (sub_eq_zero.mp (mul_self_eq_zero.mp hzero'))

private noncomputable def u4projM (h : UnitaryFieldData 2 f K) {c : ℕ}
    (hc : 3 ^ c ∣ 2 ^ f - 1) {lam : K} (hlam : lam + 1 ≠ 0)
    (hlamq : h.bar lam = lam⁻¹) (hlam0 : lam ≠ 0) :
    (rootsOfUnity (3 ^ c) K × rootsOfUnity (3 ^ c) K) →*
      StatedProj (StatedSU 4 (2 ^ f) K) :=
  (projH _).comp ((u4Mhom lam hlam).codRestrict _
    (mem_u4Mhom_SU h hc hlam hlamq hlam0))

private theorem eq_one_of_u4projM_eq_one (h : UnitaryFieldData 2 f K) {c : ℕ}
    (hc : 3 ^ c ∣ 2 ^ f - 1) {lam : K} (hlam : lam + 1 ≠ 0)
    (hlamq : h.bar lam = lam⁻¹) (hlam0 : lam ≠ 0)
    (x : rootsOfUnity (3 ^ c) K × rootsOfUnity (3 ^ c) K)
    (hx : u4projM h hc hlam hlamq hlam0 x = 1) : x = 1 := by
  have hx' : projH _ ((u4Mhom lam hlam).codRestrict _
      (mem_u4Mhom_SU h hc hlam hlamq hlam0) x) = 1 := hx
  have hmem := (QuotientGroup.eq_one_iff _).mp hx'
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c0, hc0⟩ := MonoidHom.mem_range.mp hmem
  have h01 : ((u4Mhom lam hlam x : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) 0 1 = 0 := by
    have h := congrArg (fun g : GL (Fin 4) K =>
      ((g : Matrix (Fin 4) (Fin 4) K)) 0 1) hc0.symm
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using h
  have h23 : ((u4Mhom lam hlam x : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) 2 3 = 0 := by
    have h := congrArg (fun g : GL (Fin 4) K =>
      ((g : Matrix (Fin 4) (Fin 4) K)) 2 3) hc0.symm
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using h
  rw [coe_u4Mhom, u4M_apply_zero_one lam (u4Dhom c x)] at h01
  rw [coe_u4Mhom, u4M_apply_two_three lam (u4Dhom c x)] at h23
  have hcoef : (lam + 1)⁻¹ ≠ 0 := inv_ne_zero hlam
  have ha : (x.1 : Kˣ) = 1 := by
    apply eq_one_of_add_inv_eq_zero
    have hsum : ((u4Dhom c x) 0 : K) + ((u4Dhom c x) 1 : K) = 0 :=
      (mul_eq_zero.mp h01).resolve_left hcoef
    simpa [u4Dhom] using hsum
  have hb : (x.2 : Kˣ) = 1 := by
    apply eq_one_of_add_inv_eq_zero
    have hsum : ((u4Dhom c x) 2 : K) + ((u4Dhom c x) 3 : K) = 0 :=
      (mul_eq_zero.mp h23).resolve_left hcoef
    simpa [u4Dhom] using hsum
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

private theorem u4projM_injective (h : UnitaryFieldData 2 f K) {c : ℕ}
    (hc : 3 ^ c ∣ 2 ^ f - 1) {lam : K} (hlam : lam + 1 ≠ 0)
    (hlamq : h.bar lam = lam⁻¹) (hlam0 : lam ≠ 0) :
    Function.Injective (u4projM h hc hlam hlamq hlam0) := by
  intro x y hxy
  have h1 : u4projM h hc hlam hlamq hlam0 (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have h2 : x * y⁻¹ = 1 := eq_one_of_u4projM_eq_one h hc hlam hlamq hlam0 _ h1
  calc x = x * y⁻¹ * y := by group
    _ = 1 * y := by rw [h2]
    _ = y := one_mul y

private noncomputable def u4ThreePart (K : Type*) [Field K] : ℕ :=
  (Nat.card Kˣ).factorization 3

omit [CharP K 2] in
private theorem threePart_dvd_two_pow_sub_one (h : UnitaryFieldData 2 f K) (hf : Even f) :
    3 ^ u4ThreePart K ∣ 2 ^ f - 1 := by
  have h3dvd : 3 ∣ 2 ^ f - 1 := by
    obtain ⟨k, hk⟩ := hf
    have hmod : (2 : ℕ) ^ f ≡ 1 [MOD 3] := by
      rw [hk, show k + k = 2 * k by ring, pow_mul]
      have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by norm_num
      simpa using h4.pow k
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow f 2 (by norm_num))).mp hmod.symm
  have h3ndvd : ¬ 3 ∣ 2 ^ f + 1 := by
    intro hdiv
    have hsub := Nat.dvd_sub hdiv h3dvd
    have h2 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by
      have := Nat.one_le_pow f 2 (by norm_num); omega
    rw [h2] at hsub
    norm_num at hsub
  have hunits : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, h.card, show 2 * f = f * 2 by ring, pow_mul, ← Nat.sq_sub_sq,
      one_pow]
  have hp1 : 2 ^ f + 1 ≠ 0 := by positivity
  have hp2 : 2 ^ f - 1 ≠ 0 := by
    have h1 : 1 < 2 ^ f := by
      rcases Nat.eq_or_lt_of_le h.one_le with hf1 | hf2
      · subst hf1; norm_num
      · exact Nat.one_lt_pow (by omega : f ≠ 0) (by norm_num)
    exact Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt h1)
  have hfac : (Nat.card Kˣ).factorization 3 = (2 ^ f - 1).factorization 3 := by
    rw [hunits, Nat.factorization_mul hp1 hp2,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h3ndvd, zero_add]
  rw [u4ThreePart, hfac]
  exact Nat.ordProj_dvd (2 ^ f - 1) 3

omit [CharP K 2] in
private theorem card_rootsOfUnity_threePart (h : UnitaryFieldData 2 f K) :
    Nat.card (rootsOfUnity (3 ^ u4ThreePart K) K) = 3 ^ u4ThreePart K := by
  have : Finite K := h.finite
  rw [u4ThreePart, CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, ← Nat.card_units]
  exact Nat.gcd_eq_right (Nat.ordProj_dvd (Nat.card Kˣ) 3)

omit [CharP K 2] in
private theorem factorization_card_statedSU_four_threePart
    (h : UnitaryFieldData 2 f K) (hf : Even f) :
    (Nat.card (StatedProj (StatedSU 4 (2 ^ f) K))).factorization 3 =
      2 * u4ThreePart K := by
  classical
  set q := 2 ^ f with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow f 2 (by norm_num)
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
  have h3dvd : 3 ∣ q - 1 := by
    obtain ⟨k, hk⟩ := hf
    have hmod : q ≡ 1 [MOD 3] := by
      rw [hqdef, hk, show k + k = 2 * k by ring, pow_mul]
      have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by norm_num
      simpa using h4.pow k
    exact (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
  have hq3 : ¬ 3 ∣ q := by
    intro hd
    have hsub := Nat.dvd_sub hd h3dvd
    have h1 : q - (q - 1) = 1 := by omega
    rw [h1] at hsub
    norm_num at hsub
  have hq1' : ¬ 3 ∣ q + 1 := by
    intro hd
    have hsub := Nat.dvd_sub hd h3dvd
    have h2 : q + 1 - (q - 1) = 2 := by omega
    rw [h2] at hsub
    norm_num at hsub
  have hq2m1 : 3 ∣ q ^ 2 - 1 :=
    dvd_trans h3dvd (Nat.sub_one_dvd_pow_sub_one q 2)
  have hq3m1 : 3 ∣ q ^ 3 - 1 :=
    dvd_trans h3dvd (Nat.sub_one_dvd_pow_sub_one q 3)
  have hq2p1 : ¬ 3 ∣ q ^ 2 + 1 := by
    intro hd
    have hsub := Nat.dvd_sub hd hq2m1
    have h2 : q ^ 2 + 1 - (q ^ 2 - 1) = 2 := by
      have := Nat.one_le_pow 2 q (by omega); omega
    rw [h2] at hsub
    norm_num at hsub
  have hq3p1 : ¬ 3 ∣ q ^ 3 + 1 := by
    intro hd
    have hsub := Nat.dvd_sub hd hq3m1
    have h2 : q ^ 3 + 1 - (q ^ 3 - 1) = 2 := by
      have := Nat.one_le_pow 3 q (by omega); omega
    rw [h2] at hsub
    norm_num at hsub
  have hq6 : ¬ 3 ∣ q ^ 6 := fun hd => hq3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd)
  have hA : q ^ 6 ≠ 0 := by positivity
  have hB : q ^ 2 - 1 ≠ 0 := by
    have h : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hC : q ^ 3 + 1 ≠ 0 := by positivity
  have hD : q ^ 4 - 1 ≠ 0 := by
    have h : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have h4eq : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    have hpow : q ^ 4 = (q ^ 2) ^ 2 := by ring
    rw [hpow]
    calc (q ^ 2) ^ 2 - 1 = (q ^ 2) ^ 2 - 1 ^ 2 := by norm_num
      _ = (q ^ 2 + 1) * (q ^ 2 - 1) := Nat.sq_sub_sq _ _
      _ = (q ^ 2 - 1) * (q ^ 2 + 1) := by ring
  have h4fac : (q ^ 4 - 1).factorization 3 = (q ^ 2 - 1).factorization 3 := by
    rw [h4eq, Nat.factorization_mul hB (by positivity), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hq2p1, add_zero]
  have hunits : Nat.card Kˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, h.card, show 2 * f = f * 2 by ring, pow_mul, hqdef]
  rw [card_statedProj_statedSU_four h,
    Nat.factorization_mul (mul_ne_zero (mul_ne_zero hA hB) hC) hD, Finsupp.add_apply,
    Nat.factorization_mul (mul_ne_zero hA hB) hC, Finsupp.add_apply,
    Nat.factorization_mul hA hB, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hq6, zero_add,
    Nat.factorization_eq_zero_of_not_dvd hq3p1, add_zero, h4fac, u4ThreePart, hunits]
  ring

private theorem card_range_u4projM (h : UnitaryFieldData 2 f K) (hf : Even f) {lam : K}
    (hlam : lam + 1 ≠ 0) (hlamq : h.bar lam = lam⁻¹) (hlam0 : lam ≠ 0) :
    Nat.card (u4projM h (threePart_dvd_two_pow_sub_one h hf) hlam hlamq hlam0).range =
      3 ^ (2 * u4ThreePart K) := by
  have : Finite K := h.finite
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective
      (u4projM_injective h (threePart_dvd_two_pow_sub_one h hf) hlam hlamq hlam0),
    Subgroup.card_top, Nat.card_prod, card_rootsOfUnity_threePart h, ← pow_add]
  congr 1
  ring

omit [CharP K 2] in
private theorem u4TorusHom_apply (l : rootsOfUnity (2 ^ f + 1) K) :
    u4TorusHom ![l, l, l⁻¹] =
      projH (StatedSU 4 (2 ^ f) K) ⟨torusDiag ![l, l, l⁻¹, l⁻¹],
        by simpa [u4TorusEntries] using
          (torusDiag_u4TorusEntries_mem (f := f) (K := K) ![l, l, l⁻¹])⟩ := by
  simp only [u4TorusHom, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
  congr 2
  ext i
  fin_cases i <;> simp [u4TorusEntries]

private theorem commute_torusDiag_u4GL (l : rootsOfUnity (2 ^ f + 1) K) (lam : K)
    (hlam : lam + 1 ≠ 0) :
    Commute (torusDiag ![l, l, l⁻¹, l⁻¹]) (u4GL lam hlam) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u4GL, u4G, CFSG.SectionRank.ClassicalEven.coe_torusDiag, Matrix.mul_apply,
      Fin.sum_univ_four, mul_comm]

private theorem centralizes_u4TorusHom_u4projM (h : UnitaryFieldData 2 f K) {c : ℕ}
    (hc : 3 ^ c ∣ 2 ^ f - 1) {lam : K} (hlam : lam + 1 ≠ 0)
    (hlamq : h.bar lam = lam⁻¹) (hlam0 : lam ≠ 0) (l : rootsOfUnity (2 ^ f + 1) K)
    (x : rootsOfUnity (3 ^ c) K × rootsOfUnity (3 ^ c) K) :
    u4TorusHom ![l, l, l⁻¹] * u4projM h hc hlam hlamq hlam0 x =
      u4projM h hc hlam hlamq hlam0 x * u4TorusHom ![l, l, l⁻¹] := by
  let Λ : StatedSU 4 (2 ^ f) K := ⟨torusDiag ![l, l, l⁻¹, l⁻¹], by
    simpa [u4TorusEntries] using
      (torusDiag_u4TorusEntries_mem (f := f) (K := K) ![l, l, l⁻¹])⟩
  let M : StatedSU 4 (2 ^ f) K :=
    ⟨u4Mhom lam hlam x, mem_u4Mhom_SU h hc hlam hlamq hlam0 x⟩
  have hG : Commute (torusDiag ![l, l, l⁻¹, l⁻¹]) (u4GL lam hlam) :=
    commute_torusDiag_u4GL l lam hlam
  have hD : Commute (torusDiag ![l, l, l⁻¹, l⁻¹]) (torusDiag (u4Dhom c x)) := by
    show torusDiag ![l, l, l⁻¹, l⁻¹] * torusDiag (u4Dhom c x) =
      torusDiag (u4Dhom c x) * torusDiag ![l, l, l⁻¹, l⁻¹]
    rw [← map_mul, ← map_mul, mul_comm]
  have hM : Commute (torusDiag ![l, l, l⁻¹, l⁻¹])
      (u4Mhom lam hlam x) := by
    show Commute (torusDiag ![l, l, l⁻¹, l⁻¹])
      (u4GL lam hlam * torusDiag (u4Dhom c x) * (u4GL lam hlam)⁻¹)
    exact (hG.mul_right hD).mul_right hG.inv_right
  have ht : u4TorusHom ![l, l, l⁻¹] = projH _ Λ := u4TorusHom_apply l
  have hu : u4projM h hc hlam hlamq hlam0 x = projH _ M := rfl
  rw [ht, hu, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hM.eq

omit [CharP K 2] in
private theorem pow_eq_self_rootsOfUnity {c N : ℕ} (hc : 3 ^ c ∣ N - 1)
    (a : rootsOfUnity (3 ^ c) K) (hN : 1 ≤ N) :
    ((a : Kˣ) : K) ^ N = ((a : Kˣ) : K) := by
  have ha : ((a : Kˣ) : K) ^ (3 ^ c) = 1 := by
    have h1 := (mem_rootsOfUnity (3 ^ c) (a : Kˣ)).mp a.2
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    simpa [Units.val_pow_eq_pow_val] using h2
  obtain ⟨t, ht⟩ := hc
  have hN1 : N = 3 ^ c * t + 1 := by omega
  rw [hN1, pow_succ, pow_mul, ha, one_pow, one_mul]

omit [CharP K 2] in
private theorem sigma_pow_apply {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2) (m : ℕ) (x : K) :
    (σ ^ m) x = x ^ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    change σ ((σ ^ m) x) = x ^ 2 ^ (m + 1)
    rw [ih, hσ, ← pow_mul, ← pow_succ]

private theorem glAut_sigma_pow_u4Mhom {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) {c m : ℕ} (hc : 3 ^ c ∣ 2 ^ m - 1)
    {lam : K} (hlam : lam + 1 ≠ 0) (hlm : lam ^ 2 ^ m = lam)
    (x : rootsOfUnity (3 ^ c) K × rootsOfUnity (3 ^ c) K) :
    glAut (σ ^ m) (u4Mhom lam hlam x) = u4Mhom lam hlam x := by
  have hψlam : (⇑σ)^[m] lam = lam := by
    have h : (σ ^ m) lam = lam := by rw [sigma_pow_apply hσ m lam, hlm]
    simpa using h
  have hG : glAut (σ ^ m) (u4GL lam hlam) = u4GL lam hlam := by
    apply Units.ext
    rw [coe_glAut, coe_u4GL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u4G, hψlam]
  have hD : glAut (σ ^ m) (torusDiag (u4Dhom c x)) = torusDiag (u4Dhom c x) := by
    apply Units.ext
    rw [coe_glAut, CFSG.SectionRank.ClassicalEven.coe_torusDiag,
      Matrix.diagonal_map (map_zero (σ ^ m))]
    congr 1
    funext i
    fin_cases i <;>
      simp [u4Dhom, sigma_pow_apply hσ m,
        pow_eq_self_rootsOfUnity hc (x.1 : rootsOfUnity (3 ^ c) K)
          (Nat.one_le_pow m 2 (by norm_num)),
        pow_eq_self_rootsOfUnity hc (x.2 : rootsOfUnity (3 ^ c) K)
          (Nat.one_le_pow m 2 (by norm_num))]
  change glAut (σ ^ m) (u4GL lam hlam * torusDiag (u4Dhom c x) * (u4GL lam hlam)⁻¹) =
    u4GL lam hlam * torusDiag (u4Dhom c x) * (u4GL lam hlam)⁻¹
  rw [map_mul, map_mul, map_inv, hG, hD]

private theorem fix_u4projM (h : UnitaryFieldData 2 f K) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2) {c m : ℕ} (hc3 : 3 ^ c ∣ 2 ^ f - 1)
    (hm3 : 3 ^ c ∣ 2 ^ m - 1) {lam : K} (hlam : lam + 1 ≠ 0)
    (hlamq : h.bar lam = lam⁻¹) (hlam0 : lam ≠ 0) (hlm : lam ^ 2 ^ m = lam)
    (x : rootsOfUnity (3 ^ c) K × rootsOfUnity (3 ^ c) K) :
    (uFieldAut h (n := 4) (by norm_num) σ ^ m) (u4projM h hc3 hlam hlamq hlam0 x) =
      u4projM h hc3 hlam hlamq hlam0 x := by
  let M : StatedSU 4 (2 ^ f) K :=
    ⟨u4Mhom lam hlam x, mem_u4Mhom_SU h hc3 hlam hlamq hlam0 x⟩
  have hu : u4projM h hc3 hlam hlamq hlam0 x = projH _ M := rfl
  have hψ : uFieldAut h (n := 4) (by norm_num) σ ^ m =
      uFieldAut h (n := 4) (by norm_num) (σ ^ m) :=
    (map_pow (uFieldAut h (n := 4) (by norm_num)) σ m).symm
  rw [hψ, hu, uFieldAut_proj h (by norm_num) (σ ^ m) M]
  congr 1
  exact Subtype.ext (glAut_sigma_pow_u4Mhom hσ hm3 hlam hlm x)

end

theorem exists_sylow_three_u4_commute_fieldAut (h : UnitaryFieldData 2 f K) (hf : Even f)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2) {m : ℕ}
    (hm3 : 3 ^ (Nat.card Kˣ).factorization 3 ∣ 2 ^ m - 1)
    (l : rootsOfUnity (2 ^ f + 1) K) (hl : l ≠ 1) (hlm : ((l : Kˣ) : K) ^ 2 ^ m = ((l : Kˣ) : K)) :
    ∃ S : Subgroup (StatedProj (StatedSU 4 (2 ^ f) K)), IsPGroup 3 S ∧ ¬ 3 ∣ S.index ∧
      (∀ s ∈ S, u4TorusHom ![l, l, l⁻¹] * s = s * u4TorusHom ![l, l, l⁻¹]) ∧
      ∀ s ∈ S, (uFieldAut h (n := 4) (by norm_num) σ ^ m) s = s := by
  classical
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3c : 3 ^ u4ThreePart K ∣ 2 ^ f - 1 := threePart_dvd_two_pow_sub_one h hf
  let lam : K := ((l : Kˣ) : K)
  have hlpow : (l : Kˣ) ^ (2 ^ f + 1) = 1 :=
    (mem_rootsOfUnity (2 ^ f + 1) (l : Kˣ)).mp l.2
  have hlampow : lam ^ (2 ^ f + 1) = 1 := by
    have h1 := congrArg (fun u : Kˣ => (u : K)) hlpow
    simpa [lam, Units.val_pow_eq_pow_val] using h1
  have hlamq : h.bar lam = lam⁻¹ := by
    rw [h.bar_apply]
    have h2 := hlampow
    rw [pow_succ] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hlam0 : lam ≠ 0 := by
    intro h0
    have hpos : 2 ^ f + 1 ≠ 0 := by positivity
    rw [h0, zero_pow hpos] at hlampow
    exact zero_ne_one hlampow
  have hlamne : lam ≠ 1 := by
    intro h1
    exact hl (Subtype.ext (Units.ext h1))
  have hlam : lam + 1 ≠ 0 := by
    intro h0
    apply hlamne
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination h0 - h2
  let S : Subgroup (StatedProj (StatedSU 4 (2 ^ f) K)) :=
    (u4projM h h3c hlam hlamq hlam0).range
  have hcardS : Nat.card S =
      3 ^ (Nat.card (StatedProj (StatedSU 4 (2 ^ f) K))).factorization 3 := by
    rw [show S = (u4projM h h3c hlam hlamq hlam0).range from rfl,
      factorization_card_statedSU_four_threePart h hf,
      card_range_u4projM h hf hlam hlamq hlam0]
  let P : Sylow 3 (StatedProj (StatedSU 4 (2 ^ f) K)) := Sylow.ofCard S hcardS
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact P.isPGroup'
  · exact P.not_dvd_index
  · intro s hs
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hs
    exact centralizes_u4TorusHom_u4projM h h3c hlam hlamq hlam0 l x
  · intro s hs
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hs
    exact fix_u4projM h hσ h3c hm3 hlam hlamq hlam0 hlm x

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
