module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBruhat
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherReducedWord
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique
open scoped MatrixGroups
open Matrix

section SL2

variable {K : Type*} [Field K]

theorem eq_top_of_unip_ch615 {R : Subgroup SL(2, K)}
    (hU : ∀ t : K, SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t ∈ R)
    (hL : ∀ s : K, SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) s ∈ R) :
    R = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact hU c
  | 1, 0, _ => exact hL c
  | 1, 1, h => exact absurd rfl h

theorem not_isSolvable_sl2_ch615 (hK : ∃ s : Finset K, s.card = 4) :
    ¬ Group.IsSolvable SL(2, K) := by
  intro hsolv
  have hperf := CFSG.LinearGroups.special_linear_dimension_two_perfect hK
  have hnt : Nontrivial SL(2, K) := ⟨⟨1, SpecialLinearGroup.transvection
    (show (0 : Fin 2) ≠ 1 by decide) 1, fun h => by
      have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
      simp [SpecialLinearGroup.transvection_coe] at this⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := SL(2, K))).ne
    (Group.isPerfect_def.mp hperf)

theorem lowerLeft_eq_zero_of_isSolvable_ch615 (hK : ∃ s : Finset K, s.card = 4)
    {R : Subgroup SL(2, K)}
    (hU : ∀ t : K, SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t ∈ R)
    (hR : Group.IsSolvable ↥R) {g : SL(2, K)} (hg : g ∈ R) :
    (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  by_contra hc
  set a := (g : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) K) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) K) 1 0 with hcdef
  set d := (g : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
  have hdet : a * d - b * c = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hL : ∀ s : K, SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) s ∈ R := by
    intro s
    set u := SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (-a / c) with hu
    set v := SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (-s / c ^ 2) with hv
    have e : SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) s =
        u * g * v * g⁻¹ * u⁻¹ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hu, hv, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.single_apply,
          ← ha, ← hb, ← hcdef, ← hd] <;>
        field_simp <;>
        first | linear_combination (-c) * hdet | ring
    rw [e]
    have hu' : u ∈ R := hU _
    have hv' : v ∈ R := hU _
    exact R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem hu' hg) hv') (R.inv_mem hg)) (R.inv_mem hu')
  have htop := eq_top_of_unip_ch615 hU hL
  rw [htop] at hR
  exact not_isSolvable_sl2_ch615 hK (Group.isSolvable_of_surjective
    (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup SL(2, K)) ≃* _).toMonoidHom)
    (Subgroup.topEquiv).surjective)

@[expose] def unipSub_ch615 (K : Type*) [Field K] : Subgroup SL(2, K) where
  carrier := {g | ∃ t : K, g = SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t}
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    refine ⟨s + t, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.single_apply, add_comm]
  one_mem' := ⟨0, by rw [SpecialLinearGroup.transvection_coeff_zero]⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two]

theorem conj_mem_unipSub_ch615 {g : SL(2, K)} (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    {u : SL(2, K)} (hu : u ∈ unipSub_ch615 K) : g * u * g⁻¹ ∈ unipSub_ch615 K := by
  obtain ⟨t, rfl⟩ := hu
  have hdet : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at this
    exact this
  refine ⟨(g : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 * t, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.single_apply, hg] <;>
    first
      | linear_combination hdet
      | linear_combination t * (g : Matrix (Fin 2) (Fin 2) K) 0 0 * hdet
      | ring

theorem card_sl2_field_ch615 [Finite K] :
    Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card K with hq
  have hq2 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := K)
    rw [← Nat.card_eq_fintype_card] at this
    omega
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring,
    Nat.mul_div_cancel _ (by omega)]

theorem isSylowTwoOf_unipSub_ch615 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    IsSylowTwoOf (unipSub_ch615 K) ⊤ := by
  have hinj : Function.Injective fun t : K =>
      SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t := fun s t h => by
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simpa [SpecialLinearGroup.transvection_coe, Matrix.single_apply] using this
  have hcU : Nat.card (unipSub_ch615 K) = Nat.card K := by
    refine (Nat.card_congr (Equiv.ofBijective (fun t : K => (⟨_, t, rfl⟩ : unipSub_ch615 K))
      ⟨fun s t h => hinj (congrArg Subtype.val h), ?_⟩)).symm
    rintro ⟨_, t, rfl⟩
    exact ⟨t, rfl⟩
  have hn : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at this
    omega
  refine ⟨le_top, IsPGroup.of_card (n := n) (hcU.trans hK), fun h2 => ?_⟩
  change 2 ∣ (unipSub_ch615 K).relIndex ⊤ at h2
  rw [Subgroup.relIndex_top_right] at h2
  have hidx := (unipSub_ch615 K).card_mul_index
  rw [hcU, card_sl2_field_ch615] at hidx
  have hpos : 0 < Nat.card K := Nat.card_pos
  have heq : (unipSub_ch615 K).index = Nat.card K ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left hpos hidx
  rw [heq, hK] at h2
  have hev : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 hn) (by norm_num)
  have hpos2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

theorem borel_unipSub_ch615 (hK4 : ∃ s : Finset K, s.card = 4) {R : Subgroup SL(2, K)}
    (hUR : unipSub_ch615 K ≤ R) (hR : Group.IsSolvable ↥R) :
    ∀ r ∈ R, ∀ u ∈ unipSub_ch615 K, r * u * r⁻¹ ∈ unipSub_ch615 K := fun _ hr _ hu =>
  conj_mem_unipSub_ch615 (lowerLeft_eq_zero_of_isSolvable_ch615 hK4 (fun t => hUR ⟨t, rfl⟩) hR
    hr) hu

end SL2

section SL3

variable {K : Type*} [Field K]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def blkLoMat_ch615 (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, 1]

@[expose] def blkHiMat_ch615 (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, X 0 0, X 0 1; 0, X 1 0, X 1 1]

theorem blkLoMat_mul_ch615 (X Y : Matrix (Fin 2) (Fin 2) K) :
    blkLoMat_ch615 (X * Y) = blkLoMat_ch615 X * blkLoMat_ch615 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkLoMat_ch615, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blkHiMat_mul_ch615 (X Y : Matrix (Fin 2) (Fin 2) K) :
    blkHiMat_ch615 (X * Y) = blkHiMat_ch615 X * blkHiMat_ch615 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkHiMat_ch615, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blkLoMat_one_ch615 : blkLoMat_ch615 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkLoMat_ch615]

theorem blkHiMat_one_ch615 : blkHiMat_ch615 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkHiMat_ch615]

theorem det_blkLoMat_ch615 (X : Matrix (Fin 2) (Fin 2) K) : (blkLoMat_ch615 X).det = X.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blkLoMat_ch615]

theorem det_blkHiMat_ch615 (X : Matrix (Fin 2) (Fin 2) K) : (blkHiMat_ch615 X).det = X.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blkHiMat_ch615]

variable (K) in
@[expose] def blkLo_ch615 : SL(2, K) →* SL(3, K) where
  toFun A := ⟨blkLoMat_ch615 (A : Matrix (Fin 2) (Fin 2) K), (det_blkLoMat_ch615 _).trans A.2⟩
  map_one' := Subtype.ext blkLoMat_one_ch615
  map_mul' A B := Subtype.ext (blkLoMat_mul_ch615 (A : Matrix (Fin 2) (Fin 2) K) B)

variable (K) in
@[expose] def blkHi_ch615 : SL(2, K) →* SL(3, K) where
  toFun A := ⟨blkHiMat_ch615 (A : Matrix (Fin 2) (Fin 2) K), (det_blkHiMat_ch615 _).trans A.2⟩
  map_one' := Subtype.ext blkHiMat_one_ch615
  map_mul' A B := Subtype.ext (blkHiMat_mul_ch615 (A : Matrix (Fin 2) (Fin 2) K) B)

theorem coe_blkLo_ch615 (A : SL(2, K)) :
    ((blkLo_ch615 K A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      blkLoMat_ch615 (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem coe_blkHi_ch615 (A : SL(2, K)) :
    ((blkHi_ch615 K A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      blkHiMat_ch615 (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem blkLo_injective_ch615 : Function.Injective (blkLo_ch615 K) := fun A B h => by
  have h' := congrArg (fun M : SL(3, K) => (M : Matrix (Fin 3) (Fin 3) K)) h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [coe_blkLo_ch615, blkLoMat_ch615] using congrFun (congrFun h' 0) 0
  · simpa [coe_blkLo_ch615, blkLoMat_ch615] using congrFun (congrFun h' 0) 1
  · simpa [coe_blkLo_ch615, blkLoMat_ch615] using congrFun (congrFun h' 1) 0
  · simpa [coe_blkLo_ch615, blkLoMat_ch615] using congrFun (congrFun h' 1) 1

theorem blkHi_injective_ch615 : Function.Injective (blkHi_ch615 K) := fun A B h => by
  have h' := congrArg (fun M : SL(3, K) => (M : Matrix (Fin 3) (Fin 3) K)) h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [coe_blkHi_ch615, blkHiMat_ch615] using congrFun (congrFun h' 1) 1
  · simpa [coe_blkHi_ch615, blkHiMat_ch615] using congrFun (congrFun h' 1) 2
  · simpa [coe_blkHi_ch615, blkHiMat_ch615] using congrFun (congrFun h' 2) 1
  · simpa [coe_blkHi_ch615, blkHiMat_ch615] using congrFun (congrFun h' 2) 2

theorem blkLo_up_ch615 (t : K) :
    blkLo_ch615 K (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_blkLo_ch615, blkLoMat_ch615, SpecialLinearGroup.transvection_coe]

theorem blkLo_low_ch615 (t : K) :
    blkLo_ch615 K (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t) =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_blkLo_ch615, blkLoMat_ch615, SpecialLinearGroup.transvection_coe]

theorem blkHi_up_ch615 (t : K) :
    blkHi_ch615 K (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t) =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_blkHi_ch615, blkHiMat_ch615, SpecialLinearGroup.transvection_coe]

theorem blkHi_low_ch615 (t : K) :
    blkHi_ch615 K (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t) =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_blkHi_ch615, blkHiMat_ch615, SpecialLinearGroup.transvection_coe]

theorem false_of_blk_ch615 (hK : ∃ s : Finset K, s.card = 4) {φ : SL(2, K) →* SL(3, K)}
    (hφ : Function.Injective φ) {S : Subgroup SL(3, K)} (hS : Group.IsSolvable ↥S)
    (hU : ∀ t : K, φ (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t) ∈ S)
    (hL : ∀ t : K, φ (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t) ∈ S) :
    False := by
  have htop : S.comap φ = ⊤ := eq_top_of_unip_ch615 hU hL
  have hmem : ∀ A, φ A ∈ S := fun A => by
    have : A ∈ S.comap φ := htop ▸ Subgroup.mem_top A
    exact this
  let f : SL(2, K) →* ↥S := φ.codRestrict S hmem
  have hf : Function.Injective f := fun a b h => hφ (congrArg Subtype.val h)
  exact not_isSolvable_sl2_ch615 hK (Group.isSolvable_of_isSolvable_injective hf)

theorem conj_mem_unitriangular_ch615 {n : ℕ} {b u : SpecialLinearGroup (Fin n) K}
    (hb : b ∈ upperTriangular n K) (hu : u ∈ unitriangular n K) :
    b * u * b⁻¹ ∈ unitriangular n K := by
  have hb' := mem_upperTriangular_iff_isUpperTriangular.mp hb
  have huB := unitriangular_le_upperTriangular n K hu
  have hu' := mem_upperTriangular_iff_isUpperTriangular.mp huB
  have hbi := coe_inv_isUpperTriangular hb'
  refine ⟨(upperTriangular n K).mul_mem ((upperTriangular n K).mul_mem hb huB)
    ((upperTriangular n K).inv_mem hb), fun i => ?_⟩
  have e : ((b * u * b⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (b : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K) *
        ((b⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  refine (congrFun (congrFun e i) i).trans ?_
  rw [mul_apply_self_of_isUpperTriangular (hb'.mul hu') hbi,
    mul_apply_self_of_isUpperTriangular hb' hu', hu.2 i, mul_one]
  exact coe_inv_apply_self_of_isUpperTriangular hb' i

theorem signedPermutation_one_ch615 {n : ℕ} : signedPermutation n K 1 = 1 := by
  ext a b
  by_cases h : a = b <;>
    simp [h, signedPermutation, signedPermMatrix, permMatrix_apply]

theorem le_upperTriangular_of_isSolvable_ch615 (hK : ∃ s : Finset K, s.card = 4)
    {R : Subgroup SL(3, K)} (hUR : unitriangular 3 K ≤ R) (hR : Group.IsSolvable ↥R) :
    R ≤ upperTriangular 3 K := by
  intro g hg
  obtain ⟨w, hw⟩ := (triangular_bruhat (K := K) (n := 3)).1 g
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.mp hw
  set S : Subgroup SL(3, K) := R.comap (MulAut.conj b₁).toMonoidHom with hS
  have hmemS : ∀ h, h ∈ S ↔ b₁ * h * b₁⁻¹ ∈ R := fun h => Iff.rfl
  have hSsolv : Group.IsSolvable ↥S := by
    have := hR
    let f : ↥S →* ↥R :=
      ((MulAut.conj b₁).toMonoidHom.comp S.subtype).codRestrict R (fun x => x.2)
    exact Group.isSolvable_of_isSolvable_injective (f := f)
      (fun x y h => Subtype.ext ((MulAut.conj b₁).injective (congrArg Subtype.val h)))
  have hUS : ∀ u ∈ unitriangular 3 K, u ∈ S := fun u hu =>
    (hmemS u).mpr (hUR (conj_mem_unitriangular_ch615 hb₁ hu))
  have hb : b₂ * b₁ ∈ upperTriangular 3 K := (upperTriangular 3 K).mul_mem hb₂ hb₁
  have hwS : signedPermutation 3 K w * (b₂ * b₁) ∈ S := by
    rw [hmemS]
    convert hg using 1
    group
  have hconj : ∀ u ∈ unitriangular 3 K,
      signedPermutation 3 K w * u * (signedPermutation 3 K w)⁻¹ ∈ S := by
    intro u hu
    have h2 := conj_mem_unitriangular_ch615 ((upperTriangular 3 K).inv_mem hb) hu
    have := S.mul_mem (S.mul_mem hwS (hUS _ h2)) (S.inv_mem hwS)
    convert this using 1
    group
  obtain ⟨c, hc⟩ := isMonomial_signedPermMatrix (K := K) w
  rcases (by decide : ∀ w : Equiv.Perm (Fin 3), w = 1 ∨ w⁻¹ 1 < w⁻¹ 0 ∨ w⁻¹ 2 < w⁻¹ 1) w
    with hw1 | h01 | h12
  · rw [hw1, signedPermutation_one_ch615, mul_one]
    exact (upperTriangular 3 K).mul_mem hb₁ hb₂
  · exfalso
    have hL : ∀ s : K, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) s ∈ S := by
      intro s
      have h1 := hconj _ (transvection_mem_unitriangular h01
        ((c (w⁻¹ 0) : K) * (c (w⁻¹ 1) : K)⁻¹ * s))
      rw [monomial_conj_transvection (M := signedPermutation 3 K w) hc h01.ne] at h1
      convert h1 using 1
      apply Subtype.ext
      simp only [SpecialLinearGroup.transvection_coe, perm_apply_inv]
      congr 1
      field_simp [(c (w⁻¹ 0)).ne_zero, (c (w⁻¹ 1)).ne_zero]
    exact false_of_blk_ch615 hK blkLo_injective_ch615 hSsolv
      (fun t => by
        rw [blkLo_up_ch615]
        exact hUS _ (transvection_mem_unitriangular (by decide) t))
      (fun t => by rw [blkLo_low_ch615]; exact hL t)
  · exfalso
    have hL : ∀ s : K, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) s ∈ S := by
      intro s
      have h1 := hconj _ (transvection_mem_unitriangular h12
        ((c (w⁻¹ 1) : K) * (c (w⁻¹ 2) : K)⁻¹ * s))
      rw [monomial_conj_transvection (M := signedPermutation 3 K w) hc h12.ne] at h1
      convert h1 using 1
      apply Subtype.ext
      simp only [SpecialLinearGroup.transvection_coe, perm_apply_inv]
      congr 1
      field_simp [(c (w⁻¹ 1)).ne_zero, (c (w⁻¹ 2)).ne_zero]
    exact false_of_blk_ch615 hK blkHi_injective_ch615 hSsolv
      (fun t => by
        rw [blkHi_up_ch615]
        exact hUS _ (transvection_mem_unitriangular (by decide) t))
      (fun t => by rw [blkHi_low_ch615]; exact hL t)

theorem borel_unitriangular_ch615 (hK : ∃ s : Finset K, s.card = 4) {R : Subgroup SL(3, K)}
    (hUR : unitriangular 3 K ≤ R) (hR : Group.IsSolvable ↥R) :
    ∀ r ∈ R, ∀ u ∈ unitriangular 3 K, r * u * r⁻¹ ∈ unitriangular 3 K := fun _ hr _ hu =>
  conj_mem_unitriangular_ch615 (le_upperTriangular_of_isSolvable_ch615 hK hUR hR hr) hu

theorem isSylowTwoOf_unitriangular_ch615 [Finite K] {n m : ℕ} (hK : Nat.card K = 2 ^ m)
    (hn : 1 ≤ n) : IsSylowTwoOf (unitriangular n K) ⊤ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 hn
  refine ⟨le_top, hP ▸ P.isPGroup', fun h2 => ?_⟩
  change 2 ∣ (unitriangular n K).relIndex ⊤ at h2
  rw [Subgroup.relIndex_top_right, ← hP] at h2
  exact P.not_dvd_index h2

end SL3

end CFSG.Quasithin.H13
