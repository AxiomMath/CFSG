module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4Block

public section

namespace CFSG.Quasithin.H13.NQCat.LieThompson.Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (unitri inv_unitri isUnitriangular_unitri
  sym2 sym2_transpose eq_sym2 eq_unitri_of_isUnitriangular)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauMat tauMat_apply tauPair)

variable {F : Type} [Field F]

@[expose] def uMat (x c₀ c₁ c₂ : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![1, x; 0, 1] !![c₀ + x * c₁, c₁ + x * c₂; c₁, c₂] 0 !![1, 0; x, 1]

theorem blockMat_eq_uMat [CharP F 2] (x c₀ c₁ c₂ : F) :
    blockMat (unitri x) (sym2 c₀ c₁ c₂) = uMat x c₀ c₁ c₂ := by
  rw [blockMat, inv_unitri, uMat]
  refine fromBlocks_inj.2 ⟨rfl, ?_, rfl, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unitri, sym2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [unitri, CharTwo.neg_eq]

theorem exists_uMat [CharP F 2] {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F) :
    ∃ x c₀ c₁ c₂ : F, spMat u = uMat x c₀ c₁ c₂ := by
  obtain ⟨A, C, hA, hC, hu⟩ := hu
  refine ⟨A 0 1, C 0 0, C 0 1, C 1 1, ?_⟩
  have h1 : blockMat A C = blockMat (unitri (A 0 1)) (sym2 (C 0 0) (C 0 1) (C 1 1)) := by
    rw [← eq_unitri_of_isUnitriangular hA, ← eq_sym2 hC]
  rw [show spMat u = blockMat A C from hu, h1, blockMat_eq_uMat]

theorem mem_unipotent_of_uMat [CharP F 2] {g : StatedSp 2 F} {x c₀ c₁ c₂ : F}
    (h : spMat g = uMat x c₀ c₁ c₂) : g ∈ unipotent 2 F :=
  ⟨unitri x, sym2 c₀ c₁ c₂, isUnitriangular_unitri x, sym2_transpose c₀ c₁ c₂,
    h.trans (blockMat_eq_uMat x c₀ c₁ c₂).symm⟩

theorem uMat_mul [CharP F 2] (x c₀ c₁ c₂ y d₀ d₁ d₂ : F) :
    uMat x c₀ c₁ c₂ * uMat y d₀ d₁ d₂ =
      uMat (x + y) (c₀ + d₀ + y ^ 2 * c₂) (c₁ + d₁ + y * c₂) (c₂ + d₂) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [uMat, uMat, uMat, fromBlocks_multiply]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp <;>
    first
    | ring1
    | linear_combination (y ^ 2 * c₂) * h2
    | linear_combination (-(y ^ 2 * c₂)) * h2
    | linear_combination (y * c₂) * h2
    | linear_combination (-(y * c₂)) * h2

theorem spMat_torus_conj (t : Fin 2 → Fˣ) {g : StatedSp 2 F} {x c₀ c₁ c₂ : F}
    (h : spMat g = uMat x c₀ c₁ c₂) :
    spMat (torusHom t * g * (torusHom t)⁻¹) =
      uMat ((t 0 : F) * (t 1 : F)⁻¹ * x) ((t 0 : F) ^ 2 * c₀) ((t 0 : F) * (t 1 : F) * c₁)
        ((t 1 : F) ^ 2 * c₂) := by
  rw [← map_inv]
  change spMat (torusHom t) * spMat g * spMat (torusHom t⁻¹) = _
  rw [show spMat (torusHom t) = _ from coe_torusHom t,
    show spMat (torusHom t⁻¹) = _ from coe_torusHom t⁻¹, h]
  have h0 : (t 0 : F) ≠ 0 := (t 0).ne_zero
  have h1 : (t 1 : F) ≠ 0 := (t 1).ne_zero
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [uMat, Matrix.mul_apply, diagonal_apply] <;>
    field_simp

theorem spMat_fieldSp (σ : F ≃+* F) {g : StatedSp 2 F} {x c₀ c₁ c₂ : F}
    (h : spMat g = uMat x c₀ c₁ c₂) :
    spMat (fieldSp 2 F σ g) = uMat (σ x) (σ c₀) (σ c₁) (σ c₂) := by
  change (spMat g).map σ = _
  rw [h]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> simp [uMat]

theorem spMat_tauSp [CharP F 2] {g : StatedSp 2 F} {x c₀ c₁ c₂ : F}
    (h : spMat g = uMat x c₀ c₁ c₂) :
    spMat (tauSp g) = uMat c₂ (c₁ ^ 2 + x ^ 2 * c₂ ^ 2) (c₀ + x ^ 2 * c₂) (x ^ 2) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  change tauMat (spMat g) = _
  rw [h]
  ext r c
  rw [tauMat_apply]
  rcases r with r | r <;> rcases c with c | c <;> fin_cases r <;> fin_cases c <;>
    simp [tauPair, uMat] <;>
    first
    | ring1
    | linear_combination (c₁ ^ 2 + x ^ 2 * c₂ ^ 2) * h2
    | linear_combination (-(c₁ ^ 2 + x ^ 2 * c₂ ^ 2)) * h2
    | linear_combination (c₀ + x ^ 2 * c₂) * h2
    | linear_combination (-(c₀ + x ^ 2 * c₂)) * h2
    | linear_combination (x ^ 2 * c₂) * h2
    | linear_combination (-(x ^ 2 * c₂)) * h2
    | linear_combination c₂ * h2
    | linear_combination (-c₂) * h2

@[expose] def piA (g : StatedSp 2 F) : F := spMat g (Sum.inl 0) (Sum.inl 1)

@[expose] def piB (g : StatedSp 2 F) : F := spMat g (Sum.inl 1) (Sum.inr 1)

@[expose] def zC (g : StatedSp 2 F) : F := spMat g (Sum.inl 0) (Sum.inr 0)

@[expose] def zD (g : StatedSp 2 F) : F := spMat g (Sum.inl 0) (Sum.inr 1)

theorem piA_of {g : StatedSp 2 F} {x c₀ c₁ c₂ : F} (h : spMat g = uMat x c₀ c₁ c₂) :
    piA g = x := by
  simp [piA, h, uMat]

theorem piB_of {g : StatedSp 2 F} {x c₀ c₁ c₂ : F} (h : spMat g = uMat x c₀ c₁ c₂) :
    piB g = c₂ := by
  simp [piB, h, uMat]

theorem zC_of {g : StatedSp 2 F} {x c₀ c₁ c₂ : F} (h : spMat g = uMat x c₀ c₁ c₂) :
    zC g = c₀ + x * c₁ := by
  simp [zC, h, uMat]

theorem zD_of {g : StatedSp 2 F} {x c₀ c₁ c₂ : F} (h : spMat g = uMat x c₀ c₁ c₂) :
    zD g = c₁ + x * c₂ := by
  simp [zD, h, uMat]

theorem piA_one : piA (1 : StatedSp 2 F) = 0 := by
  simp [piA, spMat_one]

theorem piB_one : piB (1 : StatedSp 2 F) = 0 := by
  simp [piB, spMat_one]

variable [CharP F 2]

theorem piA_mul {u w : StatedSp 2 F} (hu : u ∈ unipotent 2 F) (hw : w ∈ unipotent 2 F) :
    piA (u * w) = piA u + piA w := by
  obtain ⟨x, c₀, c₁, c₂, hu'⟩ := exists_uMat hu
  obtain ⟨y, d₀, d₁, d₂, hw'⟩ := exists_uMat hw
  have h := (spMat_mul u w).trans (by rw [hu', hw', uMat_mul])
  rw [piA_of h, piA_of hu', piA_of hw']

theorem piB_mul {u w : StatedSp 2 F} (hu : u ∈ unipotent 2 F) (hw : w ∈ unipotent 2 F) :
    piB (u * w) = piB u + piB w := by
  obtain ⟨x, c₀, c₁, c₂, hu'⟩ := exists_uMat hu
  obtain ⟨y, d₀, d₁, d₂, hw'⟩ := exists_uMat hw
  have h := (spMat_mul u w).trans (by rw [hu', hw', uMat_mul])
  rw [piB_of h, piB_of hu', piB_of hw']

theorem piA_conj {u w : StatedSp 2 F} (hu : u ∈ unipotent 2 F) (hw : w ∈ unipotent 2 F) :
    piA (u * w * u⁻¹) = piA w := by
  have hui := inv_mem hu
  rw [piA_mul (mul_mem hu hw) hui, piA_mul hu hw]
  have h1 : piA u + piA u⁻¹ = 0 := by rw [← piA_mul hu hui, mul_inv_cancel, piA_one]
  linear_combination h1

theorem piB_conj {u w : StatedSp 2 F} (hu : u ∈ unipotent 2 F) (hw : w ∈ unipotent 2 F) :
    piB (u * w * u⁻¹) = piB w := by
  have hui := inv_mem hu
  rw [piB_mul (mul_mem hu hw) hui, piB_mul hu hw]
  have h1 : piB u + piB u⁻¹ = 0 := by rw [← piB_mul hu hui, mul_inv_cancel, piB_one]
  linear_combination h1

theorem spMat_eq_of_piA_eq_zero {z : StatedSp 2 F} (hz : z ∈ unipotent 2 F) (hA : piA z = 0)
    (hB : piB z = 0) : spMat z = uMat 0 (zC z) (zD z) 0 := by
  obtain ⟨x, c₀, c₁, c₂, hz'⟩ := exists_uMat hz
  rw [piA_of hz'] at hA
  rw [piB_of hz'] at hB
  subst hA hB
  rw [zC_of hz', zD_of hz', hz']
  simp

theorem mul_comm_of_piA_eq_zero {u z : StatedSp 2 F} (hu : u ∈ unipotent 2 F)
    (hz : z ∈ unipotent 2 F) (hA : piA z = 0) (hB : piB z = 0) : u * z = z * u := by
  obtain ⟨x, c₀, c₁, c₂, hu'⟩ := exists_uMat hu
  have hz' := spMat_eq_of_piA_eq_zero hz hA hB
  apply statedSp_ext
  change spMat u * spMat z = spMat z * spMat u
  rw [hu', hz', uMat_mul, uMat_mul]
  congr 1 <;> ring

theorem eq_of_zC_eq {z z' : StatedSp 2 F} (hz : z ∈ unipotent 2 F) (hz' : z' ∈ unipotent 2 F)
    (hA : piA z = 0) (hB : piB z = 0) (hA' : piA z' = 0) (hB' : piB z' = 0)
    (hC : zC z = zC z') (hD : zD z = zD z') : z = z' := by
  apply statedSp_ext
  change spMat z = spMat z'
  rw [spMat_eq_of_piA_eq_zero hz hA hB, spMat_eq_of_piA_eq_zero hz' hA' hB', hC, hD]

end CFSG.Quasithin.H13.NQCat.LieThompson.Sp4
