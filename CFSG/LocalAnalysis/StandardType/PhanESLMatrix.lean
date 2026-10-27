module

public import CFSG.LocalAnalysis.StandardType.PhanEStdSetting
public import CFSG.LocalAnalysis.StandardType.PhanELangAdjust
import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Steinberg
open scoped MatrixGroups

variable {Fld : Type} [Field Fld]

private theorem hmbMat_sl2Upper_eq_componentInitial (c : Fld) :
    sl2Upper (k := Fld) c = CFSG.LocalAnalysis.ComponentInitial.sl2Upper Fld c :=
  Subtype.ext rfl

private theorem hmbMat_sl2Lower_eq_componentInitial (c : Fld) :
    sl2Lower (k := Fld) c = CFSG.LocalAnalysis.ComponentInitial.sl2Lower Fld c :=
  Subtype.ext rfl

theorem sl2_hom_ext {G : Type*} [Group G] {φ ψ : SL(2, Fld) →* G}
    (hu : ∀ c, φ (sl2Upper c) = ψ (sl2Upper c)) (hl : ∀ c, φ (sl2Lower c) = ψ (sl2Lower c)) :
    φ = ψ := by
  have hgen : Subgroup.closure (Set.range (sl2Upper (k := Fld)) ∪
      Set.range (sl2Lower (k := Fld))) = ⊤ := by
    rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := Fld)]
    refine (Subgroup.closure_le _).2 ?_
    rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [← hmbMat_sl2Upper_eq_componentInitial]
      exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
    · rw [← hmbMat_sl2Lower_eq_componentInitial]
      exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  refine MonoidHom.eq_of_eqOn_dense hgen ?_
  rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact hu c
  · exact hl c

theorem sl3_hom_ext {G : Type*} [Group G] {φ ψ : SL(3, Fld) →* G}
    (h0 : φ.comp (WeakCT.blk Fld 0) = ψ.comp (WeakCT.blk Fld 0))
    (h1 : φ.comp (WeakCT.blk Fld 1) = ψ.comp (WeakCT.blk Fld 1)) : φ = ψ := by
  have h0' : ∀ A, φ (WeakCT.blk Fld 0 A) = ψ (WeakCT.blk Fld 0 A) :=
    fun A => DFunLike.congr_fun h0 A
  have h1' : ∀ A, φ (WeakCT.blk Fld 1 A) = ψ (WeakCT.blk Fld 1 A) :=
    fun A => DFunLike.congr_fun h1 A
  have htop : MonoidHom.eqLocus φ ψ = ⊤ := by
    rw [eq_top_iff, ← WeakCT.B12_sup_B23 (K := Fld)]
    refine sup_le ?_ ?_
    · rintro x ⟨A, rfl⟩
      exact h0' A
    · rintro x ⟨A, rfl⟩
      exact h1' A
  refine MonoidHom.ext fun x => ?_
  have hx : x ∈ MonoidHom.eqLocus φ ψ := by
    rw [htop]
    exact Subgroup.mem_top x
  exact hx

variable (θ : Fld →+* Fld)

theorem slSigma_sl2Upper (c : Fld) : slSigma θ 2 (sl2Upper c) = sl2Lower (-θ c) := by
  refine Subtype.ext ?_
  rw [coe_slSigma, coe_sl2Lower, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, coe_sl2Upper]

theorem slSigma_sl2Lower (c : Fld) : slSigma θ 2 (sl2Lower c) = sl2Upper (-θ c) := by
  refine Subtype.ext ?_
  rw [coe_slSigma, coe_sl2Upper, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, coe_sl2Lower]

theorem slSigma_torusHom (a : Fldˣ) :
    slSigma θ 2 (WeakCT.torusHom Fld a) = WeakCT.torusHom Fld (Units.map θ.toMonoidHom a)⁻¹ := by
  refine Subtype.ext ?_
  rw [coe_slSigma, WeakCT.coe_torusHom, Matrix.adjugate_fin_two, WeakCT.coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, WeakCT.coe_torusHom, Units.coe_map,
      Units.val_inv_eq_inv_val, map_inv₀]

private theorem hmbMat_slSigma_blk_zero (A : SL(2, Fld)) :
    slSigma θ 3 (WeakCT.blk Fld 0 A) = WeakCT.blk Fld 0 (slSigma θ 2 A) := by
  have hdetA : θ ((A : Matrix (Fin 2) (Fin 2) Fld) 0 0)
      * θ ((A : Matrix (Fin 2) (Fin 2) Fld) 1 1)
      - θ ((A : Matrix (Fin 2) (Fin 2) Fld) 1 0)
        * θ ((A : Matrix (Fin 2) (Fin 2) Fld) 0 1) = 1 := by
    have h := congrArg θ A.2
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, map_one] at h
    linear_combination h
  change slSigma θ 3 (WeakCT.blockSL Fld 3 2 0 (by omega) A) =
    WeakCT.blockSL Fld 3 2 0 (by omega) (slSigma θ 2 A)
  refine Subtype.ext ?_
  rw [coe_slSigma, WeakCT.coe_blockSL_three_zero, WeakCT.coe_blockSL_three_zero,
    coe_slSigma, Matrix.adjugate_fin_three, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, hdetA]

private theorem hmbMat_slSigma_blk_one (A : SL(2, Fld)) :
    slSigma θ 3 (WeakCT.blk Fld 1 A) = WeakCT.blk Fld 1 (slSigma θ 2 A) := by
  have hdetA : θ ((A : Matrix (Fin 2) (Fin 2) Fld) 0 0)
      * θ ((A : Matrix (Fin 2) (Fin 2) Fld) 1 1)
      - θ ((A : Matrix (Fin 2) (Fin 2) Fld) 1 0)
        * θ ((A : Matrix (Fin 2) (Fin 2) Fld) 0 1) = 1 := by
    have h := congrArg θ A.2
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, map_one] at h
    linear_combination h
  change slSigma θ 3 (WeakCT.blockSL Fld 3 2 1 (by omega) A) =
    WeakCT.blockSL Fld 3 2 1 (by omega) (slSigma θ 2 A)
  refine Subtype.ext ?_
  rw [coe_slSigma, WeakCT.coe_blockSL_three_one, WeakCT.coe_blockSL_three_one,
    coe_slSigma, Matrix.adjugate_fin_three, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, hdetA]

theorem slSigma_blk (s : Fin 2) (A : SL(2, Fld)) :
    slSigma θ 3 (WeakCT.blk Fld s A) = WeakCT.blk Fld s (slSigma θ 2 A) := by
  fin_cases s
  · exact hmbMat_slSigma_blk_zero θ A
  · exact hmbMat_slSigma_blk_one θ A

private theorem hmbMat_map_adjugate_transpose (hθ : ∀ c, θ (θ c) = c) {m : ℕ}
    (M : Matrix (Fin m) (Fin m) Fld) :
    (Matrix.adjugate (Matrix.transpose (M.map θ))).map θ
      = Matrix.adjugate (Matrix.transpose M) := by
  have h1 : (Matrix.adjugate (Matrix.transpose (M.map θ))).map θ
      = Matrix.adjugate ((Matrix.transpose (M.map θ)).map θ) := by
    rw [show (Matrix.adjugate (Matrix.transpose (M.map θ))).map θ
        = θ.mapMatrix (Matrix.adjugate (Matrix.transpose (M.map θ))) from rfl,
      RingHom.map_adjugate]
    rfl
  rw [h1]
  congr 1
  rw [Matrix.transpose_map, Matrix.map_map]
  have hcomp : (⇑θ ∘ ⇑θ) = id := funext hθ
  rw [hcomp, Matrix.map_id]

theorem slSigma_slSigma (hθ : ∀ c, θ (θ c) = c) (m : ℕ) (A : SL(m, Fld)) :
    slSigma θ m (slSigma θ m A) = A := by
  by_cases hm : m ≤ 1
  · haveI : Subsingleton (Fin m) := ⟨fun a b => Fin.ext (by
      have ha := a.isLt
      have hb := b.isLt
      omega)⟩
    exact Subsingleton.elim _ _
  · have hm2 : 2 ≤ m := by omega
    refine Subtype.ext ?_
    rw [coe_slSigma, coe_slSigma]
    rw [hmbMat_map_adjugate_transpose θ hθ]
    rw [Matrix.adjugate_transpose, Matrix.transpose_transpose]
    rw [Matrix.adjugate_adjugate _ (by rw [Fintype.card_fin]; omega), A.2, one_pow, one_smul]

variable (Fld) in
@[expose] def sl2Borel : Subgroup SL(2, Fld) where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) Fld) 1 0 = 0}
  mul_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hB]
  one_mem' := by simp
  inv_mem' {A} hA := by
    simp only [Set.mem_setOf_eq] at hA ⊢
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hA]

private theorem hmbMat_slSigma_apply_zero_one (Y : SL(2, Fld)) (hY : Y ∈ sl2Borel Fld) :
    ((slSigma θ 2 Y : SL(2, Fld)) : Matrix (Fin 2) (Fin 2) Fld) 0 1 = 0 := by
  have hY' : (Y : Matrix (Fin 2) (Fin 2) Fld) 1 0 = 0 := hY
  rw [coe_slSigma, Matrix.adjugate_fin_two]
  simp [Matrix.transpose_apply, Matrix.map_apply, hY']

private theorem hmbMat_mem_map_sl2Borel_iff (hθ : ∀ c, θ (θ c) = c) (A : SL(2, Fld)) :
    A ∈ (sl2Borel Fld).map (slSigma θ 2) ↔ (A : Matrix (Fin 2) (Fin 2) Fld) 0 1 = 0 := by
  constructor
  · intro hA
    obtain ⟨Y, hY, hYA⟩ := Subgroup.mem_map.mp hA
    rw [← hYA]
    exact hmbMat_slSigma_apply_zero_one θ Y hY
  · intro hA
    refine Subgroup.mem_map.mpr ⟨slSigma θ 2 A, ?_, ?_⟩
    · show (slSigma θ 2 A : Matrix (Fin 2) (Fin 2) Fld) 1 0 = 0
      rw [coe_slSigma, Matrix.adjugate_fin_two]
      simp [Matrix.transpose_apply, Matrix.map_apply, hA]
    · rw [slSigma_slSigma θ hθ 2]

theorem exists_mul_mem_slSU (hθ : ∀ c, θ (θ c) = c)
    (hnorm : ∀ s : Fld, s ≠ 0 → θ s = s → ∃ a : Fld, a * θ a = s) (A : SL(2, Fld))
    (hA : ((A⁻¹ * slSigma θ 2 A : SL(2, Fld)) : Matrix (Fin 2) (Fin 2) Fld) 1 1 ≠ 0) :
    ∃ b ∈ sl2Borel Fld, A * b ∈ slSU θ 2 := by
  have hBT : sl2Borel Fld ⊓ (sl2Borel Fld).map (slSigma θ 2) = (WeakCT.torusHom Fld).range := by
    ext X
    constructor
    · intro hX
      rw [Subgroup.mem_inf] at hX
      obtain ⟨hX1, hX2⟩ := hX
      have hX01 : (X : Matrix (Fin 2) (Fin 2) Fld) 0 1 = 0 :=
        (hmbMat_mem_map_sl2Borel_iff θ hθ X).mp hX2
      exact WeakCT.mem_diagTorus2_of_offDiag X hX01 hX1
    · intro hX
      obtain ⟨a, rfl⟩ := WeakCT.mem_diagTorus2_iff.mp hX
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · show (WeakCT.torusHom Fld a : Matrix (Fin 2) (Fin 2) Fld) 1 0 = 0
        simp [WeakCT.coe_torusHom]
      · refine (hmbMat_mem_map_sl2Borel_iff θ hθ (WeakCT.torusHom Fld a)).mpr ?_
        show (WeakCT.torusHom Fld a : Matrix (Fin 2) (Fin 2) Fld) 0 1 = 0
        simp [WeakCT.coe_torusHom]
  have hlang : ∀ s ∈ (WeakCT.torusHom Fld).range, slSigma θ 2 s = s⁻¹ →
      ∃ r ∈ (WeakCT.torusHom Fld).range, s = r * (slSigma θ 2 r)⁻¹ := by
    intro s hs hs_inv
    obtain ⟨a, rfl⟩ := hs
    have hfix : θ (a : Fld) = (a : Fld) := by
      have h := hs_inv
      rw [slSigma_torusHom] at h
      rw [map_inv] at h
      have h2 : Units.map θ.toMonoidHom a = a :=
        WeakCT.torusHom_injective (inv_injective h)
      simpa [Units.coe_map] using congrArg (fun u : Fldˣ => (u : Fld)) h2
    have ha_ne : (a : Fld) ≠ 0 := a.ne_zero
    obtain ⟨r0, hr0⟩ := hnorm (a : Fld) ha_ne hfix
    have hr0_ne : r0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hr0
      exact ha_ne hr0.symm
    refine ⟨WeakCT.torusHom Fld (Units.mk0 r0 hr0_ne), ⟨_, rfl⟩, ?_⟩
    simp only [slSigma_torusHom, map_inv, inv_inv]
    rw [← map_mul]
    congr 1
    refine Units.ext ?_
    simpa [Units.val_mul, Units.coe_map, Units.val_mk0] using hr0.symm
  have hfac : ∃ β ∈ sl2Borel Fld, ∃ γ ∈ (sl2Borel Fld).map (slSigma θ 2),
      A⁻¹ * slSigma θ 2 A = β * γ := by
    set M : SL(2, Fld) := A⁻¹ * slSigma θ 2 A with hM
    have hM11 : (M : Matrix (Fin 2) (Fin 2) Fld) 1 1 ≠ 0 := hA
    set d : Fld := (M : Matrix (Fin 2) (Fin 2) Fld) 1 1 with hd
    have hdne : d ≠ 0 := hM11
    let γ : SL(2, Fld) :=
      ⟨!![d⁻¹, 0; (M : Matrix (Fin 2) (Fin 2) Fld) 1 0, d], by
        rw [Matrix.det_fin_two_of]
        field_simp
        ring⟩
    let β : SL(2, Fld) := sl2Upper ((M : Matrix (Fin 2) (Fin 2) Fld) 0 1 / d)
    have hβB : β ∈ sl2Borel Fld := by
      show (β : Matrix (Fin 2) (Fin 2) Fld) 1 0 = 0
      simp [β, coe_sl2Upper]
    have hMdet : (M : Matrix (Fin 2) (Fin 2) Fld) 0 0 * d
        - (M : Matrix (Fin 2) (Fin 2) Fld) 0 1
          * (M : Matrix (Fin 2) (Fin 2) Fld) 1 0 = 1 := by
      have h : (M : Matrix (Fin 2) (Fin 2) Fld).det = 1 := M.2
      rw [Matrix.det_fin_two] at h
      rw [hd]
      exact h
    rw [hd] at hMdet
    have hβcoe : (β : Matrix (Fin 2) (Fin 2) Fld)
        = !![1, (M : Matrix (Fin 2) (Fin 2) Fld) 0 1 / d; 0, 1] := by
      simp [β, coe_sl2Upper]
    have hγcoe : (γ : Matrix (Fin 2) (Fin 2) Fld)
        = !![d⁻¹, 0; (M : Matrix (Fin 2) (Fin 2) Fld) 1 0, d] := rfl
    have hβγ : M = β * γ := by
      refine Subtype.ext ?_
      show (M : Matrix (Fin 2) (Fin 2) Fld) =
        (β : Matrix (Fin 2) (Fin 2) Fld) * (γ : Matrix (Fin 2) (Fin 2) Fld)
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hβcoe, hγcoe, Matrix.mul_apply, Fin.sum_univ_two]
      all_goals try field_simp
      · rw [hd]
        linear_combination hMdet
      · exact hd.symm
    have hγ : γ ∈ (sl2Borel Fld).map (slSigma θ 2) := by
      refine (hmbMat_mem_map_sl2Borel_iff θ hθ γ).mpr ?_
      simp [γ]
    exact ⟨β, hβB, γ, hγ, hβγ⟩
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := hfac
  obtain ⟨b, hb, hfix⟩ := exists_mul_mem_fix (slSigma θ 2) (slSigma_slSigma θ hθ 2)
    hBT hlang hβ hγ hβγ
  exact ⟨b, hb, (mem_slSU_iff θ 2 (A * b)).mpr hfix⟩

theorem sl2_eq_torusHom_of_normalizes (A : SL(2, Fld))
    (hu : ∀ c, ∃ d, A * sl2Upper c * A⁻¹ = sl2Upper d)
    (hl : ∀ c, ∃ d, A * sl2Lower c * A⁻¹ = sl2Lower d) :
    ∃ a : Fldˣ, A = WeakCT.torusHom Fld a := by
  have h10 : (A : Matrix (Fin 2) (Fin 2) Fld) 1 0 = 0 := by
    obtain ⟨d, hd⟩ := hu 1
    have hdA : A * sl2Upper 1 = sl2Upper d * A := by
      have h1 := congrArg (· * A) hd
      simpa [mul_assoc] using h1
    have hmat := congrArg (fun B : SL(2, Fld) => (B : Matrix (Fin 2) (Fin 2) Fld)) hdA
    have h := congrFun (congrFun hmat 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_sl2Upper] at h
    linear_combination h
  have h01 : (A : Matrix (Fin 2) (Fin 2) Fld) 0 1 = 0 := by
    obtain ⟨d, hd⟩ := hl 1
    have hdA : A * sl2Lower 1 = sl2Lower d * A := by
      have h1 := congrArg (· * A) hd
      simpa [mul_assoc] using h1
    have hmat := congrArg (fun B : SL(2, Fld) => (B : Matrix (Fin 2) (Fin 2) Fld)) hdA
    have h := congrFun (congrFun hmat 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_sl2Lower] at h
    linear_combination h
  have hdet : (A : Matrix (Fin 2) (Fin 2) Fld) 0 0 * (A : Matrix (Fin 2) (Fin 2) Fld) 1 1 = 1 := by
    have h : (A : Matrix (Fin 2) (Fin 2) Fld).det = 1 := A.2
    rw [Matrix.det_fin_two] at h
    simpa [h10, h01] using h
  refine ⟨Units.mk ((A : Matrix (Fin 2) (Fin 2) Fld) 0 0) ((A : Matrix (Fin 2) (Fin 2) Fld) 1 1)
    hdet (by rw [mul_comm]; exact hdet), ?_⟩
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [WeakCT.coe_torusHom, h10, h01]

private theorem hmbMat_apply_one_zero_of_normalizes (A : SL(3, Fld))
    (h : ∀ (s : Fin 2) (c : Fld),
      (∃ d, A * WeakCT.blk Fld s (sl2Upper c) * A⁻¹ = WeakCT.blk Fld s (sl2Upper d)) ∧
        ∃ d, A * WeakCT.blk Fld s (sl2Lower c) * A⁻¹ = WeakCT.blk Fld s (sl2Lower d)) :
    (A : Matrix (Fin 3) (Fin 3) Fld) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) Fld) 2 0 = 0 := by
  obtain ⟨d, hd⟩ := (h 0 1).1
  have hdA : A * WeakCT.blk Fld 0 (sl2Upper 1) = WeakCT.blk Fld 0 (sl2Upper d) * A := by
    have h1 := congrArg (· * A) hd
    simpa [mul_assoc] using h1
  have hmat := congrArg (fun B : SL(3, Fld) => (B : Matrix (Fin 3) (Fin 3) Fld)) hdA
  have h1 := congrFun (congrFun hmat 1) 1
  have h2 := congrFun (congrFun hmat 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, WeakCT.blk, WeakCT.coe_blockSL_three_zero,
    coe_sl2Upper] at h1 h2
  exact ⟨by linear_combination h1, by linear_combination h2⟩

private theorem hmbMat_apply_zero_one_of_normalizes (A : SL(3, Fld))
    (h : ∀ (s : Fin 2) (c : Fld),
      (∃ d, A * WeakCT.blk Fld s (sl2Upper c) * A⁻¹ = WeakCT.blk Fld s (sl2Upper d)) ∧
        ∃ d, A * WeakCT.blk Fld s (sl2Lower c) * A⁻¹ = WeakCT.blk Fld s (sl2Lower d)) :
    (A : Matrix (Fin 3) (Fin 3) Fld) 0 1 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) Fld) 2 1 = 0 := by
  obtain ⟨d, hd⟩ := (h 0 1).2
  have hdA : A * WeakCT.blk Fld 0 (sl2Lower 1) = WeakCT.blk Fld 0 (sl2Lower d) * A := by
    have h1 := congrArg (· * A) hd
    simpa [mul_assoc] using h1
  have hmat := congrArg (fun B : SL(3, Fld) => (B : Matrix (Fin 3) (Fin 3) Fld)) hdA
  have h0 := congrFun (congrFun hmat 0) 0
  have h2 := congrFun (congrFun hmat 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, WeakCT.blk, WeakCT.coe_blockSL_three_zero,
    coe_sl2Lower] at h0 h2
  exact ⟨by linear_combination h0, by linear_combination h2⟩

private theorem hmbMat_apply_zero_two_of_normalizes (A : SL(3, Fld))
    (h : ∀ (s : Fin 2) (c : Fld),
      (∃ d, A * WeakCT.blk Fld s (sl2Upper c) * A⁻¹ = WeakCT.blk Fld s (sl2Upper d)) ∧
        ∃ d, A * WeakCT.blk Fld s (sl2Lower c) * A⁻¹ = WeakCT.blk Fld s (sl2Lower d)) :
    (A : Matrix (Fin 3) (Fin 3) Fld) 0 2 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) Fld) 1 2 = 0 := by
  obtain ⟨d, hd⟩ := (h 1 1).2
  have hdA : A * WeakCT.blk Fld 1 (sl2Lower 1) = WeakCT.blk Fld 1 (sl2Lower d) * A := by
    have h1 := congrArg (· * A) hd
    simpa [mul_assoc] using h1
  have hmat := congrArg (fun B : SL(3, Fld) => (B : Matrix (Fin 3) (Fin 3) Fld)) hdA
  have h0 := congrFun (congrFun hmat 0) 1
  have h1 := congrFun (congrFun hmat 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, WeakCT.blk, WeakCT.coe_blockSL_three_one,
    coe_sl2Lower] at h0 h1
  exact ⟨by linear_combination h0, by linear_combination h1⟩

theorem sl3_eq_of_normalizes (A : SL(3, Fld))
    (h : ∀ (s : Fin 2) (c : Fld),
      (∃ d, A * WeakCT.blk Fld s (sl2Upper c) * A⁻¹ = WeakCT.blk Fld s (sl2Upper d)) ∧
        ∃ d, A * WeakCT.blk Fld s (sl2Lower c) * A⁻¹ = WeakCT.blk Fld s (sl2Lower d)) :
    ∃ a b : Fldˣ,
      A = WeakCT.blk Fld 0 (WeakCT.torusHom Fld a) * WeakCT.blk Fld 1 (WeakCT.torusHom Fld b) := by
  obtain ⟨h10, h20⟩ := hmbMat_apply_one_zero_of_normalizes A h
  obtain ⟨h01, h21⟩ := hmbMat_apply_zero_one_of_normalizes A h
  obtain ⟨h02, h12⟩ := hmbMat_apply_zero_two_of_normalizes A h
  have hdet : (A : Matrix (Fin 3) (Fin 3) Fld) 0 0 * (A : Matrix (Fin 3) (Fin 3) Fld) 1 1
      * (A : Matrix (Fin 3) (Fin 3) Fld) 2 2 = 1 := by
    have := A.2
    rw [Matrix.det_fin_three] at this
    simpa [h10, h20, h01, h21, h02, h12] using this
  have h22ne : (A : Matrix (Fin 3) (Fin 3) Fld) 2 2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨Units.mk ((A : Matrix (Fin 3) (Fin 3) Fld) 0 0)
      ((A : Matrix (Fin 3) (Fin 3) Fld) 1 1 * (A : Matrix (Fin 3) (Fin 3) Fld) 2 2)
      (by linear_combination hdet)
      (by linear_combination hdet), (Units.mk0 ((A : Matrix (Fin 3) (Fin 3) Fld) 2 2) h22ne)⁻¹, ?_⟩
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, WeakCT.blk, WeakCT.coe_blockSL_three_zero,
      WeakCT.coe_blockSL_three_one, WeakCT.coe_torusHom, Matrix.mul_apply, Fin.sum_univ_three,
      h10, h20, h01, h21, h02, h12, Units.val_inv_eq_inv_val, Units.val_mk0, mul_assoc,
      mul_inv_cancel₀ h22ne]

theorem sl2_eq_one_of_commute [CharP Fld 2] (A : SL(2, Fld)) (h : ∀ B : SL(2, Fld), Commute A B) :
    A = 1 := by
  have hcenter : A ∈ Subgroup.center SL(2, Fld) :=
    Subgroup.mem_center_iff.mpr fun B => (h B).symm
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    rcases sq_eq_one_iff.mp hr with h1 | h1
    · exact h1
    · rw [h1]
      exact CharTwo.neg_eq 1
  refine Subtype.ext ?_
  rw [← hA, hr1]
  exact map_one (Matrix.scalar (Fin 2))

theorem blk_zero_eq_blk_one {A B : SL(2, Fld)}
    (h : WeakCT.blk Fld 0 A = WeakCT.blk Fld 1 B) : A = 1 ∧ B = 1 := by
  have hmat := congrArg (fun g : SL(3, Fld) => (g : Matrix (Fin 3) (Fin 3) Fld)) h
  simp only [WeakCT.blk, WeakCT.coe_blockSL_three_zero, WeakCT.coe_blockSL_three_one] at hmat
  have hA00 : (A : Matrix (Fin 2) (Fin 2) Fld) 0 0 = 1 := by
    have := congrFun (congrFun hmat 0) 0
    simpa using this
  have hA01 : (A : Matrix (Fin 2) (Fin 2) Fld) 0 1 = 0 := by
    have := congrFun (congrFun hmat 0) 1
    simpa using this
  have hA10 : (A : Matrix (Fin 2) (Fin 2) Fld) 1 0 = 0 := by
    have := congrFun (congrFun hmat 1) 0
    simpa using this
  have hA11 : (A : Matrix (Fin 2) (Fin 2) Fld) 1 1 = 1 := by
    have h : (A : Matrix (Fin 2) (Fin 2) Fld).det = 1 := A.2
    rw [Matrix.det_fin_two] at h
    simpa [hA00, hA01, hA10] using h
  have hB00 : (B : Matrix (Fin 2) (Fin 2) Fld) 0 0 = 1 := by
    have h := congrFun (congrFun hmat 1) 1
    simp at h
    rw [← h, hA11]
  have hB01 : (B : Matrix (Fin 2) (Fin 2) Fld) 0 1 = 0 := by
    have h := congrFun (congrFun hmat 1) 2
    simp at h
    exact h.symm
  have hB10 : (B : Matrix (Fin 2) (Fin 2) Fld) 1 0 = 0 := by
    have h := congrFun (congrFun hmat 2) 1
    simp at h
    exact h.symm
  have hB11 : (B : Matrix (Fin 2) (Fin 2) Fld) 1 1 = 1 := by
    have h : (B : Matrix (Fin 2) (Fin 2) Fld).det = 1 := B.2
    rw [Matrix.det_fin_two] at h
    simpa [hB00, hB01, hB10] using h
  constructor
  · refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA00, hA01, hA10, hA11]
  · refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hB00, hB01, hB10, hB11]

end CFSG.ClassicalInvolution.Phan.PhanE
