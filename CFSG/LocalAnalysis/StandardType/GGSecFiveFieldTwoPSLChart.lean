module

public import CFSG.LocalAnalysis.StandardType.GGSelPSUChart
public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeTypeA
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelPSL
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.StandardType.FieldTwoPSL

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LieType.Steinberg (sl2Upper coe_sl2Upper)
open CFSG.StandardType.PsiDiagChar (sl2Diag coe_sl2Diag)
open CFSG.StandardType.RankOneXfer (sl2UpperUniSub mem_sl2UpperUniSub_iff)

@[expose] def sl2Coords (m : ℕ) (hm : 1 ≤ m) : Fin 2 → Fin (m + 1) :=
  ![⟨0, by omega⟩, ⟨1, by omega⟩]

private theorem sl2Coords_injective {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (sl2Coords m hm) := by
  intro r s h
  fin_cases r <;> fin_cases s <;> simp [sl2Coords] at h ⊢

private theorem sl2Coords_ne {m : ℕ} (hm : 1 ≤ m) :
    sl2Coords m hm 0 ≠ sl2Coords m hm 1 := by
  intro h
  have h' := congrArg Fin.val h
  simp [sl2Coords] at h'

private theorem mem_range_sl2Coords {m : ℕ} (hm : 1 ≤ m) {x : Fin (m + 1)} :
    x ∈ Set.range (sl2Coords m hm) ↔
      x = sl2Coords m hm 0 ∨ x = sl2Coords m hm 1 := by
  constructor
  · rintro ⟨r, rfl⟩
    fin_cases r <;> simp [sl2Coords]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

private def slChart {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m) :
    Matrix.SpecialLinearGroup (Fin 2) F →*
      Matrix.SpecialLinearGroup (Fin (m + 1)) F where
  toFun A :=
    ⟨SelectedRoot.SelPSU.embM (sl2Coords m hm) (A : Matrix (Fin 2) (Fin 2) F), by
      rw [SelectedRoot.SelPSU.det_embM (sl2Coords_injective hm), A.2]⟩
  map_one' := by
    ext i j
    change SelectedRoot.SelPSU.embM (sl2Coords m hm)
      (1 : Matrix (Fin 2) (Fin 2) F) i j =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j
    rw [SelectedRoot.SelPSU.embM_one]
  map_mul' A B := by
    ext i j
    change SelectedRoot.SelPSU.embM (sl2Coords m hm)
      ((A : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)) i j =
        (SelectedRoot.SelPSU.embM (sl2Coords m hm) (A : Matrix (Fin 2) (Fin 2) F) *
          SelectedRoot.SelPSU.embM (sl2Coords m hm) (B : Matrix (Fin 2) (Fin 2) F)) i j
    rw [SelectedRoot.SelPSU.embM_mul (sl2Coords_injective hm)]

private theorem slChart_injective {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (slChart (F := F) hm) := by
  intro A B h
  refine Matrix.SpecialLinearGroup.ext A B fun r s => ?_
  have h' := congrArg (fun g : Matrix.SpecialLinearGroup (Fin (m + 1)) F =>
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (sl2Coords m hm r)
      (sl2Coords m hm s)) h
  change SelectedRoot.SelPSU.embM (sl2Coords m hm)
      (A : Matrix (Fin 2) (Fin 2) F) (sl2Coords m hm r) (sl2Coords m hm s) =
    SelectedRoot.SelPSU.embM (sl2Coords m hm)
      (B : Matrix (Fin 2) (Fin 2) F) (sl2Coords m hm r) (sl2Coords m hm s) at h'
  rwa [SelectedRoot.SelPSU.embM_apply_image (sl2Coords_injective hm),
    SelectedRoot.SelPSU.embM_apply_image (sl2Coords_injective hm)] at h'

private theorem slChart_sl2Upper {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m) (t : F) :
    ((slChart (F := F) hm (sl2Upper t) : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (Matrix.SpecialLinearGroup.transvection (sl2Coords_ne hm) t :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  change SelectedRoot.SelPSU.embM (sl2Coords m hm)
      ((sl2Upper t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    Matrix.transvection (sl2Coords m hm 0) (sl2Coords m hm 1) t
  symm
  refine SelectedRoot.SelPSU.eq_embM_of_entries (sl2Coords_injective hm) _ _ ?_ ?_
  · intro r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.transvection, coe_sl2Upper, sl2Coords_ne hm, (sl2Coords_ne hm).symm]
  · intro x y hxy
    have hsingle : Matrix.single (sl2Coords m hm 0) (sl2Coords m hm 1) t x y = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨hx, hy⟩
      exact hxy ⟨(mem_range_sl2Coords hm).mpr (Or.inl hx.symm),
        (mem_range_sl2Coords hm).mpr (Or.inr hy.symm)⟩
    rw [Matrix.transvection, Matrix.add_apply, hsingle, add_zero]

private theorem slChart_sl2Upper_eq {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m) (t : F) :
    slChart (F := F) hm (sl2Upper t) =
      Matrix.SpecialLinearGroup.transvection (sl2Coords_ne hm) t :=
  Subtype.ext (slChart_sl2Upper hm t)

private def sl2DiagVec {F : Type} [Field F] (m : ℕ) (hm : 1 ≤ m) (a : Fˣ) :
    Fin (m + 1) → F :=
  Function.update (Function.update (1 : Fin (m + 1) → F) (sl2Coords m hm 0) (a : F))
    (sl2Coords m hm 1) ((a⁻¹ : Fˣ) : F)

private theorem sl2DiagVec_apply_zero {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m)
    (a : Fˣ) : sl2DiagVec m hm a (sl2Coords m hm 0) = (a : F) := by
  simp [sl2DiagVec, Function.update, sl2Coords_ne hm]

private theorem sl2DiagVec_apply_one {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m)
    (a : Fˣ) : sl2DiagVec m hm a (sl2Coords m hm 1) = ((a⁻¹ : Fˣ) : F) := by
  simp [sl2DiagVec, Function.update]

private theorem sl2DiagVec_apply_of_ne {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m)
    (a : Fˣ) {x : Fin (m + 1)} (hx0 : x ≠ sl2Coords m hm 0)
    (hx1 : x ≠ sl2Coords m hm 1) : sl2DiagVec m hm a x = 1 := by
  simp [sl2DiagVec, Function.update, hx0, hx1]

private theorem slChart_sl2Diag {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m) (a : Fˣ) :
    ((slChart (F := F) hm (sl2Diag a) : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal (sl2DiagVec m hm a) := by
  change SelectedRoot.SelPSU.embM (sl2Coords m hm)
      ((sl2Diag a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    Matrix.diagonal (sl2DiagVec m hm a)
  symm
  refine SelectedRoot.SelPSU.eq_embM_of_entries (sl2Coords_injective hm) _ _ ?_ ?_
  · intro r s
    fin_cases r <;> fin_cases s <;>
      simp [coe_sl2Diag, sl2DiagVec, Function.update, sl2Coords]
  · intro x y hxy
    by_cases hxy' : x = y
    · subst hxy'
      have hx0 : x ≠ sl2Coords m hm 0 := by
        intro h
        exact hxy ⟨(mem_range_sl2Coords hm).mpr (Or.inl h),
          (mem_range_sl2Coords hm).mpr (Or.inl h)⟩
      have hx1 : x ≠ sl2Coords m hm 1 := by
        intro h
        exact hxy ⟨(mem_range_sl2Coords hm).mpr (Or.inr h),
          (mem_range_sl2Coords hm).mpr (Or.inr h)⟩
      rw [Matrix.diagonal_apply_eq, sl2DiagVec_apply_of_ne hm a hx0 hx1]
      simp
    · rw [Matrix.diagonal_apply_ne _ hxy', Matrix.one_apply_ne hxy']

theorem exists_selectedModel_PSL_chart {F : Type} [Field F] {m : ℕ} (hm : 1 ≤ m) :
    ∃ (γ : Fin (SpecialLinear.rootDatum m F).rank → ℤ)
      (model : SelectedRoot.SelectedSL2Model (SpecialLinear.rootDatum m F) F γ),
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
        ((model.phi A : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
          SelectedRoot.SelPSU.embM (sl2Coords m hm) (A : Matrix (Fin 2) (Fin 2) F) := by
  let γ : Fin m → ℤ := Pi.single ⟨0, hm⟩ 1
  have hstd : SpecialLinear.toStd m γ =
      Pi.single (sl2Coords m hm 0) 1 - Pi.single (sl2Coords m hm 1) 1 := by
    simpa [γ, sl2Coords] using SpecialLinear.toStd_single m (⟨0, hm⟩ : Fin m)
  have hroot : SpecialLinear.rootGroup m F γ =
      SpecialLinear.rootSubgroup m F (sl2Coords_ne hm) :=
    SpecialLinear.rootGroup_eq m F (sl2Coords_ne hm) hstd
  have hupper : (sl2UpperUniSub F).map (slChart (F := F) hm) =
      SpecialLinear.rootGroup m F γ := by
    rw [hroot]
    refine le_antisymm ?_ ?_
    · intro g hg
      obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
      obtain ⟨t, rfl⟩ := mem_sl2UpperUniSub_iff.mp hA
      exact (SpecialLinear.mem_rootSubgroup (sl2Coords_ne hm) _).mpr
        ⟨t, Subtype.ext (slChart_sl2Upper hm t).symm⟩
    · intro g hg
      obtain ⟨t, ht⟩ := (SpecialLinear.mem_rootSubgroup (sl2Coords_ne hm) g).mp hg
      refine Subgroup.mem_map.mpr
        ⟨sl2Upper t, mem_sl2UpperUniSub_iff.mpr ⟨t, rfl⟩, ?_⟩
      rw [← ht]
      exact Subtype.ext (slChart_sl2Upper hm t)
  have hdiag : ∀ a : Fˣ, slChart (F := F) hm (sl2Diag a) ∈
      ggTorus (SpecialLinear.rootDatum m F) := by
    intro a
    refine HypSixTypeA.mem_ggTorus_of_diagonal (e := sl2DiagVec m hm a) ?_ ?_
    · intro l
      by_cases h0 : l = sl2Coords m hm 0
      · rw [h0, sl2DiagVec_apply_zero]
        exact Units.ne_zero a
      · by_cases h1 : l = sl2Coords m hm 1
        · rw [h1, sl2DiagVec_apply_one]
          simp
        · rw [sl2DiagVec_apply_of_ne hm a h0 h1]
          exact one_ne_zero
    · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, slChart_sl2Diag]
  have hscalar : ∀ h ∈ ggTorus (SpecialLinear.rootDatum m F),
      ∃ c : Fˣ, ∀ t : F,
        h * slChart (F := F) hm (sl2Upper t) * h⁻¹ =
          slChart (F := F) hm (sl2Upper ((c : F) * t)) := by
    intro h hh
    have hd := CompatA.isDiag_of_mem_ggTorus hm hh
    let e : Fin (m + 1) → F := Matrix.diag (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    have he : ∀ l, e l ≠ 0 := CompatA.diag_ne_zero hd
    have hhmat : ((Matrix.SpecialLinearGroup.toGL h : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal e := by
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact hd.diagonal_diag.symm
    refine ⟨Units.mk0 (e (sl2Coords m hm 0) * (e (sl2Coords m hm 1))⁻¹)
      (mul_ne_zero (he _) (inv_ne_zero (he _))), fun t => ?_⟩
    calc h * slChart (F := F) hm (sl2Upper t) * h⁻¹
        = h * Matrix.SpecialLinearGroup.transvection (sl2Coords_ne hm) t * h⁻¹ := by
          rw [slChart_sl2Upper_eq]
      _ = Matrix.SpecialLinearGroup.transvection (sl2Coords_ne hm)
            (e (sl2Coords m hm 0) * t * (e (sl2Coords m hm 1))⁻¹) :=
          HypSixTypeA.sl_diag_conj_transvection he hhmat (sl2Coords_ne hm) t
      _ = slChart (F := F) hm
            (sl2Upper ((Units.mk0 (e (sl2Coords m hm 0) *
              (e (sl2Coords m hm 1))⁻¹) (mul_ne_zero (he _) (inv_ne_zero (he _))) : F) * t)) := by
          rw [slChart_sl2Upper_eq]
          congr 1
          simp only [Units.val_mk0]
          ring
  refine ⟨γ, ⟨?_, slChart (F := F) hm, slChart_injective hm, hupper, hdiag, hscalar⟩, ?_⟩
  · change γ ∈ CFSG.LieType.RootSystem.roots (SpecialLinear.isFiniteType_A m) ∅
    rw [SpecialLinear.roots_eq]
    exact ⟨sl2Coords m hm 0, sl2Coords m hm 1, sl2Coords_ne hm, hstd⟩
  · intro A
    rfl


private def permMat {F : Type} [Field F] {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if j = π.symm i then 1 else 0

private theorem permMat_mul_apply {F : Type} [Field F] {n : ℕ} (π : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) F) (i j) :
    (permMat (F := F) π * M) i j = M (π.symm i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π.symm i)]
  · simp [permMat]
  · intro b _ hb
    rw [permMat, Matrix.of_apply, if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem mul_permMat_apply {F : Type} [Field F] {n : ℕ} (π : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) F) (i j) :
    (M * permMat (F := F) π.symm) i j = M i (π.symm j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π.symm j)]
  · simp [permMat]
  · intro b _ hb
    rw [permMat, Matrix.of_apply, Equiv.symm_symm,
      if_neg (fun h : j = π b => hb (by rw [h, Equiv.symm_apply_apply])), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem permMat_mul_permMat_symm {F : Type} [Field F] {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    permMat (F := F) π * permMat (F := F) π.symm = 1 := by
  ext i j
  rw [permMat_mul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [permMat]
  · rw [if_neg hij, permMat, Matrix.of_apply, if_neg]
    intro h
    exact hij (by simpa [Equiv.symm_symm] using h.symm)

private theorem permMat_conj {F : Type} [Field F] {n : ℕ} (π : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) F) :
    permMat (F := F) π * M * permMat (F := F) π.symm =
      M.submatrix π.symm π.symm := by
  ext i j
  rw [Matrix.mul_assoc, permMat_mul_apply, mul_permMat_apply, Matrix.submatrix_apply]

private theorem embM_submatrix_perm {F : Type} [Field F] {n : ℕ} (π : Equiv.Perm (Fin n))
    (ι : Fin 2 → Fin n) (hι : Function.Injective ι) (B : Matrix (Fin 2) (Fin 2) F) :
    (SelectedRoot.SelPSU.embM ι B).submatrix π.symm π.symm =
      SelectedRoot.SelPSU.embM (π ∘ ι) B := by
  refine SelectedRoot.SelPSU.eq_embM_of_entries (F := F) (π.injective.comp hι) _ _ ?_ ?_
  · intro r s
    rw [Matrix.submatrix_apply, Function.comp_apply, Function.comp_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      SelectedRoot.SelPSU.embM_apply_image (F := F) hι B r s]
  · intro x y hxy
    have hxy' : ¬(π.symm x ∈ Set.range ι ∧ π.symm y ∈ Set.range ι) := by
      rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      apply hxy
      exact ⟨⟨r, by rw [Function.comp_apply, hr, Equiv.apply_symm_apply]⟩,
        ⟨s, by rw [Function.comp_apply, hs, Equiv.apply_symm_apply]⟩⟩
    rw [Matrix.submatrix_apply, SelectedRoot.SelPSU.embM_apply_of_not_mem (F := F) B hxy']
    by_cases hxy'' : x = y
    · subst hxy''
      simp
    · rw [Matrix.one_apply_ne hxy'']
      rw [Matrix.one_apply_ne (fun h => hxy'' (π.symm.injective h))]

private theorem reindex_fromBlocks_embM {F : Type} [Field F] {m r r' : ℕ}
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)) (ι : Fin 2 → Fin r)
    (hι : Function.Injective ι) (B : Matrix (Fin 2) (Fin 2) F) :
    Matrix.reindex eidx eidx
      (Matrix.fromBlocks (SelectedRoot.SelPSU.embM ι B)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (1 : Matrix (Fin r') (Fin r') F)) =
      SelectedRoot.SelPSU.embM (fun t => eidx (Sum.inl (ι t))) B := by
  have hι' : Function.Injective (fun t => eidx (Sum.inl (ι t))) :=
    fun a b h => hι (Sum.inl.inj (eidx.injective h))
  refine SelectedRoot.SelPSU.eq_embM_of_entries (F := F) hι' _ _ ?_ ?_
  · intro a b
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
      SelectedRoot.SelPSU.embM_apply_image (F := F) hι B a b]
  · intro x y hxy
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases hu : eidx.symm x with p | p <;> rcases hv : eidx.symm y with q | q
    · have hx : x = eidx (Sum.inl p) := by
        rw [← Equiv.apply_symm_apply eidx x, hu]
      have hy : y = eidx (Sum.inl q) := by
        rw [← Equiv.apply_symm_apply eidx y, hv]
      have hpq : ¬(p ∈ Set.range ι ∧ q ∈ Set.range ι) := by
        rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
        exact hxy ⟨⟨a, hx.symm⟩, ⟨b, hy.symm⟩⟩
      rw [hx, hy, Matrix.fromBlocks_apply₁₁,
        SelectedRoot.SelPSU.embM_apply_of_not_mem (F := F) B hpq]
      by_cases hpq' : p = q
      · subst hpq'
        simp
      · rw [Matrix.one_apply_ne hpq']
        rw [Matrix.one_apply_ne (fun h => hpq' (Sum.inl.inj (eidx.injective h)))]
    · have hx : x = eidx (Sum.inl p) := by
        rw [← Equiv.apply_symm_apply eidx x, hu]
      have hy : y = eidx (Sum.inr q) := by
        rw [← Equiv.apply_symm_apply eidx y, hv]
      rw [hx, hy, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      rw [Matrix.one_apply_ne (by simp)]
    · have hx : x = eidx (Sum.inr p) := by
        rw [← Equiv.apply_symm_apply eidx x, hu]
      have hy : y = eidx (Sum.inl q) := by
        rw [← Equiv.apply_symm_apply eidx y, hv]
      rw [hx, hy, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [Matrix.one_apply_ne (by simp)]
    · have hx : x = eidx (Sum.inr p) := by
        rw [← Equiv.apply_symm_apply eidx x, hu]
      have hy : y = eidx (Sum.inr q) := by
        rw [← Equiv.apply_symm_apply eidx y, hv]
      rw [hx, hy, Matrix.fromBlocks_apply₂₂]
      by_cases hpq' : p = q
      · subst hpq'
        simp
      · rw [Matrix.one_apply_ne hpq']
        rw [Matrix.one_apply_ne (fun h => hpq' (Sum.inr.inj (eidx.injective h)))]

private theorem diagonal_embM_comm {F : Type} [Field F] {n : ℕ} (ι : Fin 2 → Fin n)
    (hι : Function.Injective ι) (e : Fin n → F) (B : Matrix (Fin 2) (Fin 2) F)
    (h0 : e (ι 0) = 1) (h1 : e (ι 1) = 1) :
    Matrix.diagonal e * SelectedRoot.SelPSU.embM ι B =
      SelectedRoot.SelPSU.embM ι B * Matrix.diagonal e := by
  ext x y
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨r, rfl⟩ := hx
    by_cases hy : y ∈ Set.range ι
    · obtain ⟨s, rfl⟩ := hy
      have hr : e (ι r) = 1 := by
        fin_cases r
        · exact h0
        · exact h1
      have hs : e (ι s) = 1 := by
        fin_cases s
        · exact h0
        · exact h1
      rw [SelectedRoot.SelPSU.embM_apply_image (F := F) hι B r s, hr, hs]
      simp
    · have hxy : ¬(ι r ∈ Set.range ι ∧ y ∈ Set.range ι) := fun h => hy h.2
      rw [SelectedRoot.SelPSU.embM_apply_of_not_mem (F := F) B hxy]
      have hne : ι r ≠ y := fun h => hy (h ▸ Set.mem_range_self r)
      rw [Matrix.one_apply_ne hne]
      simp
  · have hxy : ¬(x ∈ Set.range ι ∧ y ∈ Set.range ι) := fun h => hx h.1
    rw [SelectedRoot.SelPSU.embM_apply_of_not_mem (F := F) B hxy]
    by_cases hxy' : x = y
    · subst hxy'
      simp
    · rw [Matrix.one_apply_ne hxy']
      simp

theorem exists_conj_embM_eq_embedMat {F : Type} [Field F] {m r r' : ℕ} (hm : 2 ≤ m)
    (hr : 2 ≤ r) (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1))
    (P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1) :
    ∃ u : Matrix.SpecialLinearGroup (Fin (m + 1)) F, ∀ B : Matrix (Fin 2) (Fin 2) F,
      (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          SelectedRoot.SelPSU.embM (sl2Coords m (by omega)) B *
          ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        bmPSL_embedMat eidx P Pinv
          (SelectedRoot.SelPSU.embM (n := r)
            ![⟨0, by omega⟩, ⟨1, by omega⟩] B) := by
  classical
  let ιr : Fin 2 → Fin r := ![⟨0, by omega⟩, ⟨1, by omega⟩]
  let i0 : Fin r := ιr 0
  let i1 : Fin r := ιr 1
  have hi01 : i0 ≠ i1 := by
    intro h
    have h' := congrArg Fin.val h
    simp [i0, i1, ιr] at h'
  let a : Fin (m + 1) := eidx (Sum.inl i0)
  let b : Fin (m + 1) := eidx (Sum.inl i1)
  have hab : a ≠ b := by
    intro h
    exact hi01 (Sum.inl.inj (eidx.injective h))
  let zeroN : Fin (m + 1) := ⟨0, by omega⟩
  let oneN : Fin (m + 1) := ⟨1, by omega⟩
  have hzero_one : zeroN ≠ oneN := by
    intro h
    have h' := congrArg Fin.val h
    simp [zeroN, oneN] at h'
  let π : Equiv.Perm (Fin (m + 1)) :=
    Equiv.swap a zeroN * Equiv.swap oneN (Equiv.swap a zeroN b)
  let c : Fin (m + 1) := ⟨2, by omega⟩
  have hcb : Equiv.swap a zeroN b ≠ zeroN := by
    intro h
    have hba : b = a := by
      have h' := Equiv.swap_apply_eq_iff.mp h
      simpa using h'
    exact hab hba.symm
  have hπ0 : π zeroN = a := by
    show Equiv.swap a zeroN (Equiv.swap oneN (Equiv.swap a zeroN b) zeroN) = a
    rw [Equiv.swap_apply_of_ne_of_ne hzero_one hcb.symm, Equiv.swap_apply_right]
  have hπ1 : π oneN = b := by
    show Equiv.swap a zeroN (Equiv.swap oneN (Equiv.swap a zeroN b) oneN) = b
    rw [Equiv.swap_apply_left, Equiv.swap_apply_self]
  have hπcomp : π ∘ sl2Coords m (by omega) =
      fun t => eidx (Sum.inl (ιr t)) := by
    funext t
    fin_cases t
    · simpa [sl2Coords, zeroN, i0, ιr, a] using hπ0
    · simpa [sl2Coords, oneN, i1, ιr, b] using hπ1
  have hιr : Function.Injective ιr := by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp [ιr] at h ⊢
  let Q : Matrix (Fin (m + 1)) (Fin (m + 1)) F := permMat π
  let Qinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F := permMat π.symm
  have hQ : Q * Qinv = 1 := by
    change permMat π * permMat π.symm = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    exact permMat_mul_permMat_symm (F := F) π
  have hdetPinv : Pinv.det ≠ 0 := by
    have h := congrArg Matrix.det hPP
    rw [Matrix.det_mul, Matrix.det_one] at h
    intro h0
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  have hdetQ : Q.det ≠ 0 := by
    have h := congrArg Matrix.det hQ
    rw [Matrix.det_mul, Matrix.det_one] at h
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  let d : F := Pinv.det * Q.det
  have hd : d ≠ 0 := mul_ne_zero hdetPinv hdetQ
  let e : Fin (m + 1) → F := Function.update (1 : Fin (m + 1) → F) c d⁻¹
  have he : ∀ i, e i ≠ 0 := by
    intro i
    by_cases hi : i = c
    · subst hi
      rw [show e c = d⁻¹ by simp [e]]
      exact inv_ne_zero hd
    · rw [show e i = 1 by simp [e, hi]]
      exact one_ne_zero
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.diagonal e
  let Dinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    Matrix.diagonal (fun i => (e i)⁻¹)
  have hD : D * Dinv = 1 := by
    ext x y
    change (Matrix.diagonal e * Matrix.diagonal (fun i => (e i)⁻¹)) x y =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) x y
    rw [Matrix.diagonal_mul]
    by_cases hxy : x = y
    · subst hxy
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, mul_inv_cancel₀ (he x)]
    · rw [Matrix.diagonal_apply_ne _ hxy, mul_zero, Matrix.one_apply_ne hxy]
  have hdetD : D.det = d⁻¹ := by
    change (Matrix.diagonal e).det = d⁻¹
    rw [Matrix.det_diagonal, Finset.prod_eq_single c]
    · simp [e]
    · intro b _ hbc
      simp [e, hbc]
    · intro h
      exact absurd (Finset.mem_univ c) h
  let uMat : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Pinv * Q * D
  have hdetu : uMat.det = 1 := by
    change (Pinv * Q * D).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, hdetD]
    change Pinv.det * Q.det * d⁻¹ = 1
    rw [show Pinv.det * Q.det = d from rfl, mul_inv_cancel₀ hd]
  have hX : uMat * (Dinv * Qinv * P) = 1 := by
    change Pinv * Q * D * (Dinv * Qinv * P) = 1
    calc Pinv * Q * D * (Dinv * Qinv * P)
        = Pinv * Q * (D * Dinv) * (Qinv * P) := by noncomm_ring
      _ = Pinv * Q * 1 * (Qinv * P) := by rw [hD]
      _ = Pinv * (Q * Qinv) * P := by noncomm_ring
      _ = Pinv * 1 * P := by rw [hQ]
      _ = 1 := by rw [Matrix.mul_one, hPinvP]
  have hAdjMul : uMat * Matrix.adjugate uMat = 1 := by
    have h := Matrix.mul_adjugate uMat
    rw [hdetu, one_smul] at h
    exact h
  have hAdj : Matrix.adjugate uMat = Dinv * Qinv * P :=
    (Matrix.right_inv_eq_right_inv hX hAdjMul).symm
  let u : Matrix.SpecialLinearGroup (Fin (m + 1)) F := ⟨uMat, hdetu⟩
  refine ⟨u, fun B => ?_⟩
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    SelectedRoot.SelPSU.embM (sl2Coords m (by omega)) B
  have hc0 : sl2Coords m (by omega) 0 ≠ c := by
    intro h
    have h' := congrArg Fin.val h
    simp [sl2Coords, c] at h'
  have hc1 : sl2Coords m (by omega) 1 ≠ c := by
    intro h
    have h' := congrArg Fin.val h
    simp [sl2Coords, c] at h'
  have hcommD : D * M = M * D := by
    change Matrix.diagonal e * SelectedRoot.SelPSU.embM (sl2Coords m (by omega)) B =
      SelectedRoot.SelPSU.embM (sl2Coords m (by omega)) B * Matrix.diagonal e
    apply diagonal_embM_comm (sl2Coords m (by omega))
      (sl2Coords_injective (by omega)) e B
    · simp [e, hc0]
    · simp [e, hc1]
  have hDcomm : D * M * Dinv = M := by
    rw [hcommD, Matrix.mul_assoc, hD, Matrix.mul_one]
  have hconjQ : Q * M * Qinv =
      SelectedRoot.SelPSU.embM (fun t => eidx (Sum.inl (ιr t))) B := by
    change permMat π * M * permMat π.symm = _
    rw [permMat_conj (F := F) π M,
      embM_submatrix_perm π (sl2Coords m (by omega)) (sl2Coords_injective (by omega)) B,
      hπcomp]
  have hreindex : SelectedRoot.SelPSU.embM (fun t => eidx (Sum.inl (ιr t))) B =
      Matrix.reindex eidx eidx (Matrix.fromBlocks (SelectedRoot.SelPSU.embM ιr B)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (1 : Matrix (Fin r') (Fin r') F)) :=
    (reindex_fromBlocks_embM eidx ιr hιr B).symm
  rw [Matrix.SpecialLinearGroup.coe_inv, hAdj]
  change uMat * M * (Dinv * Qinv * P) =
    bmPSL_embedMat eidx P Pinv (SelectedRoot.SelPSU.embM ιr B)
  calc uMat * M * (Dinv * Qinv * P)
      = Pinv * Q * (D * M * Dinv) * Qinv * P := by
        change Pinv * Q * D * M * (Dinv * Qinv * P) =
          Pinv * Q * (D * M * Dinv) * Qinv * P
        noncomm_ring
    _ = Pinv * Q * M * Qinv * P := by rw [hDcomm]
    _ = Pinv * (Q * M * Qinv) * P := by noncomm_ring
    _ = Pinv * Matrix.reindex eidx eidx
          (Matrix.fromBlocks (SelectedRoot.SelPSU.embM ιr B)
            (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
            (1 : Matrix (Fin r') (Fin r') F)) * P := by rw [hconjQ, hreindex]
    _ = bmPSL_embedMat eidx P Pinv (SelectedRoot.SelPSU.embM ιr B) := rfl

end CFSG.StandardType.FieldTwoPSL

end
