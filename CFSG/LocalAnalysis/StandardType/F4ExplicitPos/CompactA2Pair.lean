module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA2Part2
public import CFSG.RankThree.PartOne.KF4.A2Frame
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.RankThree.PartOne.KA5L.Frames
public import CFSG.RankThree.PartOne.CTP.UnitaryBlk
public import CFSG.LieType.Chevalley.LangRootRankOneTorus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SplitLineFix
public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType.CompactA2Pair

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.PartOne.CTP
open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups


theorem rootSpan_pair {τ : Tag} {L : Type} [Field L] (α : Fin τ.rank → ℤ) :
    rootSpan τ L ({α, -α} : Set (Fin τ.rank → ℤ)) =
      rootSubgroup τ L α ⊔ rootSubgroup τ L (-α) := by
  rw [rootSpan]
  rw [show ({α, -α} : Set (Fin τ.rank → ℤ)) = {α} ∪ {-α} by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
  rw [iSup_union]
  simp

namespace IsA2Frame

variable {τ : Tag} {L : Type} [Field L]
  {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}

theorem block0_range (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ) :
    (ρ.comp (blockSL L 3 2 0 (by omega))).range =
      rootSubgroup τ L (σ 0 1) ⊔ rootSubgroup τ L (σ 1 0) := by
  classical
  obtain ⟨ε01, hε01⟩ := h.transv 0 1 (by decide)
  obtain ⟨ε10, hε10⟩ := h.transv 1 0 (by decide)
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, Subgroup.map_le_iff_le_comap]
    have htop : Subgroup.comap (ρ.comp (blockSL L 3 2 0 (by omega)))
        (rootSubgroup τ L (σ 0 1) ⊔ rootSubgroup τ L (σ 1 0)) = ⊤ := by
      rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := L),
        Subgroup.closure_le]
      rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · change (ρ.comp (blockSL L 3 2 0 (by omega))) (uSL t) ∈
          (rootSubgroup τ L (σ 0 1) ⊔ rootSubgroup τ L (σ 1 0))
        rw [MonoidHom.comp_apply, blk0_uSL, hε01]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(ε01 : L) * t, rfl⟩)
      · change (ρ.comp (blockSL L 3 2 0 (by omega))) (vSL t) ∈
          (rootSubgroup τ L (σ 0 1) ⊔ rootSubgroup τ L (σ 1 0))
        rw [MonoidHom.comp_apply, blk0_vSL, hε10]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨(ε10 : L) * t, rfl⟩)
    rw [htop]
  · apply sup_le
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      refine ⟨uSL ((ε01 : L)⁻¹ * c), ?_⟩
      rw [MonoidHom.comp_apply, blk0_uSL, hε01]
      congr 1
      rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      refine ⟨vSL ((ε10 : L)⁻¹ * c), ?_⟩
      rw [MonoidHom.comp_apply, blk0_vSL, hε10]
      congr 1
      rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]

theorem block0_rootSpan (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ) :
    (ρ.comp (blockSL L 3 2 0 (by omega))).range =
      rootSpan τ L ({σ 0 1, -σ 0 1} : Set (Fin τ.rank → ℤ)) := by
  rw [block0_range h]
  rw [show rootSubgroup τ L (σ 1 0) = rootSubgroup τ L (-σ 0 1) by rw [h.neg 0 1]]
  rw [rootSpan_pair]

theorem block1_range (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ) :
    (ρ.comp (blockSL L 3 2 1 (by omega))).range =
      rootSubgroup τ L (σ 1 2) ⊔ rootSubgroup τ L (σ 2 1) := by
  classical
  obtain ⟨ε12, hε12⟩ := h.transv 1 2 (by decide)
  obtain ⟨ε21, hε21⟩ := h.transv 2 1 (by decide)
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, Subgroup.map_le_iff_le_comap]
    have htop : Subgroup.comap (ρ.comp (blockSL L 3 2 1 (by omega)))
        (rootSubgroup τ L (σ 1 2) ⊔ rootSubgroup τ L (σ 2 1)) = ⊤ := by
      rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := L),
        Subgroup.closure_le]
      rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · change (ρ.comp (blockSL L 3 2 1 (by omega))) (uSL t) ∈
          (rootSubgroup τ L (σ 1 2) ⊔ rootSubgroup τ L (σ 2 1))
        rw [MonoidHom.comp_apply, blk1_uSL, hε12]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(ε12 : L) * t, rfl⟩)
      · change (ρ.comp (blockSL L 3 2 1 (by omega))) (vSL t) ∈
          (rootSubgroup τ L (σ 1 2) ⊔ rootSubgroup τ L (σ 2 1))
        rw [MonoidHom.comp_apply, blk1_vSL, hε21]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨(ε21 : L) * t, rfl⟩)
    rw [htop]
  · apply sup_le
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      refine ⟨uSL ((ε12 : L)⁻¹ * c), ?_⟩
      rw [MonoidHom.comp_apply, blk1_uSL, hε12]
      congr 1
      rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      refine ⟨vSL ((ε21 : L)⁻¹ * c), ?_⟩
      rw [MonoidHom.comp_apply, blk1_vSL, hε21]
      congr 1
      rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]

theorem block1_rootSpan (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ) :
    (ρ.comp (blockSL L 3 2 1 (by omega))).range =
      rootSpan τ L ({σ 1 2, -σ 1 2} : Set (Fin τ.rank → ℤ)) := by
  rw [block1_range h]
  rw [show rootSubgroup τ L (σ 2 1) = rootSubgroup τ L (-σ 1 2) by rw [h.neg 1 2]]
  rw [rootSpan_pair]

open CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem frameSpan_le_of_two_root_spans
    (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ)
    {P : Subgroup (ModGL τ L)}
    (h0 : rootSpan τ L {σ 0 1, -σ 0 1} ≤ P)
    (h1 : rootSpan τ L {σ 1 2, -σ 1 2} ≤ P) :
    rootSpan τ L (frameRoots σ) ≤ P := by
  change rootSpan τ L {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} ≤ P
  rw [← h.range, MonoidHom.range_eq_map, Subgroup.map_le_iff_le_comap,
    ← CFSG.ClassicalInvolution.WeakCT.B12_sup_B23 (K := L)]
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    exact h0 ((block0_rootSpan h).le ⟨A, rfl⟩)
  · rintro _ ⟨A, rfl⟩
    exact h1 ((block1_rootSpan h).le ⟨A, rfl⟩)
theorem frameSpan_le_centralizer_of_two_root_chars
    (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ)
    {F : Set (Fin τ.rank → Lˣ)}
    (h0 : ∀ a ∈ F, rootChar a (σ 0 1) = 1)
    (h1 : ∀ a ∈ F, rootChar a (σ 1 2) = 1) :
    rootSpan τ L (frameRoots σ) ≤
      Subgroup.centralizer (rootDiagUnit τ '' F) := by
  intro x hx
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨a, ha, rfl⟩
  have hroot : ∀ (i j : Fin 3), i ≠ j → rootChar a (σ i j) = 1 →
      ({σ i j, -σ i j} : Set (Fin τ.rank → ℤ)) ⊆ rootCharKernel a := by
    intro i j hij hchar α hα
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl
    · exact ⟨h.isRoot i j hij, hchar⟩
    · refine ⟨?_, ?_⟩
      · rw [← h.neg i j]
        exact h.isRoot j i (Ne.symm hij)
      · rw [show -σ i j = 0 - σ i j by simp, rootChar_sub, rootChar_zero, hchar]
        simp
  have hle := frameSpan_le_of_two_root_spans h
    (rootSpan_le_centralizer a (hroot 0 1 (by decide) (h0 a ha)))
    (rootSpan_le_centralizer a (hroot 1 2 (by decide) (h1 a ha)))
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
theorem frameSpan_le_centralizer_of_two_family_kernels
    (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ)
    (F0 F1 : Set (Fin τ.rank → Lˣ))
    (h0 : CFSG.RankThree.PartOne.KE8F.famKernel F0 = {σ 0 1, -σ 0 1})
    (h1 : CFSG.RankThree.PartOne.KE8F.famKernel F1 = {σ 1 2, -σ 1 2}) :
    rootSpan τ L (frameRoots σ) ≤ Subgroup.centralizer
      ((Subgroup.closure (rootDiagUnit τ '' F0) ⊓
        Subgroup.closure (rootDiagUnit τ '' F1) : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  have hfamily : ∀ F : Set (Fin τ.rank → Lˣ),
      rootSpan τ L (CFSG.RankThree.PartOne.KE8F.famKernel F) ≤
        Subgroup.centralizer (Subgroup.closure (rootDiagUnit τ '' F) : Set (ModGL τ L)) := by
    intro F
    rw [Subgroup.centralizer_closure]
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (rootSpan_le_centralizer a (fun _ hroot => ⟨hroot.1, hroot.2 a ha⟩) hx)).symm
  apply frameSpan_le_of_two_root_spans h
  · rw [← h0]
    exact (hfamily F0).trans (Subgroup.centralizer_le fun _ hx => hx.1)
  · rw [← h1]
    exact (hfamily F1).trans (Subgroup.centralizer_le fun _ hx => hx.2)


end IsA2Frame

end CFSG.StandardType.CompactA2Pair


namespace CFSG.StandardType.CompactA2Pair

section BlockBridge

open Matrix
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply det_blockMat)
open CFSG.ClassicalInvolution.WeakCT (blockSL coe_blockSL)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem blockSL_range_eq_blockSpecialLinear_01 :
    (blockSL K 3 2 0 (by omega)).range =
      blockSpecialLinear (K := K) ({0, 1} : Finset (Fin 3)) := by
  apply le_antisymm
  · rintro X ⟨A, rfl⟩
    rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
    intro i j hij
    rw [coe_blockSL]
    fin_cases i <;> fin_cases j <;> simp_all [blockMat_apply]
  · intro X hX
    let A : Matrix (Fin 2) (Fin 2) K := !![X 0 0, X 0 1; X 1 0, X 1 1]
    have hXeq : (X : Matrix (Fin 3) (Fin 3) K) = blockMat 3 0 A := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, blockMat_apply, CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear.mp hX]
    have hdetA : A.det = 1 := by
      have h := congrArg Matrix.det hXeq
      rw [det_blockMat (by omega)] at h
      exact h.symm.trans X.2
    let A' : SL(2, K) := ⟨A, hdetA⟩
    refine ⟨A', ?_⟩
    apply Subtype.ext
    rw [coe_blockSL]
    exact hXeq.symm

theorem blockSL_range_eq_blockSpecialLinear_12 :
    (blockSL K 3 2 1 (by omega)).range =
      blockSpecialLinear (K := K) ({1, 2} : Finset (Fin 3)) := by
  apply le_antisymm
  · rintro X ⟨A, rfl⟩
    rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
    intro i j hij
    rw [coe_blockSL]
    fin_cases i <;> fin_cases j <;> simp_all [blockMat_apply]
  · intro X hX
    let A : Matrix (Fin 2) (Fin 2) K := !![X 1 1, X 1 2; X 2 1, X 2 2]
    have hXeq : (X : Matrix (Fin 3) (Fin 3) K) = blockMat 3 1 A := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, blockMat_apply, CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear.mp hX]
    have hdetA : A.det = 1 := by
      have h := congrArg Matrix.det hXeq
      rw [det_blockMat (by omega)] at h
      exact h.symm.trans X.2
    let A' : SL(2, K) := ⟨A, hdetA⟩
    refine ⟨A', ?_⟩
    apply Subtype.ext
    rw [coe_blockSL]
    exact hXeq.symm

theorem blockSL_zero_of_map_mem {L : Type} [Field L] (φ : K →+* L)
    (hφ : Function.Injective φ) {Y : SL(3, K)}
    (hY : Matrix.SpecialLinearGroup.map φ Y ∈ (blockSL L 3 2 0 (by omega)).range) :
    Y ∈ (blockSL K 3 2 0 (by omega)).range := by
  rw [blockSL_range_eq_blockSpecialLinear_01] at hY ⊢
  rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear] at hY ⊢
  intro i j hij
  have h := hY i j hij
  change φ ((Y : Matrix (Fin 3) (Fin 3) K) i j) =
    (1 : Matrix (Fin 3) (Fin 3) L) i j at h
  have h1 : (1 : Matrix (Fin 3) (Fin 3) L) i j =
      φ ((1 : Matrix (Fin 3) (Fin 3) K) i j) := by
    simp [Matrix.one_apply]
  rw [h1] at h
  exact hφ h

theorem blockSL_one_of_map_mem {L : Type} [Field L] (φ : K →+* L)
    (hφ : Function.Injective φ) {Y : SL(3, K)}
    (hY : Matrix.SpecialLinearGroup.map φ Y ∈ (blockSL L 3 2 1 (by omega)).range) :
    Y ∈ (blockSL K 3 2 1 (by omega)).range := by
  rw [blockSL_range_eq_blockSpecialLinear_12] at hY ⊢
  rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear] at hY ⊢
  intro i j hij
  have h := hY i j hij
  change φ ((Y : Matrix (Fin 3) (Fin 3) K) i j) =
    (1 : Matrix (Fin 3) (Fin 3) L) i j at h
  have h1 : (1 : Matrix (Fin 3) (Fin 3) L) i j =
      φ ((1 : Matrix (Fin 3) (Fin 3) K) i j) := by
    simp [Matrix.one_apply]
  rw [h1] at h
  exact hφ h

theorem blockSL_zero_map_mem {L : Type} [Field L] (φ : K →+* L)
    {Y : SL(3, K)}
    (hY : Y ∈ (blockSL K 3 2 0 (by omega)).range) :
    Matrix.SpecialLinearGroup.map φ Y ∈ (blockSL L 3 2 0 (by omega)).range := by
  rw [blockSL_range_eq_blockSpecialLinear_01] at hY ⊢
  rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear] at hY ⊢
  intro i j hij
  have h := hY i j hij
  change φ ((Y : Matrix (Fin 3) (Fin 3) K) i j) =
    (1 : Matrix (Fin 3) (Fin 3) L) i j
  rw [show (1 : Matrix (Fin 3) (Fin 3) L) i j =
      φ ((1 : Matrix (Fin 3) (Fin 3) K) i j) by simp [Matrix.one_apply], ← h]

theorem blockSL_one_map_mem {L : Type} [Field L] (φ : K →+* L)
    {Y : SL(3, K)}
    (hY : Y ∈ (blockSL K 3 2 1 (by omega)).range) :
    Matrix.SpecialLinearGroup.map φ Y ∈ (blockSL L 3 2 1 (by omega)).range := by
  rw [blockSL_range_eq_blockSpecialLinear_12] at hY ⊢
  rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear] at hY ⊢
  intro i j hij
  have h := hY i j hij
  change φ ((Y : Matrix (Fin 3) (Fin 3) K) i j) =
    (1 : Matrix (Fin 3) (Fin 3) L) i j
  rw [show (1 : Matrix (Fin 3) (Fin 3) L) i j =
      φ ((1 : Matrix (Fin 3) (Fin 3) K) i j) by simp [Matrix.one_apply], ← h]

theorem diagonal_conj_mem_blockSL_zero (H : SL(3, K))
    (hHdiag : ∀ i j : Fin 3, i ≠ j → (H : Matrix (Fin 3) (Fin 3) K) i j = 0)
    {X : SL(3, K)} (hX : X ∈ (blockSL K 3 2 0 (by omega)).range) :
    H * X * H⁻¹ ∈ (blockSL K 3 2 0 (by omega)).range := by
  rw [blockSL_range_eq_blockSpecialLinear_01] at hX ⊢
  have hD : ((Matrix.SpecialLinearGroup.toGL H : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => (H : Matrix (Fin 3) (Fin 3) K) i i) := by
    ext i j
    change (H : Matrix (Fin 3) (Fin 3) K) i j =
      diagonal (fun i => (H : Matrix (Fin 3) (Fin 3) K) i i) i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [hHdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  have h_inv : ((H⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      ((H : Matrix (Fin 3) (Fin 3) K))⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    rw [Matrix.inv_def, H.2]
    simp
  have hcoe : (H * X * H⁻¹ : SL(3, K)) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K
        (Matrix.SpecialLinearGroup.toGL H) X := by
    apply Subtype.ext
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation,
      Matrix.GeneralLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    simp only [Matrix.SpecialLinearGroup.coe_mul, h_inv]
  rw [hcoe]
  exact CFSG.SeitzReduction.LinearPilot.slConjugation_mem_blockSpecialLinear
    (D := Matrix.SpecialLinearGroup.toGL H) (d := fun i => (H : Matrix (Fin 3) (Fin 3) K) i i)
    hD hX

theorem diagonal_conj_mem_blockSL_one (H : SL(3, K))
    (hHdiag : ∀ i j : Fin 3, i ≠ j → (H : Matrix (Fin 3) (Fin 3) K) i j = 0)
    {X : SL(3, K)} (hX : X ∈ (blockSL K 3 2 1 (by omega)).range) :
    H * X * H⁻¹ ∈ (blockSL K 3 2 1 (by omega)).range := by
  rw [blockSL_range_eq_blockSpecialLinear_12] at hX ⊢
  have hD : ((Matrix.SpecialLinearGroup.toGL H : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => (H : Matrix (Fin 3) (Fin 3) K) i i) := by
    ext i j
    change (H : Matrix (Fin 3) (Fin 3) K) i j =
      diagonal (fun i => (H : Matrix (Fin 3) (Fin 3) K) i i) i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [hHdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  have h_inv : ((H⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      ((H : Matrix (Fin 3) (Fin 3) K))⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    rw [Matrix.inv_def, H.2]
    simp
  have hcoe : (H * X * H⁻¹ : SL(3, K)) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K
        (Matrix.SpecialLinearGroup.toGL H) X := by
    apply Subtype.ext
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation,
      Matrix.GeneralLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    simp only [Matrix.SpecialLinearGroup.coe_mul, h_inv]
  rw [hcoe]
  exact CFSG.SeitzReduction.LinearPilot.slConjugation_mem_blockSpecialLinear
    (D := Matrix.SpecialLinearGroup.toGL H) (d := fun i => (H : Matrix (Fin 3) (Fin 3) K) i i)
    hD hX

end BlockBridge

end CFSG.StandardType.CompactA2Pair

namespace CFSG.StandardType.CompactA2Pair

section ActualMap

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical2
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups
open CFSG.Open CFSG.StandardType.F4ExplicitPos.RationalA2

variable
  {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
  {f : ℕ} {τ : Tag}
  {ρ : Matrix.SpecialLinearGroup (Fin 3) Ω →* ModGL τ Ω}
  {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}

omit [CharP Ω 2] in
theorem exists_diagonal_frame_untwisting
    (hf : 1 ≤ f)
    (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ)
    (Ψ : ModGL τ Ω →* ModGL τ Ω) (hΨinj : Function.Injective Ψ)
    (Fr : Ω ≃+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f)
    (hΨ : ∀ (i j : Fin 3) (_hij : i ≠ j), ∃ b : Ωˣ, ∀ c : Ω,
      Ψ (pinnedX τ Ω (σ i j) c) = pinnedX τ Ω (σ j i) ((b : Ω) * Fr c)) :
    ∃ (H : Matrix.SpecialLinearGroup (Fin 3) Ω) (Φ' : Matrix.SpecialLinearGroup (Fin 3) Ω ≃* Matrix.SpecialLinearGroup (Fin 3) Ω),
      (∀ i j : Fin 3, i ≠ j → (H : Matrix (Fin 3) (Fin 3) Ω) i j = 0) ∧
      (∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω, Ψ (ρ X) = ρ (Φ' X)) ∧
      (∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω,
        Matrix.SpecialLinearGroup.toGL (Φ' (H * X * H⁻¹)) =
          Matrix.SpecialLinearGroup.toGL H *
            invTransposeHom (Matrix.GeneralLinearGroup.map Fr.toRingHom
              (Matrix.SpecialLinearGroup.toGL X)) *
            (Matrix.SpecialLinearGroup.toGL H)⁻¹) ∧
      (∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω, X ∈ fixSubgroup Φ' ↔
        ∃ Y ∈ unitarySet (2 ^ f) 3,
          Matrix.SpecialLinearGroup.toGL X =
            Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) := by
  classical
  obtain ⟨Φ', hΦ', b, hshape⟩ :=
    inducedAut_unitary (τ := τ) (L := Ω) (CFSG.HardMathSupport.Timmesfeld.CrossChar.IsSLFrame.of_isA2Frame h) h.injective Fr.toRingHom
      Fr.bijective Ψ hΨinj (Equiv.refl (Fin 3)) (by
        intro i j hij
        simpa using hΨ i j hij)
  have hshape' : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : Matrix.SpecialLinearGroup (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω) =
        1 + Matrix.single j i ((b i j : Ω) * t ^ 2 ^ f) := by
    intro i j hij t
    rw [hshape i j hij t, show Fr.toRingHom t = t ^ 2 ^ f from hFr t]
    simp
  obtain ⟨H, hHdiag, hfull, hfix⟩ :=
    unitary_full_intertwining_diagonal_algClosed (f := f) (Ω := Ω) hf (by norm_num) Fr.toRingHom
      hFr Φ' b hshape'
  exact ⟨H, Φ', hHdiag, hΦ', hfull, hfix⟩

noncomputable def compactA2Map (F : Subfield Ω) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hFcard : Nat.card F = (2 ^ f) ^ 2) (H : Matrix.SpecialLinearGroup (Fin 3) Ω) :
    Su F 2 f 3 →* ModGL τ Ω :=
  (kappaSU ρ H F 2 f).comp
    (MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := f) hFcard 3)).toMonoidHom

omit [IsAlgClosed Ω] [CharP Ω 2] in
theorem exists_su_block_zero_of_mem
    (F : Subfield Ω) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hF : ∀ c : Ω, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2)
    {Y : SL(3, Ω)}
    (hYblock : Y ∈ (blockSL Ω 3 2 0 (by omega)).range)
    (hYunitary : Matrix.SpecialLinearGroup.toGL Y ∈ unitarySet (2 ^ f) 3) :
    ∃ A : Su F 2 f 3, A ∈ B12 F 2 f ∧
      Matrix.SpecialLinearGroup.map F.subtype
        (suToSL (unitaryInvolution F 2 f) A) = Y := by
  classical
  let eF : Su F 2 f 3 ≃* StatedSU 3 (2 ^ f) F :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := f) hFcard 3)
  obtain ⟨A', hA'⟩ :=
    (mem_range_statedSUToSL_iff (ℓ := 2) (f := f) Nat.prime_two F hF hFcard (by norm_num) Y).mpr
      hYunitary
  let A : Su F 2 f 3 := eF.symm A'
  have hA_matrix : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((A' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl
  have hYF : Matrix.SpecialLinearGroup.map F.subtype
      (suToSL (unitaryInvolution F 2 f) A) = Y := by
    apply Subtype.ext
    change ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map F.subtype =
      (Y : Matrix (Fin 3) (Fin 3) Ω)
    rw [hA_matrix, ← coe_statedSUToSL]
    exact congrArg Subtype.val hA'
  have hYFblock : suToSL (unitaryInvolution F 2 f) A ∈
      (blockSL F 3 2 0 (by omega)).range :=
    blockSL_zero_of_map_mem (φ := F.subtype) F.subtype.injective (by
      simpa [hYF] using hYblock)
  let W : Submodule F (Fin 3 → F) := Submodule.span F {Pi.single 0 1, Pi.single 1 1}
  let ℓ : Submodule F (Fin 3 → F) := Submodule.span F {Pi.single 2 1}
  have hblk : suToSL (unitaryInvolution F 2 f) A ∈ blkGroup F W ℓ := by
    rw [blkGroup_std_B12]
    exact hYFblock
  have hublk : A ∈ ublkGroup (unitaryInvolution F 2 f) W ℓ :=
    (mem_ublkGroup_iff (unitaryInvolution F 2 f) W ℓ A).mpr hblk
  have hAB : A ∈ B12 F 2 f := by
    change A ∈ (embSUid (unitaryInvolution F 2 f) 2).range
    rw [← ublk_std_B12]
    exact hublk
  exact ⟨A, hAB, hYF⟩

omit [IsAlgClosed Ω] [CharP Ω 2] in
theorem exists_su_block_one_of_mem
    (F : Subfield Ω) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hF : ∀ c : Ω, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2)
    {Y : SL(3, Ω)}
    (hYblock : Y ∈ (blockSL Ω 3 2 1 (by omega)).range)
    (hYunitary : Matrix.SpecialLinearGroup.toGL Y ∈ unitarySet (2 ^ f) 3) :
    ∃ A : Su F 2 f 3, A ∈ B23 F 2 f ∧
      Matrix.SpecialLinearGroup.map F.subtype
        (suToSL (unitaryInvolution F 2 f) A) = Y := by
  classical
  let eF : Su F 2 f 3 ≃* StatedSU 3 (2 ^ f) F :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := f) hFcard 3)
  obtain ⟨A', hA'⟩ :=
    (mem_range_statedSUToSL_iff (ℓ := 2) (f := f) Nat.prime_two F hF hFcard (by norm_num) Y).mpr
      hYunitary
  let A : Su F 2 f 3 := eF.symm A'
  have hA_matrix : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((A' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl
  have hYF : Matrix.SpecialLinearGroup.map F.subtype
      (suToSL (unitaryInvolution F 2 f) A) = Y := by
    apply Subtype.ext
    change ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map F.subtype =
      (Y : Matrix (Fin 3) (Fin 3) Ω)
    rw [hA_matrix, ← coe_statedSUToSL]
    exact congrArg Subtype.val hA'
  have hYFblock : suToSL (unitaryInvolution F 2 f) A ∈
      (blockSL F 3 2 1 (by omega)).range :=
    blockSL_one_of_map_mem (φ := F.subtype) F.subtype.injective (by
      simpa [hYF] using hYblock)
  let W : Submodule F (Fin 3 → F) := Submodule.span F {Pi.single 1 1, Pi.single 2 1}
  let ℓ : Submodule F (Fin 3 → F) := Submodule.span F {Pi.single 0 1}
  have hblk : suToSL (unitaryInvolution F 2 f) A ∈ blkGroup F W ℓ := by
    rw [blkGroup_std_B23]
    exact hYFblock
  have hublk : A ∈ ublkGroup (unitaryInvolution F 2 f) W ℓ :=
    (mem_ublkGroup_iff (unitaryInvolution F 2 f) W ℓ A).mpr hblk
  have hAB : A ∈ B23 F 2 f := by
    change A ∈ (embSUid (unitaryInvolution F 2 f) 0).range
    rw [← ublk_std_B23]
    exact hublk
  exact ⟨A, hAB, hYF⟩

omit [IsAlgClosed Ω] [CharP Ω 2] in
theorem compactA2Map_B12
    (_hf : 1 ≤ f) (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ)
    (Ψ : ModGL τ Ω →* ModGL τ Ω)
    (F : Subfield Ω) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hF : ∀ c : Ω, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2)
    (H : Matrix.SpecialLinearGroup (Fin 3) Ω)
    (Φ' : Matrix.SpecialLinearGroup (Fin 3) Ω ≃* Matrix.SpecialLinearGroup (Fin 3) Ω)
    (hHdiag : ∀ i j : Fin 3, i ≠ j → (H : Matrix (Fin 3) (Fin 3) Ω) i j = 0)
    (hΦ' : ∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω, Ψ (ρ X) = ρ (Φ' X))
    (hfix : ∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω, X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet (2 ^ f) 3,
        Matrix.SpecialLinearGroup.toGL X =
          Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    (B12 F 2 f).map (compactA2Map (τ := τ) (ρ := ρ) (f := f) F hFcard H) =
      rootSpan τ Ω ({σ 0 1, -σ 0 1} : Set (Fin τ.rank → ℤ)) ⊓
        Ψ.eqLocus (MonoidHom.id _) := by
  classical
  let σF : F ≃+* F := unitaryInvolution F 2 f
  let eF : Su F 2 f 3 ≃* StatedSU 3 (2 ^ f) F :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := f) hFcard 3)
  let θ : Su F 2 f 3 →* ModGL τ Ω := compactA2Map (τ := τ) (ρ := ρ) (f := f) F hFcard H
  have hHdiagInv : ∀ i j : Fin 3, i ≠ j →
      ((H⁻¹ : Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) i j = 0 := by
    intro i j hij
    have h_inv : ((H⁻¹ : Matrix.SpecialLinearGroup (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω) = (H : Matrix (Fin 3) (Fin 3) Ω)⁻¹ := by
      rw [Matrix.SpecialLinearGroup.coe_inv]
      rw [Matrix.inv_def, H.2]
      simp
    have hD : (H : Matrix (Fin 3) (Fin 3) Ω) =
        diagonal (fun i => (H : Matrix (Fin 3) (Fin 3) Ω) i i) := by
      ext i j
      by_cases hij' : i = j
      · subst hij'; simp
      · rw [hHdiag i j hij', Matrix.diagonal_apply_ne _ hij']
    rw [h_inv, hD, Matrix.inv_diagonal]
    exact Matrix.diagonal_apply_ne _ hij
  have hroot : rootSpan τ Ω ({σ 0 1, -σ 0 1} : Set (Fin τ.rank → ℤ)) =
      (ρ.comp (blockSL Ω 3 2 0 (by omega))).range :=
    (IsA2Frame.block0_rootSpan h).symm
  rw [hroot, MonoidHom.range_comp]
  apply le_antisymm
  · intro Z hZ
    rcases Subgroup.mem_map.mp hZ with ⟨A, hA, rfl⟩
    let Y : Matrix.SpecialLinearGroup (Fin 3) Ω :=
      Matrix.SpecialLinearGroup.map F.subtype (suToSL σF A)
    have hYeq : Y = statedSUToSL F 3 (2 ^ f) (eF A) := rfl
    have hYblockF : suToSL σF A ∈ (blockSL F 3 2 0 (by omega)).range := by
      have hA' : A ∈ (embSUid σF 2).range := by
        change A ∈ B12 F 2 f at hA
        exact hA
      have hublk : A ∈ ublkGroup σF
          (Submodule.span F {Pi.single 0 1, Pi.single 1 1})
          (Submodule.span F {Pi.single 2 1}) := by
        rw [ublk_std_B12]
        exact hA'
      have hblk : suToSL σF A ∈ blkGroup F
          (Submodule.span F {Pi.single 0 1, Pi.single 1 1})
          (Submodule.span F {Pi.single 2 1}) :=
        (mem_ublkGroup_iff σF _ _ A).mp hublk
      change suToSL σF A ∈ CFSG.ClassicalInvolution.WeakCT.B12 F
      rw [← blkGroup_std_B12]
      exact hblk
    have hYblock : Y ∈ (blockSL Ω 3 2 0 (by omega)).range :=
      blockSL_zero_map_mem (φ := F.subtype) hYblockF
    have hYunitary : Matrix.SpecialLinearGroup.toGL Y ∈ unitarySet (2 ^ f) 3 := by
      rw [hYeq]
      exact (mem_range_statedSUToSL_iff (ℓ := 2) (f := f) Nat.prime_two F hF hFcard
        (by norm_num) (statedSUToSL F 3 (2 ^ f) (eF A))).mp ⟨eF A, rfl⟩
    have hconj : H * Y * H⁻¹ ∈ (blockSL Ω 3 2 0 (by omega)).range :=
      diagonal_conj_mem_blockSL_zero H hHdiag hYblock
    have hfixH : H * Y * H⁻¹ ∈ fixSubgroup Φ' :=
      (hfix (H * Y * H⁻¹)).2 ⟨Matrix.SpecialLinearGroup.toGL Y, hYunitary, by
        simp [Y, map_mul]⟩
    have hθ : θ A = ρ (H * Y * H⁻¹) := by
      change (kappaSU ρ H F 2 f) (eF A) = ρ (H * Y * H⁻¹)
      rw [kappaSU_apply, ← hYeq]
    rw [hθ]
    refine ⟨⟨H * Y * H⁻¹, hconj, rfl⟩, ?_⟩
    change Ψ (ρ (H * Y * H⁻¹)) = ρ (H * Y * H⁻¹)
    rw [hΦ' (H * Y * H⁻¹), (mem_fixSubgroup Φ').mp hfixH]
  · intro Z hZ
    rcases hZ with ⟨hZblock, hZfix⟩
    rcases Subgroup.mem_map.mp hZblock with ⟨X, hXblock, rfl⟩
    have hXfix : X ∈ fixSubgroup Φ' := by
      rw [mem_fixSubgroup]
      have hEq := hZfix
      change Ψ (ρ X) = ρ X at hEq
      rw [hΦ' X] at hEq
      exact h.injective hEq
    rcases (hfix X).mp hXfix with ⟨U, hUunitary, hUX⟩
    let Usl : SL(3, Ω) := ⟨(U : Matrix (Fin 3) (Fin 3) Ω), hUunitary.2.1⟩
    have hUXsl : X = H * Usl * H⁻¹ := by
      apply Subtype.ext
      have h_inv : ((H⁻¹ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
          ((H : Matrix (Fin 3) (Fin 3) Ω))⁻¹ := by
        rw [Matrix.SpecialLinearGroup.coe_inv]
        rw [Matrix.inv_def, H.2]
        simp
      have h := congrArg (fun g : GL (Fin 3) Ω => (g : Matrix (Fin 3) (Fin 3) Ω)) hUX
      change (X : Matrix (Fin 3) (Fin 3) Ω) =
        (H : Matrix (Fin 3) (Fin 3) Ω) * (Usl : Matrix (Fin 3) (Fin 3) Ω) *
          ((H⁻¹ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω)
      rw [show (Usl : Matrix (Fin 3) (Fin 3) Ω) = (U : Matrix (Fin 3) (Fin 3) Ω) from rfl]
      simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.GeneralLinearGroup.coe_inv, h_inv] using h
    have hUblock : Usl ∈ (blockSL Ω 3 2 0 (by omega)).range := by
      have hUeq : Usl = H⁻¹ * X * H := by
        rw [hUXsl]; group
      rw [hUeq]
      simpa using diagonal_conj_mem_blockSL_zero H⁻¹ hHdiagInv hXblock
    have hUunitary' : Matrix.SpecialLinearGroup.toGL Usl ∈ unitarySet (2 ^ f) 3 := by
      convert hUunitary using 1
      exact Units.ext rfl
    rcases exists_su_block_zero_of_mem F hF hFcard hUblock hUunitary' with ⟨A, hAB, hAU⟩
    refine Subgroup.mem_map.mpr ⟨A, hAB, ?_⟩
    have hθ : θ A = ρ X := by
      change (kappaSU ρ H F 2 f) (eF A) = ρ X
      rw [kappaSU_apply]
      have hYeq : statedSUToSL F 3 (2 ^ f) (eF A) = Usl := by
        rw [← hAU]
        rfl
      rw [hYeq, hUXsl]
    exact hθ

omit [IsAlgClosed Ω] [CharP Ω 2] in
theorem compactA2Map_B23
    (_hf : 1 ≤ f) (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ)
    (Ψ : ModGL τ Ω →* ModGL τ Ω)
    (F : Subfield Ω) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hF : ∀ c : Ω, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2)
    (H : Matrix.SpecialLinearGroup (Fin 3) Ω)
    (Φ' : Matrix.SpecialLinearGroup (Fin 3) Ω ≃* Matrix.SpecialLinearGroup (Fin 3) Ω)
    (hHdiag : ∀ i j : Fin 3, i ≠ j → (H : Matrix (Fin 3) (Fin 3) Ω) i j = 0)
    (hΦ' : ∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω, Ψ (ρ X) = ρ (Φ' X))
    (hfix : ∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω, X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet (2 ^ f) 3,
        Matrix.SpecialLinearGroup.toGL X =
          Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    (B23 F 2 f).map (compactA2Map (τ := τ) (ρ := ρ) (f := f) F hFcard H) =
      rootSpan τ Ω ({σ 1 2, -σ 1 2} : Set (Fin τ.rank → ℤ)) ⊓
        Ψ.eqLocus (MonoidHom.id _) := by
  classical
  let σF : F ≃+* F := unitaryInvolution F 2 f
  let eF : Su F 2 f 3 ≃* StatedSU 3 (2 ^ f) F :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := f) hFcard 3)
  let θ : Su F 2 f 3 →* ModGL τ Ω := compactA2Map (τ := τ) (ρ := ρ) (f := f) F hFcard H
  have hHdiagInv : ∀ i j : Fin 3, i ≠ j →
      ((H⁻¹ : Matrix.SpecialLinearGroup (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) i j = 0 := by
    intro i j hij
    have h_inv : ((H⁻¹ : Matrix.SpecialLinearGroup (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω) = (H : Matrix (Fin 3) (Fin 3) Ω)⁻¹ := by
      rw [Matrix.SpecialLinearGroup.coe_inv]
      rw [Matrix.inv_def, H.2]
      simp
    have hD : (H : Matrix (Fin 3) (Fin 3) Ω) =
        diagonal (fun i => (H : Matrix (Fin 3) (Fin 3) Ω) i i) := by
      ext i j
      by_cases hij' : i = j
      · subst hij'; simp
      · rw [hHdiag i j hij', Matrix.diagonal_apply_ne _ hij']
    rw [h_inv, hD, Matrix.inv_diagonal]
    exact Matrix.diagonal_apply_ne _ hij
  have hroot : rootSpan τ Ω ({σ 1 2, -σ 1 2} : Set (Fin τ.rank → ℤ)) =
      (ρ.comp (blockSL Ω 3 2 1 (by omega))).range :=
    (IsA2Frame.block1_rootSpan h).symm
  rw [hroot, MonoidHom.range_comp]
  apply le_antisymm
  · intro Z hZ
    rcases Subgroup.mem_map.mp hZ with ⟨A, hA, rfl⟩
    let Y : Matrix.SpecialLinearGroup (Fin 3) Ω :=
      Matrix.SpecialLinearGroup.map F.subtype (suToSL σF A)
    have hYeq : Y = statedSUToSL F 3 (2 ^ f) (eF A) := rfl
    have hYblockF : suToSL σF A ∈ (blockSL F 3 2 1 (by omega)).range := by
      have hA' : A ∈ (embSUid σF 0).range := by
        change A ∈ B23 F 2 f at hA
        exact hA
      have hublk : A ∈ ublkGroup σF
          (Submodule.span F {Pi.single 1 1, Pi.single 2 1})
          (Submodule.span F {Pi.single 0 1}) := by
        rw [ublk_std_B23]
        exact hA'
      have hblk : suToSL σF A ∈ blkGroup F
          (Submodule.span F {Pi.single 1 1, Pi.single 2 1})
          (Submodule.span F {Pi.single 0 1}) :=
        (mem_ublkGroup_iff σF _ _ A).mp hublk
      change suToSL σF A ∈ CFSG.ClassicalInvolution.WeakCT.B23 F
      rw [← blkGroup_std_B23]
      exact hblk
    have hYblock : Y ∈ (blockSL Ω 3 2 1 (by omega)).range :=
      blockSL_one_map_mem (φ := F.subtype) hYblockF
    have hYunitary : Matrix.SpecialLinearGroup.toGL Y ∈ unitarySet (2 ^ f) 3 := by
      rw [hYeq]
      exact (mem_range_statedSUToSL_iff (ℓ := 2) (f := f) Nat.prime_two F hF hFcard
        (by norm_num) (statedSUToSL F 3 (2 ^ f) (eF A))).mp ⟨eF A, rfl⟩
    have hconj : H * Y * H⁻¹ ∈ (blockSL Ω 3 2 1 (by omega)).range :=
      diagonal_conj_mem_blockSL_one H hHdiag hYblock
    have hfixH : H * Y * H⁻¹ ∈ fixSubgroup Φ' :=
      (hfix (H * Y * H⁻¹)).2 ⟨Matrix.SpecialLinearGroup.toGL Y, hYunitary, by
        simp [Y, map_mul]⟩
    have hθ : θ A = ρ (H * Y * H⁻¹) := by
      change (kappaSU ρ H F 2 f) (eF A) = ρ (H * Y * H⁻¹)
      rw [kappaSU_apply, ← hYeq]
    rw [hθ]
    refine ⟨⟨H * Y * H⁻¹, hconj, rfl⟩, ?_⟩
    change Ψ (ρ (H * Y * H⁻¹)) = ρ (H * Y * H⁻¹)
    rw [hΦ' (H * Y * H⁻¹), (mem_fixSubgroup Φ').mp hfixH]
  · intro Z hZ
    rcases hZ with ⟨hZblock, hZfix⟩
    rcases Subgroup.mem_map.mp hZblock with ⟨X, hXblock, rfl⟩
    have hXfix : X ∈ fixSubgroup Φ' := by
      rw [mem_fixSubgroup]
      have hEq := hZfix
      change Ψ (ρ X) = ρ X at hEq
      rw [hΦ' X] at hEq
      exact h.injective hEq
    rcases (hfix X).mp hXfix with ⟨U, hUunitary, hUX⟩
    let Usl : SL(3, Ω) := ⟨(U : Matrix (Fin 3) (Fin 3) Ω), hUunitary.2.1⟩
    have hUXsl : X = H * Usl * H⁻¹ := by
      apply Subtype.ext
      have h_inv : ((H⁻¹ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
          ((H : Matrix (Fin 3) (Fin 3) Ω))⁻¹ := by
        rw [Matrix.SpecialLinearGroup.coe_inv]
        rw [Matrix.inv_def, H.2]
        simp
      have h := congrArg (fun g : GL (Fin 3) Ω => (g : Matrix (Fin 3) (Fin 3) Ω)) hUX
      change (X : Matrix (Fin 3) (Fin 3) Ω) =
        (H : Matrix (Fin 3) (Fin 3) Ω) * (Usl : Matrix (Fin 3) (Fin 3) Ω) *
          ((H⁻¹ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω)
      rw [show (Usl : Matrix (Fin 3) (Fin 3) Ω) = (U : Matrix (Fin 3) (Fin 3) Ω) from rfl]
      simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.GeneralLinearGroup.coe_inv, h_inv] using h
    have hUblock : Usl ∈ (blockSL Ω 3 2 1 (by omega)).range := by
      have hUeq : Usl = H⁻¹ * X * H := by
        rw [hUXsl]; group
      rw [hUeq]
      simpa using diagonal_conj_mem_blockSL_one H⁻¹ hHdiagInv hXblock
    have hUunitary' : Matrix.SpecialLinearGroup.toGL Usl ∈ unitarySet (2 ^ f) 3 := by
      convert hUunitary using 1
      exact Units.ext rfl
    rcases exists_su_block_one_of_mem F hF hFcard hUblock hUunitary' with ⟨A, hAB, hAU⟩
    refine Subgroup.mem_map.mpr ⟨A, hAB, ?_⟩
    have hθ : θ A = ρ X := by
      change (kappaSU ρ H F 2 f) (eF A) = ρ X
      rw [kappaSU_apply]
      have hYeq : statedSUToSL F 3 (2 ^ f) (eF A) = Usl := by
        rw [← hAU]
        rfl
      rw [hYeq, hUXsl]
    exact hθ

omit [IsAlgClosed Ω] [CharP Ω 2] in
theorem compactA2Map_range (_hf : 1 ≤ f) (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ)
    (Ψ : ModGL τ Ω →* ModGL τ Ω)
    (F : Subfield Ω) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hF : ∀ c : Ω, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2)
    (H : Matrix.SpecialLinearGroup (Fin 3) Ω)
    (Φ' : Matrix.SpecialLinearGroup (Fin 3) Ω ≃* Matrix.SpecialLinearGroup (Fin 3) Ω)
    (_hHdiag : ∀ i j : Fin 3, i ≠ j → (H : Matrix (Fin 3) (Fin 3) Ω) i j = 0)
    (hΦ' : ∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω, Ψ (ρ X) = ρ (Φ' X))
    (hfix : ∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω, X ∈ fixSubgroup Φ' ↔
      ∃ Y ∈ unitarySet (2 ^ f) 3,
        Matrix.SpecialLinearGroup.toGL X =
          Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    (compactA2Map (τ := τ) (ρ := ρ) (f := f) F hFcard H).range =
      rootSpan τ Ω (frameRoots σ) ⊓ Ψ.eqLocus (MonoidHom.id _) := by
  classical
  let eF : Su F 2 f 3 ≃* StatedSU 3 (2 ^ f) F :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU (p := 2) (f := f) hFcard 3)
  have hκrange : (kappaSU ρ H F 2 f).range =
      ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _) := by
    exact kappaSU_range (ρ := ρ) (H := H) F (ℓ := 2) (f := f) Nat.prime_two hF hFcard
      h.injective Ψ Φ' hΦ' hfix
  have hsurj : Function.Surjective eF := eF.surjective
  calc
    (compactA2Map (τ := τ) (ρ := ρ) (f := f) F hFcard H).range
        = (kappaSU ρ H F 2 f).range := by
          rw [compactA2Map, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj,
            Subgroup.map_top]
    _ = rootSpan τ Ω (frameRoots σ) ⊓ Ψ.eqLocus (MonoidHom.id _) := by
          rw [hκrange, h.range]
          rfl

theorem compactA2Pair_of_LangDatum
    (hf : 1 ≤ f)
    (j : Matrix.SpecialLinearGroup (Fin 3) Ω →* ModGL τ Ω)
    (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ)
    (hpair : CFSG.RankThree.PartOne.KF4.IsA2Frame j σ)
    (D : LangDatum τ Ω) (ρF : Equiv.Perm (Fin τ.rank → ℤ))
    (hρmap : FrobRootMap D ρF)
    (hρ : ∀ (i k : Fin 3), i ≠ k → ρF (σ i k) = σ k i)
    (hq : D.q = 2 ^ f)
    (F : Subfield Ω) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hF : ∀ c : Ω, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2) :
    ∃ θ : Su F 2 f 3 →* ModGL τ Ω,
      Function.Injective θ ∧
      θ.range = rootSpan τ Ω (frameRoots σ) ⊓ D.model ∧
      (B12 F 2 f).map θ = rootSpan τ Ω ({σ 0 1, -σ 0 1} : Set (Fin τ.rank → ℤ)) ⊓
        D.model ∧
      (B23 F 2 f).map θ = rootSpan τ Ω ({σ 1 2, -σ 1 2} : Set (Fin τ.rank → ℤ)) ⊓
        D.model := by
  classical
  let Fr : Ω ≃+* Ω := iterateFrobeniusEquiv Ω 2 f
  have hFr : ∀ c : Ω, Fr c = c ^ 2 ^ f := fun c => iterateFrobeniusEquiv_def Ω 2 f c
  have hΨ : ∀ (i k : Fin 3) (hik : i ≠ k), ∃ b : Ωˣ, ∀ c : Ω,
      D.step (pinnedX τ Ω (σ i k) c) =
        pinnedX τ Ω (σ k i) ((b : Ω) * Fr c) := by
    intro i k hik
    obtain ⟨μ, hμ0, hμ⟩ := hρmap.step_pinnedX (by rw [hq]; exact pow_pos (by decide) _)
      (hpair.isRoot i k hik)
    refine ⟨Units.mk0 μ hμ0, ?_⟩
    intro c
    rw [hμ c, hρ i k hik, hq, hFr c]
    rfl
  have hΨinj : Function.Injective D.step :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.langDatum_step_injective D
  obtain ⟨H, Φ', hHdiag, hΦ', _hfull, hfix⟩ :=
    exists_diagonal_frame_untwisting hf hpair D.step hΨinj Fr hFr hΨ
  let θ : Su F 2 f 3 →* ModGL τ Ω := compactA2Map (τ := τ) (ρ := j) (f := f) F hFcard H
  have hθinj : Function.Injective θ := by
    have hκ : Function.Injective (kappaSU (ρ := j) H F 2 f) :=
      kappaSU_injective (ρ := j) (H := H) F 2 f hpair.injective
    exact hκ.comp (MulEquiv.injective _)
  have hSL : CFSG.HardMathSupport.Timmesfeld.CrossChar.IsSLFrame j σ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.IsSLFrame.of_isA2Frame hpair
  have hroot : j.range = rootSpan τ Ω (frameRoots σ) := hSL.range
  have hle : rootSpan τ Ω (frameRoots σ) ≤ adjointGroup τ Ω := by
    rw [← hroot]
    exact hSL.range_le_adjointGroup
  have hmodel : rootSpan τ Ω (frameRoots σ) ⊓ D.model =
      rootSpan τ Ω (frameRoots σ) ⊓ D.step.eqLocus (MonoidHom.id _) := by
    rw [show D.model = adjointGroup τ Ω ⊓ D.step.eqLocus (MonoidHom.id _) from rfl,
      ← inf_assoc, inf_eq_left.2 hle]
  have hsub01 : ({σ 0 1, -σ 0 1} : Set (Fin τ.rank → ℤ)) ⊆ frameRoots σ := by
    intro r hr
    rcases hr with rfl | rfl
    · exact ⟨0, 1, by decide, rfl⟩
    · rw [← hpair.neg 0 1]
      exact ⟨1, 0, by decide, rfl⟩
  have hsub12 : ({σ 1 2, -σ 1 2} : Set (Fin τ.rank → ℤ)) ⊆ frameRoots σ := by
    intro r hr
    rcases hr with rfl | rfl
    · exact ⟨1, 2, by decide, rfl⟩
    · rw [← hpair.neg 1 2]
      exact ⟨2, 1, by decide, rfl⟩
  have hle01 : rootSpan τ Ω ({σ 0 1, -σ 0 1} : Set (Fin τ.rank → ℤ)) ≤
      adjointGroup τ Ω :=
    (CFSG.LieType.Chevalley.rootSpan_mono hsub01).trans hle
  have hle12 : rootSpan τ Ω ({σ 1 2, -σ 1 2} : Set (Fin τ.rank → ℤ)) ≤
      adjointGroup τ Ω :=
    (CFSG.LieType.Chevalley.rootSpan_mono hsub12).trans hle
  have hmodel01 : rootSpan τ Ω ({σ 0 1, -σ 0 1} : Set (Fin τ.rank → ℤ)) ⊓ D.model =
      rootSpan τ Ω ({σ 0 1, -σ 0 1} : Set (Fin τ.rank → ℤ)) ⊓
        D.step.eqLocus (MonoidHom.id _) := by
    rw [show D.model = adjointGroup τ Ω ⊓ D.step.eqLocus (MonoidHom.id _) from rfl,
      ← inf_assoc, inf_eq_left.2 hle01]
  have hmodel12 : rootSpan τ Ω ({σ 1 2, -σ 1 2} : Set (Fin τ.rank → ℤ)) ⊓ D.model =
      rootSpan τ Ω ({σ 1 2, -σ 1 2} : Set (Fin τ.rank → ℤ)) ⊓
        D.step.eqLocus (MonoidHom.id _) := by
    rw [show D.model = adjointGroup τ Ω ⊓ D.step.eqLocus (MonoidHom.id _) from rfl,
      ← inf_assoc, inf_eq_left.2 hle12]
  refine ⟨θ, hθinj, ?_, ?_, ?_⟩
  · rw [compactA2Map_range hf hpair D.step F hF hFcard H Φ' hHdiag hΦ' hfix, hmodel]
  · rw [compactA2Map_B12 hf hpair D.step F hF hFcard H Φ' hHdiag hΦ' hfix, hmodel01]
  · rw [compactA2Map_B23 hf hpair D.step F hF hFcard H Φ' hHdiag hΦ' hfix, hmodel12]




theorem compactA2Pair_of_LangSetup
    (hf : 1 ≤ f)
    (j : Matrix.SpecialLinearGroup (Fin 3) Ω →* ModGL τ Ω)
    (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ)
    (hpair : CFSG.RankThree.PartOne.KF4.IsA2Frame j σ)
    {p : ℕ} (S : LangSetup τ Ω p)
    (hρ : ∀ (i k : Fin 3), i ≠ k → S.ρ (σ i k) = σ k i)
    (hq : S.D.q = 2 ^ f)
    (F : Subfield Ω) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hF : ∀ c : Ω, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2) :
    ∃ θ : Su F 2 f 3 →* ModGL τ Ω,
      Function.Injective θ ∧
      θ.range = rootSpan τ Ω (frameRoots σ) ⊓ S.D.model ∧
      (B12 F 2 f).map θ = rootSpan τ Ω ({σ 0 1, -σ 0 1} : Set (Fin τ.rank → ℤ)) ⊓
        S.D.model ∧
      (B23 F 2 f).map θ = rootSpan τ Ω ({σ 1 2, -σ 1 2} : Set (Fin τ.rank → ℤ)) ⊓
        S.D.model :=
  compactA2Pair_of_LangDatum hf j σ hpair S.D S.ρ S.frob hρ hq F hF hFcard

end ActualMap

end CFSG.StandardType.CompactA2Pair
