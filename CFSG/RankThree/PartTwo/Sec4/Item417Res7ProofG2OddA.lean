module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2OddCommon
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSplit
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Torus
import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
  CFSG.LieType.Steinberg.RankTwo
open scoped Matrix

namespace Res417Seven

@[expose] noncomputable def slInvTr (n : ℕ) (L : Type) [Field L] :
    Matrix.SpecialLinearGroup (Fin n) L →* Matrix.SpecialLinearGroup (Fin n) L where
  toFun A := ⟨((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ, by
    rw [Matrix.det_transpose]
    exact (A⁻¹).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    simp only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
    rfl)

@[expose] noncomputable def slUnitaryTwist (n : ℕ) {L : Type} [Field L] (σ : L →+* L) :
    Matrix.SpecialLinearGroup (Fin n) L →* Matrix.SpecialLinearGroup (Fin n) L :=
  (Matrix.SpecialLinearGroup.map σ).comp (slInvTr n L)

theorem slUnitaryTwist_transvection {n : ℕ} {L : Type} [Field L] [CharP L 2] (σ : L →+* L)
    {i j : Fin n} (hij : i ≠ j) (c : L) :
    slUnitaryTwist n σ (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij.symm (σ c) := by
  have hinv : (Matrix.SpecialLinearGroup.transvection hij c)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (-c) := by
    refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
    change Matrix.transvection i j c * Matrix.transvection i j (-c) = 1
    rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel,
      Matrix.transvection_zero]
  have hneg : σ (-c) = σ c := by
    rw [map_neg]
    exact CharTwo.neg_eq _
  apply Subtype.ext
  change ((((Matrix.SpecialLinearGroup.transvection hij c)⁻¹ :
      Matrix.SpecialLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ).map σ =
    Matrix.transvection j i (σ c)
  rw [hinv]
  change ((Matrix.transvection i j (-c))ᵀ).map σ = Matrix.transvection j i (σ c)
  rw [← hneg, Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, Matrix.map_add _ (map_add σ), Matrix.map_one _ σ.map_zero σ.map_one,
    Matrix.map_single, Matrix.transvection]

section ThreeA

variable {L : Type} [Field L]

theorem weylElt_r_conj_torusElt_a
    (s : Lˣ) :
    weylElt .G2 L g2ir 1 * torusElt .G2 L g2ia s * (weylElt .G2 L g2ir 1)⁻¹ =
      rootDiagUnit .G2 (fun j => if j = g2ia then s⁻¹ else s) := by
  rw [← canonicalRep_simple (coxeterSystem .G2) L g2ir, torusElt_eq_rootDiagUnit]
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff _ _ (simple .G2 g2ir)).mpr
    (rootChar_smul_eq_of_single fun i => ?_)).symm
  rw [simple_smul, rootChar_g2, rootChar_g2]
  have c0 : Tag.G2.cartan g2ia g2ia = 2 := by decide
  have c1 : Tag.G2.cartan g2ia g2ir = -1 := by decide
  have hne : g2ir ≠ g2ia := by decide
  simp only [c0, c1, hne, ↓reduceIte]
  rcases fin_G2_cases i with rfl | rfl
  · have e0 : reflect .G2 g2ir (Pi.single g2ia 1) g2ia = 1 := by decide
    have e1 : reflect .G2 g2ir (Pi.single g2ia 1) g2ir = 3 := by decide
    rw [e0, e1, Pi.single_eq_same, Pi.single_eq_of_ne hne]
    group
  · have e0 : reflect .G2 g2ir (Pi.single g2ir 1) g2ia = 0 := by decide
    have e1 : reflect .G2 g2ir (Pi.single g2ir 1) g2ir = -1 := by decide
    rw [e0, e1, Pi.single_eq_of_ne hne.symm, Pi.single_eq_same]
    group


variable (φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) L →* ↥(adjointGroup .G2 L))
  (hφ : ∀ γ ∈ CFSG.LieType.RootSystem.roots
    (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)), ∀ c : L,
    φ (CFSG.LieType.Steinberg.SL.x 2 L γ c) = a2y γ c)

include hφ in
theorem torusGroup_le_range_a2 :
    torusGroup .G2 L ≤ φ.range.map (adjointGroup .G2 L).subtype := by
  intro h hh
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  set t := c g2ia * c g2ir with ht
  set s := c g2ia * c g2ir ^ 2 with hs
  refine ⟨φ (wSL (show (0 : Fin 3) ≠ 1 by decide) (t : L) *
      wSL (show (0 : Fin 3) ≠ 1 by decide) (-1) *
      (wSL (show (1 : Fin 3) ≠ 2 by decide) (s : L) *
        wSL (show (1 : Fin 3) ≠ 2 by decide) (-1))), ⟨_, rfl⟩, ?_⟩
  rw [Subgroup.coe_subtype, map_mul, phi_D01 φ hφ t, phi_D12 φ hφ s]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  change torusElt .G2 L g2ia t * (weylElt .G2 L g2ir 1 * torusElt .G2 L g2ia s *
    (weylElt .G2 L g2ir 1)⁻¹) = _
  rw [weylElt_r_conj_torusElt_a, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  have c0 : Tag.G2.cartan g2ia g2ia = 2 := by decide
  have c1 : Tag.G2.cartan g2ia g2ir = -1 := by decide
  rcases fin_G2_cases j with rfl | rfl
  · simp only [Pi.mul_apply, c0, ↓reduceIte, ht, hs]
    rw [mul_zpow]
    group
  · have hne : g2ir ≠ g2ia := by decide
    simp only [Pi.mul_apply, c1, hne, ↓reduceIte, ht, hs]
    group

include hφ in
theorem rootSpan_long_le_range_a2 :
    rootSpan .G2 L {g2a, -g2a, g2b, -g2b, g2c, -g2c} ≤
      φ.range.map (adjointGroup .G2 L).subtype := by
  refine iSup₂_le fun α hα => fun g hg => ?_
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hg
  obtain ⟨γ, hγ, rfl⟩ := exists_a2_root hα
  set s := (rootOperatorFamily .G2).pinnedFamilySign (g2CommRoot (a2pos (γ 0, γ 1)))
  refine ⟨φ (CFSG.LieType.Steinberg.SL.x 2 L γ ((s : L) * c)), ⟨_, rfl⟩, ?_⟩
  rw [Subgroup.coe_subtype, hφ γ hγ, coe_a2y hγ, ← mul_assoc,
    (rootOperatorFamily .G2).pinnedFamilySign_mul_self L, one_mul]

include hφ in
theorem toralCentralizer_threeA_le_range_a2 {ζ : Lˣ} (hζ : orderOf ζ = 3) :
    toralCentralizer .G2 L (Pi.mulSingle g2ir ζ) ≤ φ.range.map (adjointGroup .G2 L).subtype := by
  rw [toralCentralizer_threeA hζ]
  exact sup_le (torusGroup_le_range_a2 φ hφ) (rootSpan_long_le_range_a2 φ hφ)

theorem int_cast_eq_one_of_mul_self [CharP L 2] {s : ℤ} (hs : (s : L) * s = 1) : (s : L) = 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have h : ((s : L) - 1) ^ 2 = 0 := by linear_combination hs + (1 - (s : L)) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)

theorem a2_neg_root {γ : Fin 2 → ℤ}
    (hγ : γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))) :
    -γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2)) ∧
    g2CommRoot (a2pos ((-γ) 0, (-γ) 1)) = -g2CommRoot (a2pos (γ 0, γ 1)) := by
  rcases mem_rootsA2.mp hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨mem_rootsA2.mpr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))), by decide +kernel⟩
  · exact ⟨mem_rootsA2.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))),
      by decide +kernel⟩
  · exact ⟨mem_rootsA2.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))),
      by decide +kernel⟩
  · exact ⟨mem_rootsA2.mpr (Or.inl (by decide)), by decide +kernel⟩
  · exact ⟨mem_rootsA2.mpr (Or.inr (Or.inl (by decide))), by decide +kernel⟩
  · exact ⟨mem_rootsA2.mpr (Or.inr (Or.inr (Or.inl (by decide)))), by decide +kernel⟩

theorem slUnitaryTwist_x [CharP L 2] (σ : L →+* L) {γ : Fin 2 → ℤ}
    (hγ : γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))) (c : L) :
    slUnitaryTwist (2 + 1) σ (CFSG.LieType.Steinberg.SL.x 2 L γ c) =
      CFSG.LieType.Steinberg.SL.x 2 L (-γ) (σ c) := by
  rcases mem_rootsA2.mp hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [CFSG.LieType.Steinberg.SL.x_eq (show (0 : Fin 3) ≠ 1 by decide) (by decide) c,
      CFSG.LieType.Steinberg.SL.x_eq (show (1 : Fin 3) ≠ 0 by decide) (by decide) (σ c),
      slUnitaryTwist_transvection]
  · rw [CFSG.LieType.Steinberg.SL.x_eq (show (1 : Fin 3) ≠ 2 by decide) (by decide) c,
      CFSG.LieType.Steinberg.SL.x_eq (show (2 : Fin 3) ≠ 1 by decide) (by decide) (σ c),
      slUnitaryTwist_transvection]
  · rw [CFSG.LieType.Steinberg.SL.x_eq (show (0 : Fin 3) ≠ 2 by decide) (by decide) c,
      CFSG.LieType.Steinberg.SL.x_eq (show (2 : Fin 3) ≠ 0 by decide) (by decide) (σ c),
      slUnitaryTwist_transvection]
  · rw [CFSG.LieType.Steinberg.SL.x_eq (show (1 : Fin 3) ≠ 0 by decide) (by decide) c,
      CFSG.LieType.Steinberg.SL.x_eq (show (0 : Fin 3) ≠ 1 by decide) (by decide) (σ c),
      slUnitaryTwist_transvection]
  · rw [CFSG.LieType.Steinberg.SL.x_eq (show (2 : Fin 3) ≠ 1 by decide) (by decide) c,
      CFSG.LieType.Steinberg.SL.x_eq (show (1 : Fin 3) ≠ 2 by decide) (by decide) (σ c),
      slUnitaryTwist_transvection]
  · rw [CFSG.LieType.Steinberg.SL.x_eq (show (2 : Fin 3) ≠ 0 by decide) (by decide) c,
      CFSG.LieType.Steinberg.SL.x_eq (show (0 : Fin 3) ≠ 2 by decide) (by decide) (σ c),
      slUnitaryTwist_transvection]

include hφ in
theorem a2_unitaryTwist [Finite L] [CharP L 2] (σ : L →+* L)
    (A : Matrix.SpecialLinearGroup (Fin (2 + 1)) L) :
    ((φ (slUnitaryTwist (2 + 1) σ A) : adjointGroup .G2 L) : ModGL .G2 L) =
      canonicalRep (coxeterSystem .G2) L g2LongestWeyl *
        baseChangeGL σ ((φ A : adjointGroup .G2 L) : ModGL .G2 L) *
        (canonicalRep (coxeterSystem .G2) L g2LongestWeyl)⁻¹ := by
  have key : (adjointGroup .G2 L).subtype.comp (φ.comp (slUnitaryTwist (2 + 1) σ)) =
      (MulAut.conj (canonicalRep (coxeterSystem .G2) L g2LongestWeyl)).toMonoidHom.comp
        ((baseChangeGL σ).comp ((adjointGroup .G2 L).subtype.comp φ)) := by
    obtain ⟨⟨-, ⟨O⟩, hx, -⟩, -⟩ := CFSG.LieType.Steinberg.RankTwo.sl3_rankTwoPresentation.{0} L
    refine MonoidHom.eq_of_eqOn_dense (closure_range_eq_top_of_presentationB hx O) ?_
    intro X hX
    simp only [Set.mem_iUnion, Set.mem_range] at hX
    obtain ⟨γ, hγ, c, rfl⟩ := hX
    obtain ⟨hnγ, hroot⟩ := a2_neg_root hγ
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [slUnitaryTwist_x σ hγ, hφ _ hnγ, hφ _ hγ, coe_a2y hnγ, coe_a2y hγ,
      baseChangeGL_pinnedX, g2_longest_conj_pinnedX (isRoot_of_long (a2_long_roots hγ)), hroot,
      int_cast_eq_one_of_mul_self ((rootOperatorFamily .G2).pinnedFamilySign_mul_self L _),
      int_cast_eq_one_of_mul_self ((rootOperatorFamily .G2).pinnedFamilySign_mul_self L _),
      one_mul, one_mul]
  exact DFunLike.congr_fun key A

theorem conjTr_eq_slUnitaryTwist_inv {n : ℕ} (σ : L ≃+* L)
    (A : Matrix.SpecialLinearGroup (Fin n) L) :
    CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) L) =
      ((slUnitaryTwist n (σ : L →+* L) A⁻¹ : Matrix.SpecialLinearGroup (Fin n) L) :
        Matrix (Fin n) (Fin n) L) := by
  change ((A : Matrix (Fin n) (Fin n) L).map σ)ᵀ =
    ((((A⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ).map σ
  rw [inv_inv, Matrix.transpose_map]

theorem conjTr_mul_inv_mul_of_twist_fixed {n : ℕ} (σ : L ≃+* L)
    {A A₀ : Matrix.SpecialLinearGroup (Fin n) L}
    (h : A₀ * slUnitaryTwist n (σ : L →+* L) A * A₀⁻¹ = A) :
    CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) L) *
        ((A₀⁻¹ : Matrix.SpecialLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        (A : Matrix (Fin n) (Fin n) L) =
      ((A₀⁻¹ : Matrix.SpecialLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  rw [conjTr_eq_slUnitaryTwist_inv, map_inv]
  have h1 : slUnitaryTwist n (σ : L →+* L) A = A₀⁻¹ * A * A₀ := by
    calc slUnitaryTwist n (σ : L →+* L) A =
        A₀⁻¹ * (A₀ * slUnitaryTwist n (σ : L →+* L) A * A₀⁻¹) * A₀ := by group
      _ = A₀⁻¹ * A * A₀ := by rw [h]
  have h2 : (A₀⁻¹ * A * A₀)⁻¹ * A₀⁻¹ * A = A₀⁻¹ := by group
  rw [h1]
  calc (((A₀⁻¹ * A * A₀)⁻¹ : Matrix.SpecialLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((A₀⁻¹ : Matrix.SpecialLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        (A : Matrix (Fin n) (Fin n) L) =
      (((A₀⁻¹ * A * A₀)⁻¹ * A₀⁻¹ * A : Matrix.SpecialLinearGroup (Fin n) L) :
        Matrix (Fin n) (Fin n) L) := by simp only [Matrix.SpecialLinearGroup.coe_mul]
    _ = _ := by rw [h2]

theorem conj_mem_statedSU_of_conjTr {n q : ℕ} (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ q)
    {G : Matrix (Fin n) (Fin n) L} {P A : GL (Fin n) L}
    (hP : CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L) * G *
      (P : Matrix (Fin n) (Fin n) L) = 1)
    (hA : CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) L) * G *
      (A : Matrix (Fin n) (Fin n) L) = G) (hdet : (A : Matrix (Fin n) (Fin n) L).det = 1) :
    P⁻¹ * A * P ∈ CFSG.Assembly.LowTwoRank.StatedSU n q L := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  · have hmap : ∀ X : Matrix (Fin n) (Fin n) L, (X.map (· ^ q))ᵀ =
        CFSG.LieType.Universal.Unitary.conjTr σ X := fun X => by
      rw [CFSG.LieType.Universal.Unitary.conjTr]
      congr 1
      ext i j
      simp [hσ]
    rw [hmap]
    have hPinv : ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        (P : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hG : G = CFSG.LieType.Universal.Unitary.conjTr σ
        ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
      have h1 : CFSG.LieType.Universal.Unitary.conjTr σ
          ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L) = 1 := by
        rw [← CFSG.LieType.Universal.Unitary.conjTr_mul, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, CFSG.LieType.Universal.Unitary.conjTr_one]
      calc G = (CFSG.LieType.Universal.Unitary.conjTr σ
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L)) * G *
            ((P : Matrix (Fin n) (Fin n) L) * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
            := by
            rw [h1, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
              Matrix.mul_one]
        _ = CFSG.LieType.Universal.Unitary.conjTr σ
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L) * G *
              (P : Matrix (Fin n) (Fin n) L)) *
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hP, Matrix.mul_one]
    rw [Units.val_mul, Units.val_mul, CFSG.LieType.Universal.Unitary.conjTr_mul,
      CFSG.LieType.Universal.Unitary.conjTr_mul]
    calc CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L) *
          (CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) L) *
            CFSG.LieType.Universal.Unitary.conjTr σ
              ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          (((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (A : Matrix (Fin n) (Fin n) L) *
            (P : Matrix (Fin n) (Fin n) L)) =
        CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L) *
          (CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) L) *
            (CFSG.LieType.Universal.Unitary.conjTr σ
              ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
              ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
            (A : Matrix (Fin n) (Fin n) L)) * (P : Matrix (Fin n) (Fin n) L) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hG, hA, hP]

theorem exists_su3_of_threeA [Finite L] [CharP L 2] {f : ℕ} (hL : Nat.card L = (2 ^ f) ^ 2)
    {G : Type*} [Group G] (β : G →* adjointGroup .G2 L) (hβ : Function.Injective β)
    (hβσ : ∀ x, haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      baseChangeGL (CFSG.LieType.BorelTits.unitaryInvolution L 2 f : L →+* L)
        (β x : ModGL .G2 L) = β x)
    {e : G} {y : ModGL .G2 L} (hy : y ∈ adjointGroup .G2 L) {ζ : Lˣ} (hζ : orderOf ζ = 3)
    (hζq : (ζ : L) ^ (2 ^ f) = ((ζ⁻¹ : Lˣ) : L))
    (he : (β e : ModGL .G2 L) = y * rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) * y⁻¹) :
    ∃ ι : Subgroup.centralizer ({e} : Set G) →* GL (Fin 3) L, Function.Injective ι ∧
      ∀ x, ι x ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := CFSG.LieType.BorelTits.unitaryInvolution L 2 f with hσdef
  have hσapp : ∀ c, σ c = c ^ (2 ^ f) := fun c =>
    CFSG.LieType.BorelTits.unitaryInvolution_apply L 2 f c
  have hσσ : ∀ c, (σ : L →+* L) ((σ : L →+* L) c) = c := fun c =>
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hL c
  set s := baseChangeGL (τ := .G2) (σ : L →+* L) with hsdef
  have hss : ∀ g, s (s g) = g := fun g => baseChangeGL_involutive hσσ g
  set n₀ := canonicalRep (coxeterSystem .G2) L g2LongestWeyl with hn₀
  have hn : s n₀ = n₀ := baseChangeGL_g2_longest _
  have hn2 : n₀ * n₀ = 1 := g2_longest_mul_self
  have hn₀C : n₀ ∈ adjointGroup .G2 L := canonicalRep_mem_adjointGroup _ L _
  set d := rootDiagUnit .G2 (Pi.mulSingle g2ir ζ) with hddef
  have hd : n₀ * d * n₀⁻¹ = s d := by
    rw [hddef, g2_longest_conj_rootDiagUnit, hsdef,
      baseChangeGL_rootDiagUnit_mulSingle (by rw [RingHom.coe_coe, hσapp]; exact hζq)]
  have hE : s (y * d * y⁻¹) = y * d * y⁻¹ := by rw [← he]; exact hβσ e
  obtain ⟨hc1, hc2, hc3⟩ := descent_of_fixed s hss hn hn2 hd hE
  set c := y⁻¹ * s y * n₀⁻¹ with hcdef
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := L)
  set Φ := (adjointGroup .G2 L).subtype.comp φ with hΦ
  have hΦinj : Function.Injective Φ := (adjointGroup .G2 L).subtype_injective.comp hφinj
  have hrange : φ.range.map (adjointGroup .G2 L).subtype = Φ.range := by
    rw [hΦ, MonoidHom.range_comp]
  have hcen : ∀ w : ModGL .G2 L, w ∈ adjointGroup .G2 L → w * d = d * w → w ∈ Φ.range := by
    intro w hw hwd
    rw [← hrange]
    refine toralCentralizer_threeA_le_range_a2 φ hφ hζ (mem_toralCentralizer.2 ⟨hw, ?_⟩)
    rw [← hwd, mul_inv_cancel_right]
  have hsC : ∀ g, g ∈ adjointGroup .G2 L → s g ∈ adjointGroup .G2 L := fun g hg =>
    baseChangeGL_mem_adjointGroup_G2 _ hg
  have hcC : c ∈ adjointGroup .G2 L :=
    mul_mem (mul_mem (inv_mem hy) (hsC y hy)) (inv_mem hn₀C)
  obtain ⟨A₀, hA₀⟩ := hcen c hcC hc1
  have htw : ∀ A, Φ (slUnitaryTwist (2 + 1) (σ : L →+* L) A) = n₀ * s (Φ A) * n₀⁻¹ := fun A =>
    a2_unitaryTwist φ hφ (σ : L →+* L) A
  have hA₀ψ : A₀ * slUnitaryTwist (2 + 1) (σ : L →+* L) A₀ = 1 := by
    apply hΦinj
    rw [map_mul, htw, hA₀, map_one]
    exact hc2
  have hψA₀ : slUnitaryTwist (2 + 1) (σ : L →+* L) A₀ = A₀⁻¹ := eq_inv_of_mul_eq_one_right hA₀ψ
  have hherm : CFSG.LieType.Universal.Unitary.conjTr σ
      ((A₀⁻¹ : Matrix.SpecialLinearGroup (Fin (2 + 1)) L) : Matrix (Fin 3) (Fin 3) L) =
      ((A₀⁻¹ : Matrix.SpecialLinearGroup (Fin (2 + 1)) L) : Matrix (Fin 3) (Fin 3) L) := by
    rw [conjTr_eq_slUnitaryTwist_inv, inv_inv, hψA₀]
  have hdet : ((A₀⁻¹ : Matrix.SpecialLinearGroup (Fin (2 + 1)) L) :
      Matrix (Fin 3) (Fin 3) L).det ≠ 0 := by
    rw [(A₀⁻¹).2]
    exact one_ne_zero
  obtain ⟨P, hP⟩ := CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one hL hherm hdet
  set j : Subgroup.centralizer ({e} : Set G) →* ModGL .G2 L :=
    (MulAut.conj y⁻¹).toMonoidHom.comp
      ((adjointGroup .G2 L).subtype.comp (β.comp (Subgroup.centralizer ({e} : Set G)).subtype))
    with hjdef
  have hjapp : ∀ x, j x = y⁻¹ * (β x : ModGL .G2 L) * y := fun x => by
    simp [hjdef]
  have hjinj : Function.Injective j := by
    intro x x' h
    rw [hjapp, hjapp] at h
    exact Subtype.ext (hβ (Subtype.ext (by simpa using h)))
  have hjfix : ∀ x : Subgroup.centralizer ({e} : Set G),
      s (β x : ModGL .G2 L) = β x ∧ (β x : ModGL .G2 L) * (y * d * y⁻¹) =
        (y * d * y⁻¹) * β x := by
    intro x
    refine ⟨hβσ x, ?_⟩
    rw [← he, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_singleton_iff.mp x.2)]
  have hjmem : ∀ x, j x ∈ Φ.range := by
    intro x
    obtain ⟨hx1, hx2⟩ := hjfix x
    rw [hjapp]
    refine hcen _ ?_ (hc3 _ hx1 hx2).1
    exact mul_mem (mul_mem (inv_mem hy) (β x).2) hy
  set j' : Subgroup.centralizer ({e} : Set G) →* Φ.range := j.codRestrict _ hjmem with hj'
  set eΦ := MonoidHom.ofInjective hΦinj with heΦ
  set k : Subgroup.centralizer ({e} : Set G) →* Matrix.SpecialLinearGroup (Fin (2 + 1)) L :=
    eΦ.symm.toMonoidHom.comp j' with hkdef
  have hk : ∀ x, Φ (k x) = j x := fun x => by
    have h1 := congrArg Subtype.val (eΦ.apply_symm_apply (j' x))
    rw [heΦ, MonoidHom.ofInjective_apply] at h1
    exact h1
  refine ⟨(MulAut.conj P⁻¹).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL.comp k), ?_,
    fun x => ?_⟩
  · refine (MulAut.conj P⁻¹).injective.comp (Matrix.SpecialLinearGroup.toGL_injective.comp ?_)
    intro x x' h
    apply hjinj
    rw [← hk, ← hk, h]
  ·
    obtain ⟨hx1, hx2⟩ := hjfix x
    have hfix := (hc3 _ hx1 hx2).2
    rw [← hjapp, ← hk, ← hA₀, ← htw] at hfix
    have hfix' : A₀ * slUnitaryTwist (2 + 1) (σ : L →+* L) (k x) * A₀⁻¹ = k x := by
      apply hΦinj
      rw [map_mul, map_mul, map_inv]
      exact hfix
    have hu := conjTr_mul_inv_mul_of_twist_fixed σ hfix'
    have hmem := conj_mem_statedSU_of_conjTr (A := Matrix.SpecialLinearGroup.toGL (k x)) σ
      hσapp hP hu (k x).2
    simpa [MulAut.conj_apply] using hmem

end ThreeA

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4
