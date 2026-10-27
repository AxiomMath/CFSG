module

public import CFSG.RankThree.PartOne.KE.E8A4Native
public import CFSG.RankThree.PartOne.KE.SLnFamily
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Standard

variable (L : Type) [Field L]

@[expose] def e8a4Equiv : SL(5, L) ≃* subsystemGroup Tag.E8 L e8a4support :=
  (MulEquiv.ofBijective (e8a4Rep L) (E8_native_A4_faithful_SL5_all_characteristics L).1).symm

@[expose] def e8rhoJ4 : SL(5, L) →* ModGL Tag.E8 L :=
  (subsystemGroup Tag.E8 L e8a4support).subtype.comp (e8a4Equiv L).toMonoidHom

variable {L}

theorem e8a4Rep_e8a4Equiv (X : SL(5, L)) : e8a4Rep L (e8a4Equiv L X) = X :=
  (MulEquiv.ofBijective (e8a4Rep L)
    (E8_native_A4_faithful_SL5_all_characteristics L).1).apply_symm_apply X

theorem e8rhoJ4_e8a4Rep {g : ModGL Tag.E8 L} (hg : g ∈ subsystemGroup Tag.E8 L e8a4support) :
    e8rhoJ4 L (e8a4Rep L ⟨g, hg⟩) = g := by
  have h : e8a4Equiv L (e8a4Rep L ⟨g, hg⟩) = ⟨g, hg⟩ :=
    (MulEquiv.ofBijective (e8a4Rep L)
      (E8_native_A4_faithful_SL5_all_characteristics L).1).symm_apply_apply ⟨g, hg⟩
  exact congrArg Subtype.val h

theorem e8rhoJ4_mem (X : SL(5, L)) : e8rhoJ4 L X ∈ subsystemGroup Tag.E8 L e8a4support :=
  (e8a4Equiv L X).2

theorem e8a4Mat_e8rhoJ4 (X : SL(5, L)) :
    e8a4Mat (e8rhoJ4 L X) = (X : Matrix (Fin 5) (Fin 5) L) := by
  have h := congrArg (fun Y : SL(5, L) => (Y : Matrix (Fin 5) (Fin 5) L)) (e8a4Rep_e8a4Equiv X)
  exact h

theorem e8rhoJ4_injective : Function.Injective (e8rhoJ4 L) := by
  intro X Y h
  apply Subtype.ext
  rw [← e8a4Mat_e8rhoJ4 X, ← e8a4Mat_e8rhoJ4 Y, h]

theorem e8rhoJ4_range : (e8rhoJ4 L).range = subsystemGroup Tag.E8 L e8a4support := by
  refine le_antisymm (fun g ⟨X, hX⟩ => hX ▸ e8rhoJ4_mem X) fun g hg => ?_
  exact ⟨e8a4Rep L ⟨g, hg⟩, e8rhoJ4_e8a4Rep hg⟩

theorem e8rhoJ4_transvection (i j : Fin 5) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, e8rhoJ4 L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E8 L (chainRoot e8a4chain i j) ((ε : L) * t) := by
  obtain ⟨e, he, h⟩ := e8a4RootFamily_all (K := L) i j hij
  have hee : ((e : ℤ) : L) * ((e : ℤ) : L) = 1 := by rcases he with rfl | rfl <;> simp
  refine ⟨⟨((e : ℤ) : L), ((e : ℤ) : L), hee, hee⟩, fun s => ?_⟩
  have hmem := pinnedX_mem_e8a4Group (K := L) (e8a4chainRoot_mem_parabolicRoots hij)
    (((e : ℤ) : L) * s)
  have hrep : e8a4Rep L ⟨pinnedX Tag.E8 L (chainRoot e8a4chain i j) (((e : ℤ) : L) * s), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij s := by
    apply Subtype.ext
    rw [coe_e8a4Rep, h, CFSG.LinearGroups.coe_transvection]
    congr 1
    rw [← mul_assoc, hee, one_mul]
  rw [← hrep]
  exact e8rhoJ4_e8a4Rep hmem

end Standard


section Transport

variable {L : Type} [Field L]

@[expose] def wbE8A4 (v : WeylGroup Tag.E8) (k : Fin 5) : Fin Tag.E8.rank → ℤ := v • e8a4Weight k

@[expose] def sigmaRootE8A4 (v : WeylGroup Tag.E8) (i j : Fin 5) : Fin Tag.E8.rank → ℤ :=
  wbE8A4 v i - wbE8A4 v j

variable (L) in
@[expose] def rhoSigmaE8A4 (v : WeylGroup Tag.E8) : SL(5, L) →* ModGL Tag.E8 L :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E8) L v)).toMonoidHom.comp (e8rhoJ4 L)

theorem rhoSigmaE8A4_apply (v : WeylGroup Tag.E8) (X : SL(5, L)) :
    rhoSigmaE8A4 L v X = canonicalRep (coxeterSystem Tag.E8) L v * e8rhoJ4 L X *
      (canonicalRep (coxeterSystem Tag.E8) L v)⁻¹ := by
  simp [rhoSigmaE8A4, MulAut.conj_apply]

theorem rhoSigmaE8A4_injective (v : WeylGroup Tag.E8) : Function.Injective (rhoSigmaE8A4 L v) :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E8) L v)).injective.comp e8rhoJ4_injective

theorem sigmaRootE8A4_eq_smul (v : WeylGroup Tag.E8) (i j : Fin 5) :
    sigmaRootE8A4 v i j = v • chainRoot e8a4chain i j := by
  rw [e8a4chainRoot_eq_sub, smul_sub]
  rfl

theorem isRoot_sigmaRootE8A4 (v : WeylGroup Tag.E8) {i j : Fin 5} (hij : i ≠ j) :
    IsRoot Tag.E8 (sigmaRootE8A4 v i j) := by
  rw [sigmaRootE8A4_eq_smul]
  exact IsRoot.smul (e8a4chainRoot_mem_parabolicRoots hij).1 v

theorem sigmaRootE8A4_neg (v : WeylGroup Tag.E8) (i j : Fin 5) :
    -sigmaRootE8A4 v i j = sigmaRootE8A4 v j i := neg_sub _ _

theorem sigmaRootE8A4_add (v : WeylGroup Tag.E8) (i j k : Fin 5) :
    sigmaRootE8A4 v i j + sigmaRootE8A4 v j k = sigmaRootE8A4 v i k := sub_add_sub_cancel _ _ _

theorem rhoSigmaE8A4_transvection (v : WeylGroup Tag.E8) (i j : Fin 5) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, rhoSigmaE8A4 L v (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E8 L (sigmaRootE8A4 v i j) ((ε : L) * t) := by
  obtain ⟨ε₀, h₀⟩ := e8rhoJ4_transvection (L := L) i j hij
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX (canonicalRep_mem_monomialSubgroup L v)
    (e8a4chainRoot_mem_parabolicRoots hij).1
  have hπ : weylQuotientHom Tag.E8 L ⟨canonicalRep (coxeterSystem Tag.E8) L v,
      canonicalRep_mem_monomialSubgroup L v⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  refine ⟨μ * ε₀, fun t => ?_⟩
  rw [rhoSigmaE8A4_apply, h₀, hμ, hπ, ← sigmaRootE8A4_eq_smul, Units.val_mul, mul_assoc]

end Transport


section Range

variable {L : Type} [Field L]

@[expose] def sigmaSetE8A4 (v : WeylGroup Tag.E8) : Set (Fin Tag.E8.rank → ℤ) :=
  (fun γ => v • γ) '' parabolicRoots Tag.E8 e8a4support

theorem rhoSigmaE8A4_range (v : WeylGroup Tag.E8) :
    (rhoSigmaE8A4 L v).range = rootSpan Tag.E8 L (sigmaSetE8A4 v) := by
  rw [rhoSigmaE8A4, MonoidHom.range_comp, e8rhoJ4_range, subsystemGroup_eq_rootSpan,
    map_conj_rootSpan v (fun γ hγ => hγ.1)]
  rfl

theorem sigmaSetE8A4_eq (v : WeylGroup Tag.E8) :
    sigmaSetE8A4 v = {r | ∃ i j : Fin 5, i ≠ j ∧ r = sigmaRootE8A4 v i j} := by
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := exists_e8a4chainRoot_of_mem hγ
    exact ⟨i, j, hij, (sigmaRootE8A4_eq_smul v i j).symm⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨chainRoot e8a4chain i j, e8a4chainRoot_mem_parabolicRoots hij,
      (sigmaRootE8A4_eq_smul v i j).symm⟩

end Range


section Torus

variable {L : Type} [Field L]

theorem rhoSigmaE8A4_torus (v : WeylGroup Tag.E8) (b : Fin Tag.E8.rank → Lˣ) (A : SL(5, L)) :
    rootDiagUnit Tag.E8 b * rhoSigmaE8A4 L v A * (rootDiagUnit Tag.E8 b)⁻¹ =
      rhoSigmaE8A4 L v (conjDiagn (fun i => rootChar b (wbE8A4 v i)) A) := by
  set d : Fin 5 → Lˣ := fun i => rootChar b (wbE8A4 v i) with hd
  have h : (MulAut.conj (rootDiagUnit Tag.E8 b)).toMonoidHom.comp (rhoSigmaE8A4 L v) =
      (rhoSigmaE8A4 L v).comp (conjDiagnHom d) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    obtain ⟨ε, hε⟩ := rhoSigmaE8A4_transvection (L := L) v i j hij
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiagnHom_apply]
    rw [hε, conjDiagn_transvection d hij, hε,
      rootDiagUnit_conj_pinnedX b (isRoot_sigmaRootE8A4 v hij)]
    congr 1
    rw [sigmaRootE8A4, rootChar_sub]
    simp only [hd, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  exact DFunLike.congr_fun h A

theorem rhoSigmaE8A4_diagonal (v : WeylGroup Tag.E8) (A : SL(5, L))
    (hA : ∀ i j : Fin 5, i ≠ j → (A : Matrix (Fin 5) (Fin 5) L) i j = 0) :
    rhoSigmaE8A4 L v A ∈ torusGroup Tag.E8 L := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hTor, -, -, -⟩ :=
    E8_native_A4_faithful_SL5_all_characteristics L
  have hdiag : (A : Matrix (Fin 5) (Fin 5) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 5) (Fin 5) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 5) (Fin 5) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_five] at hdet
  have h0 : (A : Matrix (Fin 5) (Fin 5) L) 0 0 ≠ 0 := fun h => by
    rw [h] at hdet
    simp at hdet
  have h01 : (A : Matrix (Fin 5) (Fin 5) L) 0 0 * (A : Matrix (Fin 5) (Fin 5) L) 1 1 ≠ 0 :=
    fun h => by
      rw [h] at hdet
      simp at hdet
  have h012 : (A : Matrix (Fin 5) (Fin 5) L) 0 0 * (A : Matrix (Fin 5) (Fin 5) L) 1 1 *
      (A : Matrix (Fin 5) (Fin 5) L) 2 2 ≠ 0 := fun h => by
    rw [h] at hdet
    simp at hdet
  have h0123 : (A : Matrix (Fin 5) (Fin 5) L) 0 0 * (A : Matrix (Fin 5) (Fin 5) L) 1 1 *
      (A : Matrix (Fin 5) (Fin 5) L) 2 2 * (A : Matrix (Fin 5) (Fin 5) L) 3 3 ≠ 0 :=
    fun h => by
      rw [h] at hdet
      simp at hdet
  obtain ⟨ua, hua⟩ : ∃ u : Lˣ, (u : L) = (A : Matrix (Fin 5) (Fin 5) L) 0 0 :=
    ⟨Units.mk0 _ h0, rfl⟩
  obtain ⟨ub, hub⟩ : ∃ u : Lˣ, (u : L) =
      (A : Matrix (Fin 5) (Fin 5) L) 0 0 * (A : Matrix (Fin 5) (Fin 5) L) 1 1 :=
    ⟨Units.mk0 _ h01, rfl⟩
  obtain ⟨uc, huc⟩ : ∃ u : Lˣ, (u : L) =
      (A : Matrix (Fin 5) (Fin 5) L) 0 0 * (A : Matrix (Fin 5) (Fin 5) L) 1 1 *
        (A : Matrix (Fin 5) (Fin 5) L) 2 2 :=
    ⟨Units.mk0 _ h012, rfl⟩
  obtain ⟨ud, hud⟩ : ∃ u : Lˣ, (u : L) =
      (A : Matrix (Fin 5) (Fin 5) L) 0 0 * (A : Matrix (Fin 5) (Fin 5) L) 1 1 *
        (A : Matrix (Fin 5) (Fin 5) L) 2 2 * (A : Matrix (Fin 5) (Fin 5) L) 3 3 :=
    ⟨Units.mk0 _ h0123, rfl⟩
  have d1 : ((ua⁻¹ * ub : Lˣ) : L) = (A : Matrix (Fin 5) (Fin 5) L) 1 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hua, hub]
    exact inv_mul_cancel_left₀ h0 _
  have d2 : ((ub⁻¹ * uc : Lˣ) : L) = (A : Matrix (Fin 5) (Fin 5) L) 2 2 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hub, huc]
    exact inv_mul_cancel_left₀ h01 _
  have d3 : ((uc⁻¹ * ud : Lˣ) : L) = (A : Matrix (Fin 5) (Fin 5) L) 3 3 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, huc, hud]
    exact inv_mul_cancel_left₀ h012 _
  have d4 : ((ud⁻¹ : Lˣ) : L) = (A : Matrix (Fin 5) (Fin 5) L) 4 4 := by
    rw [Units.val_inv_eq_inv_val, hud]
    exact (eq_inv_of_mul_eq_one_right hdet).symm
  have hrep : e8a4Rep L ⟨e8a4TorusElt ua ub uc ud, e8a4TorusElt_mem ua ub uc ud⟩ = A := by
    apply Subtype.ext
    rw [coe_e8a4Rep, e8a4Mat_e8a4TorusElt, hdiag]
    congr 1
    funext i
    fin_cases i
    exacts [hua, d1, d2, d3, d4]
  have hJ : e8rhoJ4 L A = e8a4TorusElt ua ub uc ud := by
    rw [← hrep]
    exact e8rhoJ4_e8a4Rep (e8a4TorusElt_mem ua ub uc ud)
  have hH : e8a4TorusElt ua ub uc ud ∈ torusGroup Tag.E8 L :=
    ((hTor _).2 ⟨ua, ub, uc, ud, rfl⟩).2
  rw [rhoSigmaE8A4_apply, hJ]
  exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1 hH

end Torus


section BlockSL

variable {L : Type} [Field L]

theorem e8rhoJ4_blockSL (Y : SL(2, L)) :
    e8rhoJ4 L (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 3 Y) =
      simpleRootSL2 Tag.E8 L (e8Index 0) Y := by
  have hx : ∀ c : L, e8rhoJ4 L (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 5) ≠ 1 by decide) c) = xUnit Tag.E8 L (e8Index 0) c := by
    intro c
    have hmem : xUnit Tag.E8 L (e8Index 0) c ∈ subsystemGroup Tag.E8 L e8a4support :=
      xUnit_mem_subsystemGroup mem_e8a4support_0 c
    have hrep : e8a4Rep L ⟨xUnit Tag.E8 L (e8Index 0) c, hmem⟩ =
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 1 by decide) c := by
      apply Subtype.ext
      rw [coe_e8a4Rep, CFSG.LinearGroups.coe_transvection]
      exact e8a4Mat_x1 c
    rw [← hrep]
    exact e8rhoJ4_e8a4Rep hmem
  have hy : ∀ c : L, e8rhoJ4 L (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 5) ≠ 0 by decide) c) = yUnit Tag.E8 L (e8Index 0) c := by
    intro c
    have hmem : yUnit Tag.E8 L (e8Index 0) c ∈ subsystemGroup Tag.E8 L e8a4support :=
      yUnit_mem_subsystemGroup mem_e8a4support_0 c
    have hrep : e8a4Rep L ⟨yUnit Tag.E8 L (e8Index 0) c, hmem⟩ =
        Matrix.SpecialLinearGroup.transvection (show (1 : Fin 5) ≠ 0 by decide) c := by
      apply Subtype.ext
      rw [coe_e8a4Rep, CFSG.LinearGroups.coe_transvection]
      exact e8a4Mat_y1 c
    rw [← hrep]
    exact e8rhoJ4_e8a4Rep hmem
  have e0 : (finSumFinEquiv.symm (0 : Fin 5) : Fin 2 ⊕ Fin 3) = Sum.inl 0 := rfl
  have e1 : (finSumFinEquiv.symm (1 : Fin 5) : Fin 2 ⊕ Fin 3) = Sum.inl 1 := rfl
  have e2 : (finSumFinEquiv.symm (2 : Fin 5) : Fin 2 ⊕ Fin 3) = Sum.inr 0 := rfl
  have e3 : (finSumFinEquiv.symm (3 : Fin 5) : Fin 2 ⊕ Fin 3) = Sum.inr 1 := rfl
  have e4 : (finSumFinEquiv.symm (4 : Fin 5) : Fin 2 ⊕ Fin 3) = Sum.inr 2 := rfl
  have hu : ∀ c : L,
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 3 (uSL c) : SL(5, L)) =
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 5) ≠ 1 by decide) c := by
    intro c
    apply Subtype.ext
    rw [CFSG.LinearGroups.coe_transvection]
    have h : ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 3 (uSL c) : SL(5, L)) :
        Matrix (Fin 5) (Fin 5) L) = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (uSL c : Matrix (Fin 2) (Fin 2) L) 0 0 1) := rfl
    rw [h]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [reindex_apply, submatrix_apply, e0, e1, e2, e3, e4, coe_uSL, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  have hv : ∀ c : L,
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 3 (vSL c) : SL(5, L)) =
        Matrix.SpecialLinearGroup.transvection (show (1 : Fin 5) ≠ 0 by decide) c := by
    intro c
    apply Subtype.ext
    rw [CFSG.LinearGroups.coe_transvection]
    have h : ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 3 (vSL c) : SL(5, L)) :
        Matrix (Fin 5) (Fin 5) L) = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (vSL c : Matrix (Fin 2) (Fin 2) L) 0 0 1) := rfl
    rw [h]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [reindex_apply, submatrix_apply, e0, e1, e2, e3, e4, coe_vSL, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  have key : (e8rhoJ4 L).comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 3) =
      simpleRootSL2 Tag.E8 L (e8Index 0) :=
    eq_simpleRootSL2 (e8Index 0) (fun c => by rw [MonoidHom.comp_apply, hu, hx])
      (fun c => by rw [MonoidHom.comp_apply, hv, hy])
  exact DFunLike.congr_fun key Y

end BlockSL

end CFSG.RankThree.PartOne.KE
