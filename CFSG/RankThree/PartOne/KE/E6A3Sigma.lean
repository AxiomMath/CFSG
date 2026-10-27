module

public import CFSG.RankThree.E6.NativeA3SL4
public import CFSG.RankThree.PartOne.KE.SLnFamily
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (a3Rep a3Mat a3Weight a3TorusElt a3TorusElt_mem a3Mat_a3TorusElt
  a3Mat_x1 a3Mat_y1 coe_a3Rep chain134 support134 chainRoot chainRoot134_mem_parabolicRoots
  exists_chainRoot_of_mem mem_support134_0 pinnedX_mem_a3Group a3RootFamily_all
  E6_native_A3_faithful_SL4_all_characteristics isRoot_a3Weight e6Index)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Standard

variable (L : Type) [Field L]

@[expose] def e6a3Equiv : SL(4, L) ≃* subsystemGroup Tag.E6 L support134 :=
  (MulEquiv.ofBijective (a3Rep L) (E6_native_A3_faithful_SL4_all_characteristics L).1).symm

@[expose] def e6rhoJ3 : SL(4, L) →* ModGL Tag.E6 L :=
  (subsystemGroup Tag.E6 L support134).subtype.comp (e6a3Equiv L).toMonoidHom

variable {L}

theorem a3Rep_e6a3Equiv (X : SL(4, L)) : a3Rep L (e6a3Equiv L X) = X :=
  (MulEquiv.ofBijective (a3Rep L)
    (E6_native_A3_faithful_SL4_all_characteristics L).1).apply_symm_apply X

theorem e6rhoJ3_a3Rep {g : ModGL Tag.E6 L} (hg : g ∈ subsystemGroup Tag.E6 L support134) :
    e6rhoJ3 L (a3Rep L ⟨g, hg⟩) = g := by
  have h : e6a3Equiv L (a3Rep L ⟨g, hg⟩) = ⟨g, hg⟩ :=
    (MulEquiv.ofBijective (a3Rep L)
      (E6_native_A3_faithful_SL4_all_characteristics L).1).symm_apply_apply ⟨g, hg⟩
  exact congrArg Subtype.val h

theorem e6rhoJ3_mem (X : SL(4, L)) : e6rhoJ3 L X ∈ subsystemGroup Tag.E6 L support134 :=
  (e6a3Equiv L X).2

theorem a3Mat_e6rhoJ3 (X : SL(4, L)) :
    a3Mat (e6rhoJ3 L X) = (X : Matrix (Fin 4) (Fin 4) L) := by
  have h := congrArg (fun Y : SL(4, L) => (Y : Matrix (Fin 4) (Fin 4) L)) (a3Rep_e6a3Equiv X)
  exact h

theorem e6rhoJ3_injective : Function.Injective (e6rhoJ3 L) := by
  intro X Y h
  apply Subtype.ext
  rw [← a3Mat_e6rhoJ3 X, ← a3Mat_e6rhoJ3 Y, h]

theorem e6rhoJ3_range : (e6rhoJ3 L).range = subsystemGroup Tag.E6 L support134 := by
  refine le_antisymm (fun g ⟨X, hX⟩ => hX ▸ e6rhoJ3_mem X) fun g hg => ?_
  exact ⟨a3Rep L ⟨g, hg⟩, e6rhoJ3_a3Rep hg⟩

theorem e6rhoJ3_transvection (i j : Fin 4) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, e6rhoJ3 L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (chainRoot chain134 i j) ((ε : L) * t) := by
  obtain ⟨e, he, h⟩ := a3RootFamily_all (K := L) i j hij
  have hee : ((e : ℤ) : L) * ((e : ℤ) : L) = 1 := by rcases he with rfl | rfl <;> simp
  refine ⟨⟨((e : ℤ) : L), ((e : ℤ) : L), hee, hee⟩, fun s => ?_⟩
  have hmem := pinnedX_mem_a3Group (K := L) (chainRoot134_mem_parabolicRoots hij)
    (((e : ℤ) : L) * s)
  have hrep : a3Rep L ⟨pinnedX Tag.E6 L (chainRoot chain134 i j) (((e : ℤ) : L) * s), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij s := by
    apply Subtype.ext
    rw [coe_a3Rep, h, CFSG.LinearGroups.coe_transvection]
    congr 1
    rw [← mul_assoc, hee, one_mul]
  rw [← hrep]
  exact e6rhoJ3_a3Rep hmem

end Standard

section Transport

variable {L : Type} [Field L]

@[expose] def wbE6A3 (v : WeylGroup Tag.E6) (k : Fin 4) : Fin Tag.E6.rank → ℤ := v • a3Weight k

@[expose] def sigmaRootE6A3 (v : WeylGroup Tag.E6) (i j : Fin 4) : Fin Tag.E6.rank → ℤ :=
  wbE6A3 v i - wbE6A3 v j

variable (L) in
@[expose] def rhoSigmaE6A3 (v : WeylGroup Tag.E6) : SL(4, L) →* ModGL Tag.E6 L :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L v)).toMonoidHom.comp (e6rhoJ3 L)

theorem rhoSigmaE6A3_apply (v : WeylGroup Tag.E6) (X : SL(4, L)) :
    rhoSigmaE6A3 L v X = canonicalRep (coxeterSystem Tag.E6) L v * e6rhoJ3 L X *
      (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ := by
  simp [rhoSigmaE6A3, MulAut.conj_apply]

theorem rhoSigmaE6A3_injective (v : WeylGroup Tag.E6) : Function.Injective (rhoSigmaE6A3 L v) :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L v)).injective.comp e6rhoJ3_injective

theorem chainRoot134_eq_sub : ∀ i j : Fin 4,
    chainRoot chain134 i j = a3Weight i - a3Weight j := by
  decide +kernel

theorem sigmaRootE6A3_eq_smul (v : WeylGroup Tag.E6) (i j : Fin 4) :
    sigmaRootE6A3 v i j = v • chainRoot chain134 i j := by
  rw [chainRoot134_eq_sub, smul_sub]
  rfl

theorem isRoot_sigmaRootE6A3 (v : WeylGroup Tag.E6) {i j : Fin 4} (hij : i ≠ j) :
    IsRoot Tag.E6 (sigmaRootE6A3 v i j) := by
  rw [sigmaRootE6A3_eq_smul]
  exact IsRoot.smul (chainRoot134_mem_parabolicRoots hij).1 v

theorem sigmaRootE6A3_neg (v : WeylGroup Tag.E6) (i j : Fin 4) :
    -sigmaRootE6A3 v i j = sigmaRootE6A3 v j i := neg_sub _ _

theorem rhoSigmaE6A3_transvection (v : WeylGroup Tag.E6) (i j : Fin 4) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, rhoSigmaE6A3 L v (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (sigmaRootE6A3 v i j) ((ε : L) * t) := by
  obtain ⟨ε₀, h₀⟩ := e6rhoJ3_transvection (L := L) i j hij
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX (canonicalRep_mem_monomialSubgroup L v)
    (chainRoot134_mem_parabolicRoots hij).1
  have hπ : weylQuotientHom Tag.E6 L ⟨canonicalRep (coxeterSystem Tag.E6) L v,
      canonicalRep_mem_monomialSubgroup L v⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  refine ⟨μ * ε₀, fun t => ?_⟩
  rw [rhoSigmaE6A3_apply, h₀, hμ, hπ, ← sigmaRootE6A3_eq_smul, Units.val_mul, mul_assoc]

end Transport

section Range

variable {L : Type} [Field L]

@[expose] def sigmaSetE6A3 (v : WeylGroup Tag.E6) : Set (Fin Tag.E6.rank → ℤ) :=
  (fun γ => v • γ) '' parabolicRoots Tag.E6 support134

theorem rhoSigmaE6A3_range (v : WeylGroup Tag.E6) :
    (rhoSigmaE6A3 L v).range = rootSpan Tag.E6 L (sigmaSetE6A3 v) := by
  rw [rhoSigmaE6A3, MonoidHom.range_comp, e6rhoJ3_range, subsystemGroup_eq_rootSpan,
    map_conj_rootSpan v (fun γ hγ => hγ.1)]
  rfl

theorem sigmaSetE6A3_eq (v : WeylGroup Tag.E6) :
    sigmaSetE6A3 v = {r | ∃ i j : Fin 4, i ≠ j ∧ r = sigmaRootE6A3 v i j} := by
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := exists_chainRoot_of_mem hγ
    exact ⟨i, j, hij, (sigmaRootE6A3_eq_smul v i j).symm⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨chainRoot chain134 i j, chainRoot134_mem_parabolicRoots hij,
      (sigmaRootE6A3_eq_smul v i j).symm⟩

end Range

section Torus

variable {L : Type} [Field L]

theorem rhoSigmaE6A3_torus (v : WeylGroup Tag.E6) (b : Fin Tag.E6.rank → Lˣ) (A : SL(4, L)) :
    rootDiagUnit Tag.E6 b * rhoSigmaE6A3 L v A * (rootDiagUnit Tag.E6 b)⁻¹ =
      rhoSigmaE6A3 L v (conjDiagn (fun i => rootChar b (wbE6A3 v i)) A) := by
  set d : Fin 4 → Lˣ := fun i => rootChar b (wbE6A3 v i) with hd
  have h : (MulAut.conj (rootDiagUnit Tag.E6 b)).toMonoidHom.comp (rhoSigmaE6A3 L v) =
      (rhoSigmaE6A3 L v).comp (conjDiagnHom d) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 4) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    obtain ⟨ε, hε⟩ := rhoSigmaE6A3_transvection (L := L) v i j hij
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiagnHom_apply]
    rw [hε, conjDiagn_transvection d hij, hε,
      rootDiagUnit_conj_pinnedX b (isRoot_sigmaRootE6A3 v hij)]
    congr 1
    rw [sigmaRootE6A3, rootChar_sub]
    simp only [hd, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  exact DFunLike.congr_fun h A

theorem rhoSigmaE6A3_diagonal (v : WeylGroup Tag.E6) (A : SL(4, L))
    (hA : ∀ i j : Fin 4, i ≠ j → (A : Matrix (Fin 4) (Fin 4) L) i j = 0) :
    rhoSigmaE6A3 L v A ∈ torusGroup Tag.E6 L := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hTor, -, -, -⟩ :=
    E6_native_A3_faithful_SL4_all_characteristics L
  have hdiag : (A : Matrix (Fin 4) (Fin 4) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 4) (Fin 4) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 4) (Fin 4) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_four] at hdet
  have h0 : (A : Matrix (Fin 4) (Fin 4) L) 0 0 ≠ 0 := fun h => by
    rw [h] at hdet
    simp at hdet
  have h01 : (A : Matrix (Fin 4) (Fin 4) L) 0 0 * (A : Matrix (Fin 4) (Fin 4) L) 1 1 ≠ 0 :=
    fun h => by
      rw [h] at hdet
      simp at hdet
  have h012 : (A : Matrix (Fin 4) (Fin 4) L) 0 0 * (A : Matrix (Fin 4) (Fin 4) L) 1 1 *
      (A : Matrix (Fin 4) (Fin 4) L) 2 2 ≠ 0 := fun h => by
    rw [h] at hdet
    simp at hdet
  obtain ⟨ua, hua⟩ : ∃ u : Lˣ, (u : L) = (A : Matrix (Fin 4) (Fin 4) L) 0 0 :=
    ⟨Units.mk0 _ h0, rfl⟩
  obtain ⟨ub, hub⟩ : ∃ u : Lˣ, (u : L) =
      (A : Matrix (Fin 4) (Fin 4) L) 0 0 * (A : Matrix (Fin 4) (Fin 4) L) 1 1 :=
    ⟨Units.mk0 _ h01, rfl⟩
  obtain ⟨uc, huc⟩ : ∃ u : Lˣ, (u : L) =
      (A : Matrix (Fin 4) (Fin 4) L) 0 0 * (A : Matrix (Fin 4) (Fin 4) L) 1 1 *
        (A : Matrix (Fin 4) (Fin 4) L) 2 2 :=
    ⟨Units.mk0 _ h012, rfl⟩
  have d1 : ((ua⁻¹ * ub : Lˣ) : L) = (A : Matrix (Fin 4) (Fin 4) L) 1 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hua, hub]
    exact inv_mul_cancel_left₀ h0 _
  have d2 : ((ub⁻¹ * uc : Lˣ) : L) = (A : Matrix (Fin 4) (Fin 4) L) 2 2 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hub, huc]
    exact inv_mul_cancel_left₀ h01 _
  have d3 : ((uc⁻¹ : Lˣ) : L) = (A : Matrix (Fin 4) (Fin 4) L) 3 3 := by
    rw [Units.val_inv_eq_inv_val, huc]
    exact (eq_inv_of_mul_eq_one_right hdet).symm
  have hrep : a3Rep L ⟨a3TorusElt ua ub uc, a3TorusElt_mem ua ub uc⟩ = A := by
    apply Subtype.ext
    rw [coe_a3Rep, a3Mat_a3TorusElt, hdiag]
    congr 1
    funext i
    fin_cases i
    exacts [hua, d1, d2, d3]
  have hJ : e6rhoJ3 L A = a3TorusElt ua ub uc := by
    rw [← hrep]
    exact e6rhoJ3_a3Rep (a3TorusElt_mem ua ub uc)
  have hH : a3TorusElt ua ub uc ∈ torusGroup Tag.E6 L :=
    ((hTor _).2 ⟨ua, ub, uc, rfl⟩).2
  rw [rhoSigmaE6A3_apply, hJ]
  exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1 hH

end Torus

section BlockSL

variable {L : Type} [Field L]

theorem e6rhoJ3_blockSL (Y : SL(2, L)) :
    e6rhoJ3 L (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 2 Y) =
      simpleRootSL2 Tag.E6 L (e6Index 0) Y := by
  have hx : ∀ c : L, e6rhoJ3 L (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 4) ≠ 1 by decide) c) = xUnit Tag.E6 L (e6Index 0) c := by
    intro c
    have hmem : xUnit Tag.E6 L (e6Index 0) c ∈ subsystemGroup Tag.E6 L support134 :=
      xUnit_mem_subsystemGroup mem_support134_0 c
    have hrep : a3Rep L ⟨xUnit Tag.E6 L (e6Index 0) c, hmem⟩ =
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) c := by
      apply Subtype.ext
      rw [coe_a3Rep, CFSG.LinearGroups.coe_transvection]
      exact a3Mat_x1 c
    rw [← hrep]
    exact e6rhoJ3_a3Rep hmem
  have hy : ∀ c : L, e6rhoJ3 L (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 4) ≠ 0 by decide) c) = yUnit Tag.E6 L (e6Index 0) c := by
    intro c
    have hmem : yUnit Tag.E6 L (e6Index 0) c ∈ subsystemGroup Tag.E6 L support134 :=
      yUnit_mem_subsystemGroup mem_support134_0 c
    have hrep : a3Rep L ⟨yUnit Tag.E6 L (e6Index 0) c, hmem⟩ =
        Matrix.SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 0 by decide) c := by
      apply Subtype.ext
      rw [coe_a3Rep, CFSG.LinearGroups.coe_transvection]
      exact a3Mat_y1 c
    rw [← hrep]
    exact e6rhoJ3_a3Rep hmem
  have e0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := rfl
  have e1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := rfl
  have e2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := rfl
  have e3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := rfl
  have hu : ∀ c : L,
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 2 (uSL c) : SL(4, L)) =
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) c := by
    intro c
    apply Subtype.ext
    rw [CFSG.LinearGroups.coe_transvection]
    have h : ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 2 (uSL c) : SL(4, L)) :
        Matrix (Fin 4) (Fin 4) L) = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (uSL c : Matrix (Fin 2) (Fin 2) L) 0 0 1) := rfl
    rw [h]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [reindex_apply, submatrix_apply, e0, e1, e2, e3, coe_uSL, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  have hv : ∀ c : L,
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 2 (vSL c) : SL(4, L)) =
        Matrix.SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 0 by decide) c := by
    intro c
    apply Subtype.ext
    rw [CFSG.LinearGroups.coe_transvection]
    have h : ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 2 (vSL c) : SL(4, L)) :
        Matrix (Fin 4) (Fin 4) L) = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (vSL c : Matrix (Fin 2) (Fin 2) L) 0 0 1) := rfl
    rw [h]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [reindex_apply, submatrix_apply, e0, e1, e2, e3, coe_vSL, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  have key : (e6rhoJ3 L).comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.blockSL L 2 2) =
      simpleRootSL2 Tag.E6 L (e6Index 0) :=
    eq_simpleRootSL2 (e6Index 0) (fun c => by rw [MonoidHom.comp_apply, hu, hx])
      (fun c => by rw [MonoidHom.comp_apply, hv, hy])
  exact DFunLike.congr_fun key Y

end BlockSL

end CFSG.RankThree.PartOne.KE
