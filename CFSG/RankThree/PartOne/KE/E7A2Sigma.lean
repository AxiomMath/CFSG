module

public import CFSG.RankThree.PartOne.KE.E7A2Native
public import CFSG.RankThree.PartOne.KE.ConjRootSpan
public import CFSG.RankThree.PartOne.KE.A2Family

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Standard

variable (L : Type) [Field L]

@[expose] def a2Equiv : SL(3, L) ≃* subsystemGroup Tag.E7 L support13 :=
  (MulEquiv.ofBijective (a2Rep L) (E7_native_A2_faithful_SL3_all_characteristics L).1).symm

@[expose] def rhoJ : SL(3, L) →* ModGL Tag.E7 L :=
  (subsystemGroup Tag.E7 L support13).subtype.comp (a2Equiv L).toMonoidHom

variable {L}

theorem a2Rep_a2Equiv (X : SL(3, L)) : a2Rep L (a2Equiv L X) = X :=
  (MulEquiv.ofBijective (a2Rep L)
    (E7_native_A2_faithful_SL3_all_characteristics L).1).apply_symm_apply X

theorem rhoJ_a2Rep {g : ModGL Tag.E7 L} (hg : g ∈ subsystemGroup Tag.E7 L support13) :
    rhoJ L (a2Rep L ⟨g, hg⟩) = g := by
  have h : a2Equiv L (a2Rep L ⟨g, hg⟩) = ⟨g, hg⟩ :=
    (MulEquiv.ofBijective (a2Rep L)
      (E7_native_A2_faithful_SL3_all_characteristics L).1).symm_apply_apply ⟨g, hg⟩
  exact congrArg Subtype.val h

theorem rhoJ_mem (X : SL(3, L)) : rhoJ L X ∈ subsystemGroup Tag.E7 L support13 :=
  (a2Equiv L X).2

theorem a2Mat_rhoJ (X : SL(3, L)) : a2Mat (rhoJ L X) = (X : Matrix (Fin 3) (Fin 3) L) := by
  have h := congrArg (fun Y : SL(3, L) => (Y : Matrix (Fin 3) (Fin 3) L)) (a2Rep_a2Equiv X)
  exact h

theorem rhoJ_injective : Function.Injective (rhoJ L) := by
  intro X Y h
  apply Subtype.ext
  rw [← a2Mat_rhoJ X, ← a2Mat_rhoJ Y, h]

theorem rhoJ_range : (rhoJ L).range = subsystemGroup Tag.E7 L support13 := by
  refine le_antisymm (fun g ⟨X, hX⟩ => hX ▸ rhoJ_mem X) fun g hg => ?_
  exact ⟨a2Rep L ⟨g, hg⟩, rhoJ_a2Rep hg⟩

theorem rhoJ_transvection (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, rhoJ L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E7 L (chainRoot chain13 i j) ((ε : L) * t) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfam, -, -⟩ := E7_native_A2_faithful_SL3_all_characteristics L
  obtain ⟨e, he, h⟩ := hfam i j hij
  have hee : ((e : ℤ) : L) * ((e : ℤ) : L) = 1 := by rcases he with rfl | rfl <;> simp
  refine ⟨⟨((e : ℤ) : L), ((e : ℤ) : L), hee, hee⟩, fun s => ?_⟩
  have hmem := pinnedX_mem_a2Group (K := L) (chainRoot13_mem_parabolicRoots hij)
    (((e : ℤ) : L) * s)
  have hrep : a2Rep L ⟨pinnedX Tag.E7 L (chainRoot chain13 i j) (((e : ℤ) : L) * s), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij s := by
    apply Subtype.ext
    rw [coe_a2Rep, h, CFSG.LinearGroups.coe_transvection]
    congr 1
    rw [← mul_assoc, hee, one_mul]
  rw [← hrep]
  exact rhoJ_a2Rep hmem

end Standard


section Transport

variable {L : Type} [Field L]

@[expose] def wbE7 (v : WeylGroup Tag.E7) (k : Fin 3) : Fin Tag.E7.rank → ℤ := v • a2Weight k

@[expose] def sigmaRoot (v : WeylGroup Tag.E7) (i j : Fin 3) : Fin Tag.E7.rank → ℤ :=
  wbE7 v i - wbE7 v j

variable (L) in
@[expose] def rhoSigma (v : WeylGroup Tag.E7) : SL(3, L) →* ModGL Tag.E7 L :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E7) L v)).toMonoidHom.comp (rhoJ L)

theorem rhoSigma_apply (v : WeylGroup Tag.E7) (X : SL(3, L)) :
    rhoSigma L v X = canonicalRep (coxeterSystem Tag.E7) L v * rhoJ L X *
      (canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ := by
  simp [rhoSigma, MulAut.conj_apply]

theorem rhoSigma_injective (v : WeylGroup Tag.E7) : Function.Injective (rhoSigma L v) :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E7) L v)).injective.comp rhoJ_injective

theorem sigmaRoot_eq_smul (v : WeylGroup Tag.E7) (i j : Fin 3) :
    sigmaRoot v i j = v • chainRoot chain13 i j := by
  rw [chainRoot13_eq_sub, smul_sub]
  rfl

theorem isRoot_sigmaRoot (v : WeylGroup Tag.E7) {i j : Fin 3} (hij : i ≠ j) :
    IsRoot Tag.E7 (sigmaRoot v i j) := by
  rw [sigmaRoot_eq_smul]
  exact IsRoot.smul (chainRoot13_mem_parabolicRoots hij).1 v

theorem sigmaRoot_neg (v : WeylGroup Tag.E7) (i j : Fin 3) :
    -sigmaRoot v i j = sigmaRoot v j i := neg_sub _ _

theorem sigmaRoot_add (v : WeylGroup Tag.E7) (i j k : Fin 3) :
    sigmaRoot v i j + sigmaRoot v j k = sigmaRoot v i k := sub_add_sub_cancel _ _ _

theorem rhoSigma_transvection (v : WeylGroup Tag.E7) (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, rhoSigma L v (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E7 L (sigmaRoot v i j) ((ε : L) * t) := by
  obtain ⟨ε₀, h₀⟩ := rhoJ_transvection (L := L) i j hij
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX (canonicalRep_mem_monomialSubgroup L v)
    (chainRoot13_mem_parabolicRoots hij).1
  have hπ : weylQuotientHom Tag.E7 L ⟨canonicalRep (coxeterSystem Tag.E7) L v,
      canonicalRep_mem_monomialSubgroup L v⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  refine ⟨μ * ε₀, fun t => ?_⟩
  rw [rhoSigma_apply, h₀, hμ, hπ, ← sigmaRoot_eq_smul, Units.val_mul, mul_assoc]

end Transport


section Range

variable {L : Type} [Field L]

@[expose] def sigmaSet (v : WeylGroup Tag.E7) : Set (Fin Tag.E7.rank → ℤ) :=
  (fun γ => v • γ) '' parabolicRoots Tag.E7 support13

theorem rhoSigma_range (v : WeylGroup Tag.E7) :
    (rhoSigma L v).range = rootSpan Tag.E7 L (sigmaSet v) := by
  rw [rhoSigma, MonoidHom.range_comp, rhoJ_range, subsystemGroup_eq_rootSpan,
    map_conj_rootSpan v (fun γ hγ => hγ.1)]
  rfl

theorem sigmaSet_eq (v : WeylGroup Tag.E7) :
    sigmaSet v = {r | ∃ i j : Fin 3, i ≠ j ∧ r = sigmaRoot v i j} := by
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := exists_chainRoot13_of_mem hγ
    exact ⟨i, j, hij, (sigmaRoot_eq_smul v i j).symm⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨chainRoot chain13 i j, chainRoot13_mem_parabolicRoots hij,
      (sigmaRoot_eq_smul v i j).symm⟩

end Range


section Torus

variable {L : Type} [Field L]

theorem rhoSigma_torus (v : WeylGroup Tag.E7) (b : Fin Tag.E7.rank → Lˣ) (A : SL(3, L)) :
    rootDiagUnit Tag.E7 b * rhoSigma L v A * (rootDiagUnit Tag.E7 b)⁻¹ =
      rhoSigma L v (conjDiag3 (fun i => rootChar b (wbE7 v i)) A) := by
  set d : Fin 3 → Lˣ := fun i => rootChar b (wbE7 v i) with hd
  have h : (MulAut.conj (rootDiagUnit Tag.E7 b)).toMonoidHom.comp (rhoSigma L v) =
      (rhoSigma L v).comp (conjDiag3Hom d) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    obtain ⟨ε, hε⟩ := rhoSigma_transvection (L := L) v i j hij
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiag3Hom_apply]
    rw [hε, conjDiag3_transvection (L := L), hε,
      rootDiagUnit_conj_pinnedX b (isRoot_sigmaRoot v hij)]
    congr 1
    rw [sigmaRoot, rootChar_sub]
    simp only [hd, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  exact DFunLike.congr_fun h A

theorem rhoSigma_diagonal (v : WeylGroup Tag.E7) (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    rhoSigma L v A ∈ torusGroup Tag.E7 L := by
  obtain ⟨-, -, -, -, -, -, -, -, hTor, -, -, -⟩ := E7_native_A2_faithful_SL3_all_characteristics L
  have hdiag : (A : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h01 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1 ≠ 0 :=
    fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
  set ua : Lˣ := Units.mk0 _ h0 with hua
  set ub : Lˣ := Units.mk0 _ h01 with hub
  have hrep : a2Rep L ⟨a2TorusElt ua ub, a2TorusElt_mem ua ub⟩ = A := by
    apply Subtype.ext
    rw [coe_a2Rep, a2Mat_a2TorusElt, hdiag]
    have h22 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 =
        ((A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hua, hub, Matrix.diagonal_apply_ne]
    rw [h22, _root_.mul_inv_rev]
  have hJ : rhoJ L A = a2TorusElt ua ub := by
    rw [← hrep]
    exact rhoJ_a2Rep (a2TorusElt_mem ua ub)
  have hH : a2TorusElt ua ub ∈ torusGroup Tag.E7 L :=
    ((hTor _).2 ⟨ua, ub, rfl⟩).2
  rw [rhoSigma_apply, hJ]
  exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1 hH

end Torus

end CFSG.RankThree.PartOne.KE
