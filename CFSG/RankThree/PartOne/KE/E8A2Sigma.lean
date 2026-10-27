module

public import CFSG.RankThree.PartOne.KE.E8A2Native
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

@[expose] def e8a2Equiv : SL(3, L) ≃* subsystemGroup Tag.E8 L e8support13 :=
  (MulEquiv.ofBijective (e8a2Rep L) (E8_native_A2_faithful_SL3_all_characteristics L).1).symm

@[expose] def e8rhoJ : SL(3, L) →* ModGL Tag.E8 L :=
  (subsystemGroup Tag.E8 L e8support13).subtype.comp (e8a2Equiv L).toMonoidHom

variable {L}

theorem e8a2Rep_e8a2Equiv (X : SL(3, L)) : e8a2Rep L (e8a2Equiv L X) = X :=
  (MulEquiv.ofBijective (e8a2Rep L)
    (E8_native_A2_faithful_SL3_all_characteristics L).1).apply_symm_apply X

theorem e8rhoJ_e8a2Rep {g : ModGL Tag.E8 L} (hg : g ∈ subsystemGroup Tag.E8 L e8support13) :
    e8rhoJ L (e8a2Rep L ⟨g, hg⟩) = g := by
  have h : e8a2Equiv L (e8a2Rep L ⟨g, hg⟩) = ⟨g, hg⟩ :=
    (MulEquiv.ofBijective (e8a2Rep L)
      (E8_native_A2_faithful_SL3_all_characteristics L).1).symm_apply_apply ⟨g, hg⟩
  exact congrArg Subtype.val h

theorem e8rhoJ_mem (X : SL(3, L)) : e8rhoJ L X ∈ subsystemGroup Tag.E8 L e8support13 :=
  (e8a2Equiv L X).2

theorem e8a2Mat_e8rhoJ (X : SL(3, L)) : e8a2Mat (e8rhoJ L X) = (X : Matrix (Fin 3) (Fin 3) L) := by
  have h := congrArg (fun Y : SL(3, L) => (Y : Matrix (Fin 3) (Fin 3) L)) (e8a2Rep_e8a2Equiv X)
  exact h

theorem e8rhoJ_injective : Function.Injective (e8rhoJ L) := by
  intro X Y h
  apply Subtype.ext
  rw [← e8a2Mat_e8rhoJ X, ← e8a2Mat_e8rhoJ Y, h]

theorem e8rhoJ_range : (e8rhoJ L).range = subsystemGroup Tag.E8 L e8support13 := by
  refine le_antisymm (fun g ⟨X, hX⟩ => hX ▸ e8rhoJ_mem X) fun g hg => ?_
  exact ⟨e8a2Rep L ⟨g, hg⟩, e8rhoJ_e8a2Rep hg⟩

theorem e8rhoJ_transvection (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, e8rhoJ L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E8 L (chainRoot e8chain13 i j) ((ε : L) * t) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfam, -, -⟩ := E8_native_A2_faithful_SL3_all_characteristics L
  obtain ⟨e, he, h⟩ := hfam i j hij
  have hee : ((e : ℤ) : L) * ((e : ℤ) : L) = 1 := by rcases he with rfl | rfl <;> simp
  refine ⟨⟨((e : ℤ) : L), ((e : ℤ) : L), hee, hee⟩, fun s => ?_⟩
  have hmem := pinnedX_mem_e8a2Group (K := L) (e8chainRoot13_mem_parabolicRoots hij)
    (((e : ℤ) : L) * s)
  have hrep : e8a2Rep L ⟨pinnedX Tag.E8 L (chainRoot e8chain13 i j) (((e : ℤ) : L) * s), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij s := by
    apply Subtype.ext
    rw [coe_e8a2Rep, h, CFSG.LinearGroups.coe_transvection]
    congr 1
    rw [← mul_assoc, hee, one_mul]
  rw [← hrep]
  exact e8rhoJ_e8a2Rep hmem

end Standard


section Transport

variable {L : Type} [Field L]

@[expose] def wbE8 (v : WeylGroup Tag.E8) (k : Fin 3) : Fin Tag.E8.rank → ℤ := v • e8a2Weight k

@[expose] def sigmaRootE8 (v : WeylGroup Tag.E8) (i j : Fin 3) : Fin Tag.E8.rank → ℤ :=
  wbE8 v i - wbE8 v j

variable (L) in
@[expose] def rhoSigmaE8 (v : WeylGroup Tag.E8) : SL(3, L) →* ModGL Tag.E8 L :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E8) L v)).toMonoidHom.comp (e8rhoJ L)

theorem rhoSigmaE8_apply (v : WeylGroup Tag.E8) (X : SL(3, L)) :
    rhoSigmaE8 L v X = canonicalRep (coxeterSystem Tag.E8) L v * e8rhoJ L X *
      (canonicalRep (coxeterSystem Tag.E8) L v)⁻¹ := by
  simp [rhoSigmaE8, MulAut.conj_apply]

theorem rhoSigmaE8_injective (v : WeylGroup Tag.E8) : Function.Injective (rhoSigmaE8 L v) :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E8) L v)).injective.comp e8rhoJ_injective

theorem sigmaRootE8_eq_smul (v : WeylGroup Tag.E8) (i j : Fin 3) :
    sigmaRootE8 v i j = v • chainRoot e8chain13 i j := by
  rw [e8chainRoot13_eq_sub, smul_sub]
  rfl

theorem isRoot_sigmaRootE8 (v : WeylGroup Tag.E8) {i j : Fin 3} (hij : i ≠ j) :
    IsRoot Tag.E8 (sigmaRootE8 v i j) := by
  rw [sigmaRootE8_eq_smul]
  exact IsRoot.smul (e8chainRoot13_mem_parabolicRoots hij).1 v

theorem sigmaRootE8_neg (v : WeylGroup Tag.E8) (i j : Fin 3) :
    -sigmaRootE8 v i j = sigmaRootE8 v j i := neg_sub _ _

theorem sigmaRootE8_add (v : WeylGroup Tag.E8) (i j k : Fin 3) :
    sigmaRootE8 v i j + sigmaRootE8 v j k = sigmaRootE8 v i k := sub_add_sub_cancel _ _ _

theorem rhoSigmaE8_transvection (v : WeylGroup Tag.E8) (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, rhoSigmaE8 L v (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E8 L (sigmaRootE8 v i j) ((ε : L) * t) := by
  obtain ⟨ε₀, h₀⟩ := e8rhoJ_transvection (L := L) i j hij
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX (canonicalRep_mem_monomialSubgroup L v)
    (e8chainRoot13_mem_parabolicRoots hij).1
  have hπ : weylQuotientHom Tag.E8 L ⟨canonicalRep (coxeterSystem Tag.E8) L v,
      canonicalRep_mem_monomialSubgroup L v⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  refine ⟨μ * ε₀, fun t => ?_⟩
  rw [rhoSigmaE8_apply, h₀, hμ, hπ, ← sigmaRootE8_eq_smul, Units.val_mul, mul_assoc]

end Transport


section Range

variable {L : Type} [Field L]

@[expose] def sigmaSetE8 (v : WeylGroup Tag.E8) : Set (Fin Tag.E8.rank → ℤ) :=
  (fun γ => v • γ) '' parabolicRoots Tag.E8 e8support13

theorem rhoSigmaE8_range (v : WeylGroup Tag.E8) :
    (rhoSigmaE8 L v).range = rootSpan Tag.E8 L (sigmaSetE8 v) := by
  rw [rhoSigmaE8, MonoidHom.range_comp, e8rhoJ_range, subsystemGroup_eq_rootSpan,
    map_conj_rootSpan v (fun γ hγ => hγ.1)]
  rfl

theorem sigmaSetE8_eq (v : WeylGroup Tag.E8) :
    sigmaSetE8 v = {r | ∃ i j : Fin 3, i ≠ j ∧ r = sigmaRootE8 v i j} := by
  ext r
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := exists_e8chainRoot13_of_mem hγ
    exact ⟨i, j, hij, (sigmaRootE8_eq_smul v i j).symm⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨chainRoot e8chain13 i j, e8chainRoot13_mem_parabolicRoots hij,
      (sigmaRootE8_eq_smul v i j).symm⟩

end Range


section Torus

variable {L : Type} [Field L]

theorem rhoSigmaE8_torus (v : WeylGroup Tag.E8) (b : Fin Tag.E8.rank → Lˣ) (A : SL(3, L)) :
    rootDiagUnit Tag.E8 b * rhoSigmaE8 L v A * (rootDiagUnit Tag.E8 b)⁻¹ =
      rhoSigmaE8 L v (conjDiag3 (fun i => rootChar b (wbE8 v i)) A) := by
  set d : Fin 3 → Lˣ := fun i => rootChar b (wbE8 v i) with hd
  have h : (MulAut.conj (rootDiagUnit Tag.E8 b)).toMonoidHom.comp (rhoSigmaE8 L v) =
      (rhoSigmaE8 L v).comp (conjDiag3Hom d) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    obtain ⟨ε, hε⟩ := rhoSigmaE8_transvection (L := L) v i j hij
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiag3Hom_apply]
    rw [hε, conjDiag3_transvection (L := L), hε,
      rootDiagUnit_conj_pinnedX b (isRoot_sigmaRootE8 v hij)]
    congr 1
    rw [sigmaRootE8, rootChar_sub]
    simp only [hd, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  exact DFunLike.congr_fun h A

theorem rhoSigmaE8_diagonal (v : WeylGroup Tag.E8) (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    rhoSigmaE8 L v A ∈ torusGroup Tag.E8 L := by
  obtain ⟨-, -, -, -, -, -, -, -, hTor, -, -, -⟩ := E8_native_A2_faithful_SL3_all_characteristics L
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
  have hrep : e8a2Rep L ⟨e8a2TorusElt ua ub, e8a2TorusElt_mem ua ub⟩ = A := by
    apply Subtype.ext
    rw [coe_e8a2Rep, e8a2Mat_e8a2TorusElt, hdiag]
    have h22 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 =
        ((A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hua, hub, Matrix.diagonal_apply_ne]
    rw [h22, _root_.mul_inv_rev]
  have hJ : e8rhoJ L A = e8a2TorusElt ua ub := by
    rw [← hrep]
    exact e8rhoJ_e8a2Rep (e8a2TorusElt_mem ua ub)
  have hH : e8a2TorusElt ua ub ∈ torusGroup Tag.E8 L :=
    ((hTor _).2 ⟨ua, ub, rfl⟩).2
  rw [rhoSigmaE8_apply, hJ]
  exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1 hH

end Torus

end CFSG.RankThree.PartOne.KE
