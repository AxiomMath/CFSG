module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Tor
public import CFSG.RankThree.PartOne.KGD.D4A2Frame

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.E6
open scoped MatrixGroups

@[expose] def weylV : WeylGroup TwistTag.D4.tag :=
  simple TwistTag.D4.tag 0 * simple TwistTag.D4.tag 2 * simple TwistTag.D4.tag 3 *
    simple TwistTag.D4.tag 1

@[expose] def weylU : WeylGroup TwistTag.D4.tag :=
  weylV * simple TwistTag.D4.tag 0 * simple TwistTag.D4.tag 2 * weylV⁻¹

@[expose] def betaRoot : Fin TwistTag.D4.tag.rank → ℤ :=
  ![1, 1, 1, 1]

theorem weylV_smul (x : Fin TwistTag.D4.tag.rank → ℤ) :
    weylV • x = reflect TwistTag.D4.tag 0 (reflect TwistTag.D4.tag 2
      (reflect TwistTag.D4.tag 3 (reflect TwistTag.D4.tag 1 x))) := by
  simp only [weylV, mul_smul, simple_smul]

theorem weylV_smul_e0 :
    weylV • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = Pi.single 2 1 := by
  rw [weylV_smul]
  decide

theorem weylV_smul_e2 :
    weylV • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = betaRoot := by
  rw [weylV_smul]
  decide

theorem permLattice_e2 :
    permLattice TwistTag.D4.perm (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      Pi.single 2 1 := by
  decide

theorem permLattice_betaRoot : permLattice TwistTag.D4.perm betaRoot = betaRoot := by
  decide

theorem permLattice_neg' (π : Equiv.Perm (Fin TwistTag.D4.tag.rank))
    (x : Fin TwistTag.D4.tag.rank → ℤ) : permLattice π (-x) = -permLattice π x :=
  rfl

theorem isRoot_betaRoot : IsRoot TwistTag.D4.tag betaRoot := by
  rw [← weylV_smul_e2]
  exact IsRoot.smul (isRoot_single _ 2) _

section Rot

variable (K : Type) [Field K]

@[expose] def d4RotElt : ModGL TwistTag.D4.tag K :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV *
    (weylElt TwistTag.D4.tag K 0 1 * weylElt TwistTag.D4.tag K 2 1) *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV)⁻¹

variable {K}

theorem d4RotElt_mem_monomialSubgroup : d4RotElt K ∈ monomialSubgroup TwistTag.D4.tag K :=
  mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup K weylV)
    (mul_mem (weylElt_mem_monomialSubgroup 0) (weylElt_mem_monomialSubgroup 2)))
    (inv_mem (canonicalRep_mem_monomialSubgroup K weylV))

theorem mapsRootLines_d4RotElt : MapsRootLines (d4RotElt K) weylU := by
  have h := ((mapsRootLines_canonicalRep (R := K) weylV).mul
    ((mapsRootLines_weylElt (R := K) 0).mul (mapsRootLines_weylElt (R := K) 2))).mul
      (mapsRootLines_canonicalRep (R := K) weylV).inv
  rw [weylU, mul_assoc weylV]
  exact h

theorem d4RotElt_mem_adjointGroup : d4RotElt K ∈ adjointGroup TwistTag.D4.tag K :=
  monomialSubgroup_le_adjointGroup' d4RotElt_mem_monomialSubgroup

theorem weylElt_one_eq_pinnedX (i : Fin TwistTag.D4.tag.rank) :
    weylElt TwistTag.D4.tag K i 1 = pinnedX TwistTag.D4.tag K (Pi.single i 1) 1 *
      pinnedX TwistTag.D4.tag K (-Pi.single i 1) (-1) *
        pinnedX TwistTag.D4.tag K (Pi.single i 1) 1 := by
  rw [pinnedX_single, pinnedX_neg_single, Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp

@[expose] def rootN (γ : Fin TwistTag.D4.tag.rank → ℤ) : ModGL TwistTag.D4.tag K :=
  pinnedX TwistTag.D4.tag K γ 1 * pinnedX TwistTag.D4.tag K (-γ) (-1) *
    pinnedX TwistTag.D4.tag K γ 1

theorem canonicalRep_conj_rootN (h2 : (2 : K) = 0) (w : WeylGroup TwistTag.D4.tag)
    (i : Fin TwistTag.D4.tag.rank) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K w * rootN (Pi.single i 1) *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ =
      rootN (w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) := by
  have hγ := isRoot_single TwistTag.D4.tag i
  rw [rootN, rootN]
  have e : ∀ a b c : ModGL TwistTag.D4.tag K,
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * (a * b * c) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ =
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * a *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * b *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * c *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹) := fun a b c => by group
  rw [e, canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hγ,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (IsRoot.neg hγ), smul_neg]

theorem d4RotElt_eq_pinnedX (h2 : (2 : K) = 0) :
    d4RotElt K = rootN (Pi.single 2 1) * rootN betaRoot := by
  have e : d4RotElt K =
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV * weylElt TwistTag.D4.tag K 0 1 *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV)⁻¹) *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV * weylElt TwistTag.D4.tag K 2 1 *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV)⁻¹) := by
    rw [d4RotElt]
    group
  rw [e, weylElt_one_eq_pinnedX, weylElt_one_eq_pinnedX]
  change canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV * rootN (Pi.single 0 1) *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV)⁻¹ *
    (canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV * rootN (Pi.single 2 1) *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV)⁻¹) = _
  rw [canonicalRep_conj_rootN h2, canonicalRep_conj_rootN h2, weylV_smul_e0, weylV_smul_e2]

theorem diagramMap_commute_pinnedX (h2 : (2 : K) = 0) {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (hρ : permLattice TwistTag.D4.perm γ = γ) (c : K) :
    diagramMap TwistTag.D4 K * pinnedX TwistTag.D4.tag K γ c =
      pinnedX TwistTag.D4.tag K γ c * diagramMap TwistTag.D4 K := by
  have h := twistHom_id_pinnedX h2 hγ c
  rw [twistHom_id_eq, hρ] at h
  rw [← mul_inv_eq_iff_eq_mul, h]

theorem diagramMap_commute_rootN (h2 : (2 : K) = 0) {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (hρ : permLattice TwistTag.D4.perm γ = γ) :
    diagramMap TwistTag.D4 K * rootN γ = rootN γ * diagramMap TwistTag.D4 K := by
  have h1 := diagramMap_commute_pinnedX h2 hγ hρ (1 : K)
  have h2' := diagramMap_commute_pinnedX h2 (IsRoot.neg hγ)
    (by rw [permLattice_neg', hρ]) (-1 : K)
  rw [rootN, ← mul_assoc, ← mul_assoc, h1, mul_assoc _ (diagramMap TwistTag.D4 K), h2',
    ← mul_assoc, mul_assoc _ (diagramMap TwistTag.D4 K), h1, ← mul_assoc]

theorem diagramMap_commute_d4RotElt (h2 : (2 : K) = 0) :
    diagramMap TwistTag.D4 K * d4RotElt K = d4RotElt K * diagramMap TwistTag.D4 K := by
  rw [d4RotElt_eq_pinnedX h2, ← mul_assoc,
    diagramMap_commute_rootN h2 (isRoot_single _ 2) permLattice_e2, mul_assoc,
    diagramMap_commute_rootN h2 isRoot_betaRoot permLattice_betaRoot, mul_assoc]

variable (K) in
@[expose] def d4Frame : SL(3, K) →* ModGL TwistTag.D4.tag K :=
  d4rhoStd K

theorem d4rhoStd_transvection_of_two (h2 : (2 : K) = 0) {i j : Fin 3} (hij : i ≠ j) (t : K) :
    d4rhoStd K (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.D4 K (chainRoot d4ChainA2 i j) t := by
  obtain ⟨ε, hε, hfam⟩ := d4A2RootFamily_all (K := K) i j hij
  have hε1 : (ε : K) = 1 := by
    rcases hε with rfl | rfl
    · simp
    · push_cast
      linear_combination -h2
  have hmem := pinnedX_mem_d4A2Group (K := K) (chainRootA2_mem_parabolicRoots hij) t
  have hrep : d4A2Rep K ⟨pinnedX Tag.D4 K (chainRoot d4ChainA2 i j) t, hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij t := by
    apply Subtype.ext
    rw [coe_d4A2Rep, hfam, CFSG.LinearGroups.coe_transvection, hε1, one_mul]
  rw [← hrep]
  exact d4rhoStd_d4A2Rep hmem

@[expose] def sl3N {i j : Fin 3} (hij : i ≠ j) : SL(3, K) :=
  Matrix.SpecialLinearGroup.transvection hij 1 *
    Matrix.SpecialLinearGroup.transvection hij.symm (-1) *
      Matrix.SpecialLinearGroup.transvection hij 1

@[expose] def rotM : SL(3, K) :=
  sl3N (show (0 : Fin 3) ≠ 1 by decide) * sl3N (show (1 : Fin 3) ≠ 2 by decide)

theorem d4rhoStd_sl3N01 (h2 : (2 : K) = 0) :
    d4rhoStd K (sl3N (show (0 : Fin 3) ≠ 1 by decide)) = weylElt TwistTag.D4.tag K 0 1 := by
  obtain ⟨c01, -, c10, -⟩ := chainRootA2_values
  rw [sl3N, map_mul, map_mul, d4rhoStd_transvection_of_two h2, d4rhoStd_transvection_of_two h2,
    c01, c10, weylElt_one_eq_pinnedX]
  rfl

theorem d4rhoStd_sl3N12 (h2 : (2 : K) = 0) :
    d4rhoStd K (sl3N (show (1 : Fin 3) ≠ 2 by decide)) = weylElt TwistTag.D4.tag K 2 1 := by
  obtain ⟨-, c12, -, c21⟩ := chainRootA2_values
  rw [sl3N, map_mul, map_mul, d4rhoStd_transvection_of_two h2, d4rhoStd_transvection_of_two h2,
    c12, c21, weylElt_one_eq_pinnedX]
  rfl

theorem d4RotElt_eq_frame (h2 : (2 : K) = 0) :
    d4RotElt K = canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV * d4Frame K rotM *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K weylV)⁻¹ := by
  have e1 : d4Frame K (sl3N (show (0 : Fin 3) ≠ 1 by decide)) =
      weylElt TwistTag.D4.tag K 0 1 := d4rhoStd_sl3N01 h2
  have e2 : d4Frame K (sl3N (show (1 : Fin 3) ≠ 2 by decide)) =
      weylElt TwistTag.D4.tag K 2 1 := d4rhoStd_sl3N12 h2
  rw [rotM, map_mul, e1, e2]
  rfl

theorem coe_rotM :
    ((rotM : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; -1, 0, 0; 0, -1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rotM, sl3N, Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem rotM_pow_three : (rotM : SL(3, K)) ^ 3 = 1 := by
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_rotM, Matrix.SpecialLinearGroup.coe_one]
  fin_cases a <;> fin_cases b <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem d4RotElt_pow_three (h2 : (2 : K) = 0) : d4RotElt K ^ 3 = 1 := by
  rw [d4RotElt_eq_frame h2]
  have e : ∀ (a b : ModGL TwistTag.D4.tag K), (a * b * a⁻¹) ^ 3 = a * b ^ 3 * a⁻¹ := fun a b => by
    rw [pow_three, pow_three]
    group
  rw [e, ← map_pow, rotM_pow_three, map_one, mul_one, mul_inv_cancel]

end Rot

section Diag

variable {L : Type} [Field L]

theorem exists_sq_add_self_add_one [IsAlgClosed L] : ∃ ω : Lˣ, (ω : L) ^ 2 + ω + 1 = 0 := by
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L).degree ≠ 0 := by
    have h : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L).degree = 2 := by
      compute_degree!
    rw [h]
    decide
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  have hz' : z ^ 2 + z + 1 = 0 := by
    simpa [Polynomial.IsRoot] using hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz'
  exact ⟨Units.mk0 z hz0, by simpa using hz'⟩

theorem exists_sl3_conj_rotM_diag (h2 : (2 : L) = 0) (ω : Lˣ) (hω : (ω : L) ^ 2 + ω + 1 = 0) :
    ∃ Z D : SL(3, L), (∀ i j, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0) ∧
      Z * rotM * Z⁻¹ = D := by
  have hω3 : (ω : L) ^ 3 = 1 := by linear_combination ((ω : L) - 1) * hω
  obtain ⟨V, hV⟩ : ∃ V : SL(3, L), (V : Matrix (Fin 3) (Fin 3) L) =
      !![1, 1, 1; 1, (ω : L) ^ 2, ω; 1, ω, (ω : L) ^ 2] := by
    refine ⟨⟨!![1, 1, 1; 1, (ω : L) ^ 2, ω; 1, ω, (ω : L) ^ 2], ?_⟩, rfl⟩
    simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination ((ω : L) ^ 2 - ω - 3) * hω + (3 * (ω : L) + 1) * h2
  obtain ⟨D, hD⟩ : ∃ D : SL(3, L), (D : Matrix (Fin 3) (Fin 3) L) =
      !![1, 0, 0; 0, (ω : L), 0; 0, 0, (ω : L) ^ 2] := by
    refine ⟨⟨!![1, 0, 0; 0, (ω : L), 0; 0, 0, (ω : L) ^ 2], ?_⟩, rfl⟩
    simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination hω3
  have hMV : rotM * V = V * D := by
    ext a b
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rotM, hV, hD]
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | linear_combination -h2
        | linear_combination -((ω : L) - 1) * hω - h2
        | linear_combination -((ω : L) ^ 2) * h2
        | linear_combination -((ω : L) * ((ω : L) - 1)) * hω - (ω : L) * h2
  refine ⟨V⁻¹, D, fun i j hij => ?_, ?_⟩
  · rw [hD]
    fin_cases i <;> fin_cases j <;> simp_all
  · rw [inv_inv, mul_assoc, hMV, ← mul_assoc, inv_mul_cancel, one_mul]

end Diag

section Conj

variable {L : Type} [Field L]

theorem permLattice_weylV_smul_chainRoot (k l : Fin 3) :
    permLattice TwistTag.D4.perm
        (weylV • (chainRoot d4ChainA2 k l : Fin TwistTag.D4.tag.rank → ℤ)) =
      weylV • (chainRoot d4ChainA2 k l : Fin TwistTag.D4.tag.rank → ℤ) := by
  rw [weylV_smul]
  revert k l
  decide +kernel

variable (L) in
@[expose] def vFrame : SL(3, L) →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) L weylV)).toMonoidHom.comp
    (d4Frame L)

theorem vFrame_apply (Z : SL(3, L)) :
    vFrame L Z = canonicalRep (coxeterSystem TwistTag.D4.tag) L weylV * d4Frame L Z *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L weylV)⁻¹ :=
  rfl

theorem vFrame_transvection (h2 : (2 : L) = 0) {i j : Fin 3} (hij : i ≠ j) (t : L) :
    vFrame L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX TwistTag.D4.tag L
        (weylV • (chainRoot d4ChainA2 i j : Fin TwistTag.D4.tag.rank → ℤ)) t := by
  have e : d4Frame L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX TwistTag.D4.tag L (chainRoot d4ChainA2 i j) t :=
    d4rhoStd_transvection_of_two h2 hij t
  rw [vFrame_apply, e]
  exact canonicalRep_mul_pinnedX_mul_inv_of_two h2 weylV
    (chainRootA2_mem_parabolicRoots hij).1 t

theorem vFrame_mem (h2 : (2 : L) = 0) (S : Subgroup (ModGL TwistTag.D4.tag L))
    (hS : ∀ (i j : Fin 3), i ≠ j → ∀ t : L, pinnedX TwistTag.D4.tag L
      (weylV • (chainRoot d4ChainA2 i j : Fin TwistTag.D4.tag.rank → ℤ)) t ∈ S)
    (Z : SL(3, L)) : vFrame L Z ∈ S := by
  have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 L) ≤ S.comap (vFrame L) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, vFrame_transvection h2 hij c]
    exact hS i j hij c
  rw [CFSG.LinearGroups.special_linear_elementary_generation] at hle
  exact hle (Subgroup.mem_top Z)

theorem vFrame_mem_adjointGroup (h2 : (2 : L) = 0) (Z : SL(3, L)) :
    vFrame L Z ∈ adjointGroup TwistTag.D4.tag L :=
  vFrame_mem h2 _ (fun _ _ _ t => pinnedX_mem_adjointGroup _ t) Z

theorem vFrame_commute_diagramMap (h2 : (2 : L) = 0) (Z : SL(3, L)) :
    vFrame L Z * diagramMap TwistTag.D4 L = diagramMap TwistTag.D4 L * vFrame L Z := by
  have h := vFrame_mem h2 (Subgroup.centralizer {diagramMap TwistTag.D4 L}) (fun i j hij t => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (diagramMap_commute_pinnedX h2
      (IsRoot.smul (chainRootA2_mem_parabolicRoots hij).1 weylV)
      (permLattice_weylV_smul_chainRoot i j) t).symm) Z
  rwa [Subgroup.mem_centralizer_singleton_iff] at h

theorem exists_conj_d4RotElt_mem_torusGroup [IsAlgClosed L] (h2 : (2 : L) = 0) :
    ∃ z ∈ adjointGroup TwistTag.D4.tag L,
      z * diagramMap TwistTag.D4 L = diagramMap TwistTag.D4 L * z ∧
        z * d4RotElt L * z⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
  obtain ⟨ω, hω⟩ := exists_sq_add_self_add_one (L := L)
  obtain ⟨Z, D, hD, hZD⟩ := exists_sl3_conj_rotM_diag h2 ω hω
  refine ⟨vFrame L Z, vFrame_mem_adjointGroup h2 Z, vFrame_commute_diagramMap h2 Z, ?_⟩
  have hm : d4RotElt L = vFrame L rotM := d4RotElt_eq_frame h2
  rw [hm, ← map_inv, ← map_mul, ← map_mul, hZD, vFrame_apply]
  have hT : d4Frame L D ∈ torusGroup TwistTag.D4.tag L := d4rhoStd_diag D hD
  exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer weylV) _).1 hT

end Conj

section Norm

variable {L : Type} [Field L]

@[expose] def weylUInvAct (x : Fin TwistTag.D4.tag.rank → ℤ) : Fin TwistTag.D4.tag.rank → ℤ :=
  reflect TwistTag.D4.tag 0 (reflect TwistTag.D4.tag 2 (reflect TwistTag.D4.tag 3
    (reflect TwistTag.D4.tag 1 (reflect TwistTag.D4.tag 2 (reflect TwistTag.D4.tag 0
      (reflect TwistTag.D4.tag 1 (reflect TwistTag.D4.tag 3 (reflect TwistTag.D4.tag 2
        (reflect TwistTag.D4.tag 0 x)))))))))

theorem weylU_inv_smul (x : Fin TwistTag.D4.tag.rank → ℤ) : weylU⁻¹ • x = weylUInvAct x := by
  have hs : ∀ i, (simple TwistTag.D4.tag i)⁻¹ = simple TwistTag.D4.tag i := fun i =>
    (coxeterSystem TwistTag.D4.tag).inv_simple i
  simp only [weylU, weylV, mul_inv_rev, hs, mul_smul, simple_smul, weylUInvAct]

theorem d4RotElt_conj_rootDiagUnit (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    d4RotElt L * rootDiagUnit TwistTag.D4.tag b * (d4RotElt L)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (weylTuple weylU b) := by
  set nv := canonicalRep (coxeterSystem TwistTag.D4.tag) L weylV with hnv
  have hv : ∀ c, nv * rootDiagUnit TwistTag.D4.tag c * nv⁻¹ =
      rootDiagUnit TwistTag.D4.tag (weylTuple weylV c) :=
    canonicalRep_conj_rootDiagUnit (K := L) weylV
  have hvinv : ∀ c, nv⁻¹ * rootDiagUnit TwistTag.D4.tag c * nv =
      rootDiagUnit TwistTag.D4.tag (weylTuple weylV⁻¹ c) := by
    intro c
    have h := hv (weylTuple weylV⁻¹ c)
    rw [weylTuple_weylTuple, mul_inv_cancel, weylTuple_one] at h
    rw [← h]
    group
  have hs : ∀ (i : Fin TwistTag.D4.tag.rank) c,
      weylElt TwistTag.D4.tag L i 1 * rootDiagUnit TwistTag.D4.tag c *
          (weylElt TwistTag.D4.tag L i 1)⁻¹ =
        rootDiagUnit TwistTag.D4.tag (weylTuple (simple TwistTag.D4.tag i) c) := by
    intro i c
    rw [← canonicalRep_simple (coxeterSystem TwistTag.D4.tag) L i]
    exact canonicalRep_conj_rootDiagUnit _ c
  calc d4RotElt L * rootDiagUnit TwistTag.D4.tag b * (d4RotElt L)⁻¹ =
      nv * (weylElt TwistTag.D4.tag L 0 1 * (weylElt TwistTag.D4.tag L 2 1 *
        (nv⁻¹ * rootDiagUnit TwistTag.D4.tag b * nv) * (weylElt TwistTag.D4.tag L 2 1)⁻¹) *
          (weylElt TwistTag.D4.tag L 0 1)⁻¹) * nv⁻¹ := by
        rw [d4RotElt, ← hnv]
        group
    _ = rootDiagUnit TwistTag.D4.tag (weylTuple weylV (weylTuple (simple TwistTag.D4.tag 0)
          (weylTuple (simple TwistTag.D4.tag 2) (weylTuple weylV⁻¹ b)))) := by
        rw [hvinv, hs, hs, hv]
    _ = _ := by
        rw [weylTuple_weylTuple, weylTuple_weylTuple, weylTuple_weylTuple, weylU]

theorem d4RotElt_pow_conj_rootDiagUnit (k : ℕ) (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    d4RotElt L ^ k * rootDiagUnit TwistTag.D4.tag b * (d4RotElt L ^ k)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (weylTuple (weylU ^ k) b) := by
  induction k generalizing b with
  | zero => rw [pow_zero, pow_zero, weylTuple_one, one_mul, inv_one, mul_one]
  | succ k ih =>
    calc d4RotElt L ^ (k + 1) * rootDiagUnit TwistTag.D4.tag b * (d4RotElt L ^ (k + 1))⁻¹ =
        d4RotElt L ^ k * (d4RotElt L * rootDiagUnit TwistTag.D4.tag b * (d4RotElt L)⁻¹) *
          (d4RotElt L ^ k)⁻¹ := by rw [pow_succ]; group
      _ = _ := by rw [d4RotElt_conj_rootDiagUnit, ih, weylTuple_weylTuple, ← pow_succ]

@[expose] def rotHom (j : ℕ) :
    (Fin TwistTag.D4.tag.rank → Lˣ) →* (Fin TwistTag.D4.tag.rank → Lˣ) where
  toFun b := weylTuple (weylU ^ j) (fun i => b (TwistTag.D4.perm i))
  map_one' := by
    funext i
    simp [weylTuple, rootChar]
  map_mul' b b' := by
    funext i
    simp only [weylTuple, rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rot_conj_rootDiagUnit (j : ℕ) (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹) * rootDiagUnit TwistTag.D4.tag b *
        (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (rotHom j b) := by
  have hP : (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag b *
      diagramMap TwistTag.D4 L =
        rootDiagUnit TwistTag.D4.tag (fun i => b (TwistTag.D4.perm i)) := by
    rw [diagramMap_inv_mul_rootDiagUnit]
    group
  calc (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹) * rootDiagUnit TwistTag.D4.tag b *
        (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹)⁻¹ =
      d4RotElt L ^ j * ((diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag b *
        diagramMap TwistTag.D4 L) * (d4RotElt L ^ j)⁻¹ := by group
    _ = _ := by rw [hP, d4RotElt_pow_conj_rootDiagUnit]; rfl

theorem rootChar_rotHom (j : ℕ) (b : Fin TwistTag.D4.tag.rank → Lˣ)
    (x : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (rotHom j b) x = rootChar b (permLattice TwistTag.D4.perm ((weylU ^ j)⁻¹ • x)) := by
  change rootChar (weylTuple (weylU ^ j) (fun i => b (TwistTag.D4.perm i))) x = _
  rw [rootChar_weylTuple, rootChar_permLattice]

theorem rot_lattice_norm_one : ∀ i : Fin TwistTag.D4.tag.rank,
    (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) +
        permLattice TwistTag.D4.perm (weylUInvAct (Pi.single i 1)) +
      permLattice TwistTag.D4.perm (weylUInvAct (permLattice TwistTag.D4.perm
        (weylUInvAct (Pi.single i 1)))) = 0 := by
  decide +kernel

theorem rot_lattice_norm_two : ∀ i : Fin TwistTag.D4.tag.rank,
    (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) +
        permLattice TwistTag.D4.perm (weylUInvAct (weylUInvAct (Pi.single i 1))) +
      permLattice TwistTag.D4.perm (weylUInvAct (weylUInvAct (permLattice TwistTag.D4.perm
        (weylUInvAct (weylUInvAct (Pi.single i 1)))))) = 0 := by
  decide +kernel

theorem rotHom_norm {j : ℕ} (hj : j = 1 ∨ j = 2) (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    b * rotHom j b * rotHom j (rotHom j b) = 1 := by
  have hsingle : ∀ (c : Fin TwistTag.D4.tag.rank → Lˣ) i, c i = rootChar c (Pi.single i 1) :=
    fun c i => by simpa using (rootChar_nsmul_single c i 1).symm
  funext i
  rw [Pi.mul_apply, Pi.mul_apply, Pi.one_apply, hsingle b i, hsingle (rotHom j b) i,
    hsingle (rotHom j (rotHom j b)) i, rootChar_rotHom, rootChar_rotHom, rootChar_rotHom,
    ← rootChar_add, ← rootChar_add]
  have hv : (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) +
      permLattice TwistTag.D4.perm ((weylU ^ j)⁻¹ • Pi.single i 1) +
        permLattice TwistTag.D4.perm ((weylU ^ j)⁻¹ •
          permLattice TwistTag.D4.perm ((weylU ^ j)⁻¹ • Pi.single i 1)) = 0 := by
    rcases hj with rfl | rfl
    · simp only [pow_one, weylU_inv_smul]
      exact rot_lattice_norm_one i
    · simp only [pow_two, mul_inv_rev, mul_smul, weylU_inv_smul]
      exact rot_lattice_norm_two i
  rw [hv, rootChar_zero]

theorem comm_norm_aux {G : Type*} [CommGroup G] (x y z : G) (h : x * y * z = 1) :
    x ^ 2 * y * (x ^ 3)⁻¹ * (y ^ 2 * z)⁻¹ = 1 := by
  have e : x ^ 2 * y * (x ^ 3)⁻¹ * (y ^ 2 * z)⁻¹ = (x * y * z)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  rw [e, h, inv_one]

theorem rot_pow_three (h2 : (2 : L) = 0) (j : ℕ) :
    (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1 := by
  have hc : Commute (d4RotElt L ^ j) (diagramMap TwistTag.D4 L)⁻¹ :=
    ((Commute.inv_right (diagramMap_commute_d4RotElt h2).symm)).pow_left j
  have hP3 : diagramMap TwistTag.D4 L ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  rw [hc.mul_pow, ← pow_mul, mul_comm j 3, pow_mul, d4RotElt_pow_three h2, one_pow, one_mul,
    inv_pow, hP3, inv_one]

theorem exists_torus_conj_rot [IsAlgClosed L] {j : ℕ} (hj : j = 1 ∨ j = 2)
    (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    ∃ c : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag c * (rootDiagUnit TwistTag.D4.tag a *
          (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹)) * (rootDiagUnit TwistTag.D4.tag c)⁻¹ =
        d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹ := by
  have hroot : ∀ i, ∃ u : Lˣ, u ^ 3 = (a i)⁻¹ := by
    intro i
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (((a i)⁻¹ : Lˣ) : L) (n := 3) (by norm_num)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hz
      exact ((a i)⁻¹).ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩
  choose e he using hroot
  have hae : a = (e ^ 3)⁻¹ := by
    funext i
    rw [Pi.inv_apply, Pi.pow_apply, he, inv_inv]
  set X := d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹ with hX
  refine ⟨e ^ 2 * rotHom j e, ?_⟩
  set c := e ^ 2 * rotHom j e with hc
  have hXc : X * (rootDiagUnit TwistTag.D4.tag c)⁻¹ * X⁻¹ =
      rootDiagUnit TwistTag.D4.tag (rotHom j c⁻¹) := by
    rw [rootDiagUnit_inv, rot_conj_rootDiagUnit]
  have hkey : c * a * rotHom j c⁻¹ = 1 := by
    rw [map_inv, hc, map_mul, map_pow, hae]
    exact comm_norm_aux e (rotHom j e) (rotHom j (rotHom j e)) (rotHom_norm hj e)
  calc rootDiagUnit TwistTag.D4.tag c * (rootDiagUnit TwistTag.D4.tag a * X) *
        (rootDiagUnit TwistTag.D4.tag c)⁻¹ =
      rootDiagUnit TwistTag.D4.tag c * rootDiagUnit TwistTag.D4.tag a *
        (X * (rootDiagUnit TwistTag.D4.tag c)⁻¹ * X⁻¹) * X := by group
    _ = rootDiagUnit TwistTag.D4.tag (c * a * rotHom j c⁻¹) * X := by
        rw [hXc, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    _ = X := by rw [hkey, rootDiagUnit_one, one_mul]

end Norm

section Main

variable {L : Type} [Field L] [IsAlgClosed L]

theorem exists_conj_of_rot (h2 : (2 : L) = 0) {h : ModGL TwistTag.D4.tag L}
    (hh : h ∈ torusGroup TwistTag.D4.tag L) {j : ℕ} (hj : j < 3)
    (h3 : (h * (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹)) ^ 3 = 1) :
    ∃ g ∈ adjointGroup TwistTag.D4.tag L,
      g * (h * (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹)) * g⁻¹ =
          (diagramMap TwistTag.D4 L)⁻¹ ∨
        g * (h * (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹)) * g⁻¹ =
          d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹ := by
  set P := diagramMap TwistTag.D4 L with hPdef
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [pow_zero, one_mul] at h3 ⊢
    exact exists_conj_of_mem_torusGroup h2 hh h3
  have hj12 : j = 1 ∨ j = 2 := by omega
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain ⟨c, hc⟩ := exists_torus_conj_rot (L := L) hj12 a
  rw [← hPdef] at hc
  have hcG : rootDiagUnit TwistTag.D4.tag c ∈ adjointGroup TwistTag.D4.tag L :=
    (exceptional_Lang_adjoint_diagonal_lift TwistTag.D4.tag L c).1
  obtain ⟨z, hzG, hzP, hzT⟩ := exists_conj_d4RotElt_mem_torusGroup (L := L) h2
  rw [← hPdef] at hzP
  set t := z * d4RotElt L * z⁻¹ with htdef
  have hzPi : z * P⁻¹ * z⁻¹ = P⁻¹ := by
    calc z * P⁻¹ * z⁻¹ = (z * P * z⁻¹)⁻¹ := by group
      _ = P⁻¹ := by rw [hzP]; group
  have hzX : z * (d4RotElt L ^ j * P⁻¹) * z⁻¹ = t ^ j * P⁻¹ := by
    calc z * (d4RotElt L ^ j * P⁻¹) * z⁻¹ = (z * d4RotElt L ^ j * z⁻¹) * (z * P⁻¹ * z⁻¹) := by
          group
      _ = t ^ j * P⁻¹ := by rw [hzPi, htdef, conj_pow]
  have htT : t ^ j ∈ torusGroup TwistTag.D4.tag L := pow_mem hzT j
  have ht3 : (t ^ j * P⁻¹) ^ 3 = 1 := by
    rw [← hzX, conj_pow, rot_pow_three h2 j, mul_one, mul_inv_cancel]
  obtain ⟨g, hgG, hg⟩ := exists_conj_of_mem_torusGroup h2 htT ht3
  refine ⟨g * z * rootDiagUnit TwistTag.D4.tag c, mul_mem (mul_mem hgG hzG) hcG, ?_⟩
  have e : g * z * rootDiagUnit TwistTag.D4.tag c *
      (rootDiagUnit TwistTag.D4.tag a * (d4RotElt L ^ j * P⁻¹)) *
        (g * z * rootDiagUnit TwistTag.D4.tag c)⁻¹ =
      g * (z * (rootDiagUnit TwistTag.D4.tag c * (rootDiagUnit TwistTag.D4.tag a *
        (d4RotElt L ^ j * P⁻¹)) * (rootDiagUnit TwistTag.D4.tag c)⁻¹) * z⁻¹) * g⁻¹ := by
    group
  rw [e, hc, hzX]
  exact hg

end Main

end CFSG.RankThree.PartTwo.Sec8.LangTwistedProof
