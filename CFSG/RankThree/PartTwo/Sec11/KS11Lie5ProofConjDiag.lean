module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofConjCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

open Matrix Polynomial Module
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KGD
open scoped MatrixGroups Pointwise

section Diag

variable {L : Type} [Field L] [IsAlgClosed L]

theorem exists_basis_eigen' (f : Module.End L (Fin 3 → L)) (hf : f.IsSemisimple) :
    ∃ (b : Basis (Fin 3) L (Fin 3 → L)) (μ : Fin 3 → L), ∀ k, f (b k) = μ k • b k := by
  classical
  have htop := hf.iSup_eigenspace_eq_top
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.eigenspaces_iSupIndep htop
  let v : ∀ μ, Basis _ L (f.eigenspace μ) := fun μ => Basis.ofVectorSpace L _
  let B := hint.collectedBasis v
  let e := B.indexEquiv (Pi.basisFun L (Fin 3))
  refine ⟨B.reindex e, fun k => (e.symm k).1, fun k => ?_⟩
  rw [Basis.reindex_apply]
  have hmem := hint.collectedBasis_mem v (e.symm k)
  exact Module.End.mem_eigenspace_iff.1 hmem

theorem exists_conj_diag_pow {n : ℕ} (hn : (n : L) ≠ 0) (M : SL(3, L)) (hM : M ^ n = 1) :
    ∃ P D : SL(3, L), (∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0) ∧
      M = P * D * P⁻¹ := by
  classical
  set A : Matrix (Fin 3) (Fin 3) L := (M : Matrix (Fin 3) (Fin 3) L) with hA
  have hAn : A ^ n = 1 := by
    have := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L)) hM
    simpa [hA] using this
  set f : Module.End L (Fin 3 → L) := Matrix.toLinAlgEquiv' A with hf
  have hsq : Squarefree (X ^ n - C (1 : L)) :=
    (separable_X_pow_sub_C (1 : L) hn one_ne_zero).squarefree
  have hev : aeval f (X ^ n - C (1 : L)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    rw [hf, ← map_pow, hAn, map_one, sub_self]
  obtain ⟨b, μ, hb⟩ := exists_basis_eigen' f
    (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hev)
  set P0 : Matrix (Fin 3) (Fin 3) L := (Pi.basisFun L (Fin 3)).toMatrix b with hP0
  set Q0 : Matrix (Fin 3) (Fin 3) L := b.toMatrix (Pi.basisFun L (Fin 3)) with hQ0
  have hPQ : P0 * Q0 = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hQP : Q0 * P0 = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hcol : ∀ i k, P0 i k = b k i := fun i k => by
    rw [hP0, Basis.toMatrix_apply, Pi.basisFun_repr]
  have hAP : A * P0 = P0 * Matrix.diagonal μ := by
    ext i k
    rw [Matrix.mul_diagonal, hcol]
    have h1 := congrFun (hb k) i
    rw [hf, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_apply, mul_comm (b k i), ← h1]
    simp only [dotProduct, hcol]
  have hAeq : A = P0 * Matrix.diagonal μ * Q0 := by
    rw [← hAP, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  have hdP : P0.det * Q0.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  have hdP0 : P0.det ≠ 0 := left_ne_zero_of_mul_eq_one hdP
  have hdetA : A.det = 1 := M.2
  have hdD : (Matrix.diagonal μ).det = 1 := by
    have h := congrArg Matrix.det hAeq
    rw [Matrix.det_mul, Matrix.det_mul, hdetA, mul_comm P0.det, mul_assoc, hdP, mul_one] at h
    exact h.symm
  set d : L := P0.det with hd
  set c : Matrix (Fin 3) (Fin 3) L := Matrix.diagonal ![d⁻¹, 1, 1] with hc
  set c' : Matrix (Fin 3) (Fin 3) L := Matrix.diagonal ![d, 1, 1] with hc'
  have hc'c : c' * c = 1 := by
    rw [hc, hc', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hdP0]
  have hdetc : c.det = d⁻¹ := by
    rw [hc, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  set P : Matrix (Fin 3) (Fin 3) L := P0 * c with hP
  have hdetP : P.det = 1 := by rw [hP, Matrix.det_mul, hdetc, ← hd, mul_inv_cancel₀ hdP0]
  let P' : SL(3, L) := ⟨P, hdetP⟩
  let D' : SL(3, L) := ⟨Matrix.diagonal μ, hdD⟩
  refine ⟨P', D', fun i j hij => Matrix.diagonal_apply_ne μ hij, ?_⟩
  apply Subtype.ext
  have hinv : ((P'⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = c' * Q0 := by
    have h1 : P * ((P'⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = 1 := by
      have := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L)) (mul_inv_cancel P')
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
      exact this
    have h2 : (c' * Q0) * P = 1 := by
      rw [hP, Matrix.mul_assoc, ← Matrix.mul_assoc Q0, hQP, Matrix.one_mul, hc'c]
    calc ((P'⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        ((c' * Q0) * P) * ((P'⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) := by
          rw [h2, Matrix.one_mul]
      _ = c' * Q0 := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hcomm : c * Matrix.diagonal μ * c' = Matrix.diagonal μ := by
    rw [hc, hc', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp
    · simp
  change A = P * Matrix.diagonal μ * ((P'⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)
  rw [hinv, hAeq, hP]
  calc P0 * Matrix.diagonal μ * Q0 = P0 * (c * Matrix.diagonal μ * c') * Q0 := by rw [hcomm]
    _ = P0 * c * Matrix.diagonal μ * (c' * Q0) := by simp only [Matrix.mul_assoc]

end Diag

section Frame

variable
  {L : Type} [Field L] [IsAlgClosed L]

omit
  [IsAlgClosed L] in
theorem exists_rootDiagUnit_of_mem_torusGroup' {τ : Tag} {h : ModGL τ L}
    (hh : h ∈ torusGroup τ L) : ∃ l : Fin τ.rank → Lˣ, h = rootDiagUnit τ l := by
  obtain ⟨l, hl⟩ := exists_torus_characters hh
  refine ⟨l, Units.ext (rootModule_end_ext (fun j => ?_) fun α hα => ?_)⟩
  · rw [((triangular_borel_structure.{0, 0} τ L).2.1 _ hh).1 j]
    exact (rootDiag_hVec l j).symm
  · rw [(hl α hα).1]
    exact (rootDiag_rootVec l hα).symm

variable (L) in
@[expose] noncomputable def rhoA : SL(3, L) →* ModGL TwistTag.D4.tag L := d4rhoStd L

theorem rhoA_frame :
    IsA2Frame (τ := TwistTag.D4.tag) (rhoA L) (fun i j => chainRoot d4ChainA2 i j) :=
  d4Std_frame (L := L)

theorem exists_diag_conj_frame {h : ModGL TwistTag.D4.tag L}
    (hh : h ∈ torusGroup TwistTag.D4.tag L) :
    ∃ D : SL(3, L), (∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0) ∧
      ∀ B : SL(3, L), h * rhoA L B * h⁻¹ = rhoA L (D * B * D⁻¹) := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_of_mem_torusGroup' hh
  set d : Fin 3 → Lˣ := fun i => rootChar b (chainRoot d4ChainA2 i 0) with hd
  obtain ⟨δ0, hδ0⟩ := IsAlgClosed.exists_pow_nat_eq ((d 0 * d 1 * d 2 : Lˣ) : L)
    (by norm_num : 0 < 3)
  have hδ0' : δ0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hδ0
    exact (Units.ne_zero _) hδ0.symm
  set δ : Lˣ := Units.mk0 δ0 hδ0' with hδ
  set e : Fin 3 → Lˣ := fun i => d i * δ⁻¹ with he
  have hδ3 : δ ^ 3 = d 0 * d 1 * d 2 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hδ]
    exact hδ0)
  have hprod : e 0 * e 1 * e 2 = 1 := by
    simp only [he]
    calc d 0 * δ⁻¹ * (d 1 * δ⁻¹) * (d 2 * δ⁻¹) = (d 0 * d 1 * d 2) * (δ * δ * δ)⁻¹ := by
          simp only [_root_.mul_inv_rev]
          simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = 1 := by rw [← pow_three', hδ3, mul_inv_cancel]
  have hdet : (Matrix.diagonal fun i => ((e i : Lˣ) : L)).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three, ← Units.val_mul, ← Units.val_mul, hprod,
      Units.val_one]
  set D : SL(3, L) := ⟨Matrix.diagonal fun i => ((e i : Lˣ) : L), hdet⟩ with hD
  refine ⟨D, fun i j hij => Matrix.diagonal_apply_ne _ hij, fun B => ?_⟩
  have htor := (rhoA_frame (L := L)).torus b B
  refine htor.trans (congrArg (rhoA L) ?_)
  have key : conjDiag3 d B * D = D * B := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_conjDiag3]
    ext i j
    simp only [hD, diagGL3, Units.inv_mk, Matrix.mul_diagonal, Matrix.diagonal_mul, he,
      Units.val_mul, Units.val_inv_eq_inv_val]
    have hdj : ((d j : Lˣ) : L) ≠ 0 := (d j).ne_zero
    field_simp
  calc conjDiag3 d B = conjDiag3 d B * D * D⁻¹ := by group
    _ = D * B * D⁻¹ := by rw [key]

omit
  [IsAlgClosed L] in
theorem three_ne_zero_of_orderOf {ζ : Lˣ} (hζ : orderOf ζ = 3) : (3 : L) ≠ 0 := by
  intro h3
  have hz3 : (ζ : L) ^ 3 = 1 := by
    have := congrArg Units.val (pow_three_of_orderOf hζ)
    simpa using this
  have h0 : ((ζ : L) - 1) ^ 3 = 0 := by
    linear_combination hz3 + (-(ζ : L) ^ 2 + ζ) * h3
  have h1 : (ζ : L) = 1 := sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h0)
  have : ζ = 1 := Units.ext h1
  rw [this, orderOf_one] at hζ
  exact absurd hζ (by norm_num)

theorem exists_conj_torus_of_cent_gA {ζ : Lˣ} (hζ : orderOf ζ = 3) {y : ModGL TwistTag.D4.tag L}
    (hy : y ∈ graphCentralizer TwistTag.D4.tag L (rootDiagUnit TwistTag.D4.tag (tup ζ gA)))
    (hy3 : y ^ 3 = 1) :
    ∃ g ∈ adjointGroup TwistTag.D4.tag L, g * y * g⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
  classical
  rw [graphCentralizer_gA hζ] at hy
  have hHQ : ((torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L sigmaA :
      Subgroup (ModGL TwistTag.D4.tag L)) : Set (ModGL TwistTag.D4.tag L)) =
      (torusGroup TwistTag.D4.tag L : Set (ModGL TwistTag.D4.tag L)) *
        (rootSpan TwistTag.D4.tag L sigmaA : Set (ModGL TwistTag.D4.tag L)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun α hα => isRoot_of_mem_sigmaA hα)
  have hy' : y ∈ (torusGroup TwistTag.D4.tag L : Set (ModGL TwistTag.D4.tag L)) *
      (rootSpan TwistTag.D4.tag L sigmaA : Set (ModGL TwistTag.D4.tag L)) := by
    rw [← hHQ]
    exact hy
  obtain ⟨h, hh, q, hq, rfl⟩ := Set.mem_mul.1 hy'
  have hrange : (rhoA L).range = rootSpan TwistTag.D4.tag L sigmaA := rhoA_frame.range
  have hq' : q ∈ (rhoA L).range := by rw [hrange]; exact hq
  obtain ⟨A, rfl⟩ := hq'
  obtain ⟨D, hDdiag, hD⟩ := exists_diag_conj_frame hh
  set ρ := rhoA L with hρ
  set h' := (ρ D)⁻¹ * h with hh'def
  have hρinj : Function.Injective ρ := rhoA_frame.injective
  have hh'c : ∀ C, h' * ρ C = ρ C * h' := by
    intro C
    have h1 := hD C
    have h2 : h * ρ C = ρ (D * C * D⁻¹) * h := by rw [← h1]; group
    calc h' * ρ C = (ρ D)⁻¹ * (h * ρ C) := by rw [hh'def]; group
      _ = (ρ D)⁻¹ * (ρ (D * C * D⁻¹) * h) := by rw [h2]
      _ = ρ C * h' := by
        rw [hh'def, map_mul, map_mul, map_inv]
        group
  have hhD : h = ρ D * h' := by rw [hh'def]; group
  set B := D * A with hB
  have hy_eq : h * ρ A = h' * ρ B := by
    rw [hhD, hB, map_mul, ← hh'c D]
    group
  rw [hy_eq] at hy3 ⊢
  have hcube : (h' * ρ B) ^ 3 = h' ^ 3 * ρ (B ^ 3) := by
    have hc : Commute h' (ρ B) := hh'c B
    rw [hc.mul_pow, map_pow]
  rw [hcube] at hy3
  have hB3 : ρ (B ^ 3) = (h' ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hy3
  have hcen : B ^ 3 ∈ Subgroup.center (SL(3, L)) := by
    refine Subgroup.mem_center_iff.2 fun C => hρinj ?_
    rw [map_mul, map_mul, hB3]
    have hc : Commute (h' ^ 3)⁻¹ (ρ C) := ((Commute.pow_left (hh'c C) 3)).inv_left
    exact hc.eq.symm
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcen
  have hB9 : B ^ 9 = 1 := by
    apply Subtype.ext
    have e9 : B ^ 9 = (B ^ 3) ^ 3 := by rw [← pow_mul]
    rw [e9, Matrix.SpecialLinearGroup.coe_pow, ← hr, Matrix.SpecialLinearGroup.coe_one]
    rw [Fintype.card_fin] at hr3
    rw [← map_pow, hr3, map_one]
  have h9 : ((9 : ℕ) : L) ≠ 0 := by
    have h3 := three_ne_zero_of_orderOf hζ
    push_cast
    intro h0
    apply h3
    have : (9 : L) = 3 * 3 := by norm_num
    rw [this] at h0
    exact (mul_self_eq_zero.1 h0)
  obtain ⟨P, Δ, hΔ, hBP⟩ := exists_conj_diag_pow h9 B hB9
  refine ⟨(ρ P)⁻¹, ?_, ?_⟩
  · have hmem : ρ P ∈ rootSpan TwistTag.D4.tag L sigmaA := by rw [← hrange]; exact ⟨P, rfl⟩
    exact inv_mem (rootSpan_le_adjointGroup _ _ hmem)
  · have hconj : (ρ P)⁻¹ * (h' * ρ B) * (ρ P)⁻¹⁻¹ = h' * ρ Δ := by
      rw [hBP, inv_inv]
      have hc : Commute h' (ρ P)⁻¹ := (show Commute h' (ρ P) from hh'c P).inv_right
      calc (ρ P)⁻¹ * (h' * ρ (P * Δ * P⁻¹)) * ρ P =
          ((ρ P)⁻¹ * h') * ρ (P * Δ * P⁻¹) * ρ P := by group
        _ = (h' * (ρ P)⁻¹) * ρ (P * Δ * P⁻¹) * ρ P := by rw [hc.eq]
        _ = h' * ρ Δ := by rw [map_mul, map_mul, map_inv]; group
    rw [hconj]
    have hh' : h' ∈ torusGroup TwistTag.D4.tag L :=
      mul_mem (inv_mem (rhoA_frame.diag D hDdiag)) hh
    exact mul_mem hh' (rhoA_frame.diag Δ hΔ)

end Frame

end CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
