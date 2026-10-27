module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofConjDiag
public import CFSG.RankThree.Chevalley.EvenTrialityElementaryNine
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

open Matrix Polynomial Module
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KGD
open scoped MatrixGroups

section Diag2

variable {L : Type} [Field L] [IsAlgClosed L]

theorem exists_basis_eigen_two (f : Module.End L (Fin 2 → L)) (hf : f.IsSemisimple) :
    ∃ (b : Basis (Fin 2) L (Fin 2 → L)) (μ : Fin 2 → L), ∀ k, f (b k) = μ k • b k := by
  classical
  have htop := hf.iSup_eigenspace_eq_top
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.eigenspaces_iSupIndep htop
  let v : ∀ μ, Basis _ L (f.eigenspace μ) := fun μ => Basis.ofVectorSpace L _
  let B := hint.collectedBasis v
  let e := B.indexEquiv (Pi.basisFun L (Fin 2))
  refine ⟨B.reindex e, fun k => (e.symm k).1, fun k => ?_⟩
  rw [Basis.reindex_apply]
  have hmem := hint.collectedBasis_mem v (e.symm k)
  exact Module.End.mem_eigenspace_iff.1 hmem

theorem exists_conj_diag_two {n : ℕ} (hn : (n : L) ≠ 0) (M : SL2 L) (hM : M ^ n = 1) :
    ∃ P D : SL2 L, (∀ i j : Fin 2, i ≠ j → (D : Matrix (Fin 2) (Fin 2) L) i j = 0) ∧
      M = P * D * P⁻¹ := by
  classical
  set A : Matrix (Fin 2) (Fin 2) L := (M : Matrix (Fin 2) (Fin 2) L) with hA
  have hAn : A ^ n = 1 := by
    have := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L)) hM
    simpa [hA] using this
  set f : Module.End L (Fin 2 → L) := Matrix.toLinAlgEquiv' A with hf
  have hsq : Squarefree (X ^ n - C (1 : L)) :=
    (separable_X_pow_sub_C (1 : L) hn one_ne_zero).squarefree
  have hev : aeval f (X ^ n - C (1 : L)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    rw [hf, ← map_pow, hAn, map_one, sub_self]
  obtain ⟨b, μ, hb⟩ := exists_basis_eigen_two f
    (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hev)
  set P0 : Matrix (Fin 2) (Fin 2) L := (Pi.basisFun L (Fin 2)).toMatrix b with hP0
  set Q0 : Matrix (Fin 2) (Fin 2) L := b.toMatrix (Pi.basisFun L (Fin 2)) with hQ0
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
  set c : Matrix (Fin 2) (Fin 2) L := Matrix.diagonal ![d⁻¹, 1] with hc
  set c' : Matrix (Fin 2) (Fin 2) L := Matrix.diagonal ![d, 1] with hc'
  have hc'c : c' * c = 1 := by
    rw [hc, hc', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hdP0]
  have hdetc : c.det = d⁻¹ := by
    rw [hc, Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  set P : Matrix (Fin 2) (Fin 2) L := P0 * c with hP
  have hdetP : P.det = 1 := by rw [hP, Matrix.det_mul, hdetc, ← hd, mul_inv_cancel₀ hdP0]
  let P' : SL2 L := ⟨P, hdetP⟩
  let D' : SL2 L := ⟨Matrix.diagonal μ, hdD⟩
  refine ⟨P', D', fun i j hij => Matrix.diagonal_apply_ne μ hij, ?_⟩
  apply Subtype.ext
  have hinv : ((P'⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) = c' * Q0 := by
    have h1 : P * ((P'⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) = 1 := by
      have := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L)) (mul_inv_cancel P')
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
      exact this
    have h2 : (c' * Q0) * P = 1 := by
      rw [hP, Matrix.mul_assoc, ← Matrix.mul_assoc Q0, hQP, Matrix.one_mul, hc'c]
    calc ((P'⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
        ((c' * Q0) * P) * ((P'⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) := by
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
  change A = P * Matrix.diagonal μ * ((P'⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L)
  rw [hinv, hAeq, hP]
  calc P0 * Matrix.diagonal μ * Q0 = P0 * (c * Matrix.diagonal μ * c') * Q0 := by rw [hcomm]
    _ = P0 * c * Matrix.diagonal μ * (c' * Q0) := by simp only [Matrix.mul_assoc]

theorem eq_HSL_of_diag {D : SL2 L}
    (hD : ∀ i j : Fin 2, i ≠ j → (D : Matrix (Fin 2) (Fin 2) L) i j = 0) :
    ∃ t : Lˣ, D = HSL t := by
  have hdet := D.2
  rw [Matrix.det_fin_two, hD 0 1 (by decide), hD 1 0 (by decide), mul_zero, sub_zero] at hdet
  have h0 : (D : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ h0, SL2_ext ?_ ?_ ?_ ?_⟩
  · simp [coe_HSL]
  · simp [coe_HSL, hD 0 1 (by decide)]
  · simp [coe_HSL, hD 1 0 (by decide)]
  · simp only [coe_HSL, Units.val_inv_eq_inv_val, Units.val_mk0]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact eq_inv_of_mul_eq_one_right hdet

end Diag2

section Rank


theorem baseChangeGL_rankOneHom {R S : Type} [Field R] [Field S] (f : R →+* S)
    (i : Fin TwistTag.D4.tag.rank) (A : SL2 R) :
    baseChangeGL f (rankOneHom TwistTag.D4 R i A) =
      rankOneHom TwistTag.D4 S i (Matrix.SpecialLinearGroup.map f A) := by
  have h : (baseChangeGL f).comp (rankOneHom TwistTag.D4 R i) =
      (rankOneHom TwistTag.D4 S i).comp (Matrix.SpecialLinearGroup.map f) := by
    refine SL2_hom_ext (fun s => ?_) (fun u => ?_) ?_
    · simp only [MonoidHom.comp_apply, rankOneHom_uSL, map_uSL, baseChangeGL_xUnit]
    · simp only [MonoidHom.comp_apply, rankOneHom_HSL, map_HSL, baseChangeGL_torusElt]
    · simp only [MonoidHom.comp_apply, rankOneHom_WSL, map_WSL,
        LieType.Chevalley.baseChangeGL_weylElt_one]
  exact DFunLike.congr_fun h A

end Rank

theorem map_sl2Three {R S : Type} [Field R] [Field S] (f : R →+* S) :
    Matrix.SpecialLinearGroup.map f (KS11Lie4Proof.sl2Three R) = KS11Lie4Proof.sl2Three S :=
  SL2_ext
    (by change f ((!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) R) 0 0) =
      (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) S) 0 0; simp)
    (by change f ((!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) R) 0 1) =
      (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) S) 0 1; simp)
    (by change f ((!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) R) 1 0) =
      (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) S) 1 0; simp)
    (by change f ((!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) R) 1 1) =
      (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) S) 1 1; simp)

theorem eq_pow_of_pow_three {L : Type} [Field L] {ζ μ : Lˣ} (hζ : orderOf ζ = 3)
    (hμ : μ ^ 3 = 1) : ∃ m < 3, μ = ζ ^ m := by
  have hprim : IsPrimitiveRoot (ζ : L) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  have h1 : (μ : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hμ, Units.val_one]
  obtain ⟨m, hm, hmμ⟩ := hprim.eq_pow_of_pow_eq_one h1
  exact ⟨m, hm, Units.ext (by rw [Units.val_pow_eq_pow_val, hmμ])⟩

theorem exists_conj_sl2Three {L : Type} [Field L] [IsAlgClosed L] {ζ : Lˣ} (hζ : orderOf ζ = 3) :
    ∃ (P : SL2 L) (m : ℕ), (m = 1 ∨ m = 2) ∧
      KS11Lie4Proof.sl2Three L = P * HSL (ζ ^ m) * P⁻¹ := by
  obtain ⟨hA3, hA1⟩ := KS11Lie4Proof.sl2Three_pow_three L
  have h3 : ((3 : ℕ) : L) ≠ 0 := by
    have := three_ne_zero_of_orderOf hζ
    exact_mod_cast this
  obtain ⟨P, D, hD, hPD⟩ := exists_conj_diag_two h3 _ hA3
  obtain ⟨μ, rfl⟩ := eq_HSL_of_diag hD
  have hμ3 : μ ^ 3 = 1 := by
    have h1 : HSL μ ^ 3 = 1 := by
      have h2 : P * HSL μ ^ 3 * P⁻¹ = 1 := by
        rw [← conj_pow, ← hPD, hA3]
      calc HSL μ ^ 3 = P⁻¹ * (P * HSL μ ^ 3 * P⁻¹) * P := by group
        _ = 1 := by rw [h2]; group
    have h4 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) 0 0) h1
    simp only [Matrix.SpecialLinearGroup.coe_pow, coe_HSL, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at h4
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h5 : (!![(μ : L), 0; 0, ((μ⁻¹ : Lˣ) : L)] ^ 3) 0 0 = (μ : L) ^ 3 := by
      simp [pow_succ]
    rw [← h5]
    exact h4
  obtain ⟨m, hm3, rfl⟩ := eq_pow_of_pow_three hζ hμ3
  refine ⟨P, m, ?_, hPD⟩
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with h0 | h1 | h2
  · exfalso
    apply hA1
    rw [hPD, h0, pow_zero]
    have hH1 : HSL (1 : Lˣ) = 1 := SL2_ext (by simp [coe_HSL]) (by simp [coe_HSL])
      (by simp [coe_HSL]) (by simp [coe_HSL])
    rw [hH1]
    group
  · exact Or.inl h1
  · exact Or.inr h2

section Reps

variable
  {K : Type} [Field K]

abbrev d4Middle : Fin TwistTag.D4.foldedTag.rank := ⟨1, by decide⟩

abbrev n2 : Fin TwistTag.D4.tag.rank := ⟨2, by decide⟩

@[expose] noncomputable def d4S0 (σ : K ≃+* K) : ModGL TwistTag.D4.tag K :=
  orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer
    (KS11Lie4Proof.sl2Three _)

theorem d4S0_mem (σ : K ≃+* K) :
    d4S0 σ ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  range_orbitRankOneHom_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
    KS11Lie4Proof.d4Outer ⟨_, rfl⟩

theorem d4S0_mem_short (σ : K ≃+* K) :
    (⟨d4S0 σ, d4S0_mem σ⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
      KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :=
  ⟨_, rfl⟩

theorem d4S0_eq (σ : K ≃+* K) :
    d4S0 σ = rankOneHom TwistTag.D4 K n0 (KS11Lie4Proof.sl2Three K) *
      rankOneHom TwistTag.D4 K n1 (KS11Lie4Proof.sl2Three K) *
        rankOneHom TwistTag.D4 K n3 (KS11Lie4Proof.sl2Three K) := by
  rw [d4S0, orbitRankOneHom_apply]
  have hc : (TwistTag.D4.orbit KS11Lie4Proof.d4Outer).card = 3 := by decide
  have hm : TwistTag.D4.orbitMin KS11Lie4Proof.d4Outer = n0 := by decide
  have hp1 : (TwistTag.D4.perm ^ 1) n0 = n1 := by decide
  have hp2 : (TwistTag.D4.perm ^ 2) n0 = n3 := by decide
  rw [hc, hm, show List.range 3 = [0, 1, 2] by rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
    hp1, hp2, map_sl2Three, Equiv.Perm.one_apply]
  rw [mul_assoc]

@[expose] noncomputable def d4HT (σ : K ≃+* K) : ModGL TwistTag.D4.tag K :=
  ([KS11Lie4Proof.d4Outer, d4Middle].map fun a =>
    (orbitN .D4 K σ.toRingHom a 1 : ModGL TwistTag.D4.tag K)).reverse.prod

theorem d4HT_mem (σ : K ≃+* K) : d4HT σ ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
  rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_mem (mul_mem (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ.toRingHom
    (orbitX_mem_graphFixedPosUnipotent _ σ.toRingHom a _))
    (graphFixedNegUnipotent_le_graphFixedRootGroup _ K σ.toRingHom
      (orbitY_mem_graphFixedNegUnipotent _ σ.toRingHom a _)))
    (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ.toRingHom
      (orbitX_mem_graphFixedPosUnipotent _ σ.toRingHom a _))

theorem d4HT_mem_adjointGroup (σ : K ≃+* K) : d4HT σ ∈ adjointGroup TwistTag.D4.tag K :=
  ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ (d4HT_mem σ))).1

@[expose] noncomputable def d4T0 (σ : K ≃+* K) : ModGL TwistTag.D4.tag K :=
  d4HT σ * orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Middle (KS11Lie4Proof.sl2Three _) *
    (d4HT σ)⁻¹

theorem d4T0_mem (σ : K ≃+* K) : d4T0 σ ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  mul_mem (mul_mem (d4HT_mem σ) (range_orbitRankOneHom_le (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) d4Middle ⟨_, rfl⟩)) (inv_mem (d4HT_mem σ))

theorem orbitRankOneHom_middle_sl2Three (σ : K ≃+* K) :
    orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Middle (KS11Lie4Proof.sl2Three _) =
      rankOneHom TwistTag.D4 K n2 (KS11Lie4Proof.sl2Three K) := by
  rw [orbitRankOneHom_apply]
  have hc : (TwistTag.D4.orbit d4Middle).card = 1 := by decide
  have hm : TwistTag.D4.orbitMin d4Middle = n2 := by decide
  rw [hc, hm, show List.range 1 = [0] by rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
    map_sl2Three]
  rfl

theorem d4T0_commute (σ : K ≃+* K) {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer).range) :
    x * d4T0 σ = d4T0 σ * x := by
  set a₁ := KS11Lie4Proof.d4Outer
  set a₂ := d4Middle
  set R₁ := orbitRankOneHom TwistTag.D4 K σ.toRingHom a₁
  set R₂ := orbitRankOneHom TwistTag.D4 K σ.toRingHom a₂
  have hj : ∀ k, (TwistTag.D4.perm ^ k) (TwistTag.D4.orbitMin a₂) = ⟨2, by decide⟩ := fun k => by
    have h := TwistTag.D4.perm_pow_mem_orbit (TwistTag.D4.orbitMin_mem a₂) k
    have h3' : TwistTag.D4.orbit a₂ = {⟨2, by decide⟩} := by decide
    rwa [h3', Finset.mem_singleton] at h
  have hR₂Q : R₂.range ≤ rootSubgroup TwistTag.D4.tag K (Pi.single ⟨2, by decide⟩ 1) ⊔
      rootSubgroup TwistTag.D4.tag K (-Pi.single ⟨2, by decide⟩ 1) := by
    rw [orbitRankOneHom_range, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitX]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj k, ← pinnedX_single]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitY]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj k, ← pinnedX_neg_single]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
  set J : Subgroup (ModGL TwistTag.D4.tag K) := Subgroup.closure
    {g | ∃ i ∈ TwistTag.D4.orbit a₁, ∃ c : K, g = xUnit TwistTag.D4.tag K i c ∨
      g = yUnit TwistTag.D4.tag K i c} with hJ
  have hR₁J : R₁.range ≤ J := by
    rw [orbitRankOneHom_range, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitX]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact Subgroup.subset_closure ⟨_, TwistTag.D4.perm_pow_mem_orbit
        (TwistTag.D4.orbitMin_mem a₁) k, _, Or.inl rfl⟩
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitY]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact Subgroup.subset_closure ⟨_, TwistTag.D4.perm_pow_mem_orbit
        (TwistTag.D4.orbitMin_mem a₁) k, _, Or.inr rfl⟩
  have hηQ : d4T0 σ ∈ rootSubgroup TwistTag.D4.tag K (d4Vec ![1, 1, 2, 1]) ⊔
      rootSubgroup TwistTag.D4.tag K (-d4Vec ![1, 1, 2, 1]) := by
    rw [← d4_fold_root, ← map_conj_orbitN_list_rootPair .D4 σ.toRingHom [a₁, a₂]
      (isRoot_single _ _)]
    exact ⟨_, hR₂Q ⟨_, rfl⟩, rfl⟩
  obtain ⟨hθ, hcheck⟩ := d4_outer_theta_check
  have hgen : ∀ x ∈ {g | ∃ i ∈ TwistTag.D4.orbit a₁, ∃ c : K,
      g = xUnit TwistTag.D4.tag K i c ∨ g = yUnit TwistTag.D4.tag K i c},
      ∀ y ∈ ((rootSubgroup TwistTag.D4.tag K (d4Vec ![1, 1, 2, 1]) ⊔
        rootSubgroup TwistTag.D4.tag K (-d4Vec ![1, 1, 2, 1]) : Subgroup _) :
          Set (ModGL TwistTag.D4.tag K)), x * y = y * x := by
    rintro x ⟨i, hi, c, hx⟩ y hy
    have hi2 : i ≠ ⟨2, by decide⟩ := by
      rintro rfl
      exact absurd hi (by decide)
    obtain ⟨hi1, h0, hp, hm⟩ := hcheck i hi2
    have hxQ : x ∈ rootSubgroup TwistTag.D4.tag K (Pi.single i 1) ⊔
        rootSubgroup TwistTag.D4.tag K (-Pi.single i 1) := by
      rcases hx with rfl | rfl
      · rw [← pinnedX_single]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
      · rw [← pinnedX_neg_single]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
    exact commute_of_mem_rootPair_of_check hi1 hθ h0 hp hm hxQ hy
  have hcomm := closure_commute hgen
  rw [Subgroup.closure_eq] at hcomm
  exact hcomm _ (hR₁J hx) _ hηQ

theorem d4T0_mem_centralizer (σ : K ≃+* K) :
    (⟨d4T0 σ, d4T0_mem σ⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
      Subgroup.centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subtype.ext (d4T0_commute σ hy)

end Reps

section Conj

variable
  {L : Type} [Field L]

theorem rankOneHom_mem_adjointGroup_D4 (i : Fin TwistTag.D4.tag.rank) (A : SL2 L) :
    rankOneHom TwistTag.D4 L i A ∈ adjointGroup TwistTag.D4.tag L := by
  have h : (rankOneHom TwistTag.D4 L i).range ≤ adjointGroup TwistTag.D4.tag L := by
    rw [rankOneHom_range, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]
  exact h ⟨A, rfl⟩

variable (L) in
@[expose] noncomputable def outerProd : SL2 L →* ModGL TwistTag.D4.tag L :=
  MonoidHom.mk' (fun A => rankOneHom TwistTag.D4 L n0 A * rankOneHom TwistTag.D4 L n1 A *
    rankOneHom TwistTag.D4 L n3 A) fun A B => by
    have h0 : n0 ∈ TwistTag.D4.orbit KS11Lie4Proof.d4Outer := by decide
    have h1 : n1 ∈ TwistTag.D4.orbit KS11Lie4Proof.d4Outer := by decide
    have h3 : n3 ∈ TwistTag.D4.orbit KS11Lie4Proof.d4Outer := by decide
    have c01 := commute_rankOneHom (K := L) h0 h1 (by decide) B A
    have c03 := commute_rankOneHom (K := L) h0 h3 (by decide) B A
    have c13 := commute_rankOneHom (K := L) h1 h3 (by decide) B A
    simp only [map_mul]
    rw [c01.mul_mul_mul_comm, (c03.mul_left c13).mul_mul_mul_comm]

theorem outerProd_apply (A : SL2 L) : outerProd L A = rankOneHom TwistTag.D4 L n0 A *
    rankOneHom TwistTag.D4 L n1 A * rankOneHom TwistTag.D4 L n3 A := rfl

theorem outerProd_mem_adjointGroup (A : SL2 L) :
    outerProd L A ∈ adjointGroup TwistTag.D4.tag L :=
  mul_mem (mul_mem (rankOneHom_mem_adjointGroup_D4 _ _) (rankOneHom_mem_adjointGroup_D4 _ _))
    (rankOneHom_mem_adjointGroup_D4 _ _)

theorem pow_zpow_eq_tup {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (m : ℕ) (c : ℤ) :
    (ζ ^ m) ^ c = ζ ^ (((m : ZMod 3) * (c : ZMod 3)).val) := by
  rw [← zpow_natCast, ← _root_.zpow_mul, zpow_eq_pow_val hζ]
  push_cast
  rfl

theorem outerProd_HSL {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (m : ℕ) :
    outerProd L (HSL (ζ ^ m)) =
      rootDiagUnit TwistTag.D4.tag (tup ζ fun j => (m : ZMod 3) * ![2, 2, 0, 2] j) := by
  rw [outerProd_apply, rankOneHom_HSL, rankOneHom_HSL, rankOneHom_HSL,
    LieType.Chevalley.torusElt_eq_rootDiagUnit, LieType.Chevalley.torusElt_eq_rootDiagUnit,
    LieType.Chevalley.torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, tup]
  rw [pow_zpow_eq_tup hζ, pow_zpow_eq_tup hζ, pow_zpow_eq_tup hζ, pow_val_add hζ,
    pow_val_add hζ, ← mul_add, ← mul_add]
  congr 3
  fin_cases j <;> decide

theorem rankOneHom_middle_HSL {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (m : ℕ) :
    rankOneHom TwistTag.D4 L n2 (HSL (ζ ^ m)) =
      rootDiagUnit TwistTag.D4.tag (tup ζ fun j => (m : ZMod 3) * ![2, 2, 2, 2] j) := by
  rw [rankOneHom_HSL, LieType.Chevalley.torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  simp only [tup]
  rw [pow_zpow_eq_tup hζ]
  congr 3
  fin_cases j <;> decide

theorem rootDiagUnit_tup_eq_conj {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (ω : List (Fin TwistTag.D4.tag.rank))
    (β : Exp3) :
    rootDiagUnit TwistTag.D4.tag (tup ζ β) =
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd ω))⁻¹ *
        rootDiagUnit TwistTag.D4.tag (tup ζ (wordExp ω β)) *
          canonicalRep (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd ω) := by
  rw [← weylTuple_wordProd_tup hζ, ← canonicalRep_conj_rootDiagUnit]
  group

variable [IsAlgClosed L]

theorem exists_conj_outer_sl2Three {ζ : Lˣ} (hζ : orderOf ζ = 3) :
    ∃ k ∈ adjointGroup TwistTag.D4.tag L, outerProd L (KS11Lie4Proof.sl2Three L) =
      k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ := by
  have hζ3 := pow_three_of_orderOf hζ
  obtain ⟨P, m, hm, hP⟩ := exists_conj_sl2Three hζ
  have hconj : outerProd L (KS11Lie4Proof.sl2Three L) =
      outerProd L P * outerProd L (HSL (ζ ^ m)) * (outerProd L P)⁻¹ := by
    rw [hP, map_mul, map_mul, map_inv]
  obtain ⟨ω, hω⟩ : ∃ ω : List (Fin TwistTag.D4.tag.rank),
      wordExp ω (fun j => (m : ZMod 3) * ![2, 2, 0, 2] j) = gA := by
    rcases hm with rfl | rfl
    · exact ⟨[1, 2, 3, 2, 1], by decide⟩
    · exact ⟨[3, 1, 2, 0], by decide⟩
  refine ⟨outerProd L P * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd ω))⁻¹, mul_mem (outerProd_mem_adjointGroup P)
    (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_⟩
  rw [hconj, outerProd_HSL hζ3, rootDiagUnit_tup_eq_conj hζ3 ω, hω]
  group

theorem exists_conj_middle_sl2Three {ζ : Lˣ} (hζ : orderOf ζ = 3) :
    ∃ k ∈ adjointGroup TwistTag.D4.tag L,
      rankOneHom TwistTag.D4 L n2 (KS11Lie4Proof.sl2Three L) =
        k * rootDiagUnit TwistTag.D4.tag (tup ζ gB) * k⁻¹ := by
  have hζ3 := pow_three_of_orderOf hζ
  obtain ⟨P, m, hm, hP⟩ := exists_conj_sl2Three hζ
  have hconj : rankOneHom TwistTag.D4 L n2 (KS11Lie4Proof.sl2Three L) =
      rankOneHom TwistTag.D4 L n2 P * rankOneHom TwistTag.D4 L n2 (HSL (ζ ^ m)) *
        (rankOneHom TwistTag.D4 L n2 P)⁻¹ := by
    rw [hP, map_mul, map_mul, map_inv]
  obtain ⟨ω, hω⟩ : ∃ ω : List (Fin TwistTag.D4.tag.rank),
      wordExp ω (fun j => (m : ZMod 3) * ![2, 2, 2, 2] j) = gB := by
    rcases hm with rfl | rfl
    · exact ⟨[2, 3, 1, 0], by decide⟩
    · exact ⟨[2, 3, 1, 0, 2], by decide⟩
  refine ⟨rankOneHom TwistTag.D4 L n2 P * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd ω))⁻¹, mul_mem
    (rankOneHom_mem_adjointGroup_D4 _ P) (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_⟩
  rw [hconj, rankOneHom_middle_HSL hζ3, rootDiagUnit_tup_eq_conj hζ3 ω, hω]
  group

theorem exists_conj_d4S0 {K : Type} [Field K] (f : K →+* L) (σ : K ≃+* K) {ζ : Lˣ}
    (hζ : orderOf ζ = 3) : ∃ k ∈ adjointGroup TwistTag.D4.tag L,
      baseChangeGL f (d4S0 σ) = k * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * k⁻¹ := by
  have h : baseChangeGL f (d4S0 σ) = outerProd L (KS11Lie4Proof.sl2Three L) := by
    rw [d4S0_eq, map_mul, map_mul, baseChangeGL_rankOneHom, baseChangeGL_rankOneHom,
      baseChangeGL_rankOneHom, map_sl2Three, outerProd_apply]
  rw [h]
  exact exists_conj_outer_sl2Three hζ

theorem exists_conj_d4T0 {K : Type} [Field K] (f : K →+* L) (σ : K ≃+* K) {ζ : Lˣ}
    (hζ : orderOf ζ = 3) : ∃ k ∈ adjointGroup TwistTag.D4.tag L,
      baseChangeGL f (d4T0 σ) = k * rootDiagUnit TwistTag.D4.tag (tup ζ gB) * k⁻¹ := by
  obtain ⟨k, hk, hkeq⟩ := exists_conj_middle_sl2Three (L := L) hζ
  have hh : baseChangeGL f (d4HT σ) ∈ adjointGroup TwistTag.D4.tag L :=
    baseChangeGL_mem_adjointGroup f (d4HT_mem_adjointGroup σ)
  refine ⟨baseChangeGL f (d4HT σ) * k, mul_mem hh hk, ?_⟩
  rw [d4T0, orbitRankOneHom_middle_sl2Three, map_mul, map_mul, map_inv, baseChangeGL_rankOneHom,
    map_sl2Three, hkeq]
  group

end Conj

end CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
