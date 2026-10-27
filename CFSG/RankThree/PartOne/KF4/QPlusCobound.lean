module

public import CFSG.RankThree.PartOne.KF4.QPlusRoots
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic
public import CFSG.RankThree.PartOne.KE.A1Main
public import CFSG.RankThree.PartOne.KF4.QPlusWeyl

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open scoped Matrix


section SL2

variable {Ω : Type} [Field Ω] [CharP Ω 2]

theorem qp_two_eq_zero : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2

@[expose] def qpA (ω : Ω) : SL2 Ω :=
  ⟨!![ω, ω + 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : Ω) * (qp_two_eq_zero (Ω := Ω))⟩

@[expose] def qpW : SL2 Ω :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : Ω) * (qp_two_eq_zero (Ω := Ω))⟩

theorem qpW_eq : (qpW : SL2 Ω) = uSL 1 * vSL 1 * uSL 1 := by
  have h2 : (2 : Ω) = 0 := qp_two_eq_zero
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [qpW, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | rfl | linear_combination h2 | linear_combination (-1 : Ω) * h2

theorem qpA_inv_mul_map (f : ℕ) {ω : Ω} (hω : ω ^ 2 ^ f = ω + 1) :
    (qpA ω)⁻¹ * Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) (qpA ω) = qpW := by
  have h2 : (2 : Ω) = 0 := qp_two_eq_zero
  have hF : iterateFrobenius Ω 2 f ω = ω + 1 := by
    rw [iterateFrobenius_def]
    exact hω
  have hF1 : iterateFrobenius Ω 2 f (ω + 1) = ω := by
    rw [map_add, hF, map_one]
    linear_combination h2
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [qpA, qpW, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hF, hF1,
      RingHom.mapMatrix_apply] <;>
    first | rfl | linear_combination h2 | linear_combination (-1 : Ω) * h2

theorem qpW_mul_self : (qpW : SL2 Ω) * qpW = 1 := by
  have h2 : (2 : Ω) = 0 := qp_two_eq_zero
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [qpW, Matrix.mul_apply, Fin.sum_univ_two]

end SL2

section Cascade

variable {Ω : Type} [Field Ω] [CharP Ω 2]

omit [CharP Ω 2] in
theorem qp_rootSL2_commute {β γ : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β)
    (hγ : IsRoot Tag.F4 γ) (h0 : CFSG.LieType.Steinberg.Adjoint.iform β γ = 0)
    (hp : ¬ IsRoot Tag.F4 (β + γ)) (hm : ¬ IsRoot Tag.F4 (β - γ)) (M N : SL2 Ω) :
    Commute (rootSL2 Tag.F4 Ω β M) (rootSL2 Tag.F4 Ω γ N) :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation Tag.F4 Ω hβ hγ h0 hp hm _
    ⟨M, rfl⟩ _ ⟨N, rfl⟩

variable {J : Finset (Fin Tag.F4.rank)} {C : List (Fin Tag.F4.rank → ℤ)}

theorem QPCascade.isRoot (hC : QPCascade J C) {β : Fin Tag.F4.rank → ℤ} (hβ : β ∈ C) :
    IsRoot Tag.F4 β :=
  isRoot_iff_f4IsRootB.2 (hC.root β hβ)

theorem QPCascade.mem_parabolicRoots (hC : QPCascade J C) {β : Fin Tag.F4.rank → ℤ}
    (hβ : β ∈ C) : β ∈ parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank)) :=
  ⟨hC.isRoot hβ, fun i hi => hC.supp β hβ i (by simpa using hi)⟩

theorem QPCascade.neg_mem_parabolicRoots (hC : QPCascade J C) {β : Fin Tag.F4.rank → ℤ}
    (hβ : β ∈ C) : -β ∈ parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank)) :=
  ⟨IsRoot.neg (hC.isRoot hβ), fun i hi => by
    have := hC.supp β hβ i (by simpa using hi)
    simp [this]⟩

omit [CharP Ω 2] in
theorem QPCascade.pairwise_commute (hC : QPCascade J C) (M N : SL2 Ω) :
    C.Pairwise fun β γ => Commute (rootSL2 Tag.F4 Ω β M) (rootSL2 Tag.F4 Ω γ N) := by
  refine List.Pairwise.imp_of_mem (fun {β γ} hβ hγ h => ?_) hC.orth
  exact qp_rootSL2_commute (hC.isRoot hβ) (hC.isRoot hγ) h.1
    (fun hr => by simpa [h.2.1] using isRoot_iff_f4IsRootB.1 hr)
    (fun hr => by simpa [h.2.2] using isRoot_iff_f4IsRootB.1 hr) M N

@[expose] def qpCas (C : List (Fin Tag.F4.rank → ℤ)) (M : SL2 Ω) : ModGL Tag.F4 Ω :=
  (C.map fun β => rootSL2 Tag.F4 Ω β M).prod

theorem list_prod_map_mul_of_pairwise {G : Type*} [Group G] {α : Type*} (l : List α)
    (f g : α → G) (h : l.Pairwise fun a b => Commute (g a) (f b)) :
    (l.map fun a => f a * g a).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨ha, hl⟩ := h
    rw [List.map_cons, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.prod_cons, ih hl]
    have hc : Commute (g a) (l.map f).prod :=
      Commute.list_prod_right _ _ (fun b hb => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
        exact ha x hx)
    calc f a * g a * ((l.map f).prod * (l.map g).prod)
        = f a * (g a * (l.map f).prod) * (l.map g).prod := by group
      _ = f a * ((l.map f).prod * g a) * (l.map g).prod := by rw [hc.eq]
      _ = f a * (l.map f).prod * (g a * (l.map g).prod) := by group

omit [CharP Ω 2] in
theorem qpCas_mem_rootSpan (hC : QPCascade J C) (M : SL2 Ω) :
    qpCas C M ∈ rootSpan Tag.F4 Ω (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank))) :=
  list_prod_mem fun x hx => by
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
    have h : rootSL2 Tag.F4 Ω β M ∈ (rootSL2 Tag.F4 Ω β).range := ⟨M, rfl⟩
    rw [range_rootSL2_of_isRoot (hC.isRoot hβ)] at h
    exact sup_le (rootSubgroup_le_rootSpan (hC.mem_parabolicRoots hβ))
      (rootSubgroup_le_rootSpan (hC.neg_mem_parabolicRoots hβ)) h

theorem qp_entrywise_rootSL2 (f : ℕ) {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β)
    (M : SL2 Ω) :
    Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) (rootSL2 Tag.F4 Ω β M) =
      rootSL2 Tag.F4 Ω β (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) M) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL_self, baseChangeGL_rootSL2_of_charTwo _ hβ]

theorem qp_entrywise_qpCas (f : ℕ) (hC : QPCascade J C) (M : SL2 Ω) :
    Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) (qpCas C M) =
      qpCas C (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) M) := by
  unfold qpCas
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun β hβ => qp_entrywise_rootSL2 f (hC.isRoot hβ) M

theorem canonicalRep_rootReflection_eq {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) :
    canonicalRep (coxeterSystem Tag.F4) Ω (rootReflection β) =
      rootSL2 Tag.F4 Ω β (qpW : SL2 Ω) := by
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 hβ
  have hm := CFSG.RankThree.PartOne.KE.qplus_canonicalRep_mul (τ := Tag.F4) (K := Ω)
  have hinv : canonicalRep (coxeterSystem Tag.F4) Ω w⁻¹ =
      (canonicalRep (coxeterSystem Tag.F4) Ω w)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hm, mul_inv_cancel, canonicalRep_one]
  have h2 : (2 : Ω) = 0 := qp_two_eq_zero
  have hj : IsRoot Tag.F4 (Pi.single j 1) := isRoot_single Tag.F4 j
  have hX : ∀ c : Ω, canonicalRep (coxeterSystem Tag.F4) Ω w * pinnedX Tag.F4 Ω (Pi.single j 1) c *
      (canonicalRep (coxeterSystem Tag.F4) Ω w)⁻¹ = pinnedX Tag.F4 Ω β c := fun c => by
    rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hj c, hwj]
  have hY : ∀ c : Ω, canonicalRep (coxeterSystem Tag.F4) Ω w *
      pinnedX Tag.F4 Ω (-(Pi.single j 1)) c * (canonicalRep (coxeterSystem Tag.F4) Ω w)⁻¹ =
        pinnedX Tag.F4 Ω (-β) c := fun c => by
    rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (IsRoot.neg hj) c, smul_neg, hwj]
  have hneg : (-1 : Ω) = 1 := CharTwo.neg_eq 1
  rw [rootReflection_eq_conj hwj, hm, hm, hinv, canonicalRep_simple,
    CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul, qpW_eq, map_mul, map_mul,
    rootSL2_uSL_of_charTwo hβ, rootSL2_vSL_of_charTwo hβ, ← hX 1, ← hY 1]
  simp only [inv_one, Units.val_one, hneg, ← pinnedX_single, ← pinnedX_neg_single]
  group

@[expose] def qpCanonicalHom (Ω : Type) [Field Ω] [CharP Ω 2] :
    WeylGroup Tag.F4 →* ModGL Tag.F4 Ω where
  toFun := canonicalRep (coxeterSystem Tag.F4) Ω
  map_one' := canonicalRep_one _ _
  map_mul' := CFSG.RankThree.PartOne.KE.qplus_canonicalRep_mul

theorem prod_rootReflection_smul {l : List (Fin Tag.F4.rank → ℤ)}
    (hl : ∀ x ∈ l, IsRoot Tag.F4 x) (v : Fin Tag.F4.rank → ℤ) :
    (l.map rootReflection).prod • v = qpReflect l v := by
  induction l with
  | nil => simp [qpReflect]
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih fun y hy => hl y (List.mem_cons_of_mem _ hy),
      rootReflection_smul (hl x List.mem_cons_self)]
    rfl

theorem smul_eq_neg_of_support {w : WeylGroup Tag.F4} {J : Finset (Fin Tag.F4.rank)}
    (hw : ∀ j ∈ J, w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = -Pi.single j 1)
    {α : Fin Tag.F4.rank → ℤ} (hα : ∀ i, i ∉ J → α i = 0) : w • α = -α := by
  rw [← weylMatrix_mulVec]
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply]
  have key : ∀ j, weylMatrix w i j * α j = (if i = j then -1 else 0) * α j := by
    intro j
    by_cases hj : j ∈ J
    · rw [weylMatrix_apply, hw j hj]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    · rw [hα j hj]
      simp
  rw [Finset.sum_congr rfl fun j _ => key j]
  simp [ite_mul]

theorem QPCascade.prod_smul (hC : QPCascade J C) {α : Fin Tag.F4.rank → ℤ}
    (hα : ∀ i, i ∉ J → α i = 0) : (C.map rootReflection).prod • α = -α :=
  smul_eq_neg_of_support (fun j hj => by
    rw [prod_rootReflection_smul fun x hx => hC.isRoot hx]
    exact hC.neg j hj) hα

theorem qp_prod_reflections_mul_neg (hC : QPCascade J C) {α : Fin Tag.F4.rank → ℤ}
    (hα : ∀ i, i ∉ J → α i = 0) : (qpNeg * (C.map rootReflection).prod) • α = α := by
  rw [mul_smul, hC.prod_smul hα, qpNeg_smul, neg_neg]

theorem qp_centralizes (hC : QPCascade J C) :
    rootSpan Tag.F4 Ω (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank))) ≤
      Subgroup.centralizer (({(qpRep Ω * canonicalRep (coxeterSystem Tag.F4) Ω
        (C.map rootReflection).prod)} : Set (ModGL Tag.F4 Ω))) := by
  have h2 : (2 : Ω) = 0 := qp_two_eq_zero
  have hm : qpRep Ω * canonicalRep (coxeterSystem Tag.F4) Ω (C.map rootReflection).prod =
      canonicalRep (coxeterSystem Tag.F4) Ω (qpNeg * (C.map rootReflection).prod) := by
    rw [qpRep, CFSG.RankThree.PartOne.KE.qplus_canonicalRep_mul]
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hm]
  have := canonicalRep_mul_pinnedX_mul_inv_of_two h2 (qpNeg * (C.map rootReflection).prod) hα.1 c
  rw [qp_prod_reflections_mul_neg hC hα.2] at this
  exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem qp_Phi_cas_inv (f : ℕ) (hC : QPCascade J C) {ω : Ω} (hω : ω ^ 2 ^ f = ω + 1) :
    Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) (qpCas C (qpA ω)⁻¹) =
      canonicalRep (coxeterSystem Tag.F4) Ω (C.map rootReflection).prod *
        qpCas C (qpA ω)⁻¹ := by
  have hM : Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) (qpA ω)⁻¹ =
      qpW * (qpA ω)⁻¹ := by
    have h := qpA_inv_mul_map f hω
    have h2 : Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) (qpA ω) = qpA ω * qpW := by
      rw [← h]
      group
    rw [map_inv, h2, mul_inv_rev, inv_eq_of_mul_eq_one_right (qpW_mul_self (Ω := Ω))]
  have hcan : canonicalRep (coxeterSystem Tag.F4) Ω (C.map rootReflection).prod =
      (C.map fun β => rootSL2 Tag.F4 Ω β qpW).prod := by
    have hh := map_list_prod (qpCanonicalHom Ω) (C.map rootReflection)
    change qpCanonicalHom Ω _ = _
    rw [hh, List.map_map]
    congr 1
    exact List.map_congr_left fun β hβ => canonicalRep_rootReflection_eq (hC.isRoot hβ)
  rw [qp_entrywise_qpCas f hC, hM, hcan]
  unfold qpCas
  have hmul : ∀ β, rootSL2 Tag.F4 Ω β (qpW * (qpA ω)⁻¹) =
      rootSL2 Tag.F4 Ω β qpW * rootSL2 Tag.F4 Ω β (qpA ω)⁻¹ := fun β => map_mul _ _ _
  simp only [hmul]
  exact list_prod_map_mul_of_pairwise _ (fun β => rootSL2 Tag.F4 Ω β qpW)
    (fun β => rootSL2 Tag.F4 Ω β (qpA ω)⁻¹) (hC.pairwise_commute _ _)

theorem qp_frobenius_bijective [IsAlgClosed Ω] (f : ℕ) :
    Function.Bijective (iterateFrobenius Ω 2 f) :=
  ⟨RingHom.injective _, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < 2 ^ f from pow_pos two_pos f)
    exact ⟨x, by rw [iterateFrobenius_def]; exact hx⟩⟩

@[expose] def qpFrobEquiv [IsAlgClosed Ω] (f : ℕ) : Ω ≃+* Ω :=
  RingEquiv.ofBijective (iterateFrobenius Ω 2 f) (qp_frobenius_bijective f)

theorem qpFrobEquiv_toRingHom [IsAlgClosed Ω] (f : ℕ) :
    (qpFrobEquiv (Ω := Ω) f).toRingHom = iterateFrobenius Ω 2 f :=
  RingHom.ext fun _ => rfl

omit
  [CharP Ω 2] in
theorem exists_qpOmega [IsAlgClosed Ω] {f : ℕ} (hf : 1 ≤ f) : ∃ ω : Ω, ω ^ 2 ^ f = ω + 1 := by
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set P : Polynomial Ω := Polynomial.X ^ 2 ^ f - (Polynomial.X + 1) with hP
  have hlt : (Polynomial.X + 1 : Polynomial Ω).degree <
      (Polynomial.X ^ 2 ^ f : Polynomial Ω).degree := by
    rw [Polynomial.degree_X_pow, show (Polynomial.X + 1 : Polynomial Ω) =
      Polynomial.X + Polynomial.C 1 by simp, Polynomial.degree_X_add_C]
    exact_mod_cast h2
  have hdeg : P.degree = ((2 ^ f : ℕ) : WithBot ℕ) := by
    rw [hP, Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root P (by
    rw [hdeg]
    exact_mod_cast (by omega : 2 ^ f ≠ 0))
  refine ⟨ω, ?_⟩
  simp only [hP, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_one] at hω
  linear_combination hω

theorem qp_theta_iff (f : ℕ) (hC : QPCascade J C) {ω : Ω} (hω : ω ^ 2 ^ f = ω + 1)
    {u : ModGL Tag.F4 Ω}
    (hu : u ∈ rootSpan Tag.F4 Ω (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank)))) :
    qpRep Ω * Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) u * (qpRep Ω)⁻¹ = u ↔
      Units.map (entrywiseHom (iterateFrobenius Ω 2 f))
          ((qpCas C (qpA ω)⁻¹)⁻¹ * u * qpCas C (qpA ω)⁻¹) =
        (qpCas C (qpA ω)⁻¹)⁻¹ * u * qpCas C (qpA ω)⁻¹ := by
  set g : ModGL Tag.F4 Ω := qpCas C (qpA ω)⁻¹ with hg
  set N : ModGL Tag.F4 Ω := canonicalRep (coxeterSystem Tag.F4) Ω (C.map rootReflection).prod
    with hN
  set Φ : ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω :=
    Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) with hΦ
  have hΦg : Φ g = N * g := qp_Phi_cas_inv f hC hω
  have hm : (qpRep Ω * N) * u = u * (qpRep Ω * N) :=
    (Subgroup.mem_centralizer_singleton_iff.1 (qp_centralizes hC hu)).symm
  have hΦ' : Φ (g⁻¹ * u * g) = g⁻¹ * (N⁻¹ * Φ u * N) * g := by
    rw [map_mul, map_mul, map_inv, hΦg]
    group
  have hconj : (qpRep Ω * N)⁻¹ * u * (qpRep Ω * N) = u := by
    rw [mul_assoc, ← hm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hconj' : (qpRep Ω * N) * u * (qpRep Ω * N)⁻¹ = u := by
    rw [hm, mul_assoc, mul_inv_cancel, mul_one]
  rw [hΦ']
  constructor
  · intro h
    have h1 : Φ u = (qpRep Ω)⁻¹ * u * qpRep Ω := by
      calc Φ u = (qpRep Ω)⁻¹ * (qpRep Ω * Φ u * (qpRep Ω)⁻¹) * qpRep Ω := by group
        _ = _ := by rw [h]
    have h2 : N⁻¹ * Φ u * N = u := by
      rw [h1]
      calc N⁻¹ * ((qpRep Ω)⁻¹ * u * qpRep Ω) * N = (qpRep Ω * N)⁻¹ * u * (qpRep Ω * N) := by
            group
        _ = u := hconj
    rw [h2]
  · intro h
    have h2 : N⁻¹ * Φ u * N = u := by
      exact mul_left_cancel (mul_right_cancel h)
    have h1 : Φ u = N * u * N⁻¹ := by
      calc Φ u = N * (N⁻¹ * Φ u * N) * N⁻¹ := by group
        _ = _ := by rw [h2]
    rw [h1]
    calc qpRep Ω * (N * u * N⁻¹) * (qpRep Ω)⁻¹ = (qpRep Ω * N) * u * (qpRep Ω * N)⁻¹ := by group
      _ = u := hconj'

theorem qp_inf_fixed_eq [IsAlgClosed Ω] (f : ℕ) (hC : QPCascade J C) {ω : Ω}
    (hω : ω ^ 2 ^ f = ω + 1) :
    subsystemGroup Tag.F4 Ω (J : Set (Fin Tag.F4.rank)) ⊓
        twistedFixedPoints (qpRep Ω) (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))) =
      ((subsystemGroup Tag.F4 (fixSubfield (qpFrobEquiv (Ω := Ω) f))
        (J : Set (Fin Tag.F4.rank))).map
          (baseChangeGL (fixSubfield (qpFrobEquiv (Ω := Ω) f)).subtype)).map
        (MulAut.conj (qpCas C (qpA ω)⁻¹)).toMonoidHom := by
  set g : ModGL Tag.F4 Ω := qpCas C (qpA ω)⁻¹ with hg
  set σ : Ω ≃+* Ω := qpFrobEquiv (Ω := Ω) f with hσ
  have hfix := subsystemGroup_inf_entrywiseFixed_F4 σ (J : Set (Fin Tag.F4.rank))
  have hroot : ∀ u, u ∈ subsystemGroup Tag.F4 Ω (J : Set (Fin Tag.F4.rank)) ↔
      u ∈ rootSpan Tag.F4 Ω (parabolicRoots Tag.F4 (J : Set (Fin Tag.F4.rank))) := fun u => by
    rw [subsystemGroup_eq_rootSpan]
  have hgQ : g ∈ subsystemGroup Tag.F4 Ω (J : Set (Fin Tag.F4.rank)) :=
    (hroot g).2 (qpCas_mem_rootSpan hC _)
  have hσ' : σ.toRingHom = iterateFrobenius Ω 2 f := qpFrobEquiv_toRingHom f
  ext u
  constructor
  · intro hu
    obtain ⟨huQ, huR⟩ := Subgroup.mem_inf.1 hu
    have h := (qp_theta_iff f hC hω ((hroot u).1 huQ)).1 (mem_twistedFixedPoints.1 huR)
    have hy : g⁻¹ * u * g ∈ subsystemGroup Tag.F4 Ω (J : Set (Fin Tag.F4.rank)) ⊓
        (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) :=
      Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hgQ) huQ) hgQ, by rw [hσ']; exact h⟩
    rw [hfix] at hy
    refine ⟨g⁻¹ * u * g, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ subsystemGroup Tag.F4 Ω (J : Set (Fin Tag.F4.rank)) ⊓
        (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) := by
      rw [hfix]; exact hz
    obtain ⟨hzQ, hzF⟩ := Subgroup.mem_inf.1 hz'
    have huQ : (MulAut.conj g).toMonoidHom z ∈ subsystemGroup Tag.F4 Ω
        (J : Set (Fin Tag.F4.rank)) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hgQ hzQ) (inv_mem hgQ)
    refine Subgroup.mem_inf.2 ⟨huQ, mem_twistedFixedPoints.2 ?_⟩
    refine (qp_theta_iff f hC hω ((hroot _).1 huQ)).2 ?_
    have : g⁻¹ * (MulAut.conj g).toMonoidHom z * g = z := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    have hzF' : Units.map (entrywiseHom σ.toRingHom) z = z := hzF
    rw [hσ'] at hzF'
    exact hzF'

end Cascade

end CFSG.RankThree.PartOne.KF4
