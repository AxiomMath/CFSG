module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenExceptional
public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusWeyl
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

section A

variable {Ω : Type} [Field Ω] [CharP Ω 2]

theorem eqp_two_eq_zero : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2

def eqpA (ω : Ω) : SL2 Ω :=
  ⟨!![ω, ω + 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : Ω) * (eqp_two_eq_zero (Ω := Ω))⟩

def eqpW : SL2 Ω :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : Ω) * (eqp_two_eq_zero (Ω := Ω))⟩

theorem eqpW_eq : (eqpW : SL2 Ω) = uSL 1 * vSL 1 * uSL 1 := by
  have h2 : (2 : Ω) = 0 := eqp_two_eq_zero
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [eqpW, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | rfl | linear_combination h2 | linear_combination (-1 : Ω) * h2

theorem eqpA_inv_mul_map (f : ℕ) {ω : Ω} (hω : ω ^ 2 ^ f = ω + 1) :
    (eqpA ω)⁻¹ * Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) (eqpA ω) = eqpW := by
  have h2 : (2 : Ω) = 0 := eqp_two_eq_zero
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
    simp [eqpA, eqpW, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hF, hF1,
      RingHom.mapMatrix_apply] <;>
    first | rfl | linear_combination h2 | linear_combination (-1 : Ω) * h2
end A

section Psi

variable {Ω : Type} [Field Ω] [CharP Ω 2]

theorem e6Delta_neg (J : Set (Fin Tag.E6.rank)) (x : Fin Tag.E6.rank → ℤ) :
    e6Delta J (-x) = -e6Delta J x := by
  simp [e6Delta, permLattice, Pi.neg_comp]

theorem isRoot_e6Delta (J : Set (Fin Tag.E6.rank)) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) : IsRoot Tag.E6 (e6Delta J β) :=
  IsRoot.neg (IsRoot.smul (IsRoot.permLattice TwistTag.E6.cartan_perm hβ) _)

theorem e6Psi_rootSL2 (J : Set (Fin Tag.E6.rank)) (f : ℕ) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (M : SL2 Ω) :
    e6Psi Ω J f (rootSL2 Tag.E6 Ω β M) =
      rootSL2 Tag.E6 Ω (e6Delta J β) (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) M) := by
  have hδ := isRoot_e6Delta J hβ
  have h : (e6Psi Ω J f).comp (rootSL2 Tag.E6 Ω β) =
      (rootSL2 Tag.E6 Ω (e6Delta J β)).comp (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f)) := by
    refine MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := Ω)) fun g hg => ?_
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · simp only [MonoidHom.comp_apply]
      change e6Psi Ω J f (rootSL2 Tag.E6 Ω β (uSL c)) = rootSL2 Tag.E6 Ω (e6Delta J β)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) (uSL c))
      rw [rootSL2_uSL_of_charTwo hβ, e6Psi_pinnedX J f hβ, map_uSL, rootSL2_uSL_of_charTwo hδ,
        iterateFrobenius_def]
    · simp only [MonoidHom.comp_apply]
      change e6Psi Ω J f (rootSL2 Tag.E6 Ω β (vSL c)) = rootSL2 Tag.E6 Ω (e6Delta J β)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) (vSL c))
      rw [rootSL2_vSL_of_charTwo hβ, e6Psi_pinnedX J f (IsRoot.neg hβ), e6Delta_neg, map_vSL,
        rootSL2_vSL_of_charTwo hδ, iterateFrobenius_def]
  exact DFunLike.congr_fun h M

end Psi

section Weyl

variable {Ω : Type} [Field Ω] [CharP Ω 2]

theorem canonicalRep_rootReflection_eq {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) :
    canonicalRep (coxeterSystem Tag.E6) Ω (rootReflection β) =
      rootSL2 Tag.E6 Ω β (eqpW : SL2 Ω) := by
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 hβ
  have hm := CFSG.RankThree.PartOne.KE.qplus_canonicalRep_mul (τ := Tag.E6) (K := Ω)
  have hinv : canonicalRep (coxeterSystem Tag.E6) Ω w⁻¹ =
      (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hm, mul_inv_cancel, canonicalRep_one]
  have hj : IsRoot Tag.E6 (Pi.single j 1) := isRoot_single Tag.E6 j
  have hX : ∀ c : Ω, canonicalRep (coxeterSystem Tag.E6) Ω w * pinnedX Tag.E6 Ω (Pi.single j 1) c *
      (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ = pinnedX Tag.E6 Ω β c := fun c => by
    rw [E6EvenFixedRootDatum.canonicalRep_conj_pinnedX w hj c, hwj]
  have hY : ∀ c : Ω, canonicalRep (coxeterSystem Tag.E6) Ω w *
      pinnedX Tag.E6 Ω (-(Pi.single j 1)) c * (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ =
        pinnedX Tag.E6 Ω (-β) c := fun c => by
    rw [E6EvenFixedRootDatum.canonicalRep_conj_pinnedX w (IsRoot.neg hj) c, smul_neg, hwj]
  have hneg : (-1 : Ω) = 1 := CharTwo.neg_eq 1
  rw [rootReflection_eq_conj hwj, hm, hm, hinv, canonicalRep_simple,
    CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul, eqpW_eq, map_mul, map_mul, rootSL2_uSL_of_charTwo hβ, rootSL2_vSL_of_charTwo hβ, ← hX 1,
    ← hY 1]
  simp only [inv_one, Units.val_one, hneg, ← pinnedX_single, ← pinnedX_neg_single]
  group

end Weyl

section Cascade

variable {Ω : Type} [Field Ω]

theorem e6_not_isRoot_add_of_orth {β γ : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (hγ : IsRoot Tag.E6 γ) (h0 : CFSG.LieType.Steinberg.Adjoint.iform β γ = 0) :
    ¬ IsRoot Tag.E6 (β + γ) := fun h => by
  have hs : ∀ i, Tag.E6.symmetrizer i i = 1 := by decide
  have h2 := CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two (τ := Tag.E6) hs h
  have hb := CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two (τ := Tag.E6) hs hβ
  have hc := CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two (τ := Tag.E6) hs hγ
  simp only [CFSG.LieType.Steinberg.Adjoint.iform_add_left,
    CFSG.LieType.Steinberg.Adjoint.iform_add_right] at h2
  rw [CFSG.LieType.Steinberg.Adjoint.iform_comm γ β] at h2
  omega

theorem e6_not_isRoot_sub_of_orth {β γ : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (hγ : IsRoot Tag.E6 γ) (h0 : CFSG.LieType.Steinberg.Adjoint.iform β γ = 0) :
    ¬ IsRoot Tag.E6 (β - γ) := fun h => by
  have hs : ∀ i, Tag.E6.symmetrizer i i = 1 := by decide
  have h2 := CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two (τ := Tag.E6) hs h
  have hb := CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two (τ := Tag.E6) hs hβ
  have hc := CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two (τ := Tag.E6) hs hγ
  simp only [CFSG.LieType.Steinberg.Adjoint.iform_sub_left,
    CFSG.LieType.Steinberg.Adjoint.iform_sub_right] at h2
  rw [CFSG.LieType.Steinberg.Adjoint.iform_comm γ β] at h2
  omega

theorem e6QpC_isRoot (m : Fin 15) {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ e6QpC m) :
    IsRoot Tag.E6 β := by
  rw [isRoot_iff_mem_artifactRoots]
  exact ((e6QpC_check m).2.1 β hβ).1

theorem e6QpC_delta_mem (m : Fin 15) {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ e6QpC m) :
    e6Delta (e6QpSupport m) β ∈ e6QpC m := by
  rw [e6Delta_qp]
  exact ((e6QpC_check m).2.1 β hβ).2.2.2

theorem e6QpC_map_delta_perm (m : Fin 15) :
    ((e6QpC m).map (e6Delta (e6QpSupport m))).Perm (e6QpC m) := by
  classical
  have hinj : Function.Injective (e6Delta (e6QpSupport m)) :=
    Function.Involutive.injective (e6Delta_qp_involutive m)
  refine List.perm_of_nodup_nodup_toFinset_eq ((e6QpC_check m).1.map hinj) (e6QpC_check m).1 ?_
  ext x
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact e6QpC_delta_mem m hy
  · intro hx
    exact ⟨e6Delta (e6QpSupport m) x, e6QpC_delta_mem m hx, e6Delta_qp_involutive m x⟩

theorem e6QpC_pairwise_commute (m : Fin 15) (M N : SL2 Ω) :
    (e6QpC m).Pairwise fun β γ => Commute (rootSL2 Tag.E6 Ω β M) (rootSL2 Tag.E6 Ω γ N) := by
  refine List.Pairwise.imp_of_mem (fun {β γ} hβ hγ hne => ?_) (e6QpC_check m).1
  have h0 := (e6QpC_check m).2.2.1 β hβ γ hγ hne
  exact rootSL2_commute_of_orth (e6QpC_isRoot m hβ) (e6QpC_isRoot m hγ) h0
    (e6_not_isRoot_add_of_orth (e6QpC_isRoot m hβ) (e6QpC_isRoot m hγ) h0)
    (e6_not_isRoot_sub_of_orth (e6QpC_isRoot m hβ) (e6QpC_isRoot m hγ) h0) M N

@[expose] def eqpCas (m : Fin 15) (M : SL2 Ω) : ModGL Tag.E6 Ω :=
  ((e6QpC m).map fun β => rootSL2 Tag.E6 Ω β M).prod


theorem list_prod_map_mul_of_pairwise {G : Type*} [Group G] {α : Type*} (l : List α) (f g : α → G)
    (h : l.Pairwise fun a b => Commute (g a) (f b)) :
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

theorem e6Psi_eqpCas [CharP Ω 2] (m : Fin 15) (f : ℕ) (M : SL2 Ω) :
    e6Psi Ω (e6QpSupport m) f (eqpCas m M) =
      eqpCas m (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) M) := by
  set M' := Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) M with hM'
  unfold eqpCas
  rw [map_list_prod, List.map_map]
  have h1 : (e6QpC m).map ((e6Psi Ω (e6QpSupport m) f) ∘ fun β => rootSL2 Tag.E6 Ω β M) =
      (e6QpC m).map ((fun β => rootSL2 Tag.E6 Ω β M') ∘ e6Delta (e6QpSupport m)) :=
    List.map_congr_left fun β hβ => e6Psi_rootSL2 _ f (e6QpC_isRoot m hβ) M
  rw [h1, ← List.map_map]
  have hpair : (e6QpC m).Pairwise fun β γ =>
      Commute (rootSL2 Tag.E6 Ω β M') (rootSL2 Tag.E6 Ω γ M') := e6QpC_pairwise_commute m M' M'
  have hperm := (e6QpC_map_delta_perm m).map (fun β => rootSL2 Tag.E6 Ω β M')
  have hpair' : ((e6QpC m).map fun β => rootSL2 Tag.E6 Ω β M').Pairwise Commute := by
    rw [List.pairwise_map]
    exact hpair
  exact (List.Perm.prod_eq' hperm
    ((List.Perm.pairwise_iff (fun {a b : ModGL Tag.E6 Ω} (h : Commute a b) => h.symm) hperm).2
      hpair'))

theorem eqpW_mul_self [CharP Ω 2] : (eqpW : SL2 Ω) * eqpW = 1 := by
  have h2 : (2 : Ω) = 0 := eqp_two_eq_zero
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [eqpW, Matrix.mul_apply, Fin.sum_univ_two]

end Cascade

section Longest

variable {Ω : Type} [Field Ω] [CharP Ω 2]

theorem prod_rootReflection_smul {l : List (Fin Tag.E6.rank → ℤ)}
    (hl : ∀ x ∈ l, IsRoot Tag.E6 x) (v : Fin Tag.E6.rank → ℤ) :
    (l.map rootReflection).prod • v = l.foldr (fun β v => v - corootPair β v • β) v := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih fun y hy => hl y (List.mem_cons_of_mem _ hy),
      rootReflection_smul (hl x List.mem_cons_self)]
    rfl

theorem e6Longest_eq_prod_reflections (m : Fin 15) :
    e6Longest (e6QpSupport m) = ((e6QpC m).map rootReflection).prod := by
  refine ext_single fun i => ?_
  rw [e6Longest_qp, wordProd_smul, prod_rootReflection_smul (fun β hβ => e6QpC_isRoot m hβ),
    (e6QpC_check m).2.2.2 i]

@[expose] def eqpCanonicalHom (Ω : Type) [Field Ω] [CharP Ω 2] :
    WeylGroup Tag.E6 →* ModGL Tag.E6 Ω where
  toFun := canonicalRep (coxeterSystem Tag.E6) Ω
  map_one' := canonicalRep_one _ _
  map_mul' := CFSG.RankThree.PartOne.KE.qplus_canonicalRep_mul

theorem canonicalRep_longest_eq_eqpCas (m : Fin 15) :
    canonicalRep (coxeterSystem Tag.E6) Ω (e6Longest (e6QpSupport m)) =
      eqpCas m (eqpW : SL2 Ω) := by
  have h := map_list_prod (eqpCanonicalHom Ω) ((e6QpC m).map rootReflection)
  rw [e6Longest_eq_prod_reflections]
  change eqpCanonicalHom Ω _ = _
  rw [h, List.map_map]
  unfold eqpCas
  congr 1
  exact List.map_congr_left fun β hβ => canonicalRep_rootReflection_eq (e6QpC_isRoot m hβ)

theorem e6Psi_eqpCas_inv (m : Fin 15) (f : ℕ) {ω : Ω} (hω : ω ^ 2 ^ f = ω + 1) :
    e6Psi Ω (e6QpSupport m) f (eqpCas m (eqpA ω)⁻¹) =
      canonicalRep (coxeterSystem Tag.E6) Ω (e6Longest (e6QpSupport m)) *
        eqpCas m (eqpA ω)⁻¹ := by
  have hM : Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) (eqpA ω)⁻¹ =
      eqpW * (eqpA ω)⁻¹ := by
    have h := eqpA_inv_mul_map f hω
    have h2 : Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) (eqpA ω) = eqpA ω * eqpW := by
      rw [← h]
      group
    rw [map_inv, h2, mul_inv_rev, inv_eq_of_mul_eq_one_right (eqpW_mul_self (Ω := Ω))]
  rw [e6Psi_eqpCas, hM, canonicalRep_longest_eq_eqpCas]
  unfold eqpCas
  have hmul : ∀ β, rootSL2 Tag.E6 Ω β (eqpW * (eqpA ω)⁻¹) =
      rootSL2 Tag.E6 Ω β eqpW * rootSL2 Tag.E6 Ω β (eqpA ω)⁻¹ := fun β => map_mul _ _ _
  simp only [hmul]
  exact list_prod_map_mul_of_pairwise _ (fun β => rootSL2 Tag.E6 Ω β eqpW)
    (fun β => rootSL2 Tag.E6 Ω β (eqpA ω)⁻¹) (e6QpC_pairwise_commute m _ _)

theorem eqp_theta_eq (m : Fin 15) (f : ℕ) {ω : Ω} (hω : ω ^ 2 ^ f = ω + 1)
    (x : ModGL Tag.E6 Ω) :
    canonicalRep (coxeterSystem Tag.E6) Ω e6W0 *
        Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) x *
          (canonicalRep (coxeterSystem Tag.E6) Ω e6W0)⁻¹ =
      eqpCas m (eqpA ω)⁻¹ * e6Psi Ω (e6QpSupport m) f ((eqpCas m (eqpA ω)⁻¹)⁻¹ * x *
        eqpCas m (eqpA ω)⁻¹) * (eqpCas m (eqpA ω)⁻¹)⁻¹ := by
  set g := eqpCas m (eqpA ω)⁻¹ with hg
  have hΨ := e6Psi_eqpCas_inv m f hω
  rw [← hg] at hΨ
  rw [map_mul, map_mul, map_inv, hΨ]
  have hx : e6Psi Ω (e6QpSupport m) f x =
      canonicalRep (coxeterSystem Tag.E6) Ω (e6Longest (e6QpSupport m)) *
        canonicalRep (coxeterSystem Tag.E6) Ω e6W0 *
          Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) x *
            (canonicalRep (coxeterSystem Tag.E6) Ω (e6Longest (e6QpSupport m)) *
              canonicalRep (coxeterSystem Tag.E6) Ω e6W0)⁻¹ := rfl
  rw [hx]
  group

end Longest

section Mem

variable {Ω : Type} [Field Ω]

theorem rootSL2_mem_rootSpan {S : Set (Fin Tag.E6.rank → ℤ)} {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (h1 : β ∈ S) (h2 : -β ∈ S) (M : SL2 Ω) :
    rootSL2 Tag.E6 Ω β M ∈ rootSpan Tag.E6 Ω S := by
  have h : rootSL2 Tag.E6 Ω β M ∈ (rootSL2 Tag.E6 Ω β).range := ⟨M, rfl⟩
  rw [range_rootSL2_of_isRoot hβ] at h
  exact sup_le (rootSubgroup_le_rootSpan h1) (rootSubgroup_le_rootSpan h2) h

theorem e6QpC_mem_parabolicRoots (m : Fin 15) {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ e6QpC m) : β ∈ parabolicRoots Tag.E6 (e6QpSupport m) :=
  ⟨e6QpC_isRoot m hβ, fun i hi => ((e6QpC_check m).2.1 β hβ).2.2.1 i hi⟩

theorem e6QpC_neg_mem_parabolicRoots (m : Fin 15) {β : Fin Tag.E6.rank → ℤ}
    (hβ : β ∈ e6QpC m) : -β ∈ parabolicRoots Tag.E6 (e6QpSupport m) :=
  ⟨IsRoot.neg (e6QpC_isRoot m hβ), fun i hi => by
    have := ((e6QpC_check m).2.1 β hβ).2.2.1 i hi
    simp [this]⟩

theorem eqpCas_mem_rootSpan (m : Fin 15) (M : SL2 Ω) :
    eqpCas m M ∈ rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 (e6QpSupport m)) :=
  list_prod_mem fun x hx => by
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
    exact rootSL2_mem_rootSpan (e6QpC_isRoot m hβ) (e6QpC_mem_parabolicRoots m hβ)
      (e6QpC_neg_mem_parabolicRoots m hβ) M

end Mem

section Conj

variable {Ω : Type} [Field Ω] [CharP Ω 2]

theorem canonicalRep_conj_rootSL2 (w : WeylGroup Tag.E6) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (M : SL2 Ω) :
    canonicalRep (coxeterSystem Tag.E6) Ω w * rootSL2 Tag.E6 Ω β M *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ = rootSL2 Tag.E6 Ω (w • β) M := by
  have hw := IsRoot.smul hβ w
  have h : (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom.comp
      (rootSL2 Tag.E6 Ω β) = rootSL2 Tag.E6 Ω (w • β) := by
    refine MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := Ω)) fun g hg => ?_
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change canonicalRep (coxeterSystem Tag.E6) Ω w * rootSL2 Tag.E6 Ω β (uSL c) *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ = rootSL2 Tag.E6 Ω (w • β) (uSL c)
      rw [rootSL2_uSL_of_charTwo hβ, rootSL2_uSL_of_charTwo hw,
        E6EvenFixedRootDatum.canonicalRep_conj_pinnedX w hβ]
    · change canonicalRep (coxeterSystem Tag.E6) Ω w * rootSL2 Tag.E6 Ω β (vSL c) *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ = rootSL2 Tag.E6 Ω (w • β) (vSL c)
      rw [rootSL2_vSL_of_charTwo hβ, rootSL2_vSL_of_charTwo hw,
        E6EvenFixedRootDatum.canonicalRep_conj_pinnedX w (IsRoot.neg hβ), smul_neg]
  exact DFunLike.congr_fun h M

end Conj

end CFSG.RankThree.PartOne.KE6
