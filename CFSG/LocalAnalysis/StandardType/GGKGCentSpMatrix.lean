module

public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
public import CFSG.Timmesfeld.Transvection.PresSp
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Open.QuasithinDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.KGCentSp

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {n : ℕ} {F : Type} [Field F]

theorem E_map (σ : F ≃+* F) (r : RootSubgroupIndex n) : (E F r).map σ = E F r := by
  cases r with
  | positiveLong i =>
      ext a b
      simp [E, Matrix.map_apply, Matrix.single_apply]
  | negativeLong i =>
      ext a b
      simp [E, Matrix.map_apply, Matrix.single_apply]
  | difference i j hij =>
      ext a b
      simp [E, Matrix.map_apply, Matrix.single_apply]
  | positiveSum i j hij =>
      ext a b
      simp [E, Matrix.map_apply, Matrix.single_apply]
  | negativeSum i j hij =>
      ext a b
      simp [E, Matrix.map_apply, Matrix.single_apply]

theorem fieldSp_elt (σ : F ≃+* F) (r : RootSubgroupIndex n) (c : F) :
    fieldSp n F σ (elt r c) = elt r (σ c) := by
  apply mat_injective
  rw [mat_apply, coe_fieldSp, ← mat_apply (elt r c), mat_elt, mat_elt]
  have hmap : (1 + c • E F r).map (σ : F → F) = 1 + σ c • E F r := by
    calc
      (1 + c • E F r).map (σ : F → F)
          = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map (σ : F → F) +
              (c • E F r).map (σ : F → F) :=
            Matrix.map_add (σ : F → F) (fun a b => map_add σ a b) _ _
      _ = 1 + σ c • (E F r).map (σ : F → F) := by
            rw [Matrix.map_one (σ : F → F) (map_zero σ) (map_one σ),
              Matrix.map_smul' (σ : F → F) c (E F r) (fun a b => map_mul σ a b)]
      _ = 1 + σ c • E F r := by
            rw [E_map σ r]
  exact hmap

theorem conj_elt_eq_of_conj_elt_one {g : StatedSp n F} {r : RootSubgroupIndex n}
    (h : g * elt r 1 * g⁻¹ = elt r 1) (c : F) : g * elt r c * g⁻¹ = elt r c := by
  apply mat_injective
  have hmat : mat n F g * (1 + E F r) * mat n F g⁻¹ = 1 + E F r := by
    have h' := congrArg (mat n F) h
    rwa [map_mul, map_mul, mat_elt, one_smul] at h'
  have hMM' : mat n F g * mat n F g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hExp : mat n F g * (1 + E F r) * mat n F g⁻¹
      = 1 + mat n F g * E F r * mat n F g⁻¹ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hMM']
  have hE : mat n F g * E F r * mat n F g⁻¹ = E F r := by
    have h1 := hmat
    rw [hExp] at h1
    exact add_left_cancel h1
  rw [map_mul, map_mul, mat_elt]
  have hExp2 : mat n F g * (1 + c • E F r) * mat n F g⁻¹
      = 1 + mat n F g * (c • E F r) * mat n F g⁻¹ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hMM']
  rw [hExp2, Matrix.mul_smul, Matrix.smul_mul, hE]

theorem eq_refl_of_conj_fieldSp_elt {g : StatedSp n F} {σ : F ≃+* F} {r : RootSubgroupIndex n}
    (h : ∀ c : F, g * fieldSp n F σ (elt r c) * g⁻¹ = elt r c) : σ = RingEquiv.refl F := by
  have h1 : g * elt r 1 * g⁻¹ = elt r 1 := by
    have h' := h 1
    rwa [fieldSp_elt, map_one] at h'
  have hc : ∀ c : F, g * elt r c * g⁻¹ = elt r c :=
    fun c => conj_elt_eq_of_conj_elt_one h1 c
  apply RingEquiv.ext
  intro c
  have h2 := h c
  rw [fieldSp_elt] at h2
  have h3 := hc (σ c)
  exact elt_injective r (h3.symm.trans h2)

noncomputable abbrev diagSp (t : Fin n → Fˣ) : StatedSp n F :=
  equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t)

private lemma mat_diagSp_eq_diagonal (t : Fin n → Fˣ) :
    mat n F (diagSp t) =
      Matrix.diagonal (Sum.elim (fun i => (t i : F))
        (fun i => (((t i)⁻¹ : Fˣ) : F))) :=
  mat_equiv_diagonal t

private lemma mat_diagSp_mulSingle_inl_self (i : Fin n) (ζ : Fˣ) :
    mat n F (diagSp (Pi.mulSingle i ζ)) (Sum.inl i) (Sum.inl i) = (ζ : F) := by
  rw [mat_diagSp_eq_diagonal, Matrix.diagonal_apply_eq]
  simp

private lemma mat_diagSp_mulSingle_inr_self (i : Fin n) (ζ : Fˣ) :
    mat n F (diagSp (Pi.mulSingle i ζ)) (Sum.inr i) (Sum.inr i) =
      ((ζ⁻¹ : Fˣ) : F) := by
  rw [mat_diagSp_eq_diagonal, Matrix.diagonal_apply_eq]
  simp

private lemma mat_diagSp_mulSingle_inl_ne {i j : Fin n} (h : j ≠ i) (ζ : Fˣ) :
    mat n F (diagSp (Pi.mulSingle i ζ)) (Sum.inl j) (Sum.inl j) = 1 := by
  rw [mat_diagSp_eq_diagonal, Matrix.diagonal_apply_eq]
  simp [Pi.mulSingle_eq_of_ne h]

private lemma mat_diagSp_mulSingle_inr_ne {i j : Fin n} (h : j ≠ i) (ζ : Fˣ) :
    mat n F (diagSp (Pi.mulSingle i ζ)) (Sum.inr j) (Sum.inr j) = 1 := by
  rw [mat_diagSp_eq_diagonal, Matrix.diagonal_apply_eq]
  simp [Pi.mulSingle_eq_of_ne h]

private lemma eq_zero_of_mul_eq_mul {x A B : F} (h : x * B = A * x) (hAB : A ≠ B) :
    x = 0 := by
  have h' : (B - A) * x = 0 := by
    rw [sub_mul, mul_comm B x, h, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hAB
  · exact h0

theorem mat_eq_zero_of_commute_diagSp {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1) {g : StatedSp n F}
    (hg : ∀ i : Fin n, Commute g (diagSp (Pi.mulSingle i ζ))) {a b : Fin n ⊕ Fin n} (hab : a ≠ b) :
    mat n F g a b = 0 := by
  have hζinv : ζ ≠ ζ⁻¹ := by
    intro h
    apply hζ2
    calc ζ ^ 2 = ζ * ζ := pow_two ζ
      _ = ζ * ζ⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ζ
  have hζinvF : (ζ : F) ≠ ((ζ⁻¹ : Fˣ) : F) := fun h => hζinv (Units.ext h)
  have hζinvF' : ((ζ⁻¹ : Fˣ) : F) ≠ (ζ : F) := hζinvF.symm
  have hζ1F : (ζ : F) ≠ 1 := fun h => hζ1 (Units.ext h)
  have hζinv1F : ((ζ⁻¹ : Fˣ) : F) ≠ 1 := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_ne_one.mpr hζ1F
  let i : Fin n := Sum.elim (fun i => i) (fun i => i) a
  have hcomm : mat n F g * mat n F (diagSp (Pi.mulSingle i ζ)) =
      mat n F (diagSp (Pi.mulSingle i ζ)) * mat n F g := by
    simpa [map_mul] using congrArg (mat n F) (hg i).eq
  have hentry : mat n F g a b * mat n F (diagSp (Pi.mulSingle i ζ)) b b
      = mat n F (diagSp (Pi.mulSingle i ζ)) a a * mat n F g a b := by
    have h := congrArg (fun M => M a b) hcomm
    rw [mat_diagSp_eq_diagonal] at h
    simpa only [mat_diagSp_eq_diagonal, Matrix.diagonal_apply_eq, Matrix.mul_diagonal,
      Matrix.diagonal_mul] using h
  have ha : a = Sum.inl i ∨ a = Sum.inr i := by
    cases a with
    | inl k => left; simp [i]
    | inr k => right; simp [i]
  rcases ha with ha | ha
  · cases b with
    | inl j =>
        by_cases hji : j = i
        · subst hji
          exact absurd ha hab
        · rw [ha] at hentry
          rw [ha]
          rw [mat_diagSp_mulSingle_inl_self i ζ,
            mat_diagSp_mulSingle_inl_ne hji ζ] at hentry
          exact eq_zero_of_mul_eq_mul hentry hζ1F
    | inr j =>
        by_cases hji : j = i
        · subst hji
          rw [ha] at hentry
          rw [ha]
          rw [mat_diagSp_mulSingle_inl_self i ζ,
            mat_diagSp_mulSingle_inr_self i ζ] at hentry
          exact eq_zero_of_mul_eq_mul hentry hζinvF
        · rw [ha] at hentry
          rw [ha]
          rw [mat_diagSp_mulSingle_inl_self i ζ,
            mat_diagSp_mulSingle_inr_ne hji ζ] at hentry
          exact eq_zero_of_mul_eq_mul hentry hζ1F
  · cases b with
    | inl j =>
        by_cases hji : j = i
        · subst hji
          rw [ha] at hentry
          rw [ha]
          rw [mat_diagSp_mulSingle_inr_self i ζ,
            mat_diagSp_mulSingle_inl_self i ζ] at hentry
          exact eq_zero_of_mul_eq_mul hentry hζinvF'
        · rw [ha] at hentry
          rw [ha]
          rw [mat_diagSp_mulSingle_inr_self i ζ,
            mat_diagSp_mulSingle_inl_ne hji ζ] at hentry
          exact eq_zero_of_mul_eq_mul hentry hζinv1F
    | inr j =>
        by_cases hji : j = i
        · subst hji
          exact absurd ha hab
        · rw [ha] at hentry
          rw [ha]
          rw [mat_diagSp_mulSingle_inr_self i ζ,
            mat_diagSp_mulSingle_inr_ne hji ζ] at hentry
          exact eq_zero_of_mul_eq_mul hentry hζinv1F

theorem pow_card_sub_one_eq_one [Fintype F] {g : StatedSp n F}
    (hg : ∀ a b : Fin n ⊕ Fin n, a ≠ b → mat n F g a b = 0) : g ^ (Fintype.card F - 1) = 1 := by
  have hdiag : mat n F g = Matrix.diagonal (fun a => mat n F g a a) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.diagonal_apply_ne _ hab, hg a b hab]
  have hdet : (mat n F g).det ≠ 0 := by
    rw [mat_apply]
    exact Matrix.GeneralLinearGroup.det_ne_zero (g : GL (Fin n ⊕ Fin n) F)
  have hprod : (∏ a, mat n F g a a) ≠ 0 := by
    rw [hdiag, Matrix.det_diagonal] at hdet
    exact hdet
  have hne : ∀ a, mat n F g a a ≠ 0 := fun a h0 =>
    hprod (Finset.prod_eq_zero (Finset.mem_univ a) h0)
  apply mat_injective
  rw [map_pow, hdiag, Matrix.diagonal_pow, map_one (mat n F)]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [FiniteField.pow_card_sub_one_eq_one (mat n F g a a) (hne a)]
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]

theorem exists_eq_conj_mul_fieldSp [Finite F] [CharP F 2] (hn : 3 ≤ n)
    (β : MulAut (StatedSp n F)) :
    ∃ (g : StatedSp n F) (σ : F ≃+* F), β = MulAut.conj g * fieldSp n F σ := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨A, ρ, hA⟩ := (automorphism_generation (K := F) hn).2
    (MulAut.congr (CFSG.SeitzReduction.F4Pilot.spProjEquiv n F) β)
  obtain ⟨s, hs⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_conjAut_eq_statedSp A
  refine ⟨s, ρ, ?_⟩
  apply (MulAut.congr (CFSG.SeitzReduction.F4Pilot.spProjEquiv n F)).injective
  rw [hA, hs, map_mul, CFSG.SeitzReduction.F4Pilot.mulAutCongr_spProjEquiv_conj,
    CFSG.SeitzReduction.F4Pilot.mulAutCongr_spProjEquiv_fieldSp]

theorem fieldSp_refl : fieldSp n F (RingEquiv.refl F) = 1 :=
  map_one (fieldSp n F)

end CFSG.StandardType.KGCentSp

end
