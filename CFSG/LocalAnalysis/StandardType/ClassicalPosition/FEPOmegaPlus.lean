module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoDualPair
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.WittOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGL
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.UnitaryForm

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

private abbrev fepomepι (n : ℕ) : Type := Fin n ⊕ Fin n

private noncomputable def fepomepQ (n : ℕ) (F : Type) [Field F] :
    QuadraticForm F (fepomepι n → F) :=
  Spin.quadPlus n F

private noncomputable def fepomepG (n : ℕ) (F : Type) [Field F] :
    Matrix (fepomepι n) (fepomepι n) F :=
  LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (fepomepQ n F))

private def fepomepA (n : ℕ) (F : Type) [Field F] (S : Set (GL (fepomepι n) F)) :
    Subalgebra F (Matrix (fepomepι n) (fepomepι n) F) :=
  Algebra.adjoin F (Units.val '' S)

private noncomputable def fepomepJ (n : ℕ) (F : Type) [Field F] :
    ↥(spinGroup (fepomepQ n F)) →* GL (fepomepι n) F :=
  Spin.spinMatrix (fepomepQ n F)

private lemma fepomep_polar_eq_dot {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma fepomep_isometry_of_quad {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (M : Matrix ι ι F)
    (hM : ∀ x : ι → F, Q (M.mulVec x) = Q x) :
    M.transpose * LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) * M =
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  have hpol : ∀ x y, QuadraticMap.polar Q (M.mulVec x) (M.mulVec y) =
      QuadraticMap.polar Q x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hM (x + y), hM x, hM y]
  apply (LinearEquiv.injective Matrix.toBilin')
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, ← fepomep_polar_eq_dot Q (M.mulVec x) (M.mulVec y),
    ← fepomep_polar_eq_dot Q x y]
  exact hpol x y

private lemma fepomep_polar_of_isometry {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (M : Matrix ι ι F)
    (hM : ∀ x : ι → F, Q (M.mulVec x) = Q x) :
    ∀ x y : ι → F, QuadraticMap.polar Q (M.mulVec x) (M.mulVec y) =
      QuadraticMap.polar Q x y := by
  intro x y
  rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hM (x + y), hM x, hM y]

private lemma fepomep_isUnit_det (n : ℕ) {F : Type} [Field F] [Finite F] :
    IsUnit (fepomepG n F).det := by
  have hnd := Spin.nondegenerate_polarBilin_quadPlus n F
  have h1 : fepomepG n F =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin (fepomepQ n F)) := rfl
  rw [h1]
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp
    ((LinearMap.BilinForm.nondegenerate_toMatrix'_iff).mpr hnd))

private lemma fepomep_transpose_G (n : ℕ) (F : Type) [Field F] :
    (fepomepG n F).transpose = fepomepG n F := by
  rw [show fepomepG n F =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin (fepomepQ n F)) from rfl]
  exact (LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm).mpr
    (LinearMap.BilinForm.IsSymm.mk (fun x y => QuadraticMap.polar_comm _ x y))

private lemma fepomep_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      Commute a b := by
  intro a ha b hb
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F (Units.val '' S) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rcases hy with ⟨s', hs', rfl⟩
    have h := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) (hS s' hs' s hs).eq
    simpa [Units.val_mul] using h
  have hA : Algebra.adjoin F (Units.val '' S) ≤ Subalgebra.centralizer F (Units.val '' S) :=
    Algebra.adjoin_le hgen
  have ha' : a ∈ Subalgebra.centralizer F (Units.val '' S) := hA ha
  have hgen2 : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h := (Subalgebra.mem_centralizer_iff F).mp ha' (s : Matrix ι ι F) ⟨s, hs, rfl⟩
    exact h.symm
  have hA2 : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := Algebra.adjoin_le hgen2
  have hb' : b ∈ Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := hA2 hb
  exact (Subalgebra.mem_centralizer_iff F).mp hb' a (Set.mem_singleton a)

private lemma fepomep_statedClassicalModel_congr
    {H G : Type} [Group H] [Group G] (ξ : H ≃* G)
    (t : StatedLieTag) (n p f : ℕ)
    (h : CFSG.Open.StatedClassicalModel H t n p f) :
    CFSG.Open.StatedClassicalModel G t n p f := by
  cases t <;> simp only [CFSG.Open.StatedClassicalModel] at h ⊢
  · rcases h with ⟨hadm, K, hfld, hfin, hcard, ⟨φ⟩⟩
    exact ⟨hadm, K, hfld, hfin, hcard, ⟨ξ.symm.trans φ⟩⟩
  · rcases h with ⟨hadm, K, hfld, hfin, hcard, ⟨φ⟩⟩
    exact ⟨hadm, K, hfld, hfin, hcard, ⟨ξ.symm.trans φ⟩⟩
  · rcases h with ⟨hadm, K, hfld, hfin, hcard, ⟨φ⟩⟩
    exact ⟨hadm, K, hfld, hfin, hcard, ⟨ξ.symm.trans φ⟩⟩
  · rcases h with ⟨hadm, K, hfld, hfin, hcard, ⟨φ⟩⟩
    exact ⟨hadm, K, hfld, hfin, hcard, ⟨ξ.symm.trans φ⟩⟩
  · rcases h with ⟨hadm, K, hfld, hfin, hcard, ⟨φ⟩⟩
    exact ⟨hadm, K, hfld, hfin, hcard, ⟨ξ.symm.trans φ⟩⟩
  · rcases h with ⟨hadm, K, hfld, hfin, hcard, b, c, hbc, ⟨φ⟩⟩
    exact ⟨hadm, K, hfld, hfin, hcard, b, c, hbc, ⟨ξ.symm.trans φ⟩⟩
  all_goals exact h.2.elim

private lemma fepomep_quotientCenter
    {U X : Type} [Group U] [Group X] (ψ : U →* X)
    (hψ : ψ.ker ≤ Subgroup.center U) {J' : Subgroup U}
    (hperf : _root_.commutator ↥J' = ⊤) :
    Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃*
      ↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) := by
  let fmap : ↥J' →* ↥(J'.map ψ) :=
    (ψ.comp J'.subtype).codRestrict (J'.map ψ) (fun x => Subgroup.mem_map_of_mem ψ x.2)
  have hf : Function.Surjective fmap := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hkerf : fmap.ker ≤ Subgroup.center ↥J' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : ((x : ↥J') : U) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      have h := congrArg (fun z : ↥(J'.map ψ) => (z : X)) hx
      simpa [fmap] using h
    have hxc := hψ hx1
    apply Subtype.ext
    simpa using (Subgroup.mem_center_iff.mp hxc ((y : ↥J') : U))
  haveI : Group.IsPerfect ↥J' := ⟨hperf⟩
  have hcen : Subgroup.center (↥J' ⧸ fmap.ker) =
      (Subgroup.center ↥J').map (QuotientGroup.mk' fmap.ker) :=
    (CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
      (QuotientGroup.mk' fmap.ker) (QuotientGroup.mk'_surjective fmap.ker)
      (by rwa [QuotientGroup.ker_mk'])).symm
  let e1 : ↥J' ⧸ fmap.ker ≃* ↥(J'.map ψ) :=
    QuotientGroup.quotientKerEquivOfSurjective fmap hf
  let e2 : ↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ) ≃*
      (↥J' ⧸ fmap.ker) ⧸ Subgroup.center (↥J' ⧸ fmap.ker) :=
    QuotientGroup.congr (Subgroup.center ↥(J'.map ψ)) (Subgroup.center (↥J' ⧸ fmap.ker))
      e1.symm (Subgroup.map_center_eq e1.symm)
  exact ⟨(e2.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ hkerf))).symm⟩

private lemma fepomep_fieldExtCase_of_model
    (f : ℕ) {X : Type} [Group X] (J : Subgroup X)
    {t' : StatedLieTag} {m' f' : ℕ} (hlt : f < f')
    (ht' : t' ∈ CFSG.Blueprint.classicalTags)
    (hmod : CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) t' m' 2 f') :
    GGSixLSevenFieldExtCase J .POmegaPlus f := by
  refine ⟨t', m', f', hlt, ?_, ?_⟩
  · exact Or.inl ⟨ht', hmod⟩
  · rintro ⟨-, -, h | h⟩ <;> exact absurd h (by decide)

private lemma fepomep_blockField_card {F : Type} [Field F] (f d : ℕ) (hc : Nat.card F = 2 ^ f)
    {K : Type} [Field K] [Finite K] [Algebra F K]
    (h : Module.finrank F K = d) : Nat.card K = 2 ^ (f * d) := by
  rw [Module.natCard_eq_pow_finrank (K := F) (V := K), h, hc, pow_mul]

private lemma fepomep_dualPair_star (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε) :
    formAdj (RingHom.id F) (fepomepG n F) e ∈ fepomepA n F S ∧
      IsIdempotentElem (formAdj (RingHom.id F) (fepomepG n F) e) ∧
      formAdj (RingHom.id F) (fepomepG n F)
          (formAdj (RingHom.id F) (fepomepG n F) e) = e ∧
      formAdj (RingHom.id F) (fepomepG n F) e * ε =
        formAdj (RingHom.id F) (fepomepG n F) e ∧
      e ≠ formAdj (RingHom.id F) (fepomepG n F) e ∧
      formAdj (RingHom.id F) (fepomepG n F) e * e = 0 ∧
      e * formAdj (RingHom.id F) (fepomepG n F) e = 0 ∧
      ε = e + formAdj (RingHom.id F) (fepomepG n F) e := by
  classical
  have hG : IsUnit (fepomepG n F).det := fepomep_isUnit_det n
  have hGh : Matrix.transpose ((fepomepG n F).map (RingHom.id F)) =
      fepomepG n F := by
    rw [show (fepomepG n F).map (RingHom.id F) = fepomepG n F from rfl]
    exact fepomep_transpose_G n F
  have hSG : ∀ s ∈ S, Matrix.transpose
      ((s : Matrix (fepomepι n) (fepomepι n) F).map (RingHom.id F)) * fepomepG n F *
      (s : Matrix (fepomepι n) (fepomepι n) F) = fepomepG n F := by
    intro s hs
    obtain ⟨x, rfl⟩ := hSU s hs
    rw [show (((fepomepJ n F x : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F)).map (RingHom.id F) =
        ((fepomepJ n F x : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) from rfl]
    exact fepomep_isometry_of_quad (fepomepQ n F)
      ((fepomepJ n F x : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)
      (Spin.spinMatrix_mem (fepomepQ n F) x)
  have hεA : ε ∈ fepomepA n F S := hε.1
  have hεadj : formAdj (RingHom.id F) (fepomepG n F) ε = ε := hε.2.2.2.1
  have hεprim := hε.2.2.2.2
  have heA : e ∈ fepomepA n F S := he.1
  have heidem : IsIdempotentElem e := he.2.1
  have hene0 : e ≠ 0 := he.2.2.1
  have hestA : formAdj (RingHom.id F) (fepomepG n F) e ∈ fepomepA n F S :=
    Geo.formAdj_mem_adjoin (RingHom.id F) hG hSG heA
  have hestidem : IsIdempotentElem (formAdj (RingHom.id F) (fepomepG n F) e) := by
    rw [isIdempotentElem_iff] at heidem ⊢
    rw [← Geo.formAdj_mul (RingHom.id F) hG e e, heidem]
  have hdouble : formAdj (RingHom.id F) (fepomepG n F)
      (formAdj (RingHom.id F) (fepomepG n F) e) = e :=
    Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh e
  have hcommA : ∀ a ∈ fepomepA n F S, ∀ b ∈ fepomepA n F S, Commute a b :=
    fepomep_adjoin_comm hS
  have hestε : formAdj (RingHom.id F) (fepomepG n F) e * ε =
      formAdj (RingHom.id F) (fepomepG n F) e := by
    have h2 : formAdj (RingHom.id F) (fepomepG n F) e =
        ε * formAdj (RingHom.id F) (fepomepG n F) e := by
      calc formAdj (RingHom.id F) (fepomepG n F) e
          = formAdj (RingHom.id F) (fepomepG n F) (e * ε) := by rw [heε]
        _ = formAdj (RingHom.id F) (fepomepG n F) ε *
              formAdj (RingHom.id F) (fepomepG n F) e :=
              Geo.formAdj_mul (RingHom.id F) hG e ε
        _ = ε * formAdj (RingHom.id F) (fepomepG n F) e := by rw [hεadj]
    exact (hcommA _ hestA ε hεA).eq.trans h2.symm
  have hneEst : e ≠ formAdj (RingHom.id F) (fepomepG n F) e := by
    intro h
    have hfix : formAdj (RingHom.id F) (fepomepG n F) e = e := h.symm
    rcases hεprim e heA heidem hfix heε with h0 | hεe
    · exact hene0 h0
    · exact hne hεe
  have hpair : formAdj (RingHom.id F) (fepomepG n F) e ≠ e := fun h => hneEst h.symm
  obtain ⟨horth1, horth2⟩ := Geo.mul_formAdj_eq_zero_of_dualPair (RingHom.id F)
    (fun x => rfl) hG hGh hSG hS he hpair
  have hsumA : e + formAdj (RingHom.id F) (fepomepG n F) e ∈ fepomepA n F S :=
    Subalgebra.add_mem _ heA hestA
  have hsumidem : IsIdempotentElem
      (e + formAdj (RingHom.id F) (fepomepG n F) e) := by
    rw [isIdempotentElem_iff] at heidem hestidem ⊢
    rw [add_mul, mul_add, mul_add, heidem, hestidem, horth1, horth2]
    abel
  have hsumadj : formAdj (RingHom.id F) (fepomepG n F)
      (e + formAdj (RingHom.id F) (fepomepG n F) e) =
      e + formAdj (RingHom.id F) (fepomepG n F) e := by
    rw [Geo.formAdj_add (RingHom.id F) (fepomepG n F) e
      (formAdj (RingHom.id F) (fepomepG n F) e), hdouble]
    abel
  have hsumε : (e + formAdj (RingHom.id F) (fepomepG n F) e) * ε =
      e + formAdj (RingHom.id F) (fepomepG n F) e := by
    rw [add_mul, heε, hestε]
  have hsum : ε = e + formAdj (RingHom.id F) (fepomepG n F) e := by
    rcases hεprim (e + formAdj (RingHom.id F) (fepomepG n F) e)
        hsumA hsumidem hsumadj hsumε with h0 | hεe
    · exfalso
      have h2est : formAdj (RingHom.id F) (fepomepG n F) e +
          formAdj (RingHom.id F) (fepomepG n F) e = 0 := by
        have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
        calc formAdj (RingHom.id F) (fepomepG n F) e +
              formAdj (RingHom.id F) (fepomepG n F) e
            = (2 : F) • formAdj (RingHom.id F) (fepomepG n F) e :=
                (two_smul F _).symm
          _ = 0 := by rw [h2, zero_smul]
      have heq : e = formAdj (RingHom.id F) (fepomepG n F) e := by
        rw [← add_right_cancel_iff
          (c := formAdj (RingHom.id F) (fepomepG n F) e)]
        rw [h0, h2est]
      exact hneEst heq
    · exact hεe.symm
  exact ⟨hestA, hestidem, hdouble, hestε, hneEst, horth2, horth1, hsum⟩

private lemma fepomep_blockActionA (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (fepomepι n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (fepomepι n) (fepomepι n) F}
    (he : IsPrimIdemIn (fepomepA n F S) e) :
    ∃ actA : fepomepA n F S →ₐ[F] Module.End F (LinearMap.range (Matrix.mulVecLin e)),
      ∀ (a : fepomepA n F S) (w : LinearMap.range (Matrix.mulVecLin e)),
        (actA a w : fepomepι n → F) =
          Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) w := by
  classical
  let A := fepomepA n F S
  let W : Submodule F (fepomepι n → F) := LinearMap.range (Matrix.mulVecLin e)
  have hpair : (Units.val '' S : Set (Matrix (fepomepι n) (fepomepι n) F)).Pairwise Commute := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ _
    exact (hS s hs s' hs').map (Units.coeHom (Matrix (fepomepι n) (fepomepι n) F))
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpair
  have hcomm : ∀ a : A, (a : Matrix (fepomepι n) (fepomepι n) F) * e =
      e * (a : Matrix (fepomepι n) (fepomepι n) F) := by
    intro a
    exact congrArg Subtype.val (mul_comm a (⟨e, he.1⟩ : A))
  let actA : A →ₐ[F] Module.End F W :=
  { toFun := fun a =>
      ((Matrix.mulVecLin (a : Matrix (fepomepι n) (fepomepι n) F)).comp W.subtype).codRestrict W
        (fun v => by
          rw [LinearMap.comp_apply, Submodule.coe_subtype]
          obtain ⟨u, hu⟩ := v.2
          rw [← hu]
          refine ⟨Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) u, ?_⟩
          calc Matrix.mulVecLin e (Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) u)
              = Matrix.mulVec e
                  (Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) u) := rfl
            _ = Matrix.mulVec (e * (a : Matrix (fepomepι n) (fepomepι n) F)) u :=
                  Matrix.mulVec_mulVec u e (a : Matrix (fepomepι n) (fepomepι n) F)
            _ = Matrix.mulVec ((a : Matrix (fepomepι n) (fepomepι n) F) * e) u := by
                  rw [hcomm a]
            _ = Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F)
                  (Matrix.mulVec e u) :=
                  (Matrix.mulVec_mulVec u (a : Matrix (fepomepι n) (fepomepι n) F) e).symm
            _ = Matrix.mulVecLin a (Matrix.mulVecLin e u) := rfl)
    map_one' := by ext w; simp
    map_mul' := by intro a b; ext w; simp
    map_zero' := by ext w; simp
    map_add' := by intro a b; ext w; simp
    commutes' := by
      intro c
      ext w
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply,
        Submodule.coe_subtype, Matrix.mulVecLin_apply, Subalgebra.coe_algebraMap,
        Module.algebraMap_end_apply, Matrix.algebraMap_eq_diagonal, Submodule.coe_smul]
      rw [show algebraMap F (fepomepι n → F) c = fun _ => c from rfl,
        Matrix.diagonal_const_mulVec] }
  refine ⟨actA, ?_⟩
  intro a w
  rfl

private lemma fepomep_blockActionA_ker (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (fepomepι n) F))
    (_hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (fepomepι n) (fepomepι n) F}
    (_he : IsPrimIdemIn (fepomepA n F S) e)
    (K : Type) [Field K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (actA : fepomepA n F S →ₐ[F] Module.End F (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (a : fepomepA n F S) (w : LinearMap.range (Matrix.mulVecLin e)),
      (actA a w : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) w) :
    RingHom.ker (π : fepomepA n F S →+* K) ≤
      RingHom.ker (actA : fepomepA n F S →+*
        Module.End F (LinearMap.range (Matrix.mulVecLin e))) := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  have hae : (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0 := (hπker a).mp ha
  refine LinearMap.ext fun w => Subtype.ext ?_
  change (actA a w : fepomepι n → F) = 0
  rw [hact a w]
  obtain ⟨v, hv⟩ := w.2
  rw [← hv, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec v (a : Matrix (fepomepι n) (fepomepι n) F) e, hae,
    Matrix.zero_mulVec]

private lemma fepomep_blockKModule (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (fepomepι n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (fepomepι n) (fepomepι n) F}
    (he : IsPrimIdemIn (fepomepA n F S) e)
    (K : Type) [Field K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0) :
    ∃ (W : Submodule F (fepomepι n → F)) (_ : W ≠ ⊥)
      (_ : Module K W) (_ : IsScalarTower F K W),
      W = LinearMap.range (Matrix.mulVecLin e) ∧
        ∀ (a : fepomepA n F S) (w : W),
          ((π a • w : W) : fepomepι n → F) =
            Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F) := by
  classical
  obtain ⟨actA, hact⟩ := fepomep_blockActionA n S hS he
  have hker : RingHom.ker (π : fepomepA n F S →+* K) ≤
      RingHom.ker (actA : fepomepA n F S →+*
        Module.End F (LinearMap.range (Matrix.mulVecLin e))) :=
    fepomep_blockActionA_ker n S hS he K π hπker actA hact
  have hp : Function.Surjective (π : fepomepA n F S →+* K) := fun k => hπsurj k
  let ψ : K →+* Module.End F (LinearMap.range (Matrix.mulVecLin e)) :=
    (Ideal.Quotient.lift
      (RingHom.ker (π : fepomepA n F S →+* K))
      (actA : fepomepA n F S →+* Module.End F (LinearMap.range (Matrix.mulVecLin e)))
      (fun a ha => RingHom.mem_ker.mp (hker ha))).comp
      (RingHom.quotientKerEquivOfSurjective
        (f := (π : fepomepA n F S →+* K)) hp).symm.toRingHom
  have hψ : ∀ a : fepomepA n F S, ψ (π a) = actA a := fun a => by
    change (Ideal.Quotient.lift
      (RingHom.ker (π : fepomepA n F S →+* K))
      (actA : fepomepA n F S →+* Module.End F (LinearMap.range (Matrix.mulVecLin e)))
      (fun a ha => RingHom.mem_ker.mp (hker ha)))
      ((RingHom.quotientKerEquivOfSurjective
        (f := (π : fepomepA n F S →+* K)) hp).symm
        ((π : fepomepA n F S →+* K) a)) = actA a
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    rfl
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.compHom (LinearMap.range (Matrix.mulVecLin e)) ψ
  have hne : LinearMap.range (Matrix.mulVecLin e) ≠ ⊥ := by
    intro hbot
    have hf : Matrix.mulVecLin e = 0 := LinearMap.range_eq_bot.mp hbot
    have h2 : e = 0 := by
      ext i j
      have h := congrFun (congrArg (fun g : (fepomepι n → F) →ₗ[F] (fepomepι n → F) =>
          g (Pi.single j (1 : F))) hf) i
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h
    exact he.2.2.1 h2
  have htower : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)) :=
    ⟨fun c k w => by
    change (ψ (c • k)) w = c • ((ψ k) w)
    obtain ⟨a, rfl⟩ := hπsurj k
    rw [← map_smul π c a, hψ (c • a), hψ a, map_smul]
    rfl⟩
  refine ⟨LinearMap.range (Matrix.mulVecLin e), hne,
    Module.compHom (LinearMap.range (Matrix.mulVecLin e)) ψ, htower, rfl, ?_⟩
  intro a w
  change (ψ (π a) w : fepomepι n → F) =
    Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)
  rw [hψ a]
  exact hact a w

private lemma fepomep_blockModuleRank (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (fepomepι n) F))
    {e : Matrix (fepomepι n) (fepomepι n) F}
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (W : Submodule F (fepomepι n → F))
    [Module K W] [IsScalarTower F K W]
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (hWne : W ≠ ⊥) :
    Module.finrank F W = blockDegree (fepomepA n F S) e * Module.finrank K W ∧
      1 ≤ Module.finrank K W := by
  haveI : Module.Free K W := Module.Free.of_divisionRing K W
  refine ⟨?_, ?_⟩
  · rw [← Module.finrank_mul_finrank F K W, hπdeg]
  · haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
    exact Module.finrank_pos

private lemma fepomep_dualPair_blockModule (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (fepomepι n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (fepomepι n) (fepomepι n) F}
    (he : IsPrimIdemIn (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e) :
    ∃ (W : Submodule F (fepomepι n → F)) (_ : W = LinearMap.range (Matrix.mulVecLin e))
      (_ : Module K W) (_ : IsScalarTower F K W) (_ : FiniteDimensional K W),
      Module.finrank F W = blockDegree (fepomepA n F S) e * Module.finrank K W ∧
        1 ≤ Module.finrank K W ∧
        ∀ (a : fepomepA n F S) (w : W),
          ((π a • w : W) : fepomepι n → F) =
            Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F) := by
  obtain ⟨W, hWne, hmod, htower, hWeq, hK⟩ :=
    fepomep_blockKModule n S hS he K π hπsurj hπker
  letI : Module K W := hmod
  letI : IsScalarTower F K W := htower
  obtain ⟨hdim, hm1⟩ := fepomep_blockModuleRank n S K W hπdeg hWne
  exact ⟨W, hWeq, hmod, htower, inferInstance, hdim, hm1, hK⟩

private lemma fepomep_blockCentralizer_commute_adjoin (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (u : glBlockCentralizer (fepomepJ n F) S ε)
    {a : Matrix (fepomepι n) (fepomepι n) F} (ha : a ∈ fepomepA n F S) :
    Commute ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
      Matrix (fepomepι n) (fepomepι n) F) a := by
  have hcent : fepomepJ n F (u : ↥(spinGroup (fepomepQ n F))) ∈
      Subgroup.centralizer S :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp u.2)).1
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha ?_
  rintro b ⟨s, hs, rfl⟩
  rw [commute_iff_eq]
  simpa only [Units.val_mul] using
    congrArg Units.val (Subgroup.mem_centralizer_iff.mp hcent s hs).symm

private lemma fepomep_blockCentralizer_stable (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    (u : glBlockCentralizer (fepomepJ n F) S ε) :
    ∀ w ∈ W, Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
      Matrix (fepomepι n) (fepomepι n) F) w ∈ W := by
  let J : Matrix (fepomepι n) (fepomepι n) F :=
    fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))
  intro w hw
  change Matrix.mulVec J w ∈ W
  rw [hW] at hw ⊢
  obtain ⟨v, hv⟩ := hw
  have hcomm : J * e = e * J :=
    (fepomep_blockCentralizer_commute_adjoin n hn S hSU hS hε u he.1).eq
  refine ⟨Matrix.mulVec J v, ?_⟩
  rw [← hv]
  show Matrix.mulVec e (Matrix.mulVec J v) = Matrix.mulVec J (Matrix.mulVec e v)
  rw [Matrix.mulVec_mulVec v e J, Matrix.mulVec_mulVec v J e, hcomm]

private lemma fepomep_blockActionEnd (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∃ (ρEnd : glBlockCentralizer (fepomepJ n F) S ε →* Module.End K W),
      ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
        ((ρEnd u w : W) : fepomepι n → F) =
          Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
            Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F) := by
  classical
  let M (u : glBlockCentralizer (fepomepJ n F) S ε) :
      Matrix (fepomepι n) (fepomepι n) F :=
    fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))
  have hM_mul (u u' : glBlockCentralizer (fepomepJ n F) S ε) :
      M (u * u') = M u * M u' := by
    change (fepomepJ n F ((u * u') : ↥(spinGroup (fepomepQ n F))) :
        Matrix (fepomepι n) (fepomepι n) F) =
      (fepomepJ n F (u : ↥(spinGroup (fepomepQ n F))) :
        Matrix (fepomepι n) (fepomepι n) F) *
      (fepomepJ n F (u' : ↥(spinGroup (fepomepQ n F))) :
        Matrix (fepomepι n) (fepomepι n) F)
    rw [map_mul, Units.val_mul]
  have hM_one : M 1 = 1 := by
    change (fepomepJ n F (1 : ↥(spinGroup (fepomepQ n F))) :
      Matrix (fepomepι n) (fepomepι n) F) = 1
    rw [map_one]
    rfl
  let rhoF (u : glBlockCentralizer (fepomepJ n F) S ε) : W →ₗ[F] W :=
    ((Matrix.mulVecLin (M u)).comp W.subtype).codRestrict W (fun v => by
      rw [LinearMap.comp_apply, Submodule.coe_subtype, Matrix.mulVecLin_apply]
      exact fepomep_blockCentralizer_stable n hn S hSU hS hε he W hW u v v.2)
  have hrhoF_apply (u : glBlockCentralizer (fepomepJ n F) S ε) (v : W) :
      (rhoF u v : fepomepι n → F) = Matrix.mulVec (M u) v := rfl
  have hrhoF_smul (u : glBlockCentralizer (fepomepJ n F) S ε) (k : K) (v : W) :
      rhoF u (k • v) = k • rhoF u v := by
    obtain ⟨a, ha⟩ := hπsurj k
    apply Subtype.ext
    have hv : k • v = π a • v := by rw [← ha]
    have hw : k • rhoF u v = π a • rhoF u v := by rw [← ha]
    rw [hv, hw, hrhoF_apply, hK a v, hK a (rhoF u v), hrhoF_apply]
    have hcomm : M u * (a : Matrix (fepomepι n) (fepomepι n) F) =
        (a : Matrix (fepomepι n) (fepomepι n) F) * M u :=
      (fepomep_blockCentralizer_commute_adjoin n hn S hSU hS hε u a.2).eq
    rw [Matrix.mulVec_mulVec (v : fepomepι n → F) (M u)
        (a : Matrix (fepomepι n) (fepomepι n) F),
      Matrix.mulVec_mulVec (v : fepomepι n → F)
        (a : Matrix (fepomepι n) (fepomepι n) F) (M u), hcomm]
  refine ⟨{ toFun := fun u =>
      { toFun := rhoF u
        map_add' := fun v v' => (rhoF u).map_add v v'
        map_smul' := fun k v => hrhoF_smul u k v }, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · refine LinearMap.ext fun v => Subtype.ext ?_
    change (rhoF 1 v : fepomepι n → F) = (v : fepomepι n → F)
    rw [hrhoF_apply, hM_one, Matrix.one_mulVec]
  · intro u u'
    refine LinearMap.ext fun v => Subtype.ext ?_
    change (rhoF (u * u') v : fepomepι n → F) = (rhoF u (rhoF u' v) : fepomepι n → F)
    rw [hrhoF_apply, hrhoF_apply, hrhoF_apply, hM_mul, Matrix.mulVec_mulVec]
  · intro u w
    exact hrhoF_apply u w

private lemma fepomep_blockActionEnd_bijective (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (ρEnd : glBlockCentralizer (fepomepJ n F) S ε →* Module.End K W)
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρEnd u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∀ u : glBlockCentralizer (fepomepJ n F) S ε, Function.Bijective (ρEnd u) := by
  intro u
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h := congrArg (ρEnd u⁻¹) hxy
    change ((ρEnd u⁻¹ * ρEnd u) x) = ((ρEnd u⁻¹ * ρEnd u) y) at h
    rw [← map_mul, inv_mul_cancel, map_one] at h
    simpa using h
  · intro y
    refine ⟨ρEnd u⁻¹ y, ?_⟩
    change ((ρEnd u * ρEnd u⁻¹) y) = y
    rw [← map_mul, mul_inv_cancel, map_one]
    simp

private lemma fepomep_dualPair_blockActionHom (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∃ (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W)),
      ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
        ((ρ u w : W) : fepomepι n → F) =
          Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
            Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F) := by
  obtain ⟨ρEnd, hρ⟩ :=
    fepomep_blockActionEnd n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg W hW
      hK
  let ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W) :=
  { toFun := fun u =>
      LinearEquiv.ofBijective (ρEnd u)
        (fepomep_blockActionEnd_bijective n hn S hSU hS hε he heε hne hdeg K π hπsurj
          hπker hπdeg W hW hK ρEnd hρ u)
    map_one' := by
      ext w
      rw [LinearEquiv.ofBijective_apply, map_one]
      rfl
    map_mul' := by
      intro u v
      ext w
      rw [LinearEquiv.ofBijective_apply, map_mul, LinearEquiv.mul_apply,
        LinearEquiv.ofBijective_apply]
      rfl }
  exact ⟨ρ, fun u w => hρ u w⟩

private lemma fepomep_fixes_star_of_isometry {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G M e estar : Matrix ι ι F} (hG : IsUnit G.det) (hMdet : IsUnit M.det)
    (hMiso : Matrix.transpose M * G * M = G)
    (hMe : M * e = e) (heM : e * M = e)
    (hGest : G * estar = Matrix.transpose e * G) :
    M * estar = estar := by
  have hMtdet : IsUnit (Matrix.transpose M).det := by
    rwa [Matrix.det_transpose]
  have hA : Matrix.transpose M * G * (M * estar) = Matrix.transpose e * G := by
    calc Matrix.transpose M * G * (M * estar)
        = (Matrix.transpose M * G * M) * estar := by rw [← Matrix.mul_assoc]
      _ = G * estar := by rw [hMiso]
      _ = Matrix.transpose e * G := hGest
  have hMinv : (Matrix.transpose M)⁻¹ * Matrix.transpose e = Matrix.transpose e := by
    rw [← Matrix.transpose_nonsing_inv, ← Matrix.transpose_mul]
    congr 1
    have h : (e * M) * M⁻¹ = e := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv M hMdet, Matrix.mul_one]
    rwa [heM] at h
  have hC : G * (M * estar) = G * estar := by
    have h := congrArg (fun X => (Matrix.transpose M)⁻¹ * X) hA
    have hl : (Matrix.transpose M)⁻¹ * (Matrix.transpose M * G * (M * estar))
        = G * (M * estar) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul (Matrix.transpose M) hMtdet, Matrix.one_mul]
    have hr : (Matrix.transpose M)⁻¹ * (Matrix.transpose e * G) = Matrix.transpose e * G := by
      rw [← Matrix.mul_assoc, hMinv]
    rwa [hl, hr, ← hGest] at h
  have hcancel := congrArg (fun X => G⁻¹ * X) hC
  have hL : G⁻¹ * (G * (M * estar)) = M * estar := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.one_mul]
  have hR : G⁻¹ * (G * estar) = estar := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.one_mul]
  rwa [hL, hR] at hcancel

private lemma fepomep_dualPair_blockAction_injective (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    Function.Injective ρ := by
  classical
  have hmatrix (w : glBlockCentralizer (fepomepJ n F) S ε) (hw : ρ w = 1) :
      ((fepomepJ n F (w : ↥(spinGroup (fepomepQ n F)))) :
        Matrix (fepomepι n) (fepomepι n) F) = 1 := by
    let M : Matrix (fepomepι n) (fepomepι n) F :=
      fepomepJ n F (w : ↥(spinGroup (fepomepQ n F)))
    obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
      fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
    set estar : Matrix (fepomepι n) (fepomepι n) F :=
      formAdj (RingHom.id F) (fepomepG n F) e with hestar
    have hGdet : IsUnit (fepomepG n F).det := fepomep_isUnit_det n
    have hMdet : IsUnit M.det :=
      Matrix.isUnits_det_units (fepomepJ n F (w : ↥(spinGroup (fepomepQ n F))))
    have hMiso : Matrix.transpose M * fepomepG n F * M = fepomepG n F := by
      simpa only [fepomepG] using
        fepomep_isometry_of_quad (fepomepQ n F) M
          (Spin.spinMatrix_mem (fepomepQ n F)
            (w : ↥(spinGroup (fepomepQ n F))))
    have hMe : M * e = e := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      have hmem : Matrix.mulVec e v ∈ W := by
        rw [hW]
        exact ⟨v, rfl⟩
      have h := hρ w ⟨Matrix.mulVec e v, hmem⟩
      rw [hw] at h
      change Matrix.mulVec (M * e) v = Matrix.mulVec e v
      rw [← Matrix.mulVec_mulVec v M e]
      exact h.symm
    have hcomm : M * e = e * M :=
      (fepomep_blockCentralizer_commute_adjoin n hn S hSU hS hε w he.1).eq
    have heM : e * M = e := by rw [← hcomm, hMe]
    have hGest : fepomepG n F * estar = Matrix.transpose e * fepomepG n F := by
      rw [hestar, formAdj]
      have hmap : e.map (⇑(RingHom.id F)) = e := by
        ext i j
        simp
      rw [hmap]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv (fepomepG n F) hGdet, Matrix.one_mul]
    have hMest : M * estar = estar :=
      fepomep_fixes_star_of_isometry hGdet hMdet hMiso hMe heM hGest
    have hfix : M * (1 - ε) = 1 - ε :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp w.2)).2
    have hsum_add : e + estar + (1 - ε) = 1 := by rw [← hsum]; abel
    calc M = M * 1 := (Matrix.mul_one M).symm
      _ = M * (e + estar + (1 - ε)) := by rw [hsum_add]
      _ = M * e + M * estar + M * (1 - ε) := by rw [Matrix.mul_add, Matrix.mul_add]
      _ = e + estar + (1 - ε) := by rw [hMe, hMest, hfix]
      _ = 1 := hsum_add
  intro u v huv
  have h1 : (u * v⁻¹ : glBlockCentralizer (fepomepJ n F) S ε) = 1 := by
    have hw : ρ (u * v⁻¹) = 1 := by
      rw [map_mul, map_inv, huv, mul_inv_cancel]
    have hM := hmatrix (u * v⁻¹) hw
    have hJ1 : fepomepJ n F
        ((u * v⁻¹ : glBlockCentralizer (fepomepJ n F) S ε) :
          ↥(spinGroup (fepomepQ n F))) = 1 :=
      Units.ext (by simpa using hM)
    have hker : ((u * v⁻¹ : glBlockCentralizer (fepomepJ n F) S ε) :
        ↥(spinGroup (fepomepQ n F))) ∈ (fepomepJ n F).ker :=
      MonoidHom.mem_ker.mpr hJ1
    rw [show (fepomepJ n F).ker = ⊥ from
      Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero F 2)] at hker
    exact Subtype.ext (Subgroup.mem_bot.mp hker)
  exact mul_inv_eq_one.mp h1

private noncomputable def fepomep_dualPair_pairingMap (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (e : Matrix (fepomepι n) (fepomepι n) F)
    (W : Submodule F (fepomepι n → F)) :
    ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))) →ₗ[F]
      Module.Dual F W where
  toFun y := (QuadraticMap.polarBilin (fepomepQ n F) (y : fepomepι n → F)).comp W.subtype
  map_add' y₁ y₂ := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.coe_subtype,
      Submodule.coe_add]
    rw [map_add, LinearMap.add_apply]
  map_smul' c y := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_subtype,
      Submodule.coe_smul]
    rw [map_smul, LinearMap.smul_apply]
    rfl

private lemma fepomep_dualPair_pairingMap_apply (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (e : Matrix (fepomepι n) (fepomepι n) F)
    (W : Submodule F (fepomepι n → F))
    (y : ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))))
    (x : W) :
    fepomep_dualPair_pairingMap n e W y x =
      QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F) := by
  rw [show fepomep_dualPair_pairingMap n e W y x =
      (QuadraticMap.polarBilin (fepomepQ n F) (y : fepomepι n → F))
        (x : fepomepι n → F) from rfl]
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

private lemma fepomep_polar_formAdj_apply (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Matrix (fepomepι n) (fepomepι n) F) (x y : fepomepι n → F) :
    QuadraticMap.polar (fepomepQ n F) x
        (Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) A) y) =
      QuadraticMap.polar (fepomepQ n F) (Matrix.mulVec A x) y := by
  rw [fepomep_polar_eq_dot, fepomep_polar_eq_dot]
  change dotProduct x ((fepomepG n F).mulVec
        ((formAdj (RingHom.id F) (fepomepG n F) A).mulVec y)) =
      dotProduct (A.mulVec x) ((fepomepG n F).mulVec y)
  have hmap : A.map (⇑(RingHom.id F)) = A := by ext i j; simp
  rw [formAdj, hmap, Matrix.mulVec_mulVec]
  have hG : fepomepG n F *
      ((fepomepG n F)⁻¹ * A.transpose * fepomepG n F) =
      A.transpose * fepomepG n F := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv (fepomepG n F)
      (fepomep_isUnit_det n ), Matrix.one_mul]
  rw [hG, ← Matrix.mulVec_mulVec y A.transpose (fepomepG n F),
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

private lemma fepomep_dualPair_pairing_injective (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e)) :
    Function.Injective (fepomep_dualPair_pairingMap n e W) := by
  have hker : ∀ y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))),
      fepomep_dualPair_pairingMap n e W y = 0 → y = 0 := by
    intro y hy
    obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
      fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
    have hBnd : (QuadraticMap.polarBilin (fepomepQ n F)).Nondegenerate :=
      Spin.nondegenerate_polarBilin_quadPlus n F
    have hw : Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e)
        (y : fepomepι n → F) = 0 := by
      have hzero : (LinearMap.BilinForm.toDual
          (QuadraticMap.polarBilin (fepomepQ n F)) hBnd)
          (Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e)
            (y : fepomepι n → F)) = 0 := by
        apply LinearMap.ext
        intro z
        rw [LinearMap.BilinForm.toDual_def, QuadraticMap.polarBilin_apply_apply,
          QuadraticMap.polar_comm, fepomep_polar_formAdj_apply n e z y]
        have hz : Matrix.mulVecLin e z ∈ W := by rw [hW]; exact ⟨z, rfl⟩
        have h2 := congrArg (fun (f : Module.Dual F W) =>
          f ⟨Matrix.mulVecLin e z, hz⟩) hy
        rw [fepomep_dualPair_pairingMap_apply n e W y
          ⟨Matrix.mulVecLin e z, hz⟩] at h2
        simpa using h2
      exact (LinearMap.BilinForm.toDual
        (QuadraticMap.polarBilin (fepomepQ n F)) hBnd).injective
        (by rw [hzero, map_zero])
    have hyw : Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e)
        (y : fepomepι n → F) = (y : fepomepι n → F) := by
      obtain ⟨y', hy'⟩ := y.2
      rw [← hy', Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hestidem]
    apply Subtype.ext
    rw [← hyw, hw]
    rfl
  intro y1 y2 h12
  have hsub : y1 - y2 = 0 := hker (y1 - y2) (by rw [map_sub, h12, sub_self])
  rwa [sub_eq_zero] at hsub

private lemma fepomep_dualPair_pairing_surjective (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e)) :
    Function.Surjective (fepomep_dualPair_pairingMap n e W) := by
  intro φ
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  have hBnd : (QuadraticMap.polarBilin (fepomepQ n F)).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus n F
  let Ψ : (fepomepι n → F) ≃ₗ[F] Module.Dual F (fepomepι n → F) :=
    LinearMap.BilinForm.toDual (QuadraticMap.polarBilin (fepomepQ n F)) hBnd
  let ψ : Module.Dual F (fepomepι n → F) :=
    φ.comp (LinearMap.codRestrict W (Matrix.mulVecLin e)
      (fun z => by rw [hW]; exact ⟨z, rfl⟩))
  let y0 : fepomepι n → F := Ψ.symm ψ
  refine ⟨⟨Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e) y0, ⟨y0, rfl⟩⟩, ?_⟩
  have hΨ : Ψ y0 = ψ := LinearEquiv.apply_symm_apply Ψ ψ
  apply LinearMap.ext
  intro x
  rw [fepomep_dualPair_pairingMap_apply n e W
    ⟨Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e) y0, ⟨y0, rfl⟩⟩ x]
  rw [fepomep_polar_formAdj_apply n e x y0, QuadraticMap.polar_comm]
  have h1 := congrArg (fun (f : Module.Dual F (fepomepι n → F)) =>
    f (Matrix.mulVecLin e x)) hΨ
  rw [LinearMap.BilinForm.toDual_def, QuadraticMap.polarBilin_apply_apply,
    Matrix.mulVecLin_apply] at h1
  rw [h1]
  have hex : Matrix.mulVec e (x : fepomepι n → F) = (x : fepomepι n → F) := by
    have hxmem : (x : fepomepι n → F) ∈ LinearMap.range (Matrix.mulVecLin e) := by
      rw [← hW]; exact x.2
    obtain ⟨x', hx'⟩ := hxmem
    rw [← hx', Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he.2.1]
  have hψ : ψ (Matrix.mulVec e x) = φ x := by
    change φ ((LinearMap.codRestrict W (Matrix.mulVecLin e)
      (fun z => by rw [hW]; exact ⟨z, rfl⟩)) (Matrix.mulVec e x)) = φ x
    congr 1
    apply Subtype.ext
    rw [LinearMap.codRestrict_apply]
    change Matrix.mulVecLin e (Matrix.mulVec e x) = (x : fepomepι n → F)
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he.2.1, hex]
  exact hψ

private lemma fepomep_dualPair_pairing_bijective (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e)) :
    Function.Bijective (fepomep_dualPair_pairingMap n e W) :=
  ⟨fepomep_dualPair_pairing_injective n hn S hSU hS hε he heε hne W hW,
    fepomep_dualPair_pairing_surjective n hn S hSU hS hε he heε hne W hW⟩

private lemma fepomep_dualPair_pairing_dualEquiv (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e)) :
    ∃ η : ↥(LinearMap.range (Matrix.mulVecLin
          (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F] Module.Dual F W,
      ∀ (y : ↥(LinearMap.range (Matrix.mulVecLin
            (formAdj (RingHom.id F) (fepomepG n F) e)))) (x : W),
        η y x = QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F)
          (y : fepomepι n → F) := by
  refine ⟨LinearEquiv.ofBijective (fepomep_dualPair_pairingMap n e W)
    (fepomep_dualPair_pairing_bijective n hn S hSU hS hε he heε hne W hW), ?_⟩
  intro y x
  exact fepomep_dualPair_pairingMap_apply n e W y x

private lemma fepomep_dualPair_levi_dual (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W) :
    ∃ gstar : ↥(LinearMap.range (Matrix.mulVecLin
          (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
        ↥(LinearMap.range (Matrix.mulVecLin
          (formAdj (RingHom.id F) (fepomepG n F) e))),
      (∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
          (formAdj (RingHom.id F) (fepomepG n F) e)))),
        QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F)
            (gstar y : fepomepι n → F) =
          QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F)
            (y : fepomepι n → F)) := by
  obtain ⟨η, hη⟩ :=
    fepomep_dualPair_pairing_dualEquiv n hn S hSU hS hε he heε hne W hW
  let gF : W ≃ₗ[F] W := g.restrictScalars F
  refine ⟨η.trans ((gF.symm).dualMap.trans η.symm), ?_⟩
  intro x y
  have h1 : η ((η.trans ((gF.symm).dualMap.trans η.symm)) y) =
      (gF.symm).dualMap (η y) := by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  calc QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F)
        (((η.trans ((gF.symm).dualMap.trans η.symm)) y) : fepomepι n → F)
      = η ((η.trans ((gF.symm).dualMap.trans η.symm)) y) (g x) :=
          (hη ((η.trans ((gF.symm).dualMap.trans η.symm)) y) (g x)).symm
    _ = ((gF.symm).dualMap (η y)) (g x) := by rw [h1]
    _ = (η y) (gF.symm (g x)) := LinearEquiv.dualMap_apply _ _ _
    _ = (η y) x := by
          congr 1
          exact LinearEquiv.symm_apply_apply gF x
    _ = QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F)
          (y : fepomepι n → F) := hη y x

private lemma fepomep_polar_eps_compl (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    {ε : Matrix (fepomepι n) (fepomepι n) F} (hεidem : IsIdempotentElem ε)
    (hεadj : formAdj (RingHom.id F) (fepomepG n F) ε = ε)
    (x y : fepomepι n → F) :
    QuadraticMap.polar (fepomepQ n F) (Matrix.mulVec ε x)
        (Matrix.mulVec (1 - ε) y) = 0 := by
  rw [← fepomep_polar_formAdj_apply n ε x (Matrix.mulVec (1 - ε) y), hεadj]
  have h : Matrix.mulVec ε (Matrix.mulVec (1 - ε) y) = 0 := by
    rw [Matrix.mulVec_mulVec]
    have hmul : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, hεidem, sub_self]
    rw [hmul, Matrix.zero_mulVec]
  rw [h]
  simp

private lemma fepomep_dualPair_eps_comm (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (fepomepι n) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (fepomepι n) (fepomepι n) F} (hεA : ε ∈ fepomepA n F S) :
    ∀ s ∈ S, (s : Matrix (fepomepι n) (fepomepι n) F) * ε =
      ε * (s : Matrix (fepomepι n) (fepomepι n) F) := by
  intro s hs
  exact (fepomep_adjoin_comm hS (s : Matrix (fepomepι n) (fepomepι n) F)
    (Algebra.subset_adjoin ⟨s, hs, rfl⟩) ε hεA).eq

private lemma fepomep_isCompl_eps_compl (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    {ε : Matrix (fepomepι n) (fepomepι n) F} (hεidem : IsIdempotentElem ε) :
    IsCompl (LinearMap.range (Matrix.mulVecLin ε))
      (LinearMap.range (Matrix.mulVecLin (1 - ε))) := by
  have hidem : IsIdempotentElem (Matrix.mulVecLin ε) := by
    change (Matrix.mulVecLin ε).comp (Matrix.mulVecLin ε) = Matrix.mulVecLin ε
    rw [← Matrix.mulVecLin_mul, hεidem]
  have hsub : Matrix.mulVecLin (1 - ε) = 1 - Matrix.mulVecLin ε := by
    ext v
    simp [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hsub, ← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hidem]
  exact LinearMap.IsIdempotentElem.isCompl hidem

private lemma fepomep_trace_quadratic_zero {F K : Type} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [Algebra F K] (g : K → F) (hg0 : g 0 = 0)
    (hgadd : ∀ μ ν : K, g (μ + ν) = g μ + g ν)
    (hgsmul : ∀ (c : F) (μ : K), g (c • μ) = c ^ 2 * g μ)
    (lam : K) (hlam : lam ≠ 1) (hinv : ∀ μ : K, g (lam * μ) = g μ) :
    g 1 = 0 := by
  classical
  have hfc : ringChar F = 2 := (ringChar.eq_iff).mpr (inferInstance : CharP F 2)
  let L : K → F := fun μ => Classical.choose (FiniteField.isSquare_of_char_two hfc (g μ))
  have hL : ∀ μ : K, (L μ) ^ 2 = g μ := fun μ => by
    rw [pow_two]
    exact (Classical.choose_spec (FiniteField.isSquare_of_char_two hfc (g μ))).symm
  have hLadd : ∀ μ ν : K, L (μ + ν) = L μ + L ν := by
    intro μ ν
    apply CharTwo.sq_inj.mp
    rw [hL (μ + ν), hgadd μ ν, CharTwo.add_sq, ← hL μ, ← hL ν]
  have hLsmul : ∀ (c : F) (μ : K), L (c • μ) = c * L μ := by
    intro c μ
    apply CharTwo.sq_inj.mp
    rw [hL (c • μ), hgsmul c μ, mul_pow, ← hL μ]
  have hLinv : ∀ μ : K, L (lam * μ) = L μ := by
    intro μ
    apply CharTwo.sq_inj.mp
    rw [hL (lam * μ), hinv μ, ← hL μ]
  let Lm : K →ₗ[F] F :=
    { toFun := L
      map_add' := hLadd
      map_smul' := fun c μ => by simpa using hLsmul c μ }
  have hnd : (Algebra.traceForm F K).Nondegenerate := traceForm_nondegenerate F K
  obtain ⟨κ, hκ⟩ : ∃ κ : K,
      (LinearMap.BilinForm.toDual (Algebra.traceForm F K) hnd) κ = Lm :=
    ⟨(LinearMap.BilinForm.toDual (Algebra.traceForm F K) hnd).symm Lm,
      LinearEquiv.apply_symm_apply _ _⟩
  have hκμ : ∀ μ : K, L μ = Algebra.trace F K (κ * μ) := by
    intro μ
    have h1 : (LinearMap.BilinForm.toDual (Algebra.traceForm F K) hnd) κ μ = Lm μ :=
      LinearMap.ext_iff.mp hκ μ
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h1
    exact h1.symm
  have hklam : ∀ μ : K, Algebra.trace F K (κ * (lam * μ)) = Algebra.trace F K (κ * μ) := by
    intro μ
    rw [← hκμ (lam * μ), ← hκμ μ, hLinv μ]
  have hzero : κ * (lam - 1) = 0 := by
    apply hnd.1
    intro μ
    have h1 := hklam μ
    rw [Algebra.traceForm_apply,
      show (κ * (lam - 1)) * μ = κ * (lam * μ) - κ * μ by ring,
      map_sub, h1, sub_self]
  have hk0 : κ = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hlam
  have hL1 : L 1 = 0 := by
    rw [hκμ 1, hk0, zero_mul, map_zero]
  rw [← hL 1, hL1]
  simp

private lemma fepomep_block_quad_zero (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∀ w : W, fepomepQ n F (w : fepomepι n → F) = 0 := by
  classical
  obtain ⟨_, _, _, _, _, hzero1, _, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  let sA : (s : GL (fepomepι n) F) → s ∈ S → fepomepA n F S :=
    fun s hs => ⟨(s : Matrix (fepomepι n) (fepomepι n) F),
      Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
  have hexlam : ∃ (s : GL (fepomepι n) F) (hs : s ∈ S), π (sA s hs) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hP : ∀ a : fepomepA n F S, ∃ f : F, π a = algebraMap F K f := by
      intro a
      refine Algebra.adjoin_induction
        (p := fun x hx => ∃ f : F, π ⟨x, hx⟩ = algebraMap F K f) ?_ ?_ ?_ ?_
        (show (a : Matrix (fepomepι n) (fepomepι n) F) ∈
          Algebra.adjoin F (Units.val '' S) from a.2)
      · rintro x ⟨s, hs, rfl⟩
        exact ⟨1, by change π (sA s hs) = algebraMap F K 1; rw [hcon s hs, map_one]⟩
      · intro r
        exact ⟨r, π.commutes r⟩
      · rintro x y hx hy ⟨f, hf⟩ ⟨g, hg⟩
        refine ⟨f + g, ?_⟩
        change π (⟨x, hx⟩ + ⟨y, hy⟩) = algebraMap F K (f + g)
        rw [map_add, hf, hg, map_add]
      · rintro x y hx hy ⟨f, hf⟩ ⟨g, hg⟩
        refine ⟨f * g, ?_⟩
        change π (⟨x, hx⟩ * ⟨y, hy⟩) = algebraMap F K (f * g)
        rw [map_mul, hf, hg, map_mul]
    have hrange : LinearMap.range (Algebra.linearMap F K) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro k
      obtain ⟨a, rfl⟩ := hπsurj k
      obtain ⟨f, hf⟩ := hP a
      exact ⟨f, hf.symm⟩
    have hle : Module.finrank F K ≤ 1 := by
      have h1 : Module.finrank F (LinearMap.range (Algebra.linearMap F K)) ≤
          Module.finrank F F := LinearMap.finrank_range_le (Algebra.linearMap F K)
      rw [hrange, Module.finrank_self] at h1
      simpa using h1
    have hge : 2 ≤ Module.finrank F K := by rw [hπdeg]; exact hdeg
    omega
  obtain ⟨s, hs, hpi⟩ := hexlam
  intro w
  let g : K → F := fun μ =>
    fepomepQ n F (((μ • w : W) : fepomepι n → F))
  have hmem : ∀ u : W, (u : fepomepι n → F) ∈
      LinearMap.range (Matrix.mulVecLin e) := by
    intro u; rw [← hW]; exact u.2
  have hfix : ∀ u : W, Matrix.mulVec e (u : fepomepι n → F) = (u : fepomepι n → F) := by
    intro u
    have h2 : Matrix.mulVecLin e (u : fepomepι n → F) = (u : fepomepι n → F) := by
      obtain ⟨x, hx⟩ := hmem u
      rw [← hx]
      show Matrix.mulVecLin e (Matrix.mulVecLin e x) = Matrix.mulVecLin e x
      rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, he.2.1.eq]
    rwa [Matrix.mulVecLin_apply] at h2
  have hBiso : ∀ u v : W,
      QuadraticMap.polar (fepomepQ n F) (u : fepomepι n → F)
        (v : fepomepι n → F) = 0 := by
    intro u v
    have h := fepomep_polar_formAdj_apply n e (u : fepomepι n → F) (v : fepomepι n → F)
    rw [hfix u] at h
    have hz : Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e)
        (Matrix.mulVec e (v : fepomepι n → F)) = 0 := by
      rw [Matrix.mulVec_mulVec, hzero1, Matrix.zero_mulVec]
    rw [hfix v] at hz
    rw [hz] at h
    simpa using h.symm
  have hg0 : g 0 = 0 := by
    change fepomepQ n F ((((0 : K) • w : W) : fepomepι n → F)) = 0
    rw [zero_smul, Submodule.coe_zero, map_zero]
  have hgadd : ∀ μ ν : K, g (μ + ν) = g μ + g ν := by
    intro μ ν
    change fepomepQ n F ((((μ + ν) • w : W) : fepomepι n → F)) =
      fepomepQ n F (((μ • w : W) : fepomepι n → F)) +
        fepomepQ n F (((ν • w : W) : fepomepι n → F))
    rw [add_smul, Submodule.coe_add, QuadraticMap.map_add (fepomepQ n F),
      hBiso (μ • w) (ν • w), add_zero]
  have hgsmul : ∀ (c : F) (μ : K), g (c • μ) = c ^ 2 * g μ := by
    intro c μ
    change fepomepQ n F ((((c • μ) • w : W) : fepomepι n → F)) =
      c ^ 2 * fepomepQ n F (((μ • w : W) : fepomepι n → F))
    rw [smul_assoc, Submodule.coe_smul,
      QuadraticMap.map_smul (fepomepQ n F) c, smul_eq_mul]
    ring
  have hinv : ∀ μ : K, g (π (sA s hs) * μ) = g μ := by
    intro μ
    change fepomepQ n F ((((π (sA s hs) * μ) • w : W) : fepomepι n → F)) =
      fepomepQ n F (((μ • w : W) : fepomepι n → F))
    rw [mul_smul, hK (sA s hs) (μ • w)]
    obtain ⟨x, hx⟩ := hSU s hs
    have hsM : (s : Matrix (fepomepι n) (fepomepι n) F) =
        (Spin.spinMatrix (fepomepQ n F) x :
          Matrix (fepomepι n) (fepomepι n) F) :=
      congrArg (fun u : GL (fepomepι n) F => (u : Matrix (fepomepι n) (fepomepι n) F))
        hx.symm
    change (fepomepQ n F)
        (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
          ((μ • w : W) : fepomepι n → F)) =
      (fepomepQ n F) ((μ • w : W) : fepomepι n → F)
    rw [hsM]
    exact Spin.spinMatrix_mem (fepomepQ n F) x ((μ • w : W) : fepomepι n → F)
  have hg1 := fepomep_trace_quadratic_zero g hg0 hgadd hgsmul (π (sA s hs)) hpi hinv
  change fepomepQ n F ((((1 : K) • w : W) : fepomepι n → F)) = 0 at hg1
  rwa [one_smul] at hg1

private lemma fepomep_isCompl_e_estar (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε) :
    IsCompl
      (Submodule.comap (LinearMap.range (Matrix.mulVecLin ε)).subtype
        (LinearMap.range (Matrix.mulVecLin e)))
      (Submodule.comap (LinearMap.range (Matrix.mulVecLin ε)).subtype
        (LinearMap.range (Matrix.mulVecLin
          (formAdj (RingHom.id F) (fepomepG n F) e)))) := by
  classical
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  have hεidem : IsIdempotentElem ε := hε.2.1
  have heidem : IsIdempotentElem e := he.2.1
  have hcommεe : Commute ε e := fepomep_adjoin_comm hS ε hε.1 e he.1
  have hcommεst : Commute ε (formAdj (RingHom.id F) (fepomepG n F) e) :=
    fepomep_adjoin_comm hS ε hε.1 _ hestA
  have hεe : ε * e = e := by rw [hcommεe.eq, heε]
  have hεst : ε * (formAdj (RingHom.id F) (fepomepG n F) e) =
      formAdj (RingHom.id F) (fepomepG n F) e := by rw [hcommεst.eq, hestε]
  have hdisj : LinearMap.range (Matrix.mulVecLin e) ⊓
      LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hve, hvst⟩ := hv
    obtain ⟨a, ha⟩ := hve
    obtain ⟨b, hb⟩ := hvst
    have h1 : Matrix.mulVec e v = v := by
      rw [← ha, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, heidem.eq]
    have h2 : Matrix.mulVec e v = 0 := by
      rw [← hb, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hzero2, Matrix.zero_mulVec]
    rw [Submodule.mem_bot, ← h1, h2]
  rw [isCompl_iff]
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxe hxst
    rw [Submodule.mem_comap] at hxe hxst
    have hxbot : (x : fepomepι n → F) ∈
        LinearMap.range (Matrix.mulVecLin e) ⊓
          LinearMap.range (Matrix.mulVecLin
            (formAdj (RingHom.id F) (fepomepG n F) e)) := ⟨hxe, hxst⟩
    exact Subtype.ext (by simpa [Submodule.mem_bot] using ((eq_bot_iff.mp hdisj) hxbot))
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    rw [Submodule.mem_sup]
    have hxP1 : Matrix.mulVec e (x : fepomepι n → F) ∈ LinearMap.range (Matrix.mulVecLin ε) := by
      refine ⟨Matrix.mulVec e (x : fepomepι n → F), ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεe]
    have hxP2 : Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e)
        (x : fepomepι n → F) ∈ LinearMap.range (Matrix.mulVecLin ε) := by
      refine ⟨Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e)
        (x : fepomepι n → F), ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεst]
    have hxR1 : (⟨Matrix.mulVec e (x : fepomepι n → F), hxP1⟩ :
          ↥(LinearMap.range (Matrix.mulVecLin ε))) ∈
        Submodule.comap (LinearMap.range (Matrix.mulVecLin ε)).subtype
          (LinearMap.range (Matrix.mulVecLin e)) := by
      rw [Submodule.mem_comap]
      exact ⟨(x : fepomepι n → F), by rw [Matrix.mulVecLin_apply]; rfl⟩
    have hxR2 : (⟨Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e)
          (x : fepomepι n → F), hxP2⟩ :
          ↥(LinearMap.range (Matrix.mulVecLin ε))) ∈
        Submodule.comap (LinearMap.range (Matrix.mulVecLin ε)).subtype
          (LinearMap.range (Matrix.mulVecLin
            (formAdj (RingHom.id F) (fepomepG n F) e))) := by
      rw [Submodule.mem_comap]
      exact ⟨(x : fepomepι n → F), by rw [Matrix.mulVecLin_apply]; rfl⟩
    refine ⟨⟨Matrix.mulVec e (x : fepomepι n → F), hxP1⟩, hxR1,
      ⟨Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e)
          (x : fepomepι n → F), hxP2⟩, hxR2, ?_⟩
    apply Subtype.ext
    show Matrix.mulVec e (x : fepomepι n → F) +
        Matrix.mulVec (formAdj (RingHom.id F) (fepomepG n F) e)
          (x : fepomepι n → F) = (x : fepomepι n → F)
    rw [← Matrix.add_mulVec, ← hsum]
    obtain ⟨w, hw⟩ := x.2
    rw [← hw, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεidem.eq]

private lemma fepomep_formAdj_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Matrix ι ι F) : formAdj (RingHom.id F) G 0 = 0 := by
  unfold formAdj
  simp

private noncomputable def fepomep_formAdjAlgEquiv (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    fepomepA n F S ≃ₐ[F] fepomepA n F S := by
  classical
  let A := fepomepA n F S
  have hG : IsUnit (fepomepG n F).det := fepomep_isUnit_det n
  have hGh : Matrix.transpose ((fepomepG n F).map (RingHom.id F)) =
      fepomepG n F := by
    rw [show (fepomepG n F).map (RingHom.id F) = fepomepG n F from rfl]
    exact fepomep_transpose_G n F
  have hSG : ∀ s ∈ S, Matrix.transpose
      ((s : Matrix (fepomepι n) (fepomepι n) F).map (RingHom.id F)) * fepomepG n F *
      (s : Matrix (fepomepι n) (fepomepι n) F) = fepomepG n F := by
    intro s hs
    obtain ⟨x, rfl⟩ := hSU s hs
    rw [show (((fepomepJ n F x : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F)).map (RingHom.id F) =
        ((fepomepJ n F x : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) from rfl]
    exact fepomep_isometry_of_quad (fepomepQ n F)
      ((fepomepJ n F x : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)
      (Spin.spinMatrix_mem (fepomepQ n F) x)
  have hmem : ∀ a : A,
      formAdj (RingHom.id F) (fepomepG n F) (a : Matrix (fepomepι n) (fepomepι n) F) ∈ A :=
    fun a => Geo.formAdj_mem_adjoin (RingHom.id F) hG hSG a.2
  have hinvol : ∀ a : A, formAdj (RingHom.id F) (fepomepG n F)
      (formAdj (RingHom.id F) (fepomepG n F)
        (a : Matrix (fepomepι n) (fepomepι n) F)) =
      (a : Matrix (fepomepι n) (fepomepι n) F) :=
    fun a => Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh
      (a : Matrix (fepomepι n) (fepomepι n) F)
  have hcommP : (Units.val '' S : Set (Matrix (fepomepι n) (fepomepι n) F)).Pairwise Commute := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ _
    exact (hS s hs s' hs').map (Units.coeHom (Matrix (fepomepι n) (fepomepι n) F))
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hcommP
  have hcommM : ∀ a b : A, Commute (a : Matrix (fepomepι n) (fepomepι n) F)
      (b : Matrix (fepomepι n) (fepomepι n) F) :=
    fun a b => fepomep_adjoin_comm hS a a.2 b b.2
  let τ : A →ₐ[F] A :=
  { toFun := fun a =>
      ⟨formAdj (RingHom.id F) (fepomepG n F) (a : Matrix (fepomepι n) (fepomepι n) F),
        hmem a⟩
    map_one' := by
      apply Subtype.ext
      exact Geo.formAdj_one (RingHom.id F) hG
    map_mul' := by
      intro a b
      apply Subtype.ext
      change formAdj (RingHom.id F) (fepomepG n F)
          ((a : Matrix (fepomepι n) (fepomepι n) F) *
            (b : Matrix (fepomepι n) (fepomepι n) F)) =
        formAdj (RingHom.id F) (fepomepG n F)
            (a : Matrix (fepomepι n) (fepomepι n) F) *
          formAdj (RingHom.id F) (fepomepG n F)
            (b : Matrix (fepomepι n) (fepomepι n) F)
      rw [Geo.formAdj_mul (RingHom.id F) hG]
      exact (hcommM ⟨formAdj (RingHom.id F) (fepomepG n F)
            (b : Matrix (fepomepι n) (fepomepι n) F), hmem b⟩
          ⟨formAdj (RingHom.id F) (fepomepG n F)
            (a : Matrix (fepomepι n) (fepomepι n) F), hmem a⟩).eq
    map_zero' := by
      apply Subtype.ext
      exact fepomep_formAdj_zero (fepomepG n F)
    map_add' := by
      intro a b
      apply Subtype.ext
      exact Geo.formAdj_add (RingHom.id F) (fepomepG n F)
        (a : Matrix (fepomepι n) (fepomepι n) F) (b : Matrix (fepomepι n) (fepomepι n) F)
    commutes' := by
      intro c
      apply Subtype.ext
      change formAdj (RingHom.id F) (fepomepG n F)
          (algebraMap F (Matrix (fepomepι n) (fepomepι n) F) c) =
        algebraMap F (Matrix (fepomepι n) (fepomepι n) F) c
      rw [Algebra.algebraMap_eq_smul_one, Geo.formAdj_smul, Geo.formAdj_one (RingHom.id F) hG]
      rfl }
  have hinj : Function.Injective τ := by
    intro a b hab
    have h := congrArg (fun u : A => (u : Matrix (fepomepι n) (fepomepι n) F)) hab
    have h2 := congrArg (formAdj (RingHom.id F) (fepomepG n F)) h
    change formAdj (RingHom.id F) (fepomepG n F)
        (formAdj (RingHom.id F) (fepomepG n F)
          (a : Matrix (fepomepι n) (fepomepι n) F)) =
      formAdj (RingHom.id F) (fepomepG n F)
        (formAdj (RingHom.id F) (fepomepG n F)
          (b : Matrix (fepomepι n) (fepomepι n) F)) at h2
    rw [hinvol a, hinvol b] at h2
    exact Subtype.ext h2
  exact AlgEquiv.ofBijective τ ⟨hinj, fun b => ⟨τ b, by
    apply Subtype.ext
    exact hinvol b⟩⟩

private lemma fepomep_estar_prim (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε) :
    IsPrimIdemIn (fepomepA n F S)
      (formAdj (RingHom.id F) (fepomepG n F) e) := by
  classical
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  have hG : IsUnit (fepomepG n F).det := fepomep_isUnit_det n
  have hGh : Matrix.transpose ((fepomepG n F).map (RingHom.id F)) =
      fepomepG n F := by
    rw [show (fepomepG n F).map (RingHom.id F) = fepomepG n F from rfl]
    exact fepomep_transpose_G n F
  have hSG : ∀ s ∈ S, Matrix.transpose
      ((s : Matrix (fepomepι n) (fepomepι n) F).map (RingHom.id F)) * fepomepG n F *
      (s : Matrix (fepomepι n) (fepomepι n) F) = fepomepG n F := by
    intro s hs
    obtain ⟨x, rfl⟩ := hSU s hs
    rw [show (((fepomepJ n F x : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F)).map (RingHom.id F) =
        ((fepomepJ n F x : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) from rfl]
    exact fepomep_isometry_of_quad (fepomepQ n F)
      ((fepomepJ n F x : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)
      (Spin.spinMatrix_mem (fepomepQ n F) x)
  refine ⟨hestA, hestidem, ?_, ?_⟩
  · intro h0
    exact hne (by simpa [hsum, h0])
  · intro f hfA hfidem hfe
    have hfadjA : formAdj (RingHom.id F) (fepomepG n F) f ∈ fepomepA n F S :=
      Geo.formAdj_mem_adjoin (RingHom.id F) hG hSG hfA
    have hfadjidem : IsIdempotentElem (formAdj (RingHom.id F) (fepomepG n F) f) := by
      rw [isIdempotentElem_iff] at hfidem ⊢
      rw [← Geo.formAdj_mul (RingHom.id F) hG f f, hfidem]
    have hfadj_e : formAdj (RingHom.id F) (fepomepG n F) f * e =
        formAdj (RingHom.id F) (fepomepG n F) f := by
      have h := congrArg (formAdj (RingHom.id F) (fepomepG n F)) hfe
      rw [Geo.formAdj_mul (RingHom.id F) hG, hdouble] at h
      simpa [h] using (fepomep_adjoin_comm hS _ hfadjA e he.1).eq
    rcases he.2.2.2 (formAdj (RingHom.id F) (fepomepG n F) f) hfadjA hfadjidem hfadj_e
      with h0 | hee
    · left
      have h := congrArg (formAdj (RingHom.id F) (fepomepG n F)) h0
      rw [Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh f,
        fepomep_formAdj_zero (fepomepG n F)] at h
      exact h
    · right
      have h := congrArg (formAdj (RingHom.id F) (fepomepG n F)) hee
      rw [Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh f] at h
      exact h

private noncomputable def fepomep_formAdjLinEquiv (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] :
    Matrix (fepomepι n) (fepomepι n) F ≃ₗ[F] Matrix (fepomepι n) (fepomepι n) F := by
  classical
  have hG : IsUnit (fepomepG n F).det := fepomep_isUnit_det n
  have hGh : Matrix.transpose ((fepomepG n F).map (RingHom.id F)) =
      fepomepG n F := by
    rw [show (fepomepG n F).map (RingHom.id F) = fepomepG n F from rfl]
    exact fepomep_transpose_G n F
  exact
  { toFun := formAdj (RingHom.id F) (fepomepG n F)
    invFun := formAdj (RingHom.id F) (fepomepG n F)
    left_inv := fun a => Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh a
    right_inv := fun a => Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh a
    map_add' := fun a b => Geo.formAdj_add (RingHom.id F) (fepomepG n F) a b
    map_smul' := fun c a => Geo.formAdj_smul (RingHom.id F) (fepomepG n F) c a }

private lemma fepomep_blockDegree_formAdj (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (fepomepι n) (fepomepι n) F} (he : e ∈ fepomepA n F S) :
    blockDegree (fepomepA n F S) (formAdj (RingHom.id F) (fepomepG n F) e) =
      blockDegree (fepomepA n F S) e := by
  classical
  have hG : IsUnit (fepomepG n F).det := fepomep_isUnit_det n
  have hGh : Matrix.transpose ((fepomepG n F).map (RingHom.id F)) =
      fepomepG n F := by
    rw [show (fepomepG n F).map (RingHom.id F) = fepomepG n F from rfl]
    exact fepomep_transpose_G n F
  have hSG : ∀ s ∈ S, Matrix.transpose
      ((s : Matrix (fepomepι n) (fepomepι n) F).map (RingHom.id F)) * fepomepG n F *
      (s : Matrix (fepomepι n) (fepomepι n) F) = fepomepG n F := by
    intro s hs
    obtain ⟨x, rfl⟩ := hSU s hs
    rw [show (((fepomepJ n F x : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F)).map (RingHom.id F) =
        ((fepomepJ n F x : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) from rfl]
    exact fepomep_isometry_of_quad (fepomepQ n F)
      ((fepomepJ n F x : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)
      (Spin.spinMatrix_mem (fepomepQ n F) x)
  have hmemE : formAdj (RingHom.id F) (fepomepG n F) e ∈ fepomepA n F S :=
    Geo.formAdj_mem_adjoin (RingHom.id F) hG hSG he
  let τL := fepomep_formAdjLinEquiv (F := F) n
  have hSmap : (Subalgebra.toSubmodule (fepomepA n F S)).map
        (LinearMap.mulRight F (formAdj (RingHom.id F) (fepomepG n F) e)) =
      ((Subalgebra.toSubmodule (fepomepA n F S)).map (LinearMap.mulRight F e)).map
        τL.toLinearMap := by
    ext x
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨formAdj (RingHom.id F) (fepomepG n F) a * e,
        ⟨formAdj (RingHom.id F) (fepomepG n F) a,
          Geo.formAdj_mem_adjoin (RingHom.id F) hG hSG ha, rfl⟩, ?_⟩
      change formAdj (RingHom.id F) (fepomepG n F)
          (formAdj (RingHom.id F) (fepomepG n F) a * e) =
        a * formAdj (RingHom.id F) (fepomepG n F) e
      rw [Geo.formAdj_mul (RingHom.id F) hG,
        Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh a]
      exact (fepomep_adjoin_comm hS (formAdj (RingHom.id F) (fepomepG n F) e)
        hmemE a ha).eq
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨formAdj (RingHom.id F) (fepomepG n F) a,
        Geo.formAdj_mem_adjoin (RingHom.id F) hG hSG ha, ?_⟩
      change formAdj (RingHom.id F) (fepomepG n F) a *
          formAdj (RingHom.id F) (fepomepG n F) e =
        formAdj (RingHom.id F) (fepomepG n F) (a * e)
      rw [Geo.formAdj_mul (RingHom.id F) hG]
      exact (fepomep_adjoin_comm hS
        (formAdj (RingHom.id F) (fepomepG n F) a)
        (Geo.formAdj_mem_adjoin (RingHom.id F) hG hSG ha)
        (formAdj (RingHom.id F) (fepomepG n F) e) hmemE).eq
  unfold blockDegree
  rw [hSmap]
  exact LinearEquiv.finrank_map_eq (τL : Matrix (fepomepι n) (fepomepι n) F ≃ₗ[F]
    Matrix (fepomepι n) (fepomepι n) F) _

private lemma fepomep_star_block_quad_zero (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e) :
    ∀ y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))),
      fepomepQ n F (y : fepomepι n → F) = 0 := by
  classical
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  have hprim := fepomep_estar_prim n hn S hSU hS hε he heε hne
  have hdegEst : 2 ≤ blockDegree (fepomepA n F S)
      (formAdj (RingHom.id F) (fepomepG n F) e) := by
    rw [fepomep_blockDegree_formAdj n hn S hSU hS he.1]
    exact hdeg
  have hneEstEps : formAdj (RingHom.id F) (fepomepG n F) e ≠ ε := by
    intro h
    have h2 : ε = e + ε := hsum.trans (congrArg (fun x => e + x) h)
    have he0 : e = 0 := by simpa using (add_eq_right.mp h2.symm)
    exact he.2.2.1 he0
  have hG : IsUnit (fepomepG n F).det := fepomep_isUnit_det n
  have hGh : Matrix.transpose ((fepomepG n F).map (RingHom.id F)) =
      fepomepG n F := by
    rw [show (fepomepG n F).map (RingHom.id F) = fepomepG n F from rfl]
    exact fepomep_transpose_G n F
  have hSG : ∀ s ∈ S, Matrix.transpose
      ((s : Matrix (fepomepι n) (fepomepι n) F).map (RingHom.id F)) * fepomepG n F *
      (s : Matrix (fepomepι n) (fepomepι n) F) = fepomepG n F := by
    intro s hs
    obtain ⟨x, rfl⟩ := hSU s hs
    rw [show (((fepomepJ n F x : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F)).map (RingHom.id F) =
        ((fepomepJ n F x : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) from rfl]
    exact fepomep_isometry_of_quad (fepomepQ n F)
      ((fepomepJ n F x : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)
      (Spin.spinMatrix_mem (fepomepQ n F) x)
  let τe := fepomep_formAdjAlgEquiv n hn S hSU hS
  let π' : fepomepA n F S →ₐ[F] K := π.comp τe.toAlgHom
  have hπ'surj : Function.Surjective π' := hπsurj.comp τe.surjective
  have hπ'ker : ∀ a, π' a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) *
      formAdj (RingHom.id F) (fepomepG n F) e = 0 := by
    intro a
    rw [show π' a = π (τe a) from rfl, hπker]
    change formAdj (RingHom.id F) (fepomepG n F)
        (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0 ↔
      (a : Matrix (fepomepι n) (fepomepι n) F) *
        formAdj (RingHom.id F) (fepomepG n F) e = 0
    constructor
    · intro h
      have h1 : formAdj (RingHom.id F) (fepomepG n F)
          (formAdj (RingHom.id F) (fepomepG n F)
              (a : Matrix (fepomepι n) (fepomepι n) F) *
            (e : Matrix (fepomepι n) (fepomepι n) F)) =
          formAdj (RingHom.id F) (fepomepG n F)
            (0 : Matrix (fepomepι n) (fepomepι n) F) := by rw [h]
      rw [Geo.formAdj_mul (RingHom.id F) hG,
        Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh
          (a : Matrix (fepomepι n) (fepomepι n) F),
        fepomep_formAdj_zero (fepomepG n F)] at h1
      rwa [← (fepomep_adjoin_comm hS (a : Matrix (fepomepι n) (fepomepι n) F) a.2
        (formAdj (RingHom.id F) (fepomepG n F) e) hestA).eq] at h1
    · intro h
      have h1 : formAdj (RingHom.id F) (fepomepG n F)
          ((a : Matrix (fepomepι n) (fepomepι n) F) *
            formAdj (RingHom.id F) (fepomepG n F)
              (e : Matrix (fepomepι n) (fepomepι n) F)) =
          formAdj (RingHom.id F) (fepomepG n F)
            (0 : Matrix (fepomepι n) (fepomepι n) F) := by rw [h]
      rw [Geo.formAdj_mul (RingHom.id F) hG,
        Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh e,
        fepomep_formAdj_zero (fepomepG n F)] at h1
      rwa [(fepomep_adjoin_comm hS e he.1
        (formAdj (RingHom.id F) (fepomepG n F)
          (a : Matrix (fepomepι n) (fepomepι n) F))
        (Geo.formAdj_mem_adjoin (RingHom.id F) hG hSG a.2)).eq] at h1
  have hπ'deg : Module.finrank F K = blockDegree (fepomepA n F S)
      (formAdj (RingHom.id F) (fepomepG n F) e) := by
    rw [hπdeg, ← fepomep_blockDegree_formAdj n hn S hSU hS he.1]
  obtain ⟨W, hWne, hmod, htower, hWeq, hK'⟩ :=
    fepomep_blockKModule n S hS hprim K π' hπ'surj hπ'ker
  letI : Module K W := hmod
  letI : IsScalarTower F K W := htower
  intro y
  have hres := fepomep_block_quad_zero n hn S hSU hS hε hprim hestε hneEstEps hdegEst K π'
    hπ'surj hπ'ker hπ'deg W hWeq hK' ⟨y, by rw [hWeq]; exact y.2⟩
  simpa using hres

private lemma fepomep_levi_blockMap (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W)
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))) :
    ∃ gV : (fepomepι n → F) →ₗ[F] (fepomepι n → F),
      (∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v) ∧
      (∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F)) ∧
      (∀ y : ↥(LinearMap.range (Matrix.mulVecLin
            (formAdj (RingHom.id F) (fepomepG n F) e))),
        gV (y : fepomepι n → F) = (gstar y : fepomepι n → F)) := by
  classical
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  let est : Matrix (fepomepι n) (fepomepι n) F :=
    formAdj (RingHom.id F) (fepomepG n F) e
  let q : Submodule F (fepomepι n → F) := LinearMap.range (Matrix.mulVecLin est)
  have hεidem : IsIdempotentElem ε := hε.2.1
  have heidem : IsIdempotentElem e := he.2.1
  have honeSub : IsIdempotentElem (1 - ε) := hεidem.one_sub
  have hεe : ε * e = e := by
    rw [(fepomep_adjoin_comm hS ε hε.1 e he.1).eq, heε]
  have hεest : ε * est = est := by
    rw [(fepomep_adjoin_comm hS ε hε.1 est hestA).eq, hestε]
  have he_oneSub : e * (1 - ε) = 0 := by rw [mul_sub, mul_one, heε, sub_self]
  have hest_oneSub : est * (1 - ε) = 0 := by rw [mul_sub, mul_one, hestε, sub_self]
  let eToW : (fepomepι n → F) →ₗ[F] W :=
    (Matrix.mulVecLin e).codRestrict W (fun v => by rw [hW]; exact ⟨v, rfl⟩)
  let estToQ : (fepomepι n → F) →ₗ[F] q :=
    (Matrix.mulVecLin est).codRestrict q (fun v => ⟨v, rfl⟩)
  let gF : W ≃ₗ[F] W := g.restrictScalars F
  let gV : (fepomepι n → F) →ₗ[F] (fepomepι n → F) :=
    W.subtype.comp (gF.toLinearMap.comp eToW) +
      q.subtype.comp (gstar.toLinearMap.comp estToQ) +
      Matrix.mulVecLin (1 - ε)
  refine ⟨gV, ?_, ?_, ?_⟩
  · intro v
    have h1 : eToW (Matrix.mulVec (1 - ε) v) = 0 := by
      apply Subtype.ext
      change Matrix.mulVec e (Matrix.mulVec (1 - ε) v) = 0
      rw [Matrix.mulVec_mulVec, he_oneSub, Matrix.zero_mulVec]
    have h2 : estToQ (Matrix.mulVec (1 - ε) v) = 0 := by
      apply Subtype.ext
      change Matrix.mulVec est (Matrix.mulVec (1 - ε) v) = 0
      rw [Matrix.mulVec_mulVec, hest_oneSub, Matrix.zero_mulVec]
    show ((gF.toLinearMap (eToW (Matrix.mulVec (1 - ε) v)) : W) : fepomepι n → F) +
        ((gstar.toLinearMap (estToQ (Matrix.mulVec (1 - ε) v)) : q) : fepomepι n → F) +
        Matrix.mulVec (1 - ε) (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v
    rw [h1, h2]
    simp only [map_zero, Submodule.coe_zero, zero_add]
    rw [Matrix.mulVec_mulVec, honeSub.eq]
  · intro w
    have hwmem : (w : fepomepι n → F) ∈ LinearMap.range (Matrix.mulVecLin e) := by
      rw [← hW]; exact w.2
    have hw1 : eToW w = w := by
      apply Subtype.ext
      change Matrix.mulVec e (w : fepomepι n → F) = (w : fepomepι n → F)
      obtain ⟨w', hw'⟩ := hwmem
      rw [← hw', Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, heidem.eq]
    have hw2 : estToQ w = 0 := by
      apply Subtype.ext
      change Matrix.mulVec est (w : fepomepι n → F) = 0
      obtain ⟨w', hw'⟩ := hwmem
      rw [← hw', Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hzero1, Matrix.zero_mulVec]
    have hw3 : Matrix.mulVec (1 - ε) (w : fepomepι n → F) = 0 := by
      have hwε : Matrix.mulVec ε (w : fepomepι n → F) = (w : fepomepι n → F) := by
        obtain ⟨w', hw'⟩ := hwmem
        rw [← hw', Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεe]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hwε, sub_self]
    show ((gF.toLinearMap (eToW w) : W) : fepomepι n → F) +
        ((gstar.toLinearMap (estToQ w) : q) : fepomepι n → F) +
        Matrix.mulVec (1 - ε) (w : fepomepι n → F) = (g w : fepomepι n → F)
    rw [hw1, hw2, hw3]
    simp only [map_zero, Submodule.coe_zero, add_zero]
    rfl
  · intro y
    have hymem : (y : fepomepι n → F) ∈ LinearMap.range (Matrix.mulVecLin est) := y.2
    have hy1 : estToQ y = y := by
      apply Subtype.ext
      change Matrix.mulVec est (y : fepomepι n → F) = (y : fepomepι n → F)
      obtain ⟨y', hy'⟩ := hymem
      rw [← hy', Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hestidem.eq]
    have hy2 : eToW y = 0 := by
      apply Subtype.ext
      change Matrix.mulVec e (y : fepomepι n → F) = 0
      obtain ⟨y', hy'⟩ := hymem
      rw [← hy', Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hzero2, Matrix.zero_mulVec]
    have hy3 : Matrix.mulVec (1 - ε) (y : fepomepι n → F) = 0 := by
      have hyε : Matrix.mulVec ε (y : fepomepι n → F) = (y : fepomepι n → F) := by
        obtain ⟨y', hy'⟩ := hymem
        rw [← hy', Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεest]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hyε, sub_self]
    show ((gF.toLinearMap (eToW y) : W) : fepomepι n → F) +
        ((gstar.toLinearMap (estToQ y) : q) : fepomepι n → F) +
        Matrix.mulVec (1 - ε) (y : fepomepι n → F) = (gstar y : fepomepι n → F)
    rw [hy1, hy2, hy3]
    simp only [map_zero, Submodule.coe_zero, add_zero, zero_add]
    rfl

private lemma fepomep_quad_add_three_expand {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (a b c : V) :
    Q (a + b + c) = Q a + Q b + Q c + QuadraticMap.polar Q a b +
      QuadraticMap.polar Q a c + QuadraticMap.polar Q b c := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.polar_add_left]
  abel

private lemma fepomep_polar_epsV_compl (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    {ε : Matrix (fepomepι n) (fepomepι n) F} (hεidem : IsIdempotentElem ε)
    (hεadj : formAdj (RingHom.id F) (fepomepG n F) ε = ε)
    {u w : fepomepι n → F} (hu : u ∈ LinearMap.range (Matrix.mulVecLin ε)) :
    QuadraticMap.polar (fepomepQ n F) u (Matrix.mulVec (1 - ε) w) = 0 := by
  obtain ⟨x, hx⟩ := hu
  rw [← hx, Matrix.mulVecLin_apply,
    fepomep_polar_eps_compl n hεidem hεadj x w]

private lemma fepomep_levi_blockMap_isometry (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W)
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))))
    (hgstar : ∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))),
      QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F)
          (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F))
    (gV : (fepomepι n → F) →ₗ[F] (fepomepι n → F))
    (hfix : ∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v)
    (hact : ∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F))
    (hstar : ∀ y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))),
      gV (y : fepomepι n → F) = (gstar y : fepomepι n → F)) :
    ∀ v : fepomepι n → F, fepomepQ n F (gV v) = fepomepQ n F v := by
  classical
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  let est : Matrix (fepomepι n) (fepomepι n) F :=
    formAdj (RingHom.id F) (fepomepG n F) e
  let q : Submodule F (fepomepι n → F) := LinearMap.range (Matrix.mulVecLin est)
  have hεidem : IsIdempotentElem ε := hε.2.1
  have hεadj : formAdj (RingHom.id F) (fepomepG n F) ε = ε := hε.2.2.2.1
  have hεe : ε * e = e := by
    rw [(fepomep_adjoin_comm hS ε hε.1 e he.1).eq, heε]
  have hεest : ε * est = est := by
    rw [(fepomep_adjoin_comm hS ε hε.1 est hestA).eq, hestε]
  have hrangeE : LinearMap.range (Matrix.mulVecLin e) ≤
      LinearMap.range (Matrix.mulVecLin ε) := by
    rintro x ⟨y, rfl⟩
    refine ⟨Matrix.mulVec e y, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεe, Matrix.mulVecLin_apply]
  have hrangeQ : LinearMap.range (Matrix.mulVecLin est) ≤
      LinearMap.range (Matrix.mulVecLin ε) := by
    rintro x ⟨y, rfl⟩
    refine ⟨Matrix.mulVec est y, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεest, Matrix.mulVecLin_apply]
  intro v
  have hmat : e + est + (1 - ε) = 1 := by rw [← hsum]; abel
  have hv : Matrix.mulVec e v + Matrix.mulVec est v + Matrix.mulVec (1 - ε) v = v := by
    rw [← Matrix.add_mulVec, ← Matrix.add_mulVec, hmat, Matrix.one_mulVec]
  let uW : W := ⟨Matrix.mulVec e v, by rw [hW]; exact ⟨v, rfl⟩⟩
  let uQ : q := ⟨Matrix.mulVec est v, ⟨v, rfl⟩⟩
  have h1 : gV (Matrix.mulVec e v) = (g uW : fepomepι n → F) := hact uW
  have h2 : gV (Matrix.mulVec est v) = (gstar uQ : fepomepι n → F) := hstar uQ
  have h3 : gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v := hfix v
  have hgV : gV v = (g uW : fepomepι n → F) + (gstar uQ : fepomepι n → F) +
      Matrix.mulVec (1 - ε) v := by
    conv_lhs => rw [← hv]
    rw [map_add, map_add, h1, h2, h3]
  have hQ1 : fepomepQ n F ((uW : W) : fepomepι n → F) = 0 :=
    fepomep_block_quad_zero n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg W hW
      hK uW
  have hQ2 : fepomepQ n F ((uQ : q) : fepomepι n → F) = 0 :=
    fepomep_star_block_quad_zero n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg uQ
  have hQ3 : fepomepQ n F ((g uW : W) : fepomepι n → F) = 0 :=
    fepomep_block_quad_zero n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg W hW
      hK (g uW)
  have hQ4 : fepomepQ n F ((gstar uQ : q) : fepomepι n → F) = 0 :=
    fepomep_star_block_quad_zero n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg
      (gstar uQ)
  have hB1 : QuadraticMap.polar (fepomepQ n F) ((g uW : W) : fepomepι n → F)
      ((gstar uQ : q) : fepomepι n → F) =
      QuadraticMap.polar (fepomepQ n F) ((uW : W) : fepomepι n → F)
        ((uQ : q) : fepomepι n → F) := hgstar uW uQ
  have hB2 : QuadraticMap.polar (fepomepQ n F) ((g uW : W) : fepomepι n → F)
      (Matrix.mulVec (1 - ε) v) = 0 :=
    fepomep_polar_epsV_compl n hεidem hεadj
      (hrangeE (by rw [← hW]; exact (g uW).2))
  have hB3 : QuadraticMap.polar (fepomepQ n F) ((gstar uQ : q) : fepomepι n → F)
      (Matrix.mulVec (1 - ε) v) = 0 :=
    fepomep_polar_epsV_compl n hεidem hεadj (hrangeQ (gstar uQ).2)
  have hB4 : QuadraticMap.polar (fepomepQ n F) ((uW : W) : fepomepι n → F)
      (Matrix.mulVec (1 - ε) v) = 0 :=
    fepomep_polar_epsV_compl n hεidem hεadj (hrangeE (by rw [← hW]; exact uW.2))
  have hB5 : QuadraticMap.polar (fepomepQ n F) ((uQ : q) : fepomepι n → F)
      (Matrix.mulVec (1 - ε) v) = 0 :=
    fepomep_polar_epsV_compl n hεidem hεadj (hrangeQ uQ.2)
  rw [hgV]
  conv_rhs => rw [← hv]
  rw [fepomep_quad_add_three_expand, fepomep_quad_add_three_expand]
  rw [hQ1, hQ2, hQ3, hQ4, hB1, hB2, hB3, hB4, hB5]

private lemma fepomep_levi_blockMap_linearEquiv (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (gV : (fepomepι n → F) →ₗ[F] (fepomepι n → F))
    (hiso : ∀ v : fepomepι n → F, fepomepQ n F (gV v) = fepomepQ n F v) :
    ∃ gV' : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F),
      (gV' : (fepomepι n → F) →ₗ[F] (fepomepι n → F)) = gV ∧
      gV' ∈ TauCeti.QuadraticMap.orthogonalGroup (fepomepQ n F) := by
  classical
  have hpol : ∀ x y : fepomepι n → F,
      QuadraticMap.polar (fepomepQ n F) (gV x) (gV y) =
        QuadraticMap.polar (fepomepQ n F) x y := by
    intro x y
    have h1 : fepomepQ n F (gV x) + fepomepQ n F (gV y) +
        QuadraticMap.polar (fepomepQ n F) (gV x) (gV y) =
        fepomepQ n F x + fepomepQ n F y +
          QuadraticMap.polar (fepomepQ n F) x y := by
      rw [← QuadraticMap.map_add (fepomepQ n F) (gV x) (gV y), ← map_add,
        hiso (x + y), QuadraticMap.map_add (fepomepQ n F) x y]
    rw [hiso x, hiso y] at h1
    exact add_left_cancel h1
  have hinj : Function.Injective gV := by
    intro x y hxy
    have hzero : gV (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hB : ∀ w : fepomepι n → F,
        QuadraticMap.polar (fepomepQ n F) (x - y) w = 0 := by
      intro w
      have h := hpol (x - y) w
      rw [hzero] at h
      simpa using h.symm
    have hnd := Spin.nondegenerate_polarBilin_quadPlus n F
    have h0 : x - y = 0 := hnd.1 (x - y) (by
      intro w
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hB w)
    exact sub_eq_zero.mp h0
  refine ⟨LinearEquiv.ofInjectiveEndo gV hinj, ?_, ?_⟩
  · rfl
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    exact hiso

private lemma fepomep_polar_smulVec (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range) :
    ∀ s ∈ S, ∀ u w : fepomepι n → F,
      QuadraticMap.polar (fepomepQ n F)
          (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) u)
          (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) w) =
        QuadraticMap.polar (fepomepQ n F) u w := by
  intro s hs u w
  obtain ⟨x, hx⟩ := hSU s hs
  have hq : ∀ z : fepomepι n → F,
      fepomepQ n F (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) z) =
        fepomepQ n F z := by
    intro z
    rw [← hx]
    exact Spin.spinMatrix_mem (fepomepQ n F) x z
  have h1 : fepomepQ n F
        (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) u +
          Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) w) =
      fepomepQ n F (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) u) +
        fepomepQ n F (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) w) +
          QuadraticMap.polar (fepomepQ n F)
            (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) u)
            (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) w) :=
    QuadraticMap.map_add (fepomepQ n F) _ _
  rw [← Matrix.mulVec_add, hq (u + w), hq u, hq w,
    QuadraticMap.map_add (fepomepQ n F) u w] at h1
  have h1' : (fepomepQ n F u + fepomepQ n F w) +
      QuadraticMap.polar (fepomepQ n F) u w =
      (fepomepQ n F u + fepomepQ n F w) +
        QuadraticMap.polar (fepomepQ n F)
          (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) u)
          (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) w) := h1
  exact (add_left_cancel h1').symm

private lemma fepomep_pairing_separating_q (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    {z : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))}
    (hz : ∀ x : W, QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F)
      (z : fepomepι n → F) = 0) :
    z = 0 := by
  have hfun : fepomep_dualPair_pairingMap n e W z = 0 := by
    ext x
    rw [fepomep_dualPair_pairingMap_apply n e W z x]
    exact hz x
  exact fepomep_dualPair_pairing_injective n hn S hSU hS hε he heε hne W hW
    (by rw [hfun, map_zero])

private lemma fepomep_gstar_comm (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W)
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))))
    (hgstar : ∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))),
      QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F) (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F)) :
    ∀ s ∈ S, ∀ (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))))
      (hy : Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (y : fepomepι n → F) ∈
        LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))),
      ((gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (y : fepomepι n → F), hy⟩) :
          fepomepι n → F) =
        Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
          (gstar y : fepomepι n → F) := by
  classical
  intro s hs y hy
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  let est : Matrix (fepomepι n) (fepomepι n) F :=
    formAdj (RingHom.id F) (fepomepG n F) e
  let q : Submodule F (fepomepι n → F) := LinearMap.range (Matrix.mulVecLin est)
  let hsa : fepomepA n F S :=
    ⟨(s : Matrix (fepomepι n) (fepomepι n) F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
  have hsaM : (hsa : Matrix (fepomepι n) (fepomepι n) F) =
      (s : Matrix (fepomepι n) (fepomepι n) F) := rfl
  have hse : (s : Matrix (fepomepι n) (fepomepι n) F) * e =
      e * (s : Matrix (fepomepι n) (fepomepι n) F) :=
    (fepomep_adjoin_comm hS (s : Matrix (fepomepι n) (fepomepι n) F) hsa.2 e he.1).eq
  have hses : (s : Matrix (fepomepι n) (fepomepι n) F) * est =
      est * (s : Matrix (fepomepι n) (fepomepι n) F) :=
    (fepomep_adjoin_comm hS (s : Matrix (fepomepι n) (fepomepι n) F) hsa.2 est hestA).eq
  have hs_inv' : (s : Matrix (fepomepι n) (fepomepι n) F) *
      ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hs_inv : ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) *
      (s : Matrix (fepomepι n) (fepomepι n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hses_inv : ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) * est =
      est * ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) := by
    calc ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) * est
        = ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) *
            (est * ((s : Matrix (fepomepι n) (fepomepι n) F) *
              ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F))) := by
            rw [hs_inv', Matrix.mul_one]
      _ = ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) *
            ((est * (s : Matrix (fepomepι n) (fepomepι n) F)) *
              ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)) := by
            rw [Matrix.mul_assoc]
      _ = ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) *
            (((s : Matrix (fepomepι n) (fepomepι n) F) * est) *
              ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)) := by
            rw [← hses]
      _ = (((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) *
              (s : Matrix (fepomepι n) (fepomepι n) F)) *
            (est * ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = est * ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) := by
            rw [hs_inv, Matrix.one_mul]
  have hw0_mem : Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
      Matrix (fepomepι n) (fepomepι n) F) (gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι
          n) F)
          (y : fepomepι n → F), hy⟩ : fepomepι n → F) ∈ q := by
    obtain ⟨z, hz⟩ := (gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
      (y : fepomepι n → F), hy⟩).2
    refine ⟨Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F) z, ?_⟩
    calc Matrix.mulVecLin est (Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) z)
        = Matrix.mulVec est (Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
            Matrix (fepomepι n) (fepomepι n) F) z) := Matrix.mulVecLin_apply est _
      _ = Matrix.mulVec (est * ((s⁻¹ : GL (fepomepι n) F) :
            Matrix (fepomepι n) (fepomepι n) F)) z :=
            Matrix.mulVec_mulVec z est ((s⁻¹ : GL (fepomepι n) F) :
              Matrix (fepomepι n) (fepomepι n) F)
      _ = Matrix.mulVec (((s⁻¹ : GL (fepomepι n) F) :
            Matrix (fepomepι n) (fepomepι n) F) * est) z := by rw [← hses_inv]
      _ = Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
            Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec est z) :=
            (Matrix.mulVec_mulVec z ((s⁻¹ : GL (fepomepι n) F) :
              Matrix (fepomepι n) (fepomepι n) F) est).symm
      _ = Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
            Matrix (fepomepι n) (fepomepι n) F) (gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n)
                (fepomepι
                n) F) (y : fepomepι n → F), hy⟩ : fepomepι n → F) := by
            rw [← hz, Matrix.mulVecLin_apply]
  have hdiff : (⟨Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F) (gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι
            n)
            F) (y : fepomepι n → F), hy⟩ : fepomepι n → F), hw0_mem⟩ : q) -
      gstar y = 0 := by
    apply fepomep_pairing_separating_q n hn S hSU hS hε he heε hne W hW
    intro x'
    have hx'' : (x' : fepomepι n → F) = (g (g.symm x') : fepomepι n → F) := by
      rw [g.apply_symm_apply]
    have hcomp1 : QuadraticMap.polar (fepomepQ n F)
          (g (g.symm x') : fepomepι n → F)
          (Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
            Matrix (fepomepι n) (fepomepι n) F) (gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n)
                (fepomepι
                n) F) (y : fepomepι n → F), hy⟩ : fepomepι n → F)) =
        QuadraticMap.polar (fepomepQ n F) ((g.symm x' : W) : fepomepι n → F)
          (y : fepomepι n → F) := by
      rw [← fepomep_polar_smulVec n hn S hSU s hs (g (g.symm x') : fepomepι n → F)
        (Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) (gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n)
              (fepomepι
              n) F) (y : fepomepι n → F), hy⟩ : fepomepι n → F))]
      rw [show Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
          (Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
            Matrix (fepomepι n) (fepomepι n) F) (gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n)
                (fepomepι
                n) F) (y : fepomepι n → F), hy⟩ : fepomepι n → F)) =
          (gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (y : fepomepι n → F), hy⟩ :
              fepomepι n → F) from by
            rw [Matrix.mulVec_mulVec, hs_inv', Matrix.one_mulVec]]
      have hs_g : Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
            (g (g.symm x') : fepomepι n → F) =
          (g (π hsa • (g.symm x')) : fepomepι n → F) := by
        calc Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (g (g.symm x') : fepomepι n → F)
            = ((π hsa • (g (g.symm x')) : W) : fepomepι n → F) := (hK hsa (g (g.symm x'))).symm
          _ = ((g (π hsa • (g.symm x')) : W) : fepomepι n → F) := by simp only [map_smul]
      rw [hs_g, hgstar (π hsa • (g.symm x')) ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
          (y : fepomepι n → F), hy⟩, hK hsa (g.symm x')]
      rw [fepomep_polar_smulVec n hn S hSU s hs (g.symm x') y]
    have hcomp2 : QuadraticMap.polar (fepomepQ n F) (g (g.symm x') : fepomepι n → F)
        (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) ((g.symm x' : W) : fepomepι n → F)
          (y : fepomepι n → F) := hgstar (g.symm x') y
    rw [Submodule.coe_sub, QuadraticMap.polar_sub_right, hx'', hcomp1, hcomp2, sub_self]
  have hw0_eq : (⟨Matrix.mulVec ((s⁻¹ : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F) (gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι
            n)
            F) (y : fepomepι n → F), hy⟩ : fepomepι n → F), hw0_mem⟩ : q) =
      gstar y := sub_eq_zero.mp hdiff
  have hgoal := congrArg (fun z : q => (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
      (z : fepomepι n → F))) hw0_eq
  simpa [Matrix.mulVec_mulVec, hs_inv', Matrix.one_mulVec] using hgoal

private lemma fepomep_dualPair_levi_pair (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W) :
    ∃ (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e)))),
      (∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
          (formAdj (RingHom.id F) (fepomepG n F) e)))),
        QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F)
            (gstar y : fepomepι n → F) =
          QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F)
            (y : fepomepι n → F)) ∧
      ∃ gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F),
        gV ∈ TauCeti.QuadraticMap.orthogonalGroup (fepomepQ n F) ∧
        (∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v) ∧
        (∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F)) ∧
        (∀ y : ↥(LinearMap.range (Matrix.mulVecLin
            (formAdj (RingHom.id F) (fepomepG n F) e))),
          gV (y : fepomepι n → F) = (gstar y : fepomepι n → F)) := by
  obtain ⟨gstar, hgstar⟩ :=
    fepomep_dualPair_levi_dual n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg
      W hW hK g
  obtain ⟨gV, hfix, hact, hstar⟩ :=
    fepomep_levi_blockMap n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg W hW hK
      g gstar
  have hiso := fepomep_levi_blockMap_isometry n hn S hSU hS hε he heε hne hdeg K π hπsurj
    hπker hπdeg W hW hK g gstar hgstar gV hfix hact hstar
  obtain ⟨gV', hgV', horth⟩ := fepomep_levi_blockMap_linearEquiv n gV hiso
  refine ⟨gstar, hgstar, gV', horth, ?_, ?_, ?_⟩
  · intro v
    change (gV' : (fepomepι n → F) →ₗ[F] (fepomepι n → F)) (Matrix.mulVec (1 - ε) v) =
      Matrix.mulVec (1 - ε) v
    rw [hgV']
    exact hfix v
  · intro w
    change (gV' : (fepomepι n → F) →ₗ[F] (fepomepι n → F)) (w : fepomepι n → F) =
      (g w : fepomepι n → F)
    rw [hgV']
    exact hact w
  · intro y
    change (gV' : (fepomepι n → F) →ₗ[F] (fepomepι n → F)) (y : fepomepι n → F) =
      (gstar y : fepomepι n → F)
    rw [hgV']
    exact hstar y

private lemma fepomep_dualPair_levi_comm (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W)
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))))
    (hgstar : ∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))),
      QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F)
          (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F))
    (gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (horth : gV ∈ TauCeti.QuadraticMap.orthogonalGroup (fepomepQ n F))
    (hfix : ∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v)
    (hact : ∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F))
    (hstar : ∀ y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))),
      gV (y : fepomepι n → F) = (gstar y : fepomepι n → F))
    (hgstarcomm : ∀ s ∈ S, ∀ (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))))
      (hy : Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (y : fepomepι n → F) ∈
        LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))),
      ((gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (y : fepomepι n → F), hy⟩) :
          fepomepι n → F) =
        Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
          (gstar y : fepomepι n → F)) :
    ∀ s ∈ S, ∀ v : fepomepι n → F,
      gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v) =
        Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (gV v) := by
  classical
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  let est : Matrix (fepomepι n) (fepomepι n) F :=
    formAdj (RingHom.id F) (fepomepG n F) e
  let q : Submodule F (fepomepι n → F) := LinearMap.range (Matrix.mulVecLin est)
  intro s hs v
  let hsa : fepomepA n F S :=
    ⟨(s : Matrix (fepomepι n) (fepomepι n) F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
  have hsaM : (hsa : Matrix (fepomepι n) (fepomepι n) F) =
      (s : Matrix (fepomepι n) (fepomepι n) F) := rfl
  have hA : (s : Matrix (fepomepι n) (fepomepι n) F) ∈
      Algebra.adjoin F (Units.val '' S) := by
    change (s : Matrix (fepomepι n) (fepomepι n) F) ∈ fepomepA n F S
    exact hsa.2
  have hse : (s : Matrix (fepomepι n) (fepomepι n) F) * e =
      e * (s : Matrix (fepomepι n) (fepomepι n) F) :=
    (fepomep_adjoin_comm hS (s : Matrix (fepomepι n) (fepomepι n) F) hA e he.1).eq
  have hses : (s : Matrix (fepomepι n) (fepomepι n) F) * est =
      est * (s : Matrix (fepomepι n) (fepomepι n) F) :=
    (fepomep_adjoin_comm hS (s : Matrix (fepomepι n) (fepomepι n) F) hA est hestA).eq
  have hse1 : (s : Matrix (fepomepι n) (fepomepι n) F) * (1 - ε) =
      (1 - ε) * (s : Matrix (fepomepι n) (fepomepι n) F) := by
    rw [mul_sub, mul_one, sub_mul, one_mul,
      (fepomep_adjoin_comm hS (s : Matrix (fepomepι n) (fepomepι n) F) hA ε hε.1).eq]
  have hmat : e + est + (1 - ε) = 1 := by rw [← hsum]; abel
  have hv : Matrix.mulVec e v + Matrix.mulVec est v + Matrix.mulVec (1 - ε) v = v := by
    rw [← Matrix.add_mulVec, ← Matrix.add_mulVec, hmat, Matrix.one_mulVec]
  have hmemv : Matrix.mulVec e v ∈ W := by rw [hW]; exact ⟨v, rfl⟩
  have hmem_sv : Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec e v) ∈
      W := by
    rw [show W = LinearMap.range (Matrix.mulVecLin e) from hW]
    refine ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hse, ← Matrix.mulVec_mulVec]
  have hWcomm : gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
        (Matrix.mulVec e v)) =
      Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
        (gV (Matrix.mulVec e v)) := by
    have hm : (⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec e v),
          hmem_sv⟩ : W) = π hsa • (⟨Matrix.mulVec e v, hmemv⟩ : W) := by
      apply Subtype.ext
      simpa only [hsaM] using (hK hsa ⟨Matrix.mulVec e v, hmemv⟩).symm
    calc gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec e v))
        = gV ((⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec e v),
              hmem_sv⟩ : W) : fepomepι n → F) := rfl
      _ = (g (⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec e v),
              hmem_sv⟩ : W) : fepomepι n → F) := hact _
      _ = (g (π hsa • (⟨Matrix.mulVec e v, hmemv⟩ : W)) : fepomepι n → F) := by rw [hm]
      _ = ((π hsa • g (⟨Matrix.mulVec e v, hmemv⟩ : W) : W) : fepomepι n → F) := by
            simp only [map_smul]
      _ = Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
            (gV (Matrix.mulVec e v)) := by
            rw [hK hsa (g (⟨Matrix.mulVec e v, hmemv⟩ : W)),
              ← hact (⟨Matrix.mulVec e v, hmemv⟩ : W), hsaM]
  have hmemq : Matrix.mulVec est v ∈ q := ⟨v, rfl⟩
  have hmem_sq : Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec est v) ∈
      q := by
    refine ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hses, ← Matrix.mulVec_mulVec]
  have hqcomm : gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
        (Matrix.mulVec est v)) =
      Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
        (gV (Matrix.mulVec est v)) := by
    calc gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec est v))
        = (gstar ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
              (Matrix.mulVec est v), hmem_sq⟩ : fepomepι n → F) :=
            hstar ⟨Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec est v),
              hmem_sq⟩
      _ = Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
            ((gstar (⟨Matrix.mulVec est v, hmemq⟩ : q)) : fepomepι n → F) :=
            hgstarcomm s hs ⟨Matrix.mulVec est v, hmemq⟩ hmem_sq
      _ = Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
            (gV (Matrix.mulVec est v)) := by
            rw [hstar (⟨Matrix.mulVec est v, hmemq⟩ : q)]
  have hrcomm : gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
        (Matrix.mulVec (1 - ε) v)) =
      Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
        (gV (Matrix.mulVec (1 - ε) v)) := by
    have hsr : Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
          (Matrix.mulVec (1 - ε) v) =
        Matrix.mulVec (1 - ε) (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v) := by
      rw [Matrix.mulVec_mulVec, hse1, ← Matrix.mulVec_mulVec]
    rw [hsr, hfix (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v), hfix v, ← hsr]
  have hsv : Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v =
      Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec e v) +
        Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec est v) +
          Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec (1 - ε) v) := by
    rw [← Matrix.mulVec_add, ← Matrix.mulVec_add, hv]
  have hgV : gV v = gV (Matrix.mulVec e v) + gV (Matrix.mulVec est v) +
      gV (Matrix.mulVec (1 - ε) v) := by
    conv_lhs => rw [← hv]
    rw [map_add, map_add]
  calc gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v)
      = gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec e v) +
          Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec est v) +
            Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
              (Matrix.mulVec (1 - ε) v)) := by rw [hsv]
    _ = gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec e v)) +
          gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (Matrix.mulVec est v)) +
            gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
              (Matrix.mulVec (1 - ε) v)) := by rw [map_add, map_add]
    _ = Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (gV (Matrix.mulVec e v)) +
          Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (gV (Matrix.mulVec est v)) +
            Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
              (gV (Matrix.mulVec (1 - ε) v)) := by rw [hWcomm, hqcomm, hrcomm]
    _ = Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F)
          (gV (Matrix.mulVec e v) + gV (Matrix.mulVec est v) +
            gV (Matrix.mulVec (1 - ε) v)) := by
          rw [Matrix.mulVec_add, Matrix.mulVec_add]
    _ = Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (gV v) := by rw [← hgV]

private lemma fepomep_dualPair_levi_isometry (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W) :
    ∃ gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F),
      gV ∈ TauCeti.QuadraticMap.orthogonalGroup (fepomepQ n F) ∧
      (∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v) ∧
      (∀ s ∈ S, ∀ v : fepomepι n → F,
        gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v) =
          Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (gV v)) ∧
      (∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F)) := by
  obtain ⟨gstar, hgstar, gV, horth, hfix, hact, hstar⟩ :=
    fepomep_dualPair_levi_pair n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg W hW
      hK g
  have hgstarcomm := fepomep_gstar_comm n hn S hSU hS hε he heε hne K π W hW hK g gstar hgstar
  exact ⟨gV, horth, hfix,
    fepomep_dualPair_levi_comm n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg W hW
      hK g gstar hgstar gV horth hfix hact hstar hgstarcomm, hact⟩

private lemma fepomep_polar_of_mem_orthogonalGroup {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] (Q : QuadraticForm F V) {gV : V ≃ₗ[F] V}
    (horth : gV ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∀ u w : V, QuadraticMap.polar Q (gV u) (gV w) = QuadraticMap.polar Q u w := by
  intro u w
  have h2 : Q (gV (u + w)) = Q (u + w) :=
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp horth) (u + w)
  have hE1 : Q (gV u) + Q (gV w) + QuadraticMap.polar Q (gV u) (gV w) =
      Q (gV (u + w)) := by
    rw [map_add, QuadraticMap.map_add Q]
  have hE2 : Q u + Q w + QuadraticMap.polar Q u w = Q (u + w) :=
    (QuadraticMap.map_add Q u w).symm
  have hE : Q (gV u) + Q (gV w) + QuadraticMap.polar Q (gV u) (gV w) =
      Q u + Q w + QuadraticMap.polar Q u w := hE1.trans (h2.trans hE2.symm)
  rw [(TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp horth) u,
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp horth) w] at hE
  exact add_left_cancel (show (Q u + Q w) + QuadraticMap.polar Q (gV u) (gV w) =
    (Q u + Q w) + QuadraticMap.polar Q u w from hE)

private lemma fepomep_levi_comm_adjoin (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (fepomepι n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (gV : (fepomepι n → F) →ₗ[F] (fepomepι n → F))
    (hcomm : ∀ s ∈ S, ∀ v : fepomepι n → F,
      gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v) =
        Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (gV v)) :
    ∀ a ∈ fepomepA n F S, ∀ v : fepomepι n → F,
      gV (Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) v) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (gV v) := by
  intro a ha
  refine (Algebra.adjoin_induction
    (p := fun x _ => ∀ v : fepomepι n → F,
      gV (Matrix.mulVec x v) = Matrix.mulVec x (gV v)) ?_ ?_ ?_ ?_ ha)
  · rintro x ⟨s, hs, rfl⟩ v
    exact hcomm s hs v
  · intro r v
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec, map_smul]
  · rintro x y hx hy hpx hpy v
    rw [Matrix.add_mulVec, Matrix.add_mulVec, map_add, hpx v, hpy v]
  · rintro x y hx hy hpx hpy v
    rw [← Matrix.mulVec_mulVec, hpx (y.mulVec v), hpy v, Matrix.mulVec_mulVec]

private lemma fepomep_levi_block_action (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W) (gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (horth : gV ∈ TauCeti.QuadraticMap.orthogonalGroup (fepomepQ n F))
    (hfix : ∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v)
    (hcomm : ∀ s ∈ S, ∀ v : fepomepι n → F,
      gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v) =
        Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (gV v))
    (hact : ∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F)) :
    ∃ gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))),
      (∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
          (formAdj (RingHom.id F) (fepomepG n F) e)))),
        QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F)
            (gstar y : fepomepι n → F) =
          QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F)
            (y : fepomepι n → F)) ∧
      (∀ y : ↥(LinearMap.range (Matrix.mulVecLin
          (formAdj (RingHom.id F) (fepomepG n F) e))),
        gV (y : fepomepι n → F) = (gstar y : fepomepι n → F)) := by
  classical
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  obtain ⟨gstar₀, hgstar₀⟩ :=
    fepomep_dualPair_levi_dual n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg
      W hW hK g
  let est : Matrix (fepomepι n) (fepomepι n) F :=
    formAdj (RingHom.id F) (fepomepG n F) e
  let q : Submodule F (fepomepι n → F) := LinearMap.range (Matrix.mulVecLin est)
  have hcommA := fepomep_levi_comm_adjoin n S hS (gV : (fepomepι n → F) →ₗ[F] (fepomepι n → F))
    (fun s hs v => hcomm s hs v)
  have hpol := fepomep_polar_of_mem_orthogonalGroup (fepomepQ n F) horth
  refine ⟨gstar₀, hgstar₀, ?_⟩
  intro y
  have hmem : gV (y : fepomepι n → F) ∈ q := by
    obtain ⟨y', hy'⟩ := y.2
    refine ⟨gV y', ?_⟩
    rw [← hy', Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    exact (hcommA est hestA y').symm
  have hz : (⟨gV (y : fepomepι n → F), hmem⟩ : q) - gstar₀ y = 0 := by
    apply fepomep_pairing_separating_q n hn S hSU hS hε he heε hne W hW
    intro x'
    have hx'' : (x' : fepomepι n → F) = (g (g.symm x') : fepomepι n → F) := by
      rw [g.apply_symm_apply]
    rw [hx'', Submodule.coe_sub, QuadraticMap.polar_sub_right]
    have h1 : QuadraticMap.polar (fepomepQ n F) (g (g.symm x') : fepomepι n → F)
        (gV (y : fepomepι n → F)) =
        QuadraticMap.polar (fepomepQ n F) ((g.symm x' : W) : fepomepι n → F)
          (y : fepomepι n → F) := by
      rw [← hact (g.symm x'), hpol (g.symm x') y]
    have h2 : QuadraticMap.polar (fepomepQ n F) (g (g.symm x') : fepomepι n → F)
        (gstar₀ y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) ((g.symm x' : W) : fepomepι n → F)
          (y : fepomepι n → F) := hgstar₀ (g.symm x') y
    rw [h1, h2, sub_self]
  exact congrArg Subtype.val (sub_eq_zero.mp hz)

private lemma fepomep_commSpace_conj {F V₁ V₂ : Type} [Field F] [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂] (Φ : V₁ ≃ₗ[F] V₂) (e : V₁ ≃ₗ[F] V₁) :
    CFSG.RankThree.OrthogonalInvolutions.commSpace (Φ.symm.trans (e.trans Φ)) =
      (CFSG.RankThree.OrthogonalInvolutions.commSpace e).map (Φ : V₁ →ₗ[F] V₂) := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hx
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply] at hv
    refine ⟨e (Φ.symm v) - Φ.symm v,
      CFSG.RankThree.OrthogonalInvolutions.sub_mem_commSpace e (Φ.symm v), ?_⟩
    simpa [map_sub, Φ.apply_symm_apply] using hv
  · intro hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨u, hu⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hy
    refine CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mpr ⟨Φ u, ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, Φ.symm_apply_apply, ← map_sub, hu]
    rfl

private lemma fepomep_commSpace_prodCongr {F V₁ V₂ : Type} [Field F] [AddCommGroup V₁]
    [Module F V₁] [AddCommGroup V₂] [Module F V₂] (φ : V₁ ≃ₗ[F] V₁) (ψ : V₂ ≃ₗ[F] V₂) :
    CFSG.RankThree.OrthogonalInvolutions.commSpace (φ.prodCongr ψ) =
      (CFSG.RankThree.OrthogonalInvolutions.commSpace φ).prod
        (CFSG.RankThree.OrthogonalInvolutions.commSpace ψ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hx
    refine ⟨⟨v.1, ?_⟩, ⟨v.2, ?_⟩⟩
    · have h1 := congrArg Prod.fst hv
      simpa [LinearEquiv.coe_prodCongr] using h1
    · have h1 := congrArg Prod.snd hv
      simpa [LinearEquiv.coe_prodCongr] using h1
  · rintro ⟨hx1, hx2⟩
    obtain ⟨v1, hv1⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hx1
    obtain ⟨v2, hv2⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hx2
    refine CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mpr ⟨(v1, v2), ?_⟩
    ext <;> simpa [LinearEquiv.coe_prodCongr] using ‹_›

private lemma fepomep_finrank_commSpace_prodCongr {F V₁ V₂ : Type} [Field F] [AddCommGroup V₁]
    [Module F V₁] [AddCommGroup V₂] [Module F V₂] [FiniteDimensional F V₁]
    [FiniteDimensional F V₂] (φ : V₁ ≃ₗ[F] V₁) (ψ : V₂ ≃ₗ[F] V₂) :
    Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace (φ.prodCongr ψ)) =
      Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace φ) +
        Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace ψ) := by
  rw [fepomep_commSpace_prodCongr, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

private lemma fepomep_finrank_commSpace_inv {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (g : W ≃ₗ[F] W) :
    Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g⁻¹) =
      Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g) := by
  have hfix : CFSG.RankThree.OrthogonalInvolutions.fixSpace g⁻¹ =
      CFSG.RankThree.OrthogonalInvolutions.fixSpace g := by
    ext x
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace,
      CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace]
    constructor
    · intro h
      calc g x = g (g⁻¹ x) := by congr 1; exact h.symm
        _ = x := g.apply_symm_apply x
    · intro h
      calc g⁻¹ x = g⁻¹ (g x) := by congr 1; exact h.symm
        _ = x := g.symm_apply_apply x
  have h1 := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace g⁻¹
  have h2 := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace g
  rw [hfix] at h1
  omega

private lemma fepomep_finrank_commSpace_dualMap {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (g : W ≃ₗ[F] W) :
    Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g.dualMap) =
      Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace g) := by
  have h1 : (g.dualMap : Module.Dual F W →ₗ[F] Module.Dual F W) - 1 =
      (g - 1 : W →ₗ[F] W).dualMap := by
    ext φ w
    simp [LinearEquiv.dualMap_apply, LinearMap.dualMap_apply]
  rw [CFSG.RankThree.OrthogonalInvolutions.commSpace,
    CFSG.RankThree.OrthogonalInvolutions.commSpace, h1,
    LinearMap.finrank_range_dualMap_eq_finrank_range]

private lemma fepomep_dualPair_gstar_dualMap (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (g : W ≃ₗ[K] W)
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))))
    (hgstar : ∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))),
      QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F) (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F))
    (η : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F] Module.Dual F W)
    (hη : ∀ (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))) (x : W),
      η y x = QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F)) :
    η.symm.trans (gstar.trans η) = (g.restrictScalars F)⁻¹.dualMap := by
  ext φ w
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hη (gstar (η.symm φ)) w,
    LinearEquiv.dualMap_apply]
  conv_rhs => rw [← η.apply_symm_apply φ]
  rw [hη (η.symm φ) ((g.restrictScalars F)⁻¹ w),
    ← hgstar ((g.restrictScalars F)⁻¹ w) (η.symm φ),
    show g ((g.restrictScalars F)⁻¹ w) = w from (g.restrictScalars F).apply_symm_apply w]

private lemma fepomep_finrank_commSpace_dual_adjoint (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (g : W ≃ₗ[K] W)
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))))
    (hgstar : ∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))),
      QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F) (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F)) :
    Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace gstar) =
      Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace (g.restrictScalars F)) := by
  obtain ⟨η, hη⟩ := fepomep_dualPair_pairing_dualEquiv n hn S hSU hS hε he heε hne W hW
  have hrel := fepomep_dualPair_gstar_dualMap n hn S hSU hS hε he heε hne K W hW g gstar hgstar
    η hη
  calc Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace gstar)
      = Module.finrank F ((CFSG.RankThree.OrthogonalInvolutions.commSpace gstar).map
          (η : _ →ₗ[F] Module.Dual F W)) :=
        (LinearEquiv.finrank_map_eq η (CFSG.RankThree.OrthogonalInvolutions.commSpace gstar)).symm
    _ = Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace
          (η.symm.trans (gstar.trans η))) := by
        rw [← fepomep_commSpace_conj η gstar]
    _ = Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace
          ((g.restrictScalars F)⁻¹.dualMap)) := by rw [hrel]
    _ = Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace
          ((g.restrictScalars F)⁻¹)) :=
        fepomep_finrank_commSpace_dualMap ((g.restrictScalars F)⁻¹)
    _ = Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace
          (g.restrictScalars F)) :=
        fepomep_finrank_commSpace_inv (g.restrictScalars F)

private lemma fepomep_finrank_commSpace_of_prodCongr {F V W₁ W₂ : Type} [Field F] [AddCommGroup V]
    [Module F V] [AddCommGroup W₁] [Module F W₁] [AddCommGroup W₂] [Module F W₂]
    [FiniteDimensional F W₁] [FiniteDimensional F W₂]
    (e : V ≃ₗ[F] V) (e₁ : W₁ ≃ₗ[F] W₁) (e₂ : W₂ ≃ₗ[F] W₂) (Φ : (W₁ × W₂) ≃ₗ[F] V)
    (hΦ : e = (LinearEquiv.symm Φ).trans ((e₁.prodCongr e₂).trans Φ)) :
    Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace e) =
      Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace e₁) +
        Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace e₂) := by
  rw [hΦ, fepomep_commSpace_conj Φ (e₁.prodCongr e₂)]
  rw [LinearEquiv.finrank_map_eq Φ
      (CFSG.RankThree.OrthogonalInvolutions.commSpace (e₁.prodCongr e₂)),
    fepomep_finrank_commSpace_prodCongr]

private lemma fepomep_finrank_commSpace_restrict_isCompl {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (e : V ≃ₗ[F] V) (p q : Submodule F V)
    (h : IsCompl p q) (hp : ∀ x ∈ p, e x ∈ p) (hq : ∀ x ∈ q, e x ∈ q)
    (ep : p ≃ₗ[F] p) (eq : q ≃ₗ[F] q)
    (hep : ∀ x : p, (ep x : V) = e x) (heq : ∀ x : q, (eq x : V) = e x) :
    Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace e) =
      Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace ep) +
        Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace eq) := by
  let Φ : (p × q) ≃ₗ[F] V := Submodule.prodEquivOfIsCompl p q h
  have hΦ : e = (LinearEquiv.symm Φ).trans ((ep.prodCongr eq).trans Φ) := by
    apply LinearEquiv.ext
    intro v
    set w : p × q := Φ.symm v with hw
    have h1 := Φ.apply_symm_apply v
    rw [← hw] at h1
    have hxy : (w.1 : V) + (w.2 : V) = v := by
      have h2 : (Φ w : V) = (w.1 : V) + (w.2 : V) := by
        simp [Φ, Submodule.coe_prodEquivOfIsCompl, LinearMap.coprod_apply]
      rw [h2] at h1
      exact h1
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← hw]
    have hR : (Φ ((ep.prodCongr eq) w) : V) = (ep w.1 : V) + (eq w.2 : V) := by
      simp [Φ, Submodule.coe_prodEquivOfIsCompl, LinearMap.coprod_apply, Submodule.coe_subtype]
    rw [hR, ← hxy, map_add, hep w.1, heq w.2]
  exact fepomep_finrank_commSpace_of_prodCongr e ep eq Φ hΦ

private lemma fepomep_finrank_commSpace_conj {F V₁ V₂ : Type} [Field F] [AddCommGroup V₁]
    [Module F V₁] [AddCommGroup V₂] [Module F V₂]
    (Φ : V₁ ≃ₗ[F] V₂) (e : V₂ ≃ₗ[F] V₂) :
    Module.finrank F
        (CFSG.RankThree.OrthogonalInvolutions.commSpace (Φ.trans (e.trans Φ.symm))) =
      Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace e) := by
  rw [show Φ.trans (e.trans Φ.symm) = (Φ.symm).symm.trans (e.trans Φ.symm) from rfl,
    fepomep_commSpace_conj Φ.symm e, LinearEquiv.finrank_map_eq]

private lemma fepomep_levi_gVP_action (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (g : W ≃ₗ[K] W) (gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))))
    (hgstar : ∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))),
      QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F) (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F))
    (hact : ∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F))
    (hstar : ∀ y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))),
      gV (y : fepomepι n → F) = (gstar y : fepomepι n → F))
    (hfix : ∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v) :
    ∃ (P r : Submodule F (fepomepι n → F)) (gVP : P ≃ₗ[F] P),
      IsCompl P r ∧
      P = LinearMap.range (Matrix.mulVecLin ε) ∧
      (∀ x : P, (gVP x : fepomepι n → F) = gV (x : fepomepι n → F)) ∧
      (∀ x : r, (LinearEquiv.refl F r x : fepomepι n → F) = gV (x : fepomepι n → F)) := by
  classical
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  let est : Matrix (fepomepι n) (fepomepι n) F := formAdj (RingHom.id F) (fepomepG n F) e
  let P : Submodule F (fepomepι n → F) := LinearMap.range (Matrix.mulVecLin ε)
  let q : Submodule F (fepomepι n → F) := LinearMap.range (Matrix.mulVecLin est)
  let r : Submodule F (fepomepι n → F) := LinearMap.range (Matrix.mulVecLin (1 - ε))
  have hεe : ε * e = e := by rw [(fepomep_adjoin_comm hS ε hε.1 e he.1).eq, heε]
  have hεest : ε * est = est := by rw [(fepomep_adjoin_comm hS ε hε.1 est hestA).eq, hestε]
  have hWP : W ≤ P := by
    intro x hx
    rw [hW] at hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨Matrix.mulVec e z, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεe, Matrix.mulVecLin_apply]
  have hWin : ∀ z, z ∈ LinearMap.range (Matrix.mulVecLin e) → z ∈ W :=
    fun z hz => by rw [hW]; exact hz
  have hqP : q ≤ P := by
    rintro x ⟨z, rfl⟩
    refine ⟨Matrix.mulVec est z, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεest, Matrix.mulVecLin_apply]
  have hPmem : ∀ x : P, Matrix.mulVec ε (x : fepomepι n → F) = (x : fepomepι n → F) := by
    intro x
    obtain ⟨y, hy⟩ := x.2
    rw [← hy, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hε.2.1.eq]
  have hPdecomp : ∀ x : P,
      (x : fepomepι n → F) = Matrix.mulVec e (x : fepomepι n → F) +
        Matrix.mulVec est (x : fepomepι n → F) := by
    intro x
    rw [← Matrix.add_mulVec e est (x : fepomepι n → F), ← hsum]
    exact (hPmem x).symm
  have hgVmem : ∀ x : P, gV (x : fepomepι n → F) ∈ P := by
    intro x
    refine ⟨gV (x : fepomepι n → F), ?_⟩
    rw [Matrix.mulVecLin_apply]
    have hd := hPdecomp x
    have hwEl : Matrix.mulVec e (x : fepomepι n → F) ∈ W :=
      hWin _ ⟨(x : fepomepι n → F), by rw [Matrix.mulVecLin_apply]⟩
    have hqEl : Matrix.mulVec est (x : fepomepι n → F) ∈ q :=
      ⟨(x : fepomepι n → F), by rw [Matrix.mulVecLin_apply]⟩
    rw [hd, map_add, hact ⟨Matrix.mulVec e (x : fepomepι n → F), hwEl⟩,
      hstar ⟨Matrix.mulVec est (x : fepomepι n → F), hqEl⟩]
    rw [Matrix.mulVec_add]
    congr 1
    · exact hPmem ⟨_, hWP (g ⟨Matrix.mulVec e (x : fepomepι n → F), hwEl⟩).2⟩
    · exact hPmem ⟨_, hqP (gstar ⟨Matrix.mulVec est (x : fepomepι n → F), hqEl⟩).2⟩
  let gVPmap : P →ₗ[F] P :=
    ((gV : (fepomepι n → F) →ₗ[F] (fepomepι n → F)).comp P.subtype).codRestrict P
      (fun x => hgVmem x)
  have hgVPmap : ∀ x : P, (gVPmap x : fepomepι n → F) = gV (x : fepomepι n → F) := fun x => rfl
  have hinj : Function.Injective gVPmap := by
    intro x y hxy
    have h := congrArg (fun z : P => (z : fepomepι n → F)) hxy
    rw [hgVPmap x, hgVPmap y] at h
    exact Subtype.ext (gV.injective h)
  have hsurj : Function.Surjective gVPmap := by
    intro y
    have hyd := hPdecomp y
    obtain ⟨w, hw⟩ : ∃ w : W,
        (g w : fepomepι n → F) = Matrix.mulVec e (y : fepomepι n → F) :=
      ⟨g.symm ⟨Matrix.mulVec e (y : fepomepι n → F),
          hWin _ ⟨(y : fepomepι n → F), by rw [Matrix.mulVecLin_apply]⟩⟩,
        congrArg Subtype.val (g.apply_symm_apply _)⟩
    obtain ⟨y', hy'⟩ : ∃ y' : q,
        (gstar y' : fepomepι n → F) = Matrix.mulVec est (y : fepomepι n → F) :=
      ⟨gstar.symm ⟨Matrix.mulVec est (y : fepomepι n → F),
          ⟨(y : fepomepι n → F), by rw [Matrix.mulVecLin_apply]⟩⟩,
        congrArg Subtype.val (gstar.apply_symm_apply _)⟩
    refine ⟨⟨(w : fepomepι n → F) + (y' : fepomepι n → F),
      Submodule.add_mem P (hWP w.2) (hqP y'.2)⟩, ?_⟩
    apply Subtype.ext
    rw [hgVPmap]
    show gV ((w : fepomepι n → F) + (y' : fepomepι n → F)) = (y : fepomepι n → F)
    rw [map_add, hact w, hstar y', hw, hy', ← hyd]
  let gVP : P ≃ₗ[F] P := LinearEquiv.ofBijective gVPmap ⟨hinj, hsurj⟩
  have hgVP : ∀ x : P, (gVP x : fepomepι n → F) = gV (x : fepomepι n → F) := by
    intro x
    change ((gVPmap x : P) : fepomepι n → F) = gV (x : fepomepι n → F)
    exact hgVPmap x
  refine ⟨P, r, gVP, fepomep_isCompl_eps_compl n hε.2.1, rfl, hgVP, ?_⟩
  intro x
  obtain ⟨v, hv⟩ := x.2
  change (x : fepomepι n → F) = gV (x : fepomepι n → F)
  rw [← hv, Matrix.mulVecLin_apply, hfix v]

private lemma fepomep_levi_gVP_dim (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (g : W ≃ₗ[K] W) (gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))))
    (hgstar : ∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))),
      QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F) (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F))
    (hact : ∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F))
    (hstar : ∀ y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))),
      gV (y : fepomepι n → F) = (gstar y : fepomepι n → F))
    (hfix : ∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v)
    (P r : Submodule F (fepomepι n → F)) (gVP : P ≃ₗ[F] P)
    (hPε : P = LinearMap.range (Matrix.mulVecLin ε))
    (hP : ∀ x : P, (gVP x : fepomepι n → F) = gV (x : fepomepι n → F))
    (hr : ∀ x : r, (LinearEquiv.refl F r x : fepomepι n → F) = gV (x : fepomepι n → F)) :
    Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace gVP) =
      Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace (g.restrictScalars F)) +
        Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace gstar) := by
  classical
  obtain ⟨hestA, hestidem, hdouble, hestε, hneEst, hzero1, hzero2, hsum⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  let est : Matrix (fepomepι n) (fepomepι n) F := formAdj (RingHom.id F) (fepomepG n F) e
  let q : Submodule F (fepomepι n → F) := LinearMap.range (Matrix.mulVecLin est)
  have hεe : ε * e = e := by rw [(fepomep_adjoin_comm hS ε hε.1 e he.1).eq, heε]
  have hεest : ε * est = est := by rw [(fepomep_adjoin_comm hS ε hε.1 est hestA).eq, hestε]
  have hWP_range : W ≤ LinearMap.range (Matrix.mulVecLin ε) := by
    intro x hx
    rw [hW] at hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨Matrix.mulVec e z, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεe, Matrix.mulVecLin_apply]
  have hqP_range : q ≤ LinearMap.range (Matrix.mulVecLin ε) := by
    rintro x ⟨z, rfl⟩
    refine ⟨Matrix.mulVec est z, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hεest, Matrix.mulVecLin_apply]
  have hWP : W ≤ P := hPε.symm ▸ hWP_range
  have hqP : q ≤ P := hPε.symm ▸ hqP_range
  let Wsub : Submodule F P := W.comap P.subtype
  let qsub : Submodule F P := q.comap P.subtype
  have hcompl' : IsCompl Wsub qsub := by
    have h := fepomep_isCompl_e_estar n hn S hSU hS hε he heε hne
    show IsCompl (W.comap P.subtype) (q.comap P.subtype)
    rw [hW, hPε]
    exact h
  have hp : ∀ x ∈ Wsub, gVP x ∈ Wsub := by
    intro x hx
    rw [Submodule.mem_comap] at hx ⊢
    change (gVP x : fepomepι n → F) ∈ W
    rw [hP x, hact ⟨(x : fepomepι n → F), hx⟩]
    exact (g ⟨(x : fepomepι n → F), hx⟩).2
  have hq : ∀ x ∈ qsub, gVP x ∈ qsub := by
    intro x hx
    rw [Submodule.mem_comap] at hx ⊢
    change (gVP x : fepomepι n → F) ∈ q
    rw [hP x, hstar ⟨(x : fepomepι n → F), hx⟩]
    exact (gstar ⟨(x : fepomepι n → F), hx⟩).2
  let eΦ : Wsub ≃ₗ[F] W := Submodule.comapSubtypeEquivOfLe hWP
  let eΨ : qsub ≃ₗ[F] q := Submodule.comapSubtypeEquivOfLe hqP
  have hΦval : ∀ x : Wsub, (eΦ x : fepomepι n → F) = (x : fepomepι n → F) := fun x => rfl
  have hΦsymm : ∀ y : W, (eΦ.symm y : fepomepι n → F) = (y : fepomepι n → F) := by
    intro y
    have h := hΦval (eΦ.symm y)
    rw [eΦ.apply_symm_apply] at h
    exact h.symm
  have hΨval : ∀ x : qsub, (eΨ x : fepomepι n → F) = (x : fepomepι n → F) := fun x => rfl
  have hΨsymm : ∀ y : q, (eΨ.symm y : fepomepι n → F) = (y : fepomepι n → F) := by
    intro y
    have h := hΨval (eΨ.symm y)
    rw [eΨ.apply_symm_apply] at h
    exact h.symm
  have hep : ∀ x : Wsub,
      ((eΦ.trans ((g.restrictScalars F).trans eΦ.symm)) x : P) = gVP x := by
    intro x
    have hxW : (x : fepomepι n → F) ∈ W := Submodule.mem_comap.mp x.2
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    apply Subtype.ext
    rw [hΦsymm ((g.restrictScalars F) (eΦ x)), hP (x : P),
      hact ⟨(x : fepomepι n → F), hxW⟩]
    exact congrArg (fun w : W => (g w : fepomepι n → F)) (Subtype.ext (hΦval x))
  have heq : ∀ x : qsub,
      ((eΨ.trans (gstar.trans eΨ.symm)) x : P) = gVP x := by
    intro x
    have hxQ : (x : fepomepι n → F) ∈ q := Submodule.mem_comap.mp x.2
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    apply Subtype.ext
    rw [hΨsymm (gstar (eΨ x)), hP (x : P), hstar ⟨(x : fepomepι n → F), hxQ⟩]
    exact congrArg (fun y : q => (gstar y : fepomepι n → F)) (Subtype.ext (hΨval x))
  have hdim := fepomep_finrank_commSpace_restrict_isCompl gVP Wsub qsub hcompl' hp hq
    (eΦ.trans ((g.restrictScalars F).trans eΦ.symm))
    (eΨ.trans (gstar.trans eΨ.symm)) hep heq
  have h1 := fepomep_finrank_commSpace_conj (F := F) (V₁ := Wsub) (V₂ := W) eΦ
    (g.restrictScalars F)
  have h2 := fepomep_finrank_commSpace_conj (F := F) (V₁ := qsub) (V₂ := q) eΨ gstar
  rw [h1, h2] at hdim
  exact hdim

private lemma fepomep_levi_decomp_data (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (g : W ≃ₗ[K] W) (gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))))
    (hgstar : ∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))),
      QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F) (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F))
    (hact : ∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F))
    (hstar : ∀ y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))),
      gV (y : fepomepι n → F) = (gstar y : fepomepι n → F))
    (hfix : ∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v) :
    ∃ (P r : Submodule F (fepomepι n → F)) (gVP : P ≃ₗ[F] P),
      IsCompl P r ∧
      P = LinearMap.range (Matrix.mulVecLin ε) ∧
      (∀ x : P, (gVP x : fepomepι n → F) = gV (x : fepomepι n → F)) ∧
      (∀ x : r, (LinearEquiv.refl F r x : fepomepι n → F) = gV (x : fepomepι n → F)) ∧
      Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace gVP) =
        Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace (g.restrictScalars F)) +
          Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace gstar) := by
  obtain ⟨P, r, gVP, hcompl, hPε, hP, hr⟩ :=
    fepomep_levi_gVP_action n hn S hSU hS hε he heε hne hdeg K W hW g gV gstar hgstar hact
      hstar hfix
  exact ⟨P, r, gVP, hcompl, hPε, hP, hr,
    fepomep_levi_gVP_dim n hn S hSU hS hε he heε hne hdeg K W hW g gV gstar hgstar hact
      hstar hfix P r gVP hPε hP hr⟩

private lemma fepomep_finrank_commSpace_levi_block (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (g : W ≃ₗ[K] W) (gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))))
    (hgstar : ∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))),
      QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F) (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F))
    (hact : ∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F))
    (hstar : ∀ y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))),
      gV (y : fepomepι n → F) = (gstar y : fepomepι n → F))
    (hfix : ∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v) :
    Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace gV) =
      Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace (g.restrictScalars F)) +
        Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace gstar) := by
  obtain ⟨P, r, gVP, hcompl, hPε, hP, hr, hdim⟩ :=
    fepomep_levi_decomp_data n hn S hSU hS hε he heε hne hdeg K W hW g gV gstar hgstar hact
      hstar hfix
  have hp : ∀ x ∈ P, gV x ∈ P := fun x hx => by
    have h := hP ⟨x, hx⟩
    rw [← h]
    exact (gVP ⟨x, hx⟩).2
  have hq : ∀ x ∈ r, gV x ∈ r := fun x hx => by
    rw [← hr ⟨x, hx⟩]
    exact hx
  have h0 : Module.finrank F
      (CFSG.RankThree.OrthogonalInvolutions.commSpace (LinearEquiv.refl F r)) = 0 := by
    rw [CFSG.RankThree.OrthogonalInvolutions.commSpace]
    have hzero : ((LinearEquiv.refl F r : r ≃ₗ[F] r) - 1 : r →ₗ[F] r) = 0 := by
      ext x
      simp
    rw [hzero, LinearMap.range_zero, finrank_bot]
  have h2 := fepomep_finrank_commSpace_restrict_isCompl gV P r hcompl hp hq gVP
    (LinearEquiv.refl F r) hP hr
  rw [h0, add_zero, hdim] at h2
  exact h2

private lemma fepomep_commSpace_even_of_block_action (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (g : W ≃ₗ[K] W) (gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (gstar : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))) ≃ₗ[F]
      ↥(LinearMap.range (Matrix.mulVecLin (formAdj (RingHom.id F) (fepomepG n F) e))))
    (hgstar : ∀ (x : W) (y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e)))),
      QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F) (gstar y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F))
    (hact : ∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F))
    (hstar : ∀ y : ↥(LinearMap.range (Matrix.mulVecLin
        (formAdj (RingHom.id F) (fepomepG n F) e))),
      gV (y : fepomepι n → F) = (gstar y : fepomepι n → F))
    (hfix : ∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v) :
    Even (Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace gV)) := by
  rw [fepomep_finrank_commSpace_levi_block n hn S hSU hS hε he heε hne hdeg K W hW g gV gstar
    hgstar hact hstar hfix]
  rw [fepomep_finrank_commSpace_dual_adjoint n hn S hSU hS hε he heε hne K W hW g gstar hgstar]
  exact ⟨Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace (g.restrictScalars F)),
    rfl⟩

private lemma fepomep_levi_commSpace_even (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W) (gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (horth : gV ∈ TauCeti.QuadraticMap.orthogonalGroup (fepomepQ n F))
    (hfix : ∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v)
    (hcomm : ∀ s ∈ S, ∀ v : fepomepι n → F,
      gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v) =
        Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (gV v))
    (hact : ∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F)) :
    Even (Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace gV)) := by
  obtain ⟨gstar, hgstar, hstar⟩ :=
    fepomep_levi_block_action n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg W hW
      hK g gV horth hfix hcomm hact
  exact fepomep_commSpace_even_of_block_action n hn S hSU hS hε he heε hne hdeg K W hW g gV
    gstar hgstar hact hstar hfix

private lemma fepomep_dualPair_levi_omega (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W) (gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (horth : gV ∈ TauCeti.QuadraticMap.orthogonalGroup (fepomepQ n F))
    (hfix : ∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v)
    (hcomm : ∀ s ∈ S, ∀ v : fepomepι n → F,
      gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v) =
        Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (gV v))
    (hact : ∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F)) :
    gV ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (fepomepQ n F)
        (Spin.nondegenerate_polarBilin_quadPlus n F) := by
  exact (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup).mpr
    ⟨horth, fepomep_levi_commSpace_even n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker
      hπdeg W hW hK g gV horth hfix hcomm hact⟩

private lemma fepomep_dualPair_levi_linear (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W) :
    ∃ gV : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F),
      gV ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (fepomepQ n F)
          (Spin.nondegenerate_polarBilin_quadPlus n F) ∧
      (∀ v : fepomepι n → F, gV (Matrix.mulVec (1 - ε) v) = Matrix.mulVec (1 - ε) v) ∧
      (∀ s ∈ S, ∀ v : fepomepι n → F,
        gV (Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) v) =
          Matrix.mulVec (s : Matrix (fepomepι n) (fepomepι n) F) (gV v)) ∧
      (∀ w : W, gV (w : fepomepι n → F) = (g w : fepomepι n → F)) := by
  obtain ⟨gV, horth, hfix, hcomm, hact⟩ :=
    fepomep_dualPair_levi_isometry n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg
      W hW hK g
  exact ⟨gV, fepomep_dualPair_levi_omega n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker
      hπdeg W hW hK g gV horth hfix hcomm hact, hfix, hcomm, hact⟩

private lemma fepomep_dualPair_levi_lift (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (g : W ≃ₗ[K] W) :
    ∃ u : ↥(spinGroup (fepomepQ n F)),
      ((fepomepJ n F u : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) * (1 - ε) = 1 - ε ∧
      (∀ s ∈ S, ((fepomepJ n F u : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) * s =
        s * ((fepomepJ n F u : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F)) ∧
      (∀ w : W, Matrix.mulVec ((fepomepJ n F u : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F) =
        (g w : fepomepι n → F)) := by
  obtain ⟨gV, hΩ, hfix, hcomm, hact⟩ :=
    fepomep_dualPair_levi_linear n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg W hW
      hK g
  obtain ⟨h, hh⟩ :=
    CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus hn hΩ
  let h' : ↥(spinGroup (fepomepQ n F)) := h
  have hh' : Spin.spinAction (fepomepQ n F) h' = gV := hh
  have hM (v : fepomepι n → F) :
      Matrix.mulVec ((fepomepJ n F h' : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F) v = gV v := by
    rw [show ((fepomepJ n F h' : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F) =
        (Spin.spinMatrix (fepomepQ n F) h' :
          Matrix (fepomepι n) (fepomepι n) F) from rfl,
      Spin.spinMatrix_mulVec (Q := fepomepQ n F), hh']
  refine ⟨h', ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    change Matrix.mulVec (((fepomepJ n F h' : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F) * (1 - ε)) v = Matrix.mulVec (1 - ε) v
    rw [← Matrix.mulVec_mulVec v ((fepomepJ n F h' : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F) (1 - ε), hM, hfix]
  · intro s hs
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    change Matrix.mulVec (((fepomepJ n F h' : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F) * (s : Matrix (fepomepι n) (fepomepι n) F)) v =
      Matrix.mulVec ((s : Matrix (fepomepι n) (fepomepι n) F) *
        ((fepomepJ n F h' : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F)) v
    rw [← Matrix.mulVec_mulVec v ((fepomepJ n F h' : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F) (s : Matrix (fepomepι n) (fepomepι n) F), hM,
      hcomm s hs v, ← Matrix.mulVec_mulVec v (s : Matrix (fepomepι n) (fepomepι n) F)
        ((fepomepJ n F h' : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F), hM]
  · intro w
    rw [hM]
    exact hact w

private lemma fepomep_dualPair_blockAction_surjective (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    Function.Surjective ρ := by
  intro g
  obtain ⟨u, hfix, hcomm, hact⟩ :=
    fepomep_dualPair_levi_lift n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg W hW
      hK g
  have hcent : (fepomepJ n F u : GL (fepomepι n) F) ∈ Subgroup.centralizer S :=
    Subgroup.mem_centralizer_iff.mpr fun s hs => Units.ext (hcomm s hs).symm
  let uG : glBlockCentralizer (fepomepJ n F) S ε :=
    ⟨u, Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨hcent, hfix⟩)⟩
  refine ⟨uG, ?_⟩
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  exact (hρ uG w).trans (hact w)

private lemma fepomep_dualPair_blockAction (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∃ (φ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W)),
      Function.Bijective φ := by
  obtain ⟨ρ, hρ⟩ :=
    fepomep_dualPair_blockActionHom n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker
      hπdeg W hW hK
  exact ⟨ρ,
    fepomep_dualPair_blockAction_injective n hn S hSU hS hε he heε hne hdeg K π hπsurj
      hπker hπdeg W hW hK ρ hρ,
    fepomep_dualPair_blockAction_surjective n hn S hSU hS hε he heε hne hdeg K π hπsurj
      hπker hπdeg W hW hK ρ hρ⟩

private lemma fepomep_blockLinearEquiv_gl (K : Type) [Field K]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] :
    Nonempty ((W ≃ₗ[K] W) ≃* Matrix.GeneralLinearGroup (Fin (Module.finrank K W)) K) := by
  exact ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm.trans
    ((Matrix.GeneralLinearGroup.toLin' (Module.finBasis K W)).symm)⟩

private lemma fepomep_isMulCommutative_gl_of_le_one {K : Type} [Field K] {m' : ℕ}
    (hm' : m' ≤ 1) : IsMulCommutative (Matrix.GeneralLinearGroup (Fin m') K) := by
  rcases (by omega : m' = 0 ∨ m' = 1) with rfl | rfl
  · haveI : Subsingleton (Matrix.GeneralLinearGroup (Fin 0) K) := inferInstance
    exact isMulCommutative_iff.mpr (fun a b => Subsingleton.elim (a * b) (b * a))
  · exact isMulCommutative_iff.mpr (fun a b => by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_one, mul_comm])

private lemma fepomep_rank_two_of_component {G : Type} [Group G] (H : Subgroup G)
    {J' : Subgroup G} (hJ : IsComponentOf J' ⁅H, H⁆)
    {K : Type} [Field K] [Finite K] {m' : ℕ}
    (hiso : Nonempty (↥H ≃* Matrix.GeneralLinearGroup (Fin m') K)) : 2 ≤ m' := by
  by_contra h
  have hm' : m' ≤ 1 := by omega
  have hcommGL := fepomep_isMulCommutative_gl_of_le_one (K := K) hm'
  obtain ⟨φ⟩ := hiso
  have hcommH : ∀ a b : H, a * b = b * a := by
    intro a b
    apply φ.injective
    rw [map_mul, map_mul]
    exact (isMulCommutative_iff.mp hcommGL) (φ a) (φ b)
  have hJleH : J' ≤ H := hJ.1.trans (Subgroup.commutator_le_self H)
  haveI : IsMulCommutative ↥J' :=
    isMulCommutative_iff.mpr (fun a b => Subtype.ext
      (congrArg (fun h : H => (h : G))
        (hcommH ⟨(a : G), hJleH a.2⟩ ⟨(b : G), hJleH b.2⟩)))
  haveI : Group.IsPerfect ↥J' := Group.IsPerfect.mk hJ.2.2.1
  haveI : Nontrivial (↥J' ⧸ Subgroup.center ↥J') := hJ.2.2.2.toNontrivial
  haveI : Nontrivial ↥J' := (QuotientGroup.mk'_surjective (Subgroup.center ↥J')).nontrivial
  have hsub : Subsingleton ↥J' := Group.IsPerfect.subsingleton_of_isMulCommutative
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial ↥J')
  exact hxy (hsub.elim x y)

private lemma fepomep_dualPair_blockGroup_iso (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e) :
    ∃ m' : ℕ, 2 ≤ m' ∧ Nonempty
      (glBlockCentralizer (fepomepJ n F) S ε ≃*
        Matrix.GeneralLinearGroup (Fin m') K) := by
  obtain ⟨W, hW, hmod, htower, hfin, hdim, hm1, hK⟩ :=
    fepomep_dualPair_blockModule n S hS he K π hπsurj hπker hπdeg
  letI : Module K W := hmod
  letI : IsScalarTower F K W := htower
  letI : FiniteDimensional K W := hfin
  obtain ⟨φ, hφ⟩ :=
    fepomep_dualPair_blockAction n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker
      hπdeg W hW hK
  obtain ⟨eGL⟩ := fepomep_blockLinearEquiv_gl K W
  have hiso : Nonempty (glBlockCentralizer (fepomepJ n F) S ε ≃*
      Matrix.GeneralLinearGroup (Fin (Module.finrank K W)) K) :=
    ⟨(MulEquiv.ofBijective φ hφ).trans eGL⟩
  exact ⟨Module.finrank K W,
    fepomep_rank_two_of_component (glBlockCentralizer (fepomepJ n F) S ε) hJε hiso,
    hiso⟩

private lemma fepomep_commutator_iso_SL (m' : ℕ) (hm' : 2 ≤ m') (K : Type) [Field K] [Finite K]
    (hcond : 3 ≤ m' ∨ ∃ s : Finset K, s.card = 4) :
    Nonempty (↥(commutator (Matrix.GeneralLinearGroup (Fin m') K)) ≃*
      Matrix.SpecialLinearGroup (Fin m') K) := by
  have hGL := GGNbrLSideKit.commutator_generalLinear_eq_statedSL hm' hcond
  refine ⟨(MulEquiv.subgroupCongr hGL).trans ?_⟩
  refine ((Subgroup.equivMapOfInjective (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin m') K))
    (Matrix.SpecialLinearGroup.toGL (n := Fin m') (R := K))
    Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (by
        rw [Subgroup.map_top]
        exact (CFSG.Open.StatedAPI.statedSL_eq_range_toGL m' K).symm))).symm.trans
    Subgroup.topEquiv

private lemma fepomep_dualPair_blockGroup_commutator_sl (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e) :
    ∃ m' : ℕ, 2 ≤ m' ∧ Nonempty
      ((⁅glBlockCentralizer (fepomepJ n F) S ε,
          glBlockCentralizer (fepomepJ n F) S ε⁆ :
          Subgroup ↥(spinGroup (fepomepQ n F))) ≃*
        Matrix.SpecialLinearGroup (Fin m') K) := by
  obtain ⟨m', hm', ⟨φ⟩⟩ :=
    fepomep_dualPair_blockGroup_iso n hn f hc S hSU hS hε hJε he heε hne hdeg K π hπsurj
      hπker hπdeg
  have hKcard : Nat.card K = 2 ^ (f * blockDegree (fepomepA n F S) e) :=
    fepomep_blockField_card f _ hc hπdeg
  have hf1 : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    subst f
    rw [pow_zero] at hc
    have h2 : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
    omega
  have hKcard4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    have h2 : 2 ≤ f * blockDegree (fepomepA n F S) e := by
      calc 2 = 1 * 2 := by norm_num
        _ ≤ f * blockDegree (fepomepA n F S) e := Nat.mul_le_mul hf1 hdeg
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * blockDegree (fepomepA n F S) e) :=
          Nat.pow_le_pow_right (by norm_num) h2
  haveI : Fintype K := Fintype.ofFinite K
  have hcond : 3 ≤ m' ∨ ∃ s : Finset K, s.card = 4 := by
    rcases Nat.lt_or_ge m' 3 with h3 | h3
    · right
      have h4' : 4 ≤ (Finset.univ : Finset K).card := by
        simpa [Nat.card_eq_fintype_card] using hKcard4
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4'
      exact ⟨t, ht⟩
    · exact Or.inl h3
  obtain ⟨eSL⟩ := fepomep_commutator_iso_SL m' hm' K hcond
  let G := glBlockCentralizer (fepomepJ n F) S ε
  have hcomm_sub : (commutator ↥G).map G.subtype = ⁅G, G⁆ :=
    Subgroup.map_subtype_commutator G
  have e1 : ↥(⁅G, G⁆) ≃* ↥(commutator ↥G) :=
    (MulEquiv.subgroupCongr hcomm_sub.symm).trans
      (Subgroup.equivMapOfInjective (commutator ↥G) G.subtype G.subtype_injective).symm
  have hmap : (commutator ↥G).map φ.toMonoidHom =
      commutator (Matrix.GeneralLinearGroup (Fin m') K) := by
    have hrange : φ.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr φ.surjective
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, hrange]
    rfl
  have e2 : ↥(commutator ↥G) ≃*
      ↥(commutator (Matrix.GeneralLinearGroup (Fin m') K)) :=
    (MulEquiv.subgroupMap φ (commutator ↥G)).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨m', hm', ⟨e1.trans (e2.trans eSL)⟩⟩

private lemma fepomep_dualPair_component_sl (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e) :
    ∃ m' : ℕ, 2 ≤ m' ∧ Nonempty (↥J' ≃* Matrix.SpecialLinearGroup (Fin m') K) := by
  obtain ⟨m', hm', ⟨φ⟩⟩ :=
    fepomep_dualPair_blockGroup_commutator_sl n hn f hc S hSU hS hε hJε he heε hne hdeg K π
      hπsurj hπker hπdeg
  have hKcard : Nat.card K = 2 ^ (f * blockDegree (fepomepA n F S) e) :=
    fepomep_blockField_card f _ hc hπdeg
  have hf1 : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    subst f
    rw [pow_zero] at hc
    have h2 : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
    omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    have h2 : 2 ≤ f * blockDegree (fepomepA n F S) e := by
      calc 2 = 1 * 2 := by norm_num
        _ ≤ f * blockDegree (fepomepA n F S) e := Nat.mul_le_mul hf1 hdeg
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * blockDegree (fepomepA n F S) e) :=
          Nat.pow_le_pow_right (by norm_num) h2
  have h22 : m' ≠ 2 ∨ Nat.card K ≠ 2 := by
    rcases Nat.lt_or_ge m' 3 with h3 | h3
    · right; omega
    · left; omega
  have h23 : m' ≠ 2 ∨ Nat.card K ≠ 3 := by
    rcases Nat.lt_or_ge m' 3 with h3 | h3
    · right; omega
    · left; omega
  let H := ⁅glBlockCentralizer (fepomepJ n F) S ε,
    glBlockCentralizer (fepomepJ n F) S ε⁆
  have hSLq : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m') K) :=
    ⟨(CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
        m' K hm' h22 h23).1.commutator_eq_top,
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
        m' K hm' h22 h23).2.1⟩
  have hHq : CFSG.Open.IsQuasisimple H := CFSG.Open.IsQuasisimple.of_mulEquiv φ hSLq
  have hsub : CFSG.Open.IsSubnormal (J'.subgroupOf H) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib (CFSG.Assembly.IsSubnormal.subgroupOf hJε.2.1)
  haveI : Group.IsPerfect J' := Group.IsPerfect.mk hJε.2.2.1
  haveI : Group.IsPerfect (J'.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJε.1).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJε.1).symm.surjective
  have hJeq : J' = H := by
    rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
      hHq (J'.subgroupOf H) hsub with hbot | htop
    · exfalso
      have hJ'bot : J' = ⊥ := by
        have hdisj : Disjoint J' H := Subgroup.subgroupOf_eq_bot.mp hbot
        rwa [disjoint_iff, inf_eq_left.mpr hJε.1] at hdisj
      have hnt : Nontrivial J' := CFSG.ComponentClassification.Quasisimple.nontrivial
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥J').mp
          hJε.2.2)
      rw [hJ'bot] at hnt
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
    · exact le_antisymm hJε.1 (Subgroup.subgroupOf_eq_top.mp htop)
  exact ⟨m', hm', by rw [hJeq]; exact ⟨φ⟩⟩

private lemma fepomep_dualPair_model (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e) :
    ∃ m' : ℕ, 2 ≤ m' ∧ CFSG.Open.StatedClassicalModel
      (↥J' ⧸ Subgroup.center ↥J') .PSL m' 2 (blockDegree (fepomepA n F S) e * f) := by
  obtain ⟨m', hm', ⟨φ⟩⟩ :=
    fepomep_dualPair_component_sl n hn f hc S hSU hS hodd hε hJε he heε hne hdeg K π hπsurj
      hπker hπdeg
  have hKcard : Nat.card K = 2 ^ (f * blockDegree (fepomepA n F S) e) :=
    fepomep_blockField_card f _ hc hπdeg
  have hproj : Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL m' K)) :=
    ⟨(QuotientGroup.congr (Subgroup.center ↥J')
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin m') K)) φ
        (Subgroup.map_center_eq φ)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m' K)⟩
  have hfd : 2 ≤ blockDegree (fepomepA n F S) e * f := by
    have h := Nat.mul_le_mul hdeg hf
    simpa using h
  have hpow2 : 2 ^ (blockDegree (fepomepA n F S) e * f) ≠ 2 := by
    intro h2
    have hle : 2 ^ 2 ≤ 2 ^ (blockDegree (fepomepA n F S) e * f) :=
      Nat.pow_le_pow_right (by norm_num) hfd
    omega
  have hpow3 : 2 ^ (blockDegree (fepomepA n F S) e * f) ≠ 3 := by
    intro h3
    have hle : 2 ^ 2 ≤ 2 ^ (blockDegree (fepomepA n F S) e * f) :=
      Nat.pow_le_pow_right (by norm_num) hfd
    omega
  have hadm : CFSG.Open.StatedLieAdmissible .PSL m' 2
      (blockDegree (fepomepA n F S) e * f) :=
    ⟨Nat.prime_two, by omega, hm', fun h => hpow2 (congrArg Prod.snd h),
      fun h => hpow3 (congrArg Prod.snd h)⟩
  have hKcard' : Nat.card K = 2 ^ (blockDegree (fepomepA n F S) e * f) := by
    rw [hKcard, Nat.mul_comm]
  refine ⟨m', hm', ?_⟩
  refine ⟨hadm, K, ‹Field K›, ‹Finite K›, hKcard', ?_⟩
  exact hproj

private lemma fepomep_selfDual_degree_even (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e) :
    ∃ l : ℕ, blockDegree (fepomepA n F S) e = 2 * l ∧ 2 ≤ l := by
  have hG : IsUnit (fepomepG n F).det := fepomep_isUnit_det n
  have hSG : ∀ s ∈ S, Matrix.transpose
      ((s : Matrix (fepomepι n) (fepomepι n) F).map (RingHom.id F)) * fepomepG n F *
      (s : Matrix (fepomepι n) (fepomepι n) F) = fepomepG n F := by
    intro s hs
    obtain ⟨x, rfl⟩ := hSU s hs
    rw [show (((fepomepJ n F x : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F)).map (RingHom.id F) =
        ((fepomepJ n F x : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) from rfl]
    exact fepomep_isometry_of_quad (fepomepQ n F)
      ((fepomepJ n F x : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)
      (Spin.spinMatrix_mem (fepomepQ n F) x)
  have hadj : formAdj (RingHom.id F) (fepomepG n F) e = e := by
    rw [hself]
    exact hε.2.2.2.1
  have hpar := blockDegree_eq_one_or_even_of_formAdj_eq (G := fepomepG n F) hG hS hodd
    hSG (show IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e from he) hadj
  have hEven : Even (blockDegree (fepomepA n F S) e) := by
    rcases hpar with h1 | hev
    · have hd1 : blockDegree (fepomepA n F S) e = 1 := by simpa only [fepomepA] using h1
      omega
    · exact hev
  obtain ⟨l, hl⟩ := hEven
  exact ⟨l, by omega, by omega⟩

private lemma fepomep_selfDual_adjoint_invol (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε) :
    (fepomep_formAdjAlgEquiv n hn S hSU hS (⟨e, he.1⟩ : fepomepA n F S) = ⟨e, he.1⟩) ∧
      (∀ a : fepomepA n F S,
        fepomep_formAdjAlgEquiv n hn S hSU hS
          (fepomep_formAdjAlgEquiv n hn S hSU hS a) = a) := by
  constructor
  · apply Subtype.ext
    change formAdj (RingHom.id F) (fepomepG n F) e = e
    rw [hself]
    exact hε.2.2.2.1
  · intro a
    apply Subtype.ext
    change formAdj (RingHom.id F) (fepomepG n F)
      (formAdj (RingHom.id F) (fepomepG n F) (a : Matrix (fepomepι n) (fepomepι n) F)) =
      (a : Matrix (fepomepι n) (fepomepι n) F)
    exact Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) (fepomep_isUnit_det n )
      (by
        rw [show (fepomepG n F).map (RingHom.id F) = fepomepG n F from rfl]
        exact fepomep_transpose_G n F)
      (a : Matrix (fepomepι n) (fepomepι n) F)

private lemma fepomep_selfDual_ker_eq_map (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hfe : fepomep_formAdjAlgEquiv n hn S hSU hS (⟨e, he.1⟩ : fepomepA n F S) =
      ⟨e, he.1⟩) :
    RingHom.ker π = (RingHom.ker π).map
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S) := by
  have hinvol : ∀ a : fepomepA n F S,
      fepomep_formAdjAlgEquiv n hn S hSU hS
        (fepomep_formAdjAlgEquiv n hn S hSU hS a) = a :=
    (fepomep_selfDual_adjoint_invol n hn S hSU hS hε he hself).2
  have hIle : RingHom.ker π ≤ (RingHom.ker π).comap
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S) := by
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    rw [hπker]
    change (((fepomep_formAdjAlgEquiv n hn S hSU hS a) *
        (⟨e, he.1⟩ : fepomepA n F S) : fepomepA n F S) :
        Matrix (fepomepι n) (fepomepι n) F) = 0
    have hae : a * (⟨e, he.1⟩ : fepomepA n F S) = 0 := by
      rw [RingHom.mem_ker] at ha
      rw [hπker] at ha
      rw [← Subtype.coe_inj]
      simpa using ha
    have h1 : (fepomep_formAdjAlgEquiv n hn S hSU hS a) *
          (⟨e, he.1⟩ : fepomepA n F S) =
        fepomep_formAdjAlgEquiv n hn S hSU hS (a * ⟨e, he.1⟩) := by
      rw [map_mul, hfe]
    rw [h1, hae, map_zero]
    rfl
  apply le_antisymm
  · intro a ha
    have hmem : fepomep_formAdjAlgEquiv n hn S hSU hS a ∈ RingHom.ker π := hIle ha
    have h := Ideal.mem_map_of_mem
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S) hmem
    simpa [hinvol a] using h
  · exact Ideal.map_le_iff_le_comap.mpr hIle

private lemma fepomep_selfDual_tau_kernel_le (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K)
    (hker : RingHom.ker π = (RingHom.ker π).map
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S)) :
    RingHom.ker π ≤ RingHom.ker
      (π.comp (fepomep_formAdjAlgEquiv n hn S hSU hS).toAlgHom) := by
  have hle : RingHom.ker π ≤ (RingHom.ker π).comap
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S) := by
    have h := Ideal.le_comap_map
      (f := (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S))
      (I := RingHom.ker π)
    rwa [← hker] at h
  intro a ha
  have hmem : a ∈ (RingHom.ker π).comap
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S) := hle ha
  rw [Ideal.mem_comap] at hmem
  rw [RingHom.mem_ker] at hmem ⊢
  exact hmem

private lemma fepomep_selfDual_ker_map_of_le (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K)
    (hH : RingHom.ker π ≤ RingHom.ker
      (π.comp (fepomep_formAdjAlgEquiv n hn S hSU hS).toAlgHom)) :
    RingHom.ker π = (RingHom.ker π).map
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S) := by
  have hinvol : ∀ a : fepomepA n F S,
      fepomep_formAdjAlgEquiv n hn S hSU hS
        (fepomep_formAdjAlgEquiv n hn S hSU hS a) = a :=
    (fepomep_selfDual_adjoint_invol n hn S hSU hS hε he hself).2
  have hH' : RingHom.ker π ≤ (RingHom.ker π).comap
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S) := by
    intro a ha
    rw [Ideal.mem_comap]
    have h := hH ha
    rw [RingHom.mem_ker] at h ⊢
    exact h
  apply le_antisymm
  · intro a ha
    have hmem : fepomep_formAdjAlgEquiv n hn S hSU hS a ∈ RingHom.ker π := hH' ha
    have h := Ideal.mem_map_of_mem
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S) hmem
    simpa [hinvol a] using h
  · exact Ideal.map_le_iff_le_comap.mpr hH'

private lemma fepomep_selfDual_liftHom_exists (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hker : RingHom.ker π = (RingHom.ker π).map
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S)) :
    ∃ fK : K →ₐ[F] K, ∀ a : fepomepA n F S, fK (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a) := by
  have hstable : RingHom.ker π ≤ (RingHom.ker π).comap
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S) := by
    have h := Ideal.le_comap_map
      (f := (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S))
      (I := RingHom.ker π)
    rwa [← hker] at h
  have hwell : ∀ a a' : fepomepA n F S, π a = π a' →
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a') := by
    intro a a' h
    have hmem : a - a' ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, h, sub_self]
    have hmem2 : fepomep_formAdjAlgEquiv n hn S hSU hS (a - a') ∈ RingHom.ker π :=
      hstable hmem
    rw [RingHom.mem_ker, map_sub, map_sub] at hmem2
    exact sub_eq_zero.mp hmem2
  let fKfun : K → K := fun x =>
    π (fepomep_formAdjAlgEquiv n hn S hSU hS (Classical.choose (hπsurj x)))
  have hfKfun : ∀ a : fepomepA n F S, fKfun (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a) := by
    intro a
    exact hwell (Classical.choose (hπsurj (π a))) a
      (Classical.choose_spec (hπsurj (π a)))
  let fK : K →ₐ[F] K :=
    { toFun := fKfun
      map_one' := by
        have h := hwell (Classical.choose (hπsurj 1)) 1
          (by rw [Classical.choose_spec (hπsurj 1), map_one])
        simpa [fKfun, map_one] using h
      map_zero' := by
        have h := hwell (Classical.choose (hπsurj 0)) 0
          (by rw [Classical.choose_spec (hπsurj 0), map_zero])
        simpa [fKfun, map_zero] using h
      map_add' := by
        intro x y
        have h := hwell (Classical.choose (hπsurj x) + Classical.choose (hπsurj y))
          (Classical.choose (hπsurj (x + y)))
          (by rw [map_add, Classical.choose_spec (hπsurj x),
            Classical.choose_spec (hπsurj y), Classical.choose_spec (hπsurj (x + y))])
        simp only [map_add] at h
        simpa [fKfun] using h.symm
      map_mul' := by
        intro x y
        have h := hwell (Classical.choose (hπsurj x) * Classical.choose (hπsurj y))
          (Classical.choose (hπsurj (x * y)))
          (by rw [map_mul, Classical.choose_spec (hπsurj x),
            Classical.choose_spec (hπsurj y), Classical.choose_spec (hπsurj (x * y))])
        simp only [map_mul] at h
        simpa [fKfun] using h.symm
      commutes' := by
        intro r
        have hfixed : fepomep_formAdjAlgEquiv n hn S hSU hS
            (algebraMap F (fepomepA n F S) r) = algebraMap F (fepomepA n F S) r :=
          AlgEquiv.commutes _ r
        have h := hwell (algebraMap F (fepomepA n F S) r)
          (Classical.choose (hπsurj (algebraMap F K r)))
          (by rw [Classical.choose_spec (hπsurj (algebraMap F K r)), AlgHom.commutes])
        rw [hfixed, AlgHom.commutes] at h
        simpa [fKfun] using h.symm }
  exact ⟨fK, fun a => hfKfun a⟩

private lemma fepomep_selfDual_tau_liftHom (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hH : RingHom.ker π ≤ RingHom.ker
      (π.comp (fepomep_formAdjAlgEquiv n hn S hSU hS).toAlgHom)) :
    ∃ fK : K →ₐ[F] K, ∀ a : fepomepA n F S, fK (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a) := by
  exact fepomep_selfDual_liftHom_exists n hn S hSU hS hε he hself K π hπsurj
    (fepomep_selfDual_ker_map_of_le n hn S hSU hS hε he hself K π hH)

private lemma fepomep_selfDual_tau_liftHom_sq (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (fK : K →ₐ[F] K)
    (hcompat : ∀ a : fepomepA n F S, fK (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) :
    fK.comp fK = AlgHom.id F K := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := hπsurj x
  have hinvol : ∀ a : fepomepA n F S,
      fepomep_formAdjAlgEquiv n hn S hSU hS
        (fepomep_formAdjAlgEquiv n hn S hSU hS a) = a :=
    (fepomep_selfDual_adjoint_invol n hn S hSU hS hε he hself).2
  change fK (fK (π a)) = π a
  rw [hcompat a]
  change fK (π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) = π a
  rw [hcompat (fepomep_formAdjAlgEquiv n hn S hSU hS a)]
  exact congrArg π (hinvol a)

private lemma fepomep_selfDual_tau_lift_of_liftHom (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K)
    (fK : K →ₐ[F] K) (hfK : fK.comp fK = AlgHom.id F K)
    (hcompat : ∀ a : fepomepA n F S, fK (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) :
    ∃ fK' : K →ₐ[F] K, fK'.comp fK' = AlgHom.id F K ∧
      (∀ a : fepomepA n F S, fK' (π a) =
        π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) :=
  ⟨fK, hfK, hcompat⟩

private lemma fepomep_selfDual_tau_lift (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hH : RingHom.ker π ≤ RingHom.ker
      (π.comp (fepomep_formAdjAlgEquiv n hn S hSU hS).toAlgHom)) :
    ∃ fK : K →ₐ[F] K, fK.comp fK = AlgHom.id F K ∧
      (∀ a : fepomepA n F S, fK (π a) =
        π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) := by
  obtain ⟨fK, hcompat⟩ :=
    fepomep_selfDual_tau_liftHom n hn S hSU hS hε he hself K π hπsurj hH
  exact fepomep_selfDual_tau_lift_of_liftHom n hn S hSU hS hε he hself K π fK
    (fepomep_selfDual_tau_liftHom_sq n hn S hSU hS hε he hself K π hπsurj fK hcompat)
    hcompat

private lemma fepomep_selfDual_tau_of_lift (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (fK : K →ₐ[F] K)
    (hfK : fK.comp fK = AlgHom.id F K)
    (hcompat : ∀ a : fepomepA n F S, fK (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) :
    ∃ τ : K ≃+* K,
      ∀ a : fepomepA n F S, τ (π a) =
        π (fepomep_formAdjAlgEquiv n hn S hSU hS a) := by
  let tauK : K ≃ₐ[F] K := AlgEquiv.ofAlgHom fK fK hfK hfK
  exact ⟨tauK.toRingEquiv, hcompat⟩

private lemma fepomep_selfDual_tau_compat (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hker : RingHom.ker π = (RingHom.ker π).map
      (fepomep_formAdjAlgEquiv n hn S hSU hS : fepomepA n F S →+* fepomepA n F S)) :
    ∃ τ : K ≃+* K,
      ∀ a : fepomepA n F S, τ (π a) =
        π (fepomep_formAdjAlgEquiv n hn S hSU hS a) := by
  have hH := fepomep_selfDual_tau_kernel_le n hn S hSU hS hε he hself K π hker
  obtain ⟨fK, hfK, hcompat⟩ :=
    fepomep_selfDual_tau_lift n hn S hSU hS hε he hself K π hπsurj hH
  exact fepomep_selfDual_tau_of_lift n hn S hSU hS hε he hself K π fK hfK hcompat

private lemma fepomep_selfDual_tau_sq (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (τ : K ≃+* K)
    (hτ : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) :
    τ ^ 2 = 1 := by
  have hinvol : ∀ a : fepomepA n F S,
      fepomep_formAdjAlgEquiv n hn S hSU hS
        (fepomep_formAdjAlgEquiv n hn S hSU hS a) = a :=
    (fepomep_selfDual_adjoint_invol n hn S hSU hS hε he hself).2
  rw [sq]
  ext x
  obtain ⟨a, rfl⟩ := hπsurj x
  change τ (τ (π a)) = π a
  rw [hτ a]
  change τ (π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) = π a
  rw [hτ (fepomep_formAdjAlgEquiv n hn S hSU hS a)]
  exact congrArg π (hinvol a)

private lemma fepomep_selfDual_tau_exists (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0) :
    ∃ τ : K ≃+* K,
      (∀ a : fepomepA n F S, τ (π a) =
        π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) ∧ τ ^ 2 = 1 := by
  have hinv := fepomep_selfDual_adjoint_invol n hn S hSU hS hε he hself
  have hker := fepomep_selfDual_ker_eq_map n hn S hSU hS hε he hself K π hπker hinv.1
  obtain ⟨τ, hτ⟩ :=
    fepomep_selfDual_tau_compat n hn S hSU hS hε he hself K π hπsurj hπker hker
  exact ⟨τ, hτ, fepomep_selfDual_tau_sq n hn S hSU hS hε he hself K π hπsurj hπker τ hτ⟩

private lemma fepomep_selfDual_tau_ne (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτ : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) :
    τ ≠ 1 := by
  intro hτ1
  have hfix : ∀ a : fepomepA n F S,
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a) = π a := by
    intro a
    have h := hτ a
    rw [hτ1] at h
    simpa using h.symm
  have hG : IsUnit (fepomepG n F).det := fepomep_isUnit_det n
  have hSG : ∀ s ∈ S, Matrix.transpose
      ((s : Matrix (fepomepι n) (fepomepι n) F).map (RingHom.id F)) * fepomepG n F *
      (s : Matrix (fepomepι n) (fepomepι n) F) = fepomepG n F := by
    intro s hs
    obtain ⟨x, rfl⟩ := hSU s hs
    rw [show (((fepomepJ n F x : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F)).map (RingHom.id F) =
        ((fepomepJ n F x : GL (fepomepι n) F) :
          Matrix (fepomepι n) (fepomepι n) F) from rfl]
    exact fepomep_isometry_of_quad (fepomepQ n F)
      ((fepomepJ n F x : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)
      (Spin.spinMatrix_mem (fepomepQ n F) x)
  have hgen : ∀ (s : GL (fepomepι n) F) (hs : s ∈ S),
      π (⟨(s : Matrix (fepomepι n) (fepomepι n) F),
        Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : fepomepA n F S) = 1 := by
    intro s hs
    let sA : fepomepA n F S := ⟨(s : Matrix (fepomepι n) (fepomepι n) F),
      Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
    have hmem_inv : ((s⁻¹ : GL (fepomepι n) F) :
        Matrix (fepomepι n) (fepomepι n) F) ∈ fepomepA n F S := by
      rw [← Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSG s hs)]
      exact Geo.formAdj_mem_adjoin (RingHom.id F) hG
        (by intro t ht; simpa using hSG t ht) (Algebra.subset_adjoin ⟨s, hs, rfl⟩)
    let sAinv : fepomepA n F S := ⟨((s⁻¹ : GL (fepomepι n) F) :
      Matrix (fepomepι n) (fepomepι n) F), hmem_inv⟩
    have hsA_mul : sA * sAinv = 1 := by
      apply Subtype.ext
      change (s : Matrix (fepomepι n) (fepomepι n) F) *
        ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hfsA : fepomep_formAdjAlgEquiv n hn S hSU hS sA = sAinv := by
      apply Subtype.ext
      change formAdj (RingHom.id F) (fepomepG n F)
          (s : Matrix (fepomepι n) (fepomepι n) F) =
        ((s⁻¹ : GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F)
      exact Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSG s hs)
    have hπeq : π sAinv = π sA := by
      have h := hfix sA
      rw [hfsA] at h
      exact h
    have hx2 : (π sA) ^ 2 = 1 := by
      rw [pow_two]
      calc π sA * π sA = π sA * π sAinv := by rw [← hπeq]
        _ = π (sA * sAinv) := (map_mul _ _ _).symm
        _ = 1 := by rw [hsA_mul, map_one]
    have hsA_pow : sA ^ orderOf s = 1 := by
      apply Subtype.ext
      change (s : Matrix (fepomepι n) (fepomepι n) F) ^ orderOf s = 1
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    have hxo : (π sA) ^ orderOf s = 1 := by
      rw [← map_pow, hsA_pow, map_one]
    obtain ⟨k, hk⟩ := hodd s hs
    have hxodd : (π sA) ^ (2 * k + 1) = 1 := by
      rw [← hk]; exact hxo
    rw [pow_succ, pow_mul, hx2, one_pow, one_mul] at hxodd
    exact hxodd
  have hspan : Submodule.span F ({1} : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, rfl⟩ := hπsurj x
    have hmem : ∀ b : fepomepA n F S, π b ∈ (⊥ : Subalgebra F K) := by
      intro b
      refine Algebra.adjoin_induction
        (p := fun z hz => π (⟨z, hz⟩ : fepomepA n F S) ∈ (⊥ : Subalgebra F K))
        ?_ ?_ ?_ ?_ b.2
      · rintro z ⟨s, hs, rfl⟩
        simpa only using (show π (⟨(s : Matrix (fepomepι n) (fepomepι n) F),
            Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : fepomepA n F S) ∈ (⊥ : Subalgebra F K) from by
              rw [hgen s hs]
              exact Subalgebra.one_mem (⊥ : Subalgebra F K))
      · intro r
        have hz : (algebraMap F (Matrix (fepomepι n) (fepomepι n) F)) r ∈
            Algebra.adjoin F (Units.val '' S) := Subalgebra.algebraMap_mem _ r
        have heq : (⟨(algebraMap F (Matrix (fepomepι n) (fepomepι n) F)) r, hz⟩ :
            fepomepA n F S) = algebraMap F (fepomepA n F S) r := Subtype.ext rfl
        rw [heq, AlgHom.commutes]
        exact Subalgebra.algebraMap_mem (⊥ : Subalgebra F K) r
      · intro y z hy hz ihy ihz
        have hyz : y + z ∈ Algebra.adjoin F (Units.val '' S) := Subalgebra.add_mem _ hy hz
        have heq : (⟨y + z, hyz⟩ : fepomepA n F S) = ⟨y, hy⟩ + ⟨z, hz⟩ := Subtype.ext rfl
        rw [heq, map_add]
        exact Subalgebra.add_mem _ ihy ihz
      · intro y z hy hz ihy ihz
        have hyz : y * z ∈ Algebra.adjoin F (Units.val '' S) := Subalgebra.mul_mem _ hy hz
        have heq : (⟨y * z, hyz⟩ : fepomepA n F S) = ⟨y, hy⟩ * ⟨z, hz⟩ := Subtype.ext rfl
        rw [heq, map_mul]
        exact Subalgebra.mul_mem _ ihy ihz
    have hxbot : π a ∈ (⊥ : Subalgebra F K) := hmem a
    rw [Algebra.mem_bot] at hxbot
    obtain ⟨c, hc⟩ := hxbot
    rw [← hc, Algebra.algebraMap_eq_smul_one]
    exact (Submodule.mem_span_singleton).mpr ⟨c, rfl⟩
  have hfin : Module.finrank F K = 1 :=
    (finrank_eq_one_iff_of_nonzero (1 : K) one_ne_zero).mpr hspan
  have hd1 : blockDegree (fepomepA n F S) e = 1 := by rw [← hπdeg, hfin]
  omega

private lemma fepomep_selfDual_hermitian (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e) :
    ∃ l : ℕ, blockDegree (fepomepA n F S) e = 2 * l ∧ 2 ≤ l ∧
      ∃ τ : K ≃+* K,
        (∀ a : fepomepA n F S, τ (π a) =
          π (fepomep_formAdjAlgEquiv n hn S hSU hS a)) ∧
        τ ^ 2 = 1 ∧ τ ≠ 1 := by
  obtain ⟨l, hdl, hl2⟩ :=
    fepomep_selfDual_degree_even n hn S hSU hS hodd hε he hself hd4
  obtain ⟨τ, hτ, hτ2⟩ :=
    fepomep_selfDual_tau_exists n hn S hSU hS hε he hself K π hπsurj hπker
  have hτne := fepomep_selfDual_tau_ne n hn S hSU hS hodd hε he hself hd4 K π hπsurj
    hπker hπdeg τ hτ
  exact ⟨l, hdl, hl2, τ, hτ, hτ2, hτne⟩

private lemma fepomep_selfDual_blockModule (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e) :
    ∃ (W : Submodule F (fepomepι n → F)) (_ : W = LinearMap.range (Matrix.mulVecLin e))
      (_ : Module K W) (_ : IsScalarTower F K W) (_ : FiniteDimensional K W),
      Module.finrank F W = blockDegree (fepomepA n F S) e * Module.finrank K W ∧
        1 ≤ Module.finrank K W ∧
        ∀ (a : fepomepA n F S) (w : W),
          ((π a • w : W) : fepomepι n → F) =
            Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F) := by
  exact fepomep_dualPair_blockModule n S hS he K π hπsurj hπker hπdeg

private lemma fepomep_selfDual_blockActionEnd (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∃ (ρEnd : glBlockCentralizer (fepomepJ n F) S ε →* Module.End K W),
      ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
        ((ρEnd u w : W) : fepomepι n → F) =
          Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
            Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F) := by
  classical
  let M (u : glBlockCentralizer (fepomepJ n F) S ε) :
      Matrix (fepomepι n) (fepomepι n) F :=
    fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))
  have hM_mul (u u' : glBlockCentralizer (fepomepJ n F) S ε) :
      M (u * u') = M u * M u' := by
    change (fepomepJ n F ((u * u') : ↥(spinGroup (fepomepQ n F))) :
        Matrix (fepomepι n) (fepomepι n) F) =
      (fepomepJ n F (u : ↥(spinGroup (fepomepQ n F))) :
        Matrix (fepomepι n) (fepomepι n) F) *
      (fepomepJ n F (u' : ↥(spinGroup (fepomepQ n F))) :
        Matrix (fepomepι n) (fepomepι n) F)
    rw [map_mul, Units.val_mul]
  have hM_one : M 1 = 1 := by
    change (fepomepJ n F (1 : ↥(spinGroup (fepomepQ n F))) :
      Matrix (fepomepι n) (fepomepι n) F) = 1
    rw [map_one]
    rfl
  let rhoF (u : glBlockCentralizer (fepomepJ n F) S ε) : W →ₗ[F] W :=
    ((Matrix.mulVecLin (M u)).comp W.subtype).codRestrict W (fun v => by
      rw [LinearMap.comp_apply, Submodule.coe_subtype, Matrix.mulVecLin_apply]
      exact fepomep_blockCentralizer_stable n hn S hSU hS hε he W hW u v v.2)
  have hrhoF_apply (u : glBlockCentralizer (fepomepJ n F) S ε) (v : W) :
      (rhoF u v : fepomepι n → F) = Matrix.mulVec (M u) v := rfl
  have hrhoF_smul (u : glBlockCentralizer (fepomepJ n F) S ε) (k : K) (v : W) :
      rhoF u (k • v) = k • rhoF u v := by
    obtain ⟨a, ha⟩ := hπsurj k
    apply Subtype.ext
    have hv : k • v = π a • v := by rw [← ha]
    have hw : k • rhoF u v = π a • rhoF u v := by rw [← ha]
    rw [hv, hw, hrhoF_apply, hK a v, hK a (rhoF u v), hrhoF_apply]
    have hcomm : M u * (a : Matrix (fepomepι n) (fepomepι n) F) =
        (a : Matrix (fepomepι n) (fepomepι n) F) * M u :=
      (fepomep_blockCentralizer_commute_adjoin n hn S hSU hS hε u a.2).eq
    rw [Matrix.mulVec_mulVec (v : fepomepι n → F) (M u)
        (a : Matrix (fepomepι n) (fepomepι n) F),
      Matrix.mulVec_mulVec (v : fepomepι n → F)
        (a : Matrix (fepomepι n) (fepomepι n) F) (M u), hcomm]
  refine ⟨{ toFun := fun u =>
      { toFun := rhoF u
        map_add' := fun v v' => (rhoF u).map_add v v'
        map_smul' := fun k v => hrhoF_smul u k v }, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · refine LinearMap.ext fun v => Subtype.ext ?_
    change (rhoF 1 v : fepomepι n → F) = (v : fepomepι n → F)
    rw [hrhoF_apply, hM_one, Matrix.one_mulVec]
  · intro u u'
    refine LinearMap.ext fun v => Subtype.ext ?_
    change (rhoF (u * u') v : fepomepι n → F) = (rhoF u (rhoF u' v) : fepomepι n → F)
    rw [hrhoF_apply, hrhoF_apply, hrhoF_apply, hM_mul, Matrix.mulVec_mulVec]
  · intro u w
    exact hrhoF_apply u w

private lemma fepomep_selfDual_blockActionEnd_bijective (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (ρEnd : glBlockCentralizer (fepomepJ n F) S ε →* Module.End K W)
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρEnd u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∀ u : glBlockCentralizer (fepomepJ n F) S ε, Function.Bijective (ρEnd u) := by
  intro u
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have h := congrArg (ρEnd u⁻¹) hxy
    change ((ρEnd u⁻¹ * ρEnd u) x) = ((ρEnd u⁻¹ * ρEnd u) y) at h
    rw [← map_mul, inv_mul_cancel, map_one] at h
    simpa using h
  · intro y
    refine ⟨ρEnd u⁻¹ y, ?_⟩
    change ((ρEnd u * ρEnd u⁻¹) y) = y
    rw [← map_mul, mul_inv_cancel, map_one]
    simp

private lemma fepomep_selfDual_blockActionHom (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∃ (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W)),
      ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
        ((ρ u w : W) : fepomepι n → F) =
          Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
            Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F) := by
  obtain ⟨ρEnd, hρ⟩ :=
    fepomep_selfDual_blockActionEnd n hn S hSU hS hε he heε hdeg K π hπsurj hπker hπdeg W hW
      hK
  let ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W) :=
  { toFun := fun u =>
      LinearEquiv.ofBijective (ρEnd u)
        (fepomep_selfDual_blockActionEnd_bijective n hn S hSU hS hε he heε hdeg K π hπsurj
          hπker hπdeg W hW hK ρEnd hρ u)
    map_one' := by
      ext w
      rw [LinearEquiv.ofBijective_apply, map_one]
      rfl
    map_mul' := by
      intro u v
      ext w
      rw [LinearEquiv.ofBijective_apply, map_mul, LinearEquiv.mul_apply,
        LinearEquiv.ofBijective_apply]
      rfl }
  exact ⟨ρ, fun u w => hρ u w⟩

private lemma fepomep_selfDual_formInvariant (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      QuadraticMap.polar (fepomepQ n F) (ρ u x : fepomepι n → F)
          (ρ u y : fepomepι n → F) =
        QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F) := by
  intro u x y
  rw [hρ u x, hρ u y,
    fepomep_polar_of_isometry (fepomepQ n F)
      ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
        Matrix (fepomepι n) (fepomepι n) F)
      (Spin.spinMatrix_mem (fepomepQ n F) (u : ↥(spinGroup (fepomepQ n F))))]

private lemma fepomep_selfDual_moduleMatrixEquiv (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (fepomepι n) (fepomepι n) F}
    (he : IsPrimIdemIn (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W] :
    Nonempty (W ≃ₗ[K] (Fin (Module.finrank K W) → K)) := by
  exact ⟨(Module.finBasis K W).equivFun⟩

private lemma fepomep_selfDual_blockAction_injective (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hdeg : 2 ≤ blockDegree (fepomepA n F S) e)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    Function.Injective ρ := by
  intro u v huv
  have h1 : (u * v⁻¹ : glBlockCentralizer (fepomepJ n F) S ε) = 1 := by
    have hw : ρ (u * v⁻¹) = 1 := by
      rw [map_mul, map_inv, huv, mul_inv_cancel]
    have hM : ((fepomepJ n F
        ((u * v⁻¹ : glBlockCentralizer (fepomepJ n F) S ε) :
          ↥(spinGroup (fepomepQ n F)))) : Matrix (fepomepι n) (fepomepι n) F) = 1 := by
      let M : Matrix (fepomepι n) (fepomepι n) F :=
        fepomepJ n F ((u * v⁻¹ : glBlockCentralizer (fepomepJ n F) S ε) :
          ↥(spinGroup (fepomepQ n F)))
      have hMe : M * e = e := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun x => ?_
        have hmem : Matrix.mulVec e x ∈ W := by rw [hW]; exact ⟨x, rfl⟩
        have h := hρ (u * v⁻¹) ⟨Matrix.mulVec e x, hmem⟩
        rw [hw] at h
        change Matrix.mulVec (M * e) x = Matrix.mulVec e x
        rw [← Matrix.mulVec_mulVec x M e]
        exact h.symm
      have hMfix : M * (1 - ε) = 1 - ε :=
        (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp (u * v⁻¹).2)).2
      have hone : e + (1 - ε) = 1 := by rw [hself]; abel
      calc M = M * 1 := (Matrix.mul_one M).symm
        _ = M * (e + (1 - ε)) := by rw [hone, Matrix.mul_one]
        _ = M * e + M * (1 - ε) := by rw [Matrix.mul_add]
        _ = e + (1 - ε) := by rw [hMe, hMfix]
        _ = 1 := hone
    have hJ1 : fepomepJ n F
        ((u * v⁻¹ : glBlockCentralizer (fepomepJ n F) S ε) :
          ↥(spinGroup (fepomepQ n F))) = 1 :=
      Units.ext (by simpa using hM)
    have hker : ((u * v⁻¹ : glBlockCentralizer (fepomepJ n F) S ε) :
        ↥(spinGroup (fepomepQ n F))) ∈ (fepomepJ n F).ker :=
      MonoidHom.mem_ker.mpr hJ1
    rw [show (fepomepJ n F).ker = ⊥ from
      Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero F 2)] at hker
    exact Subtype.ext (Subgroup.mem_bot.mp hker)
  exact mul_inv_eq_one.mp h1

private lemma fepomep_selfDual_blockBasis (K : Type) [Field K] (W : Type) [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (m' : ℕ) (Φ : W ≃ₗ[K] (Fin m' → K)) :
    ∃ bW : Module.Basis (Fin m') K W, ∀ i : Fin m', bW i = Φ.symm (Pi.single i 1) := by
  refine ⟨(Pi.basisFun K (Fin m')).map Φ.symm, ?_⟩
  intro i
  rw [Module.Basis.map_apply, Pi.basisFun_apply]

private lemma fepomep_selfDual_blockBasis_linearCombination (K : Type) [Field K] (W : Type)
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (m' : ℕ) (Φ : W ≃ₗ[K] (Fin m' → K))
    (bW : Module.Basis (Fin m') K W) (hbW : ∀ i : Fin m', bW i = Φ.symm (Pi.single i 1)) :
    ∀ v : Fin m' → K, Φ (Fintype.linearCombination K (⇑bW) v) = v := by
  intro v
  rw [Fintype.linearCombination_apply]
  simp only [map_sum, map_smul]
  have hbWi : ∀ i, Φ (bW i) = Pi.single i 1 := by
    intro i
    rw [hbW i]
    exact Φ.apply_symm_apply _
  simp only [hbWi]
  funext j
  simp [Pi.single_apply, Finset.sum_apply]

private lemma fepomep_selfDual_blockMatrixIso_of_basis (K : Type) [Field K] (W : Type)
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (m' : ℕ) (Φ : W ≃ₗ[K] (Fin m' → K))
    (bW : Module.Basis (Fin m') K W) (hbW : ∀ i : Fin m', bW i = Φ.symm (Pi.single i 1)) :
    ∃ ψ : (W ≃ₗ[K] W) ≃* Matrix.GeneralLinearGroup (Fin m') K,
      ∀ (e : W ≃ₗ[K] W) (i : Fin m'),
        Matrix.mulVec ((ψ e : GL (Fin m') K) : Matrix (Fin m') (Fin m') K) (Pi.single i 1) =
          Φ (e (Φ.symm (Pi.single i 1))) := by
  let ψ : (W ≃ₗ[K] W) ≃* Matrix.GeneralLinearGroup (Fin m') K :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm).trans
      ((Matrix.GeneralLinearGroup.toLin' bW).symm)
  refine ⟨ψ, ?_⟩
  intro e i
  have htoLin : (Matrix.GeneralLinearGroup.toLin' bW) (ψ e) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm e := by
    simp only [ψ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hcoe : ((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm e :
      LinearMap.GeneralLinearGroup K W).toLinearEquiv = e := by
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv K W)
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm e) = e
    exact MulEquiv.apply_symm_apply _ _
  have happ := Matrix.GeneralLinearGroup.toLin'_apply bW (ψ e) (bW i)
  rw [htoLin, hcoe] at happ
  rw [Module.Basis.repr_self bW i, hbW i] at happ
  rw [happ, fepomep_selfDual_blockBasis_linearCombination K W m' Φ bW hbW]
  have harg : (⇑((fun₀ | i => (1 : K)) : Fin m' →₀ K) : Fin m' → K) = Pi.single i 1 :=
    Finsupp.single_eq_pi_single i 1
  rw [harg]

private lemma fepomep_selfDual_blockMatrixIso (K : Type) [Field K] (W : Type) [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (m' : ℕ) (Φ : W ≃ₗ[K] (Fin m' → K)) :
    ∃ ψ : (W ≃ₗ[K] W) ≃* Matrix.GeneralLinearGroup (Fin m') K,
      ∀ (e : W ≃ₗ[K] W) (i : Fin m'),
        Matrix.mulVec ((ψ e : GL (Fin m') K) : Matrix (Fin m') (Fin m') K) (Pi.single i 1) = Φ (e
            (Φ.symm (Pi.single i 1))) := by
  obtain ⟨bW, hbW⟩ := fepomep_selfDual_blockBasis K W m' Φ
  exact fepomep_selfDual_blockMatrixIso_of_basis K W m' Φ bW hbW

private lemma fepomep_selfDual_coord_expansion (K : Type) [Field K] (W : Type) [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (m' : ℕ) (Φ : W ≃ₗ[K] (Fin m' → K)) (x : W) :
    Fintype.linearCombination K
      (fun i => (((Pi.basisFun K (Fin m')).map Φ.symm) i : W)) (Φ x) = x := by
  have hbW : ∀ i : Fin m', ((Pi.basisFun K (Fin m')).map Φ.symm) i = Φ.symm (Pi.single i 1) := by
    intro i
    rw [Module.Basis.map_apply, Pi.basisFun_apply]
  exact Φ.injective (fepomep_selfDual_blockBasis_linearCombination K W m' Φ
    ((Pi.basisFun K (Fin m')).map Φ.symm) hbW (Φ x))

private lemma fepomep_commutator_le_statedSU (m q : ℕ) (K : Type) [Field K]
    (U : Subgroup (GL (Fin m) K))
    (hU : ∀ A ∈ U,
      (((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map (fun x => x ^ q)).transpose *
        ((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1) :
    ⁅U, U⁆ ≤ CFSG.Open.StatedSU m q K := by
  have hSL : ⁅U, U⁆ ≤ MonoidHom.ker (Matrix.GeneralLinearGroup.det (n := Fin m) (R := K)) := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact (commutatorElement_eq_one_iff_mul_comm).mpr (mul_comm _ _)
  refine le_trans (le_inf (Subgroup.commutator_le_self U) hSL) ?_
  rw [CFSG.Open.StatedSU]
  intro A hA
  refine Subgroup.subset_closure ⟨?_, hU A hA.1⟩
  have h := MonoidHom.mem_ker.mp hA.2
  have h2 : ((Matrix.GeneralLinearGroup.det A : Kˣ) : K) = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) h
  simpa [Matrix.GeneralLinearGroup.det] using h2

private lemma fepomep_statedSU_commutator_self {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact (Nat.Prime p)] (hK : Nat.card K = (p ^ f) ^ 2) {m : ℕ} (hm : 3 ≤ m)
    (hne : (m, p ^ f) ≠ (3, 2)) :
    ⁅CFSG.Open.StatedSU m (p ^ f) K, CFSG.Open.StatedSU m (p ^ f) K⁆ =
      CFSG.Open.StatedSU m (p ^ f) K := by
  haveI : Group.IsPerfect ↥(CFSG.Open.StatedSU m (p ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hm hne
  exact Subgroup.commutator_eq_self

private lemma fepomep_selfDual_commutatorSU (m'' : ℕ) {p f : ℕ} [Fact (Nat.Prime p)]
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2)
    (U : Subgroup (GL (Fin m'') K))
    (hU : ∀ A : GL (Fin m'') K, A ∈ U ↔
      (((A : GL (Fin m'') K) : Matrix (Fin m'') (Fin m'') K).map
          (fun x => x ^ (p ^ f))).transpose *
        ((A : GL (Fin m'') K) : Matrix (Fin m'') (Fin m'') K) = 1)
    (hm'' : 3 ≤ m'') (hne : (m'', p ^ f) ≠ (3, 2)) :
    Nonempty (↥⁅U, U⁆ ≃* CFSG.Open.StatedSU m'' (p ^ f) K) := by
  have hle : ⁅U, U⁆ ≤ CFSG.Open.StatedSU m'' (p ^ f) K :=
    fepomep_commutator_le_statedSU m'' (p ^ f) K U (fun A hA => (hU A).mp hA)
  have hSUleU : CFSG.Open.StatedSU m'' (p ^ f) K ≤ U := by
    rw [CFSG.Open.StatedSU, Subgroup.closure_le]
    rintro A ⟨-, huni⟩
    exact (hU A).mpr huni
  have hself := fepomep_statedSU_commutator_self (K := K) (p := p) (f := f) hK hm'' hne
  have hge : CFSG.Open.StatedSU m'' (p ^ f) K ≤ ⁅U, U⁆ := by
    rw [← hself]
    exact Subgroup.commutator_mono hSUleU hSUleU
  exact ⟨MulEquiv.subgroupCongr (le_antisymm hle hge)⟩

private lemma fepomep_commutator_iso {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Nonempty (↥(commutator G) ≃* ↥(commutator H)) := by
  have h : (commutator G).map (e : G →* H) = commutator H := by
    rw [map_commutator_eq]
    simp [commutator_def]
  exact ⟨(e.subgroupMap (commutator G)).trans (MulEquiv.subgroupCongr h)⟩

private lemma fepomep_commutator_subtype_iso {G : Type} [Group G] (H : Subgroup G) :
    Nonempty (↥⁅H, H⁆ ≃* ↥(commutator ↥H)) := by
  have h := Subgroup.map_subtype_commutator H
  exact ⟨((Subgroup.equivMapOfInjective (commutator ↥H) H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr h)).symm⟩

private lemma fepomep_selfDual_extension_polarNondegOn_W (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n) (f l : ℕ)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (A : GL (Fin (Module.finrank K W)) K)
    (hA : (((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
        (fun x => x ^ (2 ^ (l * f)))).transpose *
      ((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) = 1)
 :
    CFSG.ClassicalGroups.Orthogonal.PolarNondegOn (fepomepQ n F) W := by
  intro x hxW hx
  have hnd : (QuadraticMap.polarBilin (fepomepQ n F)).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus n F
  have hεidem : IsIdempotentElem ε := by rw [← hself]; exact he.2.1
  have hεadj : formAdj (RingHom.id F) (fepomepG n F) ε = ε := hε.2.2.2.1
  have hWε : W = LinearMap.range (Matrix.mulVecLin ε) := by rw [hW, hself]
  have hdec : ∀ w : fepomepι n → F, Matrix.mulVec ε w + Matrix.mulVec (1 - ε) w = w := by
    intro w
    rw [← Matrix.add_mulVec]
    have : ε + (1 - ε) = 1 := by abel
    rw [this, Matrix.one_mulVec]
  have hx_mem : x ∈ LinearMap.range (Matrix.mulVecLin ε) := by rw [← hWε]; exact hxW
  obtain ⟨v, hv⟩ := hx_mem
  apply CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero hnd
  intro w
  have h1 : QuadraticMap.polar (fepomepQ n F) x (Matrix.mulVec ε w) = 0 :=
    hx (Matrix.mulVec ε w) (by rw [hWε]; exact ⟨w, rfl⟩)
  have h2 : QuadraticMap.polar (fepomepQ n F) x (Matrix.mulVec (1 - ε) w) = 0 := by
    rw [← hv]
    simpa [Matrix.mulVecLin_apply] using fepomep_polar_eps_compl n hεidem hεadj v w
  rw [← hdec w, QuadraticMap.polar_add_right, h1, h2, add_zero]

private lemma fepomep_selfDual_extension_mem_map (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n) (f l : ℕ)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (A : GL (Fin (Module.finrank K W)) K)
    (hA : (((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
        (fun x => x ^ (2 ^ (l * f)))).transpose *
      ((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) = 1)
    (E : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (hcomm : ∀ s ∈ S, ∀ v : fepomepι n → F,
      E ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec v) =
        (s : Matrix (fepomepι n) (fepomepι n) F).mulVec (E v))
    (hEfix : ∀ v : fepomepι n → F, E ((1 - ε).mulVec v) = (1 - ε).mulVec v)
    (hrange : E ∈ (Spin.spinAction (fepomepQ n F)).range) :
    E ∈ (glBlockCentralizer (fepomepJ n F) S ε).map
      (Spin.spinAction (fepomepQ n F)) := by
  rw [Subgroup.mem_map]
  obtain ⟨g, hg⟩ := hrange
  refine ⟨g, ?_, hg⟩
  rw [glBlockCentralizer, Subgroup.mem_comap]
  refine ⟨?_, ?_⟩
  · apply Subgroup.mem_centralizer_iff.mpr
    intro h hh
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [fepomepJ]
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Spin.spinMatrix_mulVec,
      Spin.spinMatrix_mulVec, hg]
    exact (hcomm h hh x).symm
  · change (Spin.spinMatrix (fepomepQ n F) g :
        Matrix (fepomepι n) (fepomepι n) F) * (1 - ε) = 1 - ε
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro y
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
      Spin.spinMatrix_mulVec, hg, hEfix y]

private lemma fepomep_selfDual_blockGroup_blockCardinality
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W] :
    Nat.card K = (2 ^ (l * f)) ^ 2 ∧
      (Module.finrank K W, 2 ^ (l * f)) ≠ (3, 2) := by
  have hcard2 : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
  have hf1 : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    have h1 : Nat.card F = 1 := by rw [hc, hf0, pow_zero]
    omega
  have hfin : Module.finrank F K = 2 * l := by rw [hπdeg, hl]
  have hKcard : Nat.card K = (2 ^ (l * f)) ^ 2 := by
    rw [fepomep_blockField_card f (2 * l) hc hfin, ← pow_mul]
    congr 1
    ring
  refine ⟨hKcard, ?_⟩
  intro hcon
  have h2 : 2 ^ (l * f) = 2 := congrArg Prod.snd hcon
  have hlf2 : 2 ≤ l * f := by
    have := Nat.mul_le_mul hl2 hf1
    omega
  have h4 : 4 ≤ 2 ^ (l * f) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (l * f) := Nat.pow_le_pow_right (by norm_num) hlf2
  omega

private lemma fepomep_statedSU_two_perfect {K : Type} [Field K] [Finite K] {p f' : ℕ}
    [Fact (Nat.Prime p)] (hK : Nat.card K = (p ^ f') ^ 2) (hq : 4 ≤ p ^ f') :
    Group.IsPerfect ↥(CFSG.Open.StatedSU 2 (p ^ f') K) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ (2 * f') := by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm f' 2]
  haveI : CharP K p := charP_of_card_eq_prime_pow hcard
  exact CFSG.RankThree.SubgroupLists.isPerfect_statedSU_two (r := p) (f := f') hK hq

private lemma fepomep_selfDual_commutatorSU_two
    (m'' : ℕ) {p f' : ℕ} [Fact (Nat.Prime p)]
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f') ^ 2)
    (U : Subgroup (GL (Fin m'') K))
    (hU : ∀ A : GL (Fin m'') K, A ∈ U ↔
      (((A : GL (Fin m'') K) : Matrix (Fin m'') (Fin m'') K).map
          (fun x => x ^ (p ^ f'))).transpose *
        ((A : GL (Fin m'') K) : Matrix (Fin m'') (Fin m'') K) = 1)
    (hm2 : m'' = 2) (hq : 4 ≤ p ^ f') :
    Nonempty (↥⁅U, U⁆ ≃* CFSG.Open.StatedSU m'' (p ^ f') K) := by
  subst hm2
  have hle : ⁅U, U⁆ ≤ CFSG.Open.StatedSU 2 (p ^ f') K :=
    fepomep_commutator_le_statedSU 2 (p ^ f') K U (fun A hA => (hU A).mp hA)
  have hSUleU : CFSG.Open.StatedSU 2 (p ^ f') K ≤ U := by
    rw [CFSG.Open.StatedSU, Subgroup.closure_le]
    rintro A ⟨-, huni⟩
    exact (hU A).mpr huni
  have hself : ⁅CFSG.Open.StatedSU 2 (p ^ f') K, CFSG.Open.StatedSU 2 (p ^ f') K⁆ =
      CFSG.Open.StatedSU 2 (p ^ f') K := by
    haveI : Group.IsPerfect ↥(CFSG.Open.StatedSU 2 (p ^ f') K) :=
      fepomep_statedSU_two_perfect (K := K) (p := p) (f' := f') hK hq
    exact Subgroup.commutator_eq_self
  have hge : CFSG.Open.StatedSU 2 (p ^ f') K ≤ ⁅U, U⁆ := by
    rw [← hself]
    exact Subgroup.commutator_mono hSUleU hSUleU
  exact ⟨MulEquiv.subgroupCongr (le_antisymm hle hge)⟩

private lemma fepomep_selfDual_blockGroup_su_of_unitary
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hf : 1 ≤ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ι : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι : Function.Injective ι)
    (hU : ∀ A : GL (Fin (Module.finrank K W)) K, A ∈ ι.range ↔
      (((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
          (fun x => x ^ (2 ^ (l * f)))).transpose *
        ((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) = 1)
    (hKcard : Nat.card K = (2 ^ (l * f)) ^ 2)
    (hm2 : 2 ≤ Module.finrank K W)
    (hne : (Module.finrank K W, 2 ^ (l * f)) ≠ (3, 2)) :
    ∃ m' : ℕ, 2 ≤ m' ∧ Nonempty
      (↥(⁅glBlockCentralizer (fepomepJ n F) S ε,
          glBlockCentralizer (fepomepJ n F) S ε⁆) ≃*
        CFSG.Open.StatedSU m' (2 ^ (l * f)) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 4 ≤ 2 ^ (l * f) := by
    have hlf2 : 2 ≤ l * f := by
      have := Nat.mul_le_mul hl2 hf
      omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (l * f) := Nat.pow_le_pow_right (by norm_num) hlf2
  let e : ↥(glBlockCentralizer (fepomepJ n F) S ε) ≃* ↥(ι.range) :=
    MonoidHom.ofInjective hι
  have htrans (u : ↥⁅ι.range, ι.range⁆ ≃* CFSG.Open.StatedSU (Module.finrank K W) (2 ^ (l * f)) K) :
      Nonempty (↥⁅glBlockCentralizer (fepomepJ n F) S ε,
          glBlockCentralizer (fepomepJ n F) S ε⁆ ≃*
        CFSG.Open.StatedSU (Module.finrank K W) (2 ^ (l * f)) K) := by
    obtain ⟨i1⟩ := fepomep_commutator_subtype_iso (glBlockCentralizer (fepomepJ n F) S ε)
    obtain ⟨i2⟩ := fepomep_commutator_iso e
    obtain ⟨i3⟩ := fepomep_commutator_subtype_iso ι.range
    exact ⟨(i1.trans (i2.trans i3.symm)).trans u⟩
  by_cases hm : Module.finrank K W = 2
  · obtain ⟨u⟩ :=
      fepomep_selfDual_commutatorSU_two (Module.finrank K W) (p := 2) (f' := l * f) K hKcard
        ι.range hU hm hq
    exact ⟨Module.finrank K W, by omega, htrans u⟩
  · have hm3 : 3 ≤ Module.finrank K W := by omega
    obtain ⟨u⟩ :=
      fepomep_selfDual_commutatorSU (Module.finrank K W) (p := 2) (f := l * f) K hKcard
        ι.range hU hm3 hne
    exact ⟨Module.finrank K W, by omega, htrans u⟩

private lemma fepomep_selfDual_blockGroup_blockRank_pos
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W] :
    1 ≤ Module.finrank K W := by
  have hWne : W ≠ ⊥ := by
    rw [hW]
    intro hbot
    have hzero : Matrix.mulVecLin e = 0 := LinearMap.range_eq_bot.mp hbot
    apply he.2.2.1
    ext i j
    have hv := congrArg (fun f : (fepomepι n → F) →ₗ[F] (fepomepι n → F) =>
      f (Pi.single j 1)) hzero
    have h := congrFun hv i
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.mul_apply, Pi.single_apply] using h
  exact (fepomep_blockModuleRank n S K W hπdeg hWne).2

private lemma fepomep_selfDual_blockGroup_blockRank_ne_one
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    Module.finrank K W ≠ 1 := by
  intro hm1
  obtain ⟨ρ, hρ⟩ :=
    fepomep_selfDual_blockActionHom n hn S hSU hS hε he heε hself (by omega) K π hπsurj
      hπker hπdeg W hW hK
  have hinjρ : Function.Injective ρ :=
    fepomep_selfDual_blockAction_injective n hn S hSU hS hε he heε hself (by omega) K π hπsurj
      hπker hπdeg W hW hK ρ hρ
  have hle1 : Module.finrank K W ≤ 1 := by omega
  haveI : IsMulCommutative (W ≃ₗ[K] W) := by
    obtain ⟨eGL⟩ := fepomep_blockLinearEquiv_gl K W
    refine isMulCommutative_iff.mpr fun a b => eGL.injective ?_
    rw [map_mul, map_mul]
    exact (isMulCommutative_iff.mp (fepomep_isMulCommutative_gl_of_le_one (K := K) hle1))
      (eGL a) (eGL b)
  have hcommG : ∀ a b : glBlockCentralizer (fepomepJ n F) S ε, a * b = b * a := by
    intro a b
    apply hinjρ
    rw [map_mul, map_mul]
    exact (isMulCommutative_iff.mp (inferInstance : IsMulCommutative (W ≃ₗ[K] W)))
      (ρ a) (ρ b)
  have hJleH : J' ≤ glBlockCentralizer (fepomepJ n F) S ε :=
    hJε.1.trans (Subgroup.commutator_le_self _)
  haveI : IsMulCommutative ↥J' :=
    isMulCommutative_iff.mpr (fun a b => Subtype.ext (by
      simpa using hcommG ⟨(a : _), hJleH a.2⟩ ⟨(b : _), hJleH b.2⟩))
  haveI : Group.IsPerfect ↥J' := Group.IsPerfect.mk hJε.2.2.1
  haveI : Nontrivial (↥J' ⧸ Subgroup.center ↥J') := hJε.2.2.2.toNontrivial
  haveI : Nontrivial ↥J' := (QuotientGroup.mk'_surjective (Subgroup.center ↥J')).nontrivial
  have hsub : Subsingleton ↥J' := Group.IsPerfect.subsingleton_of_isMulCommutative
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial ↥J')
  exact hxy (hsub.elim x y)

private lemma fepomep_selfDual_blockGroup_formRankBound
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    2 ≤ Module.finrank K W := by
  have h1 := fepomep_selfDual_blockGroup_blockRank_pos n hn f hc S hSU hS hodd hε hJε he heε
    hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW
  have h2 := fepomep_selfDual_blockGroup_blockRank_ne_one n hn f hc S hSU hS hodd hε hJε he
    heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW hK
  omega

private lemma fepomep_selfDual_blockGroup_formRank
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    Nat.card K = (2 ^ (l * f)) ^ 2 ∧ 2 ≤ Module.finrank K W ∧
      (Module.finrank K W, 2 ^ (l * f)) ≠ (3, 2) := by
  obtain ⟨hcard, hne⟩ :=
    fepomep_selfDual_blockGroup_blockCardinality n hn f hc S hSU hS hodd hε hJε he heε hself
      hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW
  exact ⟨hcard,
    fepomep_selfDual_blockGroup_formRankBound n hn f hc S hSU hS hodd hε hJε he heε hself hd4
      l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW hK,
    hne⟩

private lemma fepomep_hermForm_trace {F E U : Type*} [Field F] [Field E] [Algebra F E] [Finite E]
    [AddCommGroup U] [Module F U] [Module E U] [IsScalarTower F E U]
    (β : U →ₗ[F] U →ₗ[F] F) (hβ : ∀ u w, β u w = β w u)
    (hnd : ∀ u, (∀ w, β u w = 0) → u = 0)
    (σ : E ≃ₐ[F] E) (hσσ : ∀ z, σ (σ z) = z)
    (hbal : ∀ (a : E) (u w : U), β (a • u) w = β u (σ a • w)) :
    ∃ H : U →ₛₗ[σ.toRingHom] U →ₗ[E] E, H.IsSymm ∧ H.SeparatingLeft ∧
      (∀ u w, Algebra.trace F E (H u w) = β u w) := by
  classical
  have hdual : ∀ f : E →ₗ[F] F, ∃ e : E, ∀ c, Algebra.trace F E (e * c) = f c := by
    intro f
    obtain ⟨e, he⟩ := ((Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)).surjective f
    refine ⟨e, fun c => ?_⟩
    have := LinearMap.congr_fun he c
    simpa [LinearMap.BilinForm.toDual_def] using this
  have heq : ∀ {e e' : E}, (∀ c, Algebra.trace F E (e * c) = Algebra.trace F E (e' * c)) → e = e' :=
      by
    intro e e' h
    refine sub_eq_zero.mp ((traceForm_nondegenerate F E).1 (e - e') fun c => ?_)
    rw [Algebra.traceForm_apply, sub_mul, map_sub, h, sub_self]
  let ffun (u w : U) : E →ₗ[F] F :=
    { toFun := fun c => β u (c • w)
      map_add' := fun c c' => by rw [add_smul, map_add]
      map_smul' := fun a c => by rw [smul_assoc, map_smul, RingHom.id_apply] }
  let H₀ : U → U → E := fun u w => Classical.choose (hdual (ffun u w))
  have hH₀ : ∀ u w c, Algebra.trace F E (H₀ u w * c) = β u (c • w) :=
    fun u w c => Classical.choose_spec (hdual (ffun u w)) c
  have htr : ∀ u w, Algebra.trace F E (H₀ u w) = β u w := by
    intro u w
    simpa using hH₀ u w 1
  have haddl : ∀ u u' w, H₀ (u + u') w = H₀ u w + H₀ u' w := by
    intro u u' w
    refine heq fun c => ?_
    rw [add_mul, map_add, hH₀ (u + u') w c, hH₀ u w c, hH₀ u' w c, map_add]
    rfl
  have haddr : ∀ u w w', H₀ u (w + w') = H₀ u w + H₀ u w' := by
    intro u w w'
    refine heq fun c => ?_
    rw [add_mul, map_add, hH₀ u (w + w') c, hH₀ u w c, hH₀ u w' c, smul_add, map_add]
  have hsmulr : ∀ (a : E) u w, H₀ u (a • w) = a * H₀ u w := by
    intro a u w
    refine heq fun c => ?_
    have e : a * H₀ u w * c = H₀ u w * (a * c) := by ring
    rw [e, hH₀ u (a • w) c, smul_smul, mul_comm, ← hH₀ u w (a * c)]
  have hsmull : ∀ (a : E) u w, H₀ (a • u) w = σ a * H₀ u w := by
    intro a u w
    refine heq fun c => ?_
    have e : σ a * H₀ u w * c = H₀ u w * (σ a * c) := by ring
    rw [e, hH₀ (a • u) w c, hbal a u (c • w), smul_smul, ← hH₀ u w (σ a * c)]
  have hsymm : ∀ u w, H₀ w u = σ (H₀ u w) := by
    intro u w
    refine heq fun c => ?_
    rw [hH₀ w u c]
    have h1 : β w (c • u) = Algebra.trace F E (H₀ u w * σ c) := by
      rw [← hβ (c • u) w, hbal c u w, ← hH₀ u w (σ c)]
    have h3 : Algebra.trace F E (H₀ u w * σ c) = Algebra.trace F E (σ (H₀ u w) * c) := by
      rw [← Algebra.trace_eq_of_algEquiv σ (H₀ u w * σ c), map_mul, hσσ]
    rw [h1, h3]
  have hsep : ∀ u, (∀ w, H₀ u w = 0) → u = 0 := by
    intro u hu
    apply hnd u
    intro w
    rw [← htr u w, hu w, map_zero]
  refine ⟨LinearMap.mk₂'ₛₗ σ.toRingHom (RingHom.id E) H₀ ?_ ?_ ?_ ?_, ⟨fun x y => (hsymm x y).symm⟩,
      ?_, htr⟩
  · exact haddl
  · intro l v w
    exact hsmull l v w
  · intro v w w'
    exact haddr v w w'
  · intro l v w
    exact hsmulr l v w
  · intro x hx
    exact hsep x fun w => by have h := hx w; change H₀ x w = 0 at h; exact h

private lemma fepomep_selfDual_blockGroup_descentPolarBilin
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K)) :
    ∃ β : W →ₗ[F] W →ₗ[F] F,
      (∀ u w, β u w = QuadraticMap.polar (fepomepQ n F) (u : fepomepι n → F) (w : fepomepι n →
          F)) ∧
      (∀ u w, β u w = β w u) ∧
      (∀ u, (∀ w, β u w = 0) → u = 0) := by
  let β : W →ₗ[F] W →ₗ[F] F :=
    { toFun := fun u => (QuadraticMap.polarBilin (fepomepQ n F)
          (u : fepomepι n → F)).comp W.subtype
      map_add' := fun u u' => by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.coe_subtype,
          Submodule.coe_add]
        rw [map_add, LinearMap.add_apply]
      map_smul' := fun a u => by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_subtype,
          Submodule.coe_smul]
        rw [map_smul, LinearMap.smul_apply]
        rfl }
  have hβ : ∀ u w, β u w = QuadraticMap.polar (fepomepQ n F) (u : fepomepι n → F) (w : fepomepι n
      → F) := fun u w => rfl
  have hsymm : ∀ u w, β u w = β w u := by
    intro u w
    rw [hβ, hβ]
    exact QuadraticMap.polar_comm (fepomepQ n F) (u : fepomepι n → F)
      (w : fepomepι n → F)
  have hnd : ∀ u : W, (∀ w : W, β u w = 0) → u = 0 := by
    intro u hu
    apply Subtype.ext
    refine fepomep_selfDual_extension_polarNondegOn_W n hn f l S hSU hS hε he heε hself K π
      hπsurj hπker hπdeg W hW Φ 1 ?_ u u.2 ?_
    · simp
    · intro w hw
      exact hu ⟨w, hw⟩
  exact ⟨β, hβ, hsymm, hnd⟩

private lemma fepomep_selfDual_blockGroup_descentTau
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
 :
    ∃ σ : K ≃ₐ[F] K, (∀ z, σ z = τ z) ∧ (∀ z, σ (σ z) = z) := by
  have hτF : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a := by
    intro a
    have hπa : π (algebraMap F (fepomepA n F S) a) = algebraMap F K a := π.commutes a
    have hadj : fepomep_formAdjAlgEquiv n hn S hSU hS (algebraMap F (fepomepA n F S) a) =
        algebraMap F (fepomepA n F S) a :=
      (fepomep_formAdjAlgEquiv n hn S hSU hS).commutes a
    have h := hτcompat (algebraMap F (fepomepA n F S) a)
    rw [hπa, hadj, hπa] at h
    exact h
  refine ⟨AlgEquiv.ofRingEquiv (f := τ) hτF, ?_, ?_⟩
  · intro z
    rfl
  · intro z
    have h := congrFun (congrArg (fun f : K ≃+* K => (f : K → K)) hτ2) z
    simpa using h

private lemma fepomep_selfDual_blockGroup_descentPolarAdjoint
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (β : W →ₗ[F] W →ₗ[F] F) (hβ : ∀ u w, β u w = QuadraticMap.polar (fepomepQ n F) (u : fepomepι
        n → F) (w : fepomepι n → F))
    (σ : K ≃ₐ[F] K) (hσ : ∀ z, σ z = τ z) :
    ∀ (a : K) (u w : W), β (a • u) w = β u (σ a • w) := by
  intro a u w
  obtain ⟨b, rfl⟩ := hπsurj a
  simp only [hβ]
  rw [hσ (π b), hτcompat b, hK b u, hK (fepomep_formAdjAlgEquiv n hn S hSU hS b) w]
  exact (fepomep_polar_formAdj_apply n (b : Matrix (fepomepι n) (fepomepι n) F)
    (u : fepomepι n → F) (w : fepomepι n → F)).symm

private lemma fepomep_selfDual_blockGroup_descentFormExists
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∃ H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K,
      H.IsSymm ∧ H.SeparatingLeft ∧
      (∀ v w : W, Algebra.trace F K (H v w) = QuadraticMap.polar (fepomepQ n F) (v : fepomepι n
          → F) (w : fepomepι n → F)) := by
  obtain ⟨β, hβ, hβsymm, hβnd⟩ :=
    fepomep_selfDual_blockGroup_descentPolarBilin n hn f hc S hSU hS hodd hε hJε he heε hself
      hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW Φ
  obtain ⟨σ, hσ, hσσ⟩ :=
    fepomep_selfDual_blockGroup_descentTau n hn f hc S hSU hS hodd hε hJε he heε hself hd4 l hl
      hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne
  have hbal :=
    fepomep_selfDual_blockGroup_descentPolarAdjoint n hn f hc S hSU hS hodd hε hJε he heε hself
      hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW hK β hβ σ hσ
  obtain ⟨H, hHsymm, hHsep, hHtr⟩ := fepomep_hermForm_trace β hβsymm hβnd σ hσσ hbal
  have hring : σ.toRingHom = τ.toRingHom := RingHom.ext fun z => hσ z
  let H' : W →ₛₗ[τ.toRingHom] W →ₗ[K] K :=
    { toFun := H
      map_add' := H.map_add'
      map_smul' := fun c x => by
        rw [← hring]
        exact H.map_smul' c x }
  have hH'val : ∀ u w, H' u w = H u w := fun u w => rfl
  refine ⟨H', ?_, ?_, ?_⟩
  · refine ⟨fun x y => ?_⟩
    have h1 : τ.toRingHom (H x y) = H y x := (hσ (H x y)).symm.trans (hHsymm.eq x y)
    simpa only [hH'val] using h1
  · intro x hx
    exact hHsep x fun w => by rw [← hH'val x w]; exact hx w
  · intro u w
    rw [hH'val u w, ← hβ u w]
    exact hHtr u w

private lemma fepomep_selfDual_blockGroup_descentFormInvariant
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) = QuadraticMap.polar (fepomepQ n F) (v :
        fepomepι n → F) (w : fepomepι n → F))
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F)) :
    ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y := by
  intro u x y
  refine sub_eq_zero.mp ((traceForm_nondegenerate F K).1 (H (ρ u x) (ρ u y) - H x y) fun c => ?_)
  rw [Algebra.traceForm_apply, sub_mul, map_sub,
    show H (ρ u x) (ρ u y) * c = H (ρ u x) (c • ρ u y) from by
      rw [map_smul, smul_eq_mul, mul_comm],
    show H x y * c = H x (c • y) from by rw [map_smul, smul_eq_mul, mul_comm],
    hHtr (ρ u x) (c • ρ u y), hHtr x (c • y),
    show c • ρ u y = ρ u (c • y) from (map_smul (ρ u) c y).symm,
    fepomep_selfDual_formInvariant n hn S hSU hS hε he heε hself K π hπsurj hπker
      hπdeg W hW ρ hρ u x (c • y),
    sub_self]

private lemma fepomep_selfDual_blockGroup_descentCoordinateMap
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hinjρ : Function.Injective ρ)
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K)) :
    ∃ ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K,
      Function.Injective ι₀ ∧
      (∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
        Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W))
            (Fin (Module.finrank K W)) K) (Pi.single i 1) =
          Φ (ρ g (Φ.symm (Pi.single i 1)))) := by
  obtain ⟨ψ, hψ⟩ := fepomep_selfDual_blockMatrixIso K W (Module.finrank K W) Φ
  let ι₀ : glBlockCentralizer (fepomepJ n F) S ε →*
      GL (Fin (Module.finrank K W)) K := ψ.toMonoidHom.comp ρ
  refine ⟨ι₀, ?_, ?_⟩
  · intro g h hgh
    apply hinjρ
    apply ψ.injective
    simpa only [ι₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hgh
  · intro g i
    simpa only [ι₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hψ (ρ g) i

private lemma fepomep_selfDual_sesq_isometry_toMatrix {K W : Type} [Field K] [AddCommGroup W]
    [Module K W] {m : ℕ} {τ : K →+* K} (H : W →ₛₗ[τ] W →ₗ[K] K)
    (Φ : W ≃ₗ[K] (Fin m → K)) (f : W ≃ₗ[K] W) (A : Matrix (Fin m) (Fin m) K)
    (hA : ∀ i, A.mulVec (Pi.single i 1) = Φ (f (Φ.symm (Pi.single i 1))))
    (hiso : ∀ x y, H (f x) (f y) = H x y) :
    (A.map τ).transpose * (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1))
      (Φ.symm (Pi.single j 1)))) * A =
      (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) := by
  let b : Fin m → W := fun i => Φ.symm (Pi.single i 1)
  have hcol : ∀ i, (∑ k, A k i • b k) = f (b i) := by
    intro i
    apply Φ.injective
    rw [map_sum]
    have h1 : ∀ k, Φ (A k i • b k) = A k i • Pi.single k 1 := by
      intro k
      rw [map_smul, LinearEquiv.apply_symm_apply]
    rw [Finset.sum_congr rfl fun k _ => h1 k]
    rw [← hA i]
    ext j
    simp [Matrix.mulVec, Pi.single_apply]
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  have h1 : ∀ x, (∑ y, τ (A y i) * H (b y) (b x)) = H (f (b i)) (b x) := by
    intro x
    rw [← hcol i, map_sum]
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun y _ => by rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  have h2 : (∑ x, H (f (b i)) (b x) * A x j) = H (f (b i)) (f (b j)) := by
    rw [← hcol j, map_sum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [LinearMap.map_smul, smul_eq_mul, mul_comm]
  have h3 : (∑ x, (∑ y, τ (A y i) * H (b y) (b x)) * A x j) =
      (∑ x, H (f (b i)) (b x) * A x j) :=
    Finset.sum_congr rfl fun x _ => by rw [h1 x]
  rw [h3, h2, hiso (b i) (b j)]

private lemma fepomep_selfDual_blockGroup_descentJForward
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K) (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε)
      (x y : W), H (ρ u x) (ρ u y) = H x y)
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W))
          (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f))) :
    ∀ g : glBlockCentralizer (fepomepJ n F) S ε,
      ((((ι₀ g : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin
          (Module.finrank K W)) K).map (fun x => x ^ (2 ^ (l * f)))).transpose *
        (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) * ((ι₀ g : GL
            (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K
                W)) K)) = (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j
                    1)))) := by
  intro g
  have h := fepomep_selfDual_sesq_isometry_toMatrix H Φ (ρ g)
    (((ι₀ g : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin
        (Module.finrank K W)) K))
    (fun i => hι₀ g i) (hHinv g)
  have hmap : (((ι₀ g : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin
      (Module.finrank K W)) K)).map
        (fun x => x ^ (2 ^ (l * f))) =
      (((ι₀ g : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin
          (Module.finrank K W)) K)).map τ.toRingHom := by
    ext i j
    simp only [Matrix.map_apply]
    exact (hτeq _).symm
  rw [hmap]
  exact h

private lemma fepomep_selfDual_blockGroup_descentJRangeLe
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K) (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε)
      (x y : W), H (ρ u x) (ρ u y) = H x y)
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W))
          (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f))) :
    ∀ A : GL (Fin (Module.finrank K W)) K, A ∈ ι₀.range →
      (((A : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin
          (Module.finrank K W)) K).map (fun x => x ^ (2 ^ (l * f)))).transpose * (Matrix.of (fun i j
              => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) *
        ((A : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin
            (Module.finrank K W)) K) = (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm
                (Pi.single j 1)))) := by
  intro A hA
  rcases hA with ⟨g, rfl⟩
  exact fepomep_selfDual_blockGroup_descentJForward n hn f hc S hSU hS hodd hε hJε he heε hself
      hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW hK ρ hρ hinjρ H hHinv Φ ι₀ hι₀
          hτeq g

private lemma fepomep_selfDual_gram_conjTr {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
    {m : ℕ} (l f : ℕ) {τ : K ≃+* K} (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K) (hHsymm : H.IsSymm)
    (Φ : W ≃ₗ[K] (Fin m → K)) :
    CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution K 2 (l * f))
      (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) =
      (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) := by
  ext i j
  rw [CFSG.LieType.Universal.Unitary.conjTr, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.of_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [← hτeq (H (Φ.symm (Pi.single j 1)) (Φ.symm (Pi.single i 1)))]
  exact hHsymm.eq (Φ.symm (Pi.single j 1)) (Φ.symm (Pi.single i 1))

private lemma fepomep_selfDual_gram_det_ne_zero {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {m : ℕ} {τ : K →+* K}
    (H : W →ₛₗ[τ] W →ₗ[K] K) (hHsymm : H.IsSymm) (hHnd : H.SeparatingLeft)
    (Φ : W ≃ₗ[K] (Fin m → K)) :
    (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))).det ≠ 0 := by
  let h : (Fin m → K) →ₛₗ[τ] (Fin m → K) →ₗ[K] K :=
    LinearMap.mk₂'ₛₗ τ (RingHom.id K) (fun x y => H (Φ.symm x) (Φ.symm y))
      (fun x y z => by simp only [map_add, LinearMap.add_apply])
      (fun a x y => by
        simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply])
      (fun x y z => by simp only [map_add, LinearMap.add_apply])
      (fun a x y => by
        simp only [map_smul, LinearMap.map_smul, LinearMap.smul_apply, RingHom.id_apply])
  have hnd : h.Nondegenerate := by
    refine ⟨?_, ?_⟩
    · intro x hx
      apply Φ.symm.injective
      rw [map_zero]
      apply hHnd (Φ.symm x)
      intro y
      simpa only [h, LinearMap.mk₂'ₛₗ_apply, LinearEquiv.symm_apply_apply] using hx (Φ y)
    · intro y hy
      apply Φ.symm.injective
      rw [map_zero]
      apply hHnd (Φ.symm y)
      intro x
      have h2 := hHsymm.eq x (Φ.symm y)
      rw [show H x (Φ.symm y) = 0 from by
        simpa only [h, LinearMap.mk₂'ₛₗ_apply, LinearEquiv.symm_apply_apply] using hy (Φ x),
        map_zero] at h2
      exact h2.symm
  have := CFSG.UnitaryInvolutionIndex.det_gram_ne_zero hnd
  have hgram : CFSG.UnitaryInvolutionIndex.gram h =
      Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1))) := rfl
  rw [hgram] at this
  exact this
private lemma fepomep_selfDual_blockGroup_descentNormalization
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K) (hHsymm : H.IsSymm) (hHnd : H.SeparatingLeft)
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K)) :
    ∃ C : GL (Fin (Module.finrank K W)) K,
      (((C : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin
          (Module.finrank K W)) K).map (fun x => x ^ (2 ^ (l * f)))).transpose *
        (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) * ((C : GL (Fin
            (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W))
                K) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  have hKcard : Nat.card K = (2 ^ (l * f)) ^ 2 := by
    rw [fepomep_blockField_card f (2 * l) hc (by rw [hπdeg, hl]), ← pow_mul]
    congr 1
    ring
  obtain ⟨P, hP⟩ := CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one (F := K) (p := 2)
    (f := l * f) hKcard (fepomep_selfDual_gram_conjTr l f hτeq H hHsymm Φ)
    (fepomep_selfDual_gram_det_ne_zero H hHsymm hHnd Φ)
  refine ⟨P, ?_⟩
  have hmap : (P : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
        (fun x => x ^ (2 ^ (l * f))) =
      (P : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 (l * f)) := by
    ext i j
    simp only [Matrix.map_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [hmap]
  exact hP

private lemma fepomep_conj_transpose_expansion {K : Type} [Field K] {m : ℕ} (σ : K →+* K)
    (A X B : Matrix (Fin m) (Fin m) K) :
    ((A * X * B).map σ).transpose =
      (B.map σ).transpose * (X.map σ).transpose * (A.map σ).transpose := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.mul_assoc]

private lemma fepomep_conj_J_relation {K : Type} [Field K] {m : ℕ} (σ : K →+* K)
    (J : Matrix (Fin m) (Fin m) K) (A B : Matrix (Fin m) (Fin m) K)
    (hAB : A * B = 1) (hC : (A.map σ).transpose * J * A = 1) :
    J = (A.map σ).transpose⁻¹ * B ∧
      (B.map σ).transpose = (A.map σ).transpose⁻¹ := by
  have hABσ : (A.map σ) * (B.map σ) = 1 := by
    rw [← Matrix.map_mul, hAB]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hunit : IsUnit ((A.map σ).transpose).det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_det_of_right_inverse hABσ
  have hBinv : (B.map σ).transpose = (A.map σ).transpose⁻¹ := by
    have h1 : (B.map σ).transpose * (A.map σ).transpose = 1 := by
      rw [← Matrix.transpose_mul, hABσ, Matrix.transpose_one]
    have hA'A : (A.map σ).transpose * ((A.map σ).transpose)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hunit
    calc (B.map σ).transpose
        = (B.map σ).transpose * ((A.map σ).transpose * ((A.map σ).transpose)⁻¹) := by
          rw [hA'A, Matrix.mul_one]
      _ = ((B.map σ).transpose * (A.map σ).transpose) * ((A.map σ).transpose)⁻¹ := by
          rw [Matrix.mul_assoc]
      _ = ((A.map σ).transpose)⁻¹ := by rw [h1, Matrix.one_mul]
  refine ⟨?_, hBinv⟩
  have h1 : (A.map σ).transpose * J = B := by
    have h := congrArg (fun x => x * B) hC
    rw [Matrix.mul_assoc, hAB, Matrix.mul_one, Matrix.one_mul] at h
    exact h
  rw [← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]

private lemma fepomep_conj_forward {K : Type} [Field K] {m : ℕ} (σ : K →+* K)
    (J : Matrix (Fin m) (Fin m) K) (A B X : Matrix (Fin m) (Fin m) K)
    (hAB : A * B = 1) (hC : (A.map σ).transpose * J * A = 1)
    (hX : (X.map σ).transpose * X = 1) :
    ((A * X * B).map σ).transpose * J * (A * X * B) = J := by
  obtain ⟨hJ, hB⟩ := fepomep_conj_J_relation σ J A B hAB hC
  have hT := fepomep_conj_transpose_expansion σ A X B
  rw [hT]
  calc (B.map σ).transpose * (X.map σ).transpose * (A.map σ).transpose * J * (A * X * B)
      = (B.map σ).transpose * (X.map σ).transpose * ((A.map σ).transpose * J * A) * X * B := by
        noncomm_ring
    _ = (B.map σ).transpose * (X.map σ).transpose * 1 * X * B := by rw [hC]
    _ = (B.map σ).transpose * (X.map σ).transpose * X * B := by rw [Matrix.mul_one]
    _ = (B.map σ).transpose * ((X.map σ).transpose * X) * B := by noncomm_ring
    _ = (B.map σ).transpose * 1 * B := by rw [hX]
    _ = (B.map σ).transpose * B := by rw [Matrix.mul_one]
    _ = (A.map σ).transpose⁻¹ * B := by rw [hB]
    _ = J := hJ.symm

private lemma fepomep_conj_reverse {K : Type} [Field K] {m : ℕ} (σ : K →+* K)
    (J : Matrix (Fin m) (Fin m) K) (A B X : Matrix (Fin m) (Fin m) K)
    (hAB : A * B = 1) (hC : (A.map σ).transpose * J * A = 1)
    (hY : ((A * X * B).map σ).transpose * J * (A * X * B) = J) :
    (X.map σ).transpose * X = 1 := by
  have hABσ : (A.map σ) * (B.map σ) = 1 := by
    rw [← Matrix.map_mul, hAB]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hunitAT : IsUnit ((A.map σ).transpose).det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_det_of_right_inverse hABσ
  have hunitA : IsUnit A.det := Matrix.isUnit_det_of_right_inverse hAB
  have hBA : B * A = 1 := by
    have h : B = A⁻¹ := (Matrix.inv_eq_right_inv hAB).symm
    rw [h, Matrix.nonsing_inv_mul _ hunitA]
  obtain ⟨hJ, hB⟩ := fepomep_conj_J_relation σ J A B hAB hC
  have hY2 : (B.map σ).transpose * ((X.map σ).transpose * X) * B = J := by
    have h0 := hY
    rw [fepomep_conj_transpose_expansion σ A X B] at h0
    have hr : (B.map σ).transpose * (X.map σ).transpose * (A.map σ).transpose * J *
          (A * X * B)
        = (B.map σ).transpose * ((X.map σ).transpose * X) * B := by
      calc (B.map σ).transpose * (X.map σ).transpose * (A.map σ).transpose * J *
            (A * X * B)
          = (B.map σ).transpose * (X.map σ).transpose *
              ((A.map σ).transpose * J * A) * X * B := by noncomm_ring
        _ = (B.map σ).transpose * (X.map σ).transpose * 1 * X * B := by rw [hC]
        _ = (B.map σ).transpose * (X.map σ).transpose * X * B := by rw [Matrix.mul_one]
        _ = (B.map σ).transpose * ((X.map σ).transpose * X) * B := by noncomm_ring
    rw [hr] at h0
    exact h0
  have hY3 : (A.map σ).transpose⁻¹ * ((X.map σ).transpose * X) * B =
      (A.map σ).transpose⁻¹ * B := by
    rw [hB, hJ] at hY2
    exact hY2
  have h1 : (A.map σ).transpose⁻¹ * ((X.map σ).transpose * X) =
      (A.map σ).transpose⁻¹ := by
    calc (A.map σ).transpose⁻¹ * ((X.map σ).transpose * X)
        = (A.map σ).transpose⁻¹ * ((X.map σ).transpose * X) * (B * A) := by
          rw [hBA, Matrix.mul_one]
      _ = ((A.map σ).transpose⁻¹ * ((X.map σ).transpose * X) * B) * A := by
          noncomm_ring
      _ = ((A.map σ).transpose⁻¹ * B) * A := by rw [hY3]
      _ = (A.map σ).transpose⁻¹ * (B * A) := by noncomm_ring
      _ = (A.map σ).transpose⁻¹ := by rw [hBA, Matrix.mul_one]
  have h2 : (X.map σ).transpose * X = 1 := by
    have h := congrArg (fun M => (A.map σ).transpose * M) h1
    rw [← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv ((A.map σ).transpose) hunitAT] at h
    simpa only [Matrix.one_mul] using h
  exact h2

private lemma fepomep_conj_unitary_iff {K : Type} [Field K] {m : ℕ} (σ : K →+* K)
    (J : Matrix (Fin m) (Fin m) K) (C : GL (Fin m) K)
    (hC : ((C : Matrix (Fin m) (Fin m) K).map σ).transpose * J *
      (C : Matrix (Fin m) (Fin m) K) = 1) :
    ∀ X : GL (Fin m) K,
      ((((X : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map σ).transpose *
        ((X : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 ↔
      (((((C * X * C⁻¹ : GL (Fin m) K)) : Matrix (Fin m) (Fin m) K).map σ).transpose * J *
        (((C * X * C⁻¹ : GL (Fin m) K)) : Matrix (Fin m) (Fin m) K) = J)) := by
  intro X
  have hAB : (C : Matrix (Fin m) (Fin m) K) * ((C⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1
      := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro hX
    exact fepomep_conj_forward σ J (C : Matrix (Fin m) (Fin m) K)
      ((C⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) (X : Matrix (Fin m) (Fin m) K) hAB hC hX
  · intro hY
    exact fepomep_conj_reverse σ J (C : Matrix (Fin m) (Fin m) K)
      ((C⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) (X : Matrix (Fin m) (Fin m) K) hAB hC hY
private lemma fepomep_selfDual_blockGroup_descentTransport
    {G : Type} [Group G] {K : Type} [Field K] {τ : K ≃+* K} (m : ℕ) (σ : K →+* K)
    (J : Matrix (Fin m) (Fin m) K)
    (ι₀ : G →* GL (Fin m) K) (hι₀ : Function.Injective ι₀)
    (hU₀ : ∀ A : GL (Fin m) K, A ∈ ι₀.range ↔
      (((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map σ).transpose * J *
        ((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = J)
    (C : GL (Fin m) K)
    (hC : (((C : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map σ).transpose * J *
        ((C : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1) :
    ∃ ι : G →* GL (Fin m) K, Function.Injective ι ∧
      (∀ A : GL (Fin m) K, A ∈ ι.range ↔
        (((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map σ).transpose *
          ((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1) := by
  let ι : G →* GL (Fin m) K := (MulAut.conj C⁻¹).toMonoidHom.comp ι₀
  refine ⟨ι, ?_, ?_⟩
  · intro a b hab
    have h1 : MulAut.conj C⁻¹ (ι₀ a) = MulAut.conj C⁻¹ (ι₀ b) := by
      simpa only [ι, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] using hab
    exact hι₀ ((MulAut.conj C⁻¹).injective h1)
  · intro A
    have hmem : A ∈ ι.range ↔ MulAut.conj C A ∈ ι₀.range := by
      dsimp only [ι]
      rw [MonoidHom.range_comp, Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom]
        convert hx using 1
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      · intro hA
        refine ⟨MulAut.conj C A, hA, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom]
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
    rw [hmem, hU₀ (MulAut.conj C A)]
    constructor
    · intro hA
      exact (fepomep_conj_unitary_iff σ J C hC A).mpr hA
    · intro hA
      exact (fepomep_conj_unitary_iff σ J C hC A).mp hA

private lemma fepomep_dvd_of_pow_sub_one_dvd {a m n : ℕ} (hm : 0 < m) (ha : 1 < a) (h : a ^ m - 1 ∣
    a
    ^ n - 1) : m ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hmod1 : a ^ m ≡ 1 [MOD a ^ m - 1] := by
    rw [Nat.modEq_iff_dvd]
    refine ⟨-1, ?_⟩
    rw [Nat.cast_sub (Nat.one_le_pow m a (by omega)), Nat.cast_one]
    ring
  have hmodq : (a ^ m) ^ (n / m) ≡ 1 [MOD a ^ m - 1] := by
    simpa using hmod1.pow (n / m)
  have hmodmul : (a ^ m) ^ (n / m) * a ^ (n % m) ≡ a ^ (n % m) [MOD a ^ m - 1] := by
    simpa using hmodq.mul (Nat.ModEq.refl (a ^ (n % m)))
  have hn_eq : (a ^ m) ^ (n / m) * a ^ (n % m) = a ^ n := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hmodn : a ^ n ≡ 1 [MOD a ^ m - 1] := by
    have h' : (↑(a ^ m - 1) : ℤ) ∣ ↑(a ^ n - 1) := by exact_mod_cast h
    rw [Nat.cast_sub (Nat.one_le_pow n a (by omega)), Nat.cast_one] at h'
    rw [Nat.modEq_iff_dvd]
    have hneg : (↑(a ^ m - 1) : ℤ) ∣ -((↑(a ^ n) : ℤ) - 1) := dvd_neg.mpr h'
    simpa only [neg_sub, Int.natCast_one] using hneg
  have hmodr : a ^ (n % m) ≡ 1 [MOD a ^ m - 1] := by
    have h2 : (a ^ m) ^ (n / m) * a ^ (n % m) ≡ 1 [MOD a ^ m - 1] := by
      rw [hn_eq]; exact hmodn
    exact hmodmul.symm.trans h2
  have hApos : 0 < a ^ m - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hm) ha)
  have hdvd : a ^ m - 1 ∣ a ^ (n % m) - 1 := by
    by_cases hA1 : a ^ m - 1 = 1
    · rw [hA1]; exact one_dvd _
    · have hle : 1 ≤ a ^ m - 1 := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hApos)
      have hAgt : 1 < a ^ m - 1 := Nat.lt_of_le_of_ne hle (Ne.symm hA1)
      have hmod : a ^ (n % m) % (a ^ m - 1) = 1 := by
        have hh := hmodr
        change a ^ (n % m) % (a ^ m - 1) = 1 % (a ^ m - 1) at hh
        rwa [Nat.mod_eq_of_lt hAgt] at hh
      rw [Nat.dvd_iff_mod_eq_zero]
      have hdec := Nat.div_add_mod (a ^ (n % m)) (a ^ m - 1)
      rw [hmod] at hdec
      have hsub : a ^ (n % m) - 1 = (a ^ m - 1) * (a ^ (n % m) / (a ^ m - 1)) := by omega
      rw [hsub, Nat.mul_mod_right]
  have hlt : a ^ (n % m) < a ^ m := Nat.pow_lt_pow_right ha (Nat.mod_lt _ hm)
  have hltA : a ^ (n % m) - 1 < a ^ m - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_pow (n % m) a (by omega)) hlt
  have hzero : a ^ (n % m) - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hltA
  have hle2 : a ^ (n % m) ≤ 1 := Nat.sub_eq_zero_iff_le.mp hzero
  have hge : 1 ≤ a ^ (n % m) := Nat.one_le_pow (n % m) a (by omega)
  have h1 : a ^ (n % m) = 1 := le_antisymm hle2 hge
  by_contra hr
  have h2 : 1 < a ^ (n % m) := Nat.one_lt_pow hr ha
  omega

private lemma fepomep_selfDual_tau_eq_frobenius {F K : Type} [Field F] [Finite F] [CharP F 2] [Field
    K] [Finite K]
    [Algebra F K]
    (f : ℕ) (hc : Nat.card F = 2 ^ f) (l : ℕ) (hl2 : 2 ≤ l)
    (hdeg : Module.finrank F K = 2 * l)
    (τ : K ≃+* K) (hτF : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a)
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1) :
    ∀ x : K, τ x = x ^ (2 ^ (l * f)) := by
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype K := Fintype.ofFinite K
  have hfpos : 0 < f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    have h2 : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
    rw [hc, hf0, pow_zero] at h2
    omega
  have hcardF : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hc]
  have hcardK : Fintype.card K = (2 ^ f) ^ (2 * l) := by
    rw [Module.card_eq_pow_finrank (K := F) (V := K), hcardF, hdeg]
  let σ : K ≃ₐ[F] K := AlgEquiv.ofRingEquiv hτF
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (k := F) (p := 2) (l := K) σ
  let e : ℕ := (2 ^ f) ^ i
  have hi' : ∀ x : K, σ x = x ^ e := by
    intro x
    rw [hi x, hc]
  have hσ2 : ∀ x : K, σ (σ x) = x := by
    intro x
    have h := congrFun (congrArg (fun g : K ≃+* K => (g : K → K)) hτ2) x
    simpa [σ, pow_two] using h
  have hsq : ∀ x : K, x ^ (e * e) = x := by
    intro x
    rw [pow_mul, ← hi' x, ← hi' (σ x), hσ2 x]
  have h2lt : 1 < (2 : ℕ) ^ f := Nat.one_lt_pow (by omega) (by norm_num)
  have hunit : ∀ u : Kˣ, u ^ (e * e - 1) = 1 := by
    intro u
    have h := hsq (u : K)
    have hne : e * e ≠ 0 := by
      have h2 : 0 < e := by dsimp [e]; positivity
      positivity
    have h' : (u : K) ^ (e * e - 1) * (u : K) = (u : K) := by
      rw [pow_sub_one_mul hne]
      exact h
    have h1 : (u : K) ^ (e * e - 1) * (u : K) = 1 * (u : K) := by
      rw [one_mul]; exact h'
    exact Units.ext (mul_right_cancel₀ (show (u : K) ≠ 0 from u.ne_zero) h1)
  have hdiv : Fintype.card K - 1 ∣ e * e - 1 :=
    (FiniteField.forall_pow_eq_one_iff K (e * e - 1)).mp hunit
  have hee : e * e = (2 ^ f) ^ (2 * i) := by
    dsimp [e]
    rw [show (2 ^ f) ^ i * (2 ^ f) ^ i = ((2 ^ f) ^ i) ^ 2 from by rw [pow_two], ← pow_mul]
    congr 1
    ring
  have hdiv2 : (2 ^ f) ^ (2 * l) - 1 ∣ (2 ^ f) ^ (2 * i) - 1 := by
    rw [hcardK, hee] at hdiv
    exact hdiv
  have hkey := fepomep_dvd_of_pow_sub_one_dvd (a := 2 ^ f) (m := 2 * l) (n := 2 * i) (by omega) h2lt
      hdiv2
  have hli : l ∣ i := (Nat.mul_dvd_mul_iff_left (show 0 < 2 by norm_num)).mp hkey
  let Q : ℕ := (2 ^ f) ^ l
  have hQeq : Q = 2 ^ (l * f) := by
    dsimp [Q]
    rw [← pow_mul, Nat.mul_comm]
  have hQ2 : Q * Q = Fintype.card K := by
    dsimp [Q]
    rw [show (2 ^ f) ^ l * (2 ^ f) ^ l = ((2 ^ f) ^ l) ^ 2 from by rw [pow_two], ← pow_mul,
      hcardK]
    congr 1
    ring
  have hCiter : ∀ (m : ℕ) (y : K), y ^ (Fintype.card K ^ m) = y := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
        intro y
        rw [pow_succ, pow_mul, ih, FiniteField.pow_card]
  have hQ2m : ∀ (m : ℕ) (x : K), x ^ (Q ^ (2 * m)) = x := by
    intro m x
    rw [show Q ^ (2 * m) = (Q * Q) ^ m from by rw [pow_mul, pow_two], hQ2]
    exact hCiter m x
  have hQodd : ∀ (m : ℕ) (x : K), x ^ (Q ^ (2 * m + 1)) = x ^ Q := by
    intro m x
    rw [pow_succ, pow_mul, hQ2m m x]
  obtain ⟨k, rfl⟩ := hli
  have hek : e = Q ^ k := by
    dsimp [e, Q]
    rw [pow_mul]
  have hkodd : k % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
    · exfalso
      have hk : k = 2 * (k / 2) := by
        have := Nat.div_add_mod k 2
        omega
      have hx1 : ∀ x : K, τ x = x := by
        intro x
        rw [show τ x = σ x from rfl, hi' x, hek, hk, hQ2m (k / 2) x]
      exact hτne (RingEquiv.ext (fun x => by simpa using hx1 x))
    · exact h1
  intro x
  have hk : k = 2 * (k / 2) + 1 := by
    have := Nat.div_add_mod k 2
    omega
  rw [show τ x = σ x from rfl, hi' x, hek, hk, hQodd (k / 2) x, ← hQeq]

private lemma fepomep_selfDual_blockGroup_descentHermitianForm
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    :
    ∃ H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K,
      H.IsSymm ∧ H.SeparatingLeft ∧
      (∀ v w : W, Algebra.trace F K (H v w) =
        QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F)) ∧
      (∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
        H (ρ u x) (ρ u y) = H x y) := by
  obtain ⟨H, hsymm, hsep, htr⟩ :=
    fepomep_selfDual_blockGroup_descentFormExists n hn f hc S hSU hS hodd hε hJε he
      heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW Φ hK
  exact ⟨H, hsymm, hsep, htr,
    fepomep_selfDual_blockGroup_descentFormInvariant n hn f hc S hSU hS hodd hε hJε he
      heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW hK H htr ρ hρ⟩

private lemma fepomep_sesq_expansion {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {τ : K →+* K} (H : W →ₛₗ[τ] W →ₗ[K] K)
    (m : ℕ) (Φ : W ≃ₗ[K] (Fin m → K)) (x y : W) :
    H x y = ∑ c, ∑ d, τ ((Φ x) c) * H (Φ.symm (Pi.single c 1)) (Φ.symm (Pi.single d 1)) * (Φ y) d :=
        by
  let b : Fin m → W := fun i => ((Pi.basisFun K (Fin m)).map Φ.symm) i
  have hb : ∀ i, b i = Φ.symm (Pi.single i 1) := by
    intro i
    change ((Pi.basisFun K (Fin m)).map Φ.symm) i = Φ.symm (Pi.single i 1)
    rw [Module.Basis.map_apply, Pi.basisFun_apply]
  have hx : x = ∑ c, (Φ x) c • b c := by
    conv_lhs => rw [← fepomep_selfDual_coord_expansion K W m Φ x]
    rw [Fintype.linearCombination_apply]
  have hy : y = ∑ d, (Φ y) d • b d := by
    conv_lhs => rw [← fepomep_selfDual_coord_expansion K W m Φ y]
    rw [Fintype.linearCombination_apply]
  conv_lhs => rw [hx, hy]
  have hH : H (∑ c, (Φ x) c • b c) = ∑ c, H ((Φ x) c • b c) := by rw [map_sum]
  rw [hH, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  have hHc : H (b c) (∑ d, (Φ y) d • b d) = ∑ d, H (b c) ((Φ y) d • b d) := by rw [map_sum]
  rw [hHc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [LinearMap.map_smul, smul_eq_mul]
  rw [hb c, hb d]
  ring

private lemma fepomep_selfDual_blockGroup_descentJIsometry
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ x y : W, Algebra.trace F K (H x y) =
      QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (A : GL (Fin (Module.finrank K W)) K)
    (hA : (((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
        (fun x => x ^ (2 ^ (l * f)))).transpose *
      (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) *
      ((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) =
    (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1))))) :
    ∀ x y : W, H (Φ.symm (Matrix.mulVec ((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Φ x)))
      (Φ.symm (Matrix.mulVec ((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Φ y))) = H x y := by
  let M : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K :=
    (A : GL (Fin (Module.finrank K W)) K)
  let J : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K :=
    Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))
  let a : W →ₗ[K] W := (Φ.symm.toLinearMap).comp ((Matrix.mulVecLin M).comp Φ.toLinearMap)
  have ha : ∀ x : W, a x = Φ.symm (Matrix.mulVec M (Φ x)) := fun x => rfl
  have hτmap : M.map (fun x => x ^ (2 ^ (l * f))) = M.map τ.toRingHom := by
    ext i j
    simp only [Matrix.map_apply]
    exact (hτeq _).symm
  have hAτ : (M.map τ.toRingHom).transpose * (J * M) = J := by
    have h := hA
    rw [hτmap] at h
    rw [← Matrix.mul_assoc]
    simpa only [J] using h
  let H' : W →ₛₗ[τ.toRingHom] W →ₗ[K] K :=
    LinearMap.mk₂'ₛₗ τ.toRingHom (RingHom.id K) (fun x y => H (a x) (a y))
      (fun x y z => by simp only [map_add, LinearMap.add_apply])
      (fun c x y => by
        simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply])
      (fun x y z => by simp only [map_add, LinearMap.add_apply])
      (fun c x y => by
        simp only [map_smul, LinearMap.map_smul, LinearMap.smul_apply, RingHom.id_apply])
  have hH' : ∀ x y : W, H' x y = H (a x) (a y) := fun x y => rfl
  have hpair : ∀ c d : Fin (Module.finrank K W),
      H' (Φ.symm (Pi.single c 1)) (Φ.symm (Pi.single d 1))
        = H (Φ.symm (Pi.single c 1)) (Φ.symm (Pi.single d 1)) := by
    intro c d
    rw [hH' (Φ.symm (Pi.single c 1)) (Φ.symm (Pi.single d 1))]
    rw [fepomep_sesq_expansion H (Module.finrank K W) Φ
          (a (Φ.symm (Pi.single c 1))) (a (Φ.symm (Pi.single d 1)))]
    have hc : ∀ k, (Φ (a (Φ.symm (Pi.single c 1)))) k = M k c := by
      intro k
      have h1 : Φ (a (Φ.symm (Pi.single c 1))) = Matrix.mulVec M (Pi.single c 1) := by
        rw [ha (Φ.symm (Pi.single c 1)), LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
      rw [h1, Matrix.mulVec_single]
      simp [Matrix.col_apply]
    have hd : ∀ l, (Φ (a (Φ.symm (Pi.single d 1)))) l = M l d := by
      intro l
      have h1 : Φ (a (Φ.symm (Pi.single d 1))) = Matrix.mulVec M (Pi.single d 1) := by
        rw [ha (Φ.symm (Pi.single d 1)), LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
      rw [h1, Matrix.mulVec_single]
      simp [Matrix.col_apply]
    simp only [hc, hd]
    have hentry : (∑ k, ∑ l, τ.toRingHom (M k c) * J k l * M l d) = J c d := by
      have h := congrFun (congrFun hAτ c) d
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    simp only [J, Matrix.of_apply] at hentry
    rw [hentry]
  have hHeq : H' = H := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [fepomep_sesq_expansion H' (Module.finrank K W) Φ x y,
        fepomep_sesq_expansion H (Module.finrank K W) Φ x y]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [hpair c d]
  intro x y
  change H (a x) (a y) = H x y
  rw [← hH' x y, hHeq]

private def fepomep_selfDual_blockGroup_sUnitSet (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (S : Set (GL (fepomepι n) F)) (K : Type) [Field K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) : Set Kˣ :=
  {u | ∃ (s : GL (fepomepι n) F) (hs : s ∈ S),
    (u : K) = π ⟨(s : Matrix (fepomepι n) (fepomepι n) F),
      Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩}

private lemma fepomep_selfDual_blockGroup_descentPolarPreserved
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (g : W ≃ₗ[K] W)
    (hg : ∀ x y : W, H (g x) (g y) = H x y)
    :
    ∀ x y : W, QuadraticMap.polar (fepomepQ n F) (g x : fepomepι n → F) (g y : fepomepι n → F) =
      QuadraticMap.polar (fepomepQ n F) (x : fepomepι n → F) (y : fepomepι n → F) := by
  intro x y
  rw [← hHtr (g x) (g y), ← hHtr x y, hg x y]

private lemma fepomep_selfDual_blockGroup_descentQClosureInvariant
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (g : W ≃ₗ[K] W)
    (hg : ∀ x y : W, H (g x) (g y) = H x y)
    :
    ∀ (κ : Kˣ), κ ∈ Subgroup.closure (fepomep_selfDual_blockGroup_sUnitSet n S K π) → ∀ x : W,
      fepomepQ n F (g (((κ : K) • x : W)) : fepomepι n → F) -
          fepomepQ n F ((((κ : K) • x : W)) : fepomepι n → F) =
        fepomepQ n F (g x : fepomepι n → F) - fepomepQ n F (x : fepomepι n → F) := by
  intro κ hκ
  have hQgen : ∀ (κ : Kˣ), κ ∈ fepomep_selfDual_blockGroup_sUnitSet n S K π → ∀ x : W,
      fepomepQ n F (((κ : K) • x : W) : fepomepι n → F) =
        fepomepQ n F (x : fepomepι n → F) := by
    intro κ hκ x
    rcases hκ with ⟨s, hs, hκs⟩
    obtain ⟨u, hu⟩ := hSU s hs
    have h1 : (((κ : K) • x : W) : fepomepι n → F) =
        Matrix.mulVec s (x : fepomepι n → F) := by
      rw [hκs]
      exact hK ⟨(s : Matrix (fepomepι n) (fepomepι n) F),
        Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ x
    rw [h1, ← hu,
      show fepomepJ n F u = Spin.spinMatrix (fepomepQ n F) u from rfl,
      Spin.spinMatrix_mulVec, Spin.map_spinAction]
  have hPgen : ∀ (κ : Kˣ), κ ∈ fepomep_selfDual_blockGroup_sUnitSet n S K π → ∀ x : W,
      fepomepQ n F (g (((κ : K) • x : W)) : fepomepι n → F) -
          fepomepQ n F ((((κ : K) • x : W)) : fepomepι n → F) =
        fepomepQ n F (g x : fepomepι n → F) - fepomepQ n F (x : fepomepι n → F) := by
    intro κ hκ x
    have hQ1 := hQgen κ hκ x
    have hQ2 := hQgen κ hκ (g x)
    have hgκ : g (((κ : K) • x : W)) = (κ : K) • g x := map_smul g (κ : K) x
    rw [hgκ, hQ2, hQ1]
  induction hκ using Subgroup.closure_induction with
  | mem y hy => exact hPgen y hy
  | one =>
      intro x
      simp
  | mul a b _ _ ha hb =>
      intro x
      have h1 := ha (((b : K) • x : W))
      have h2 := hb x
      rw [Units.val_mul, ← smul_smul]
      exact h1.trans h2
  | inv a _ ha =>
      intro x
      have h := ha (((a⁻¹ : K) • x : W))
      have hsmul : (a : K) • ((a⁻¹ : K) • x) = x := by
        rw [smul_smul]
        have h1 : (↑a : K) * (↑a)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero a)
        rw [h1, one_smul]
      rw [hsmul] at h
      simpa using h.symm

private lemma fepomep_selfDual_blockGroup_descentQZero
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (g : W ≃ₗ[K] W)
    (hg : ∀ x y : W, H (g x) (g y) = H x y)
    (hκ : ∀ (κ : Kˣ), κ ∈ Subgroup.closure (fepomep_selfDual_blockGroup_sUnitSet n S K π) → ∀ x : W,
      fepomepQ n F (g (((κ : K) • x : W)) : fepomepι n → F) -
          fepomepQ n F ((((κ : K) • x : W)) : fepomepι n → F) =
        fepomepQ n F (g x : fepomepι n → F) - fepomepQ n F (x : fepomepι n → F)) :
    ∀ x : W, fepomepQ n F (g x : fepomepι n → F) =
      fepomepQ n F (x : fepomepι n → F) := by
  classical
  intro x
  let sA : (s : GL (fepomepι n) F) → s ∈ S → fepomepA n F S :=
    fun s hs => ⟨(s : Matrix (fepomepι n) (fepomepι n) F),
      Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
  have hge2 : 2 ≤ Module.finrank F K := by
    rw [hπdeg, hl]
    omega
  have hexlam : ∃ (s : GL (fepomepι n) F) (hs : s ∈ S), π (sA s hs) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hP : ∀ a : fepomepA n F S, ∃ f : F, π a = algebraMap F K f := by
      intro a
      refine Algebra.adjoin_induction
        (p := fun x hx => ∃ f : F, π ⟨x, hx⟩ = algebraMap F K f) ?_ ?_ ?_ ?_
        (show (a : Matrix (fepomepι n) (fepomepι n) F) ∈
          Algebra.adjoin F (Units.val '' S) from a.2)
      · rintro x ⟨s, hs, rfl⟩
        exact ⟨1, by change π (sA s hs) = algebraMap F K 1; rw [hcon s hs, map_one]⟩
      · intro r
        exact ⟨r, π.commutes r⟩
      · rintro x y hx hy ⟨f, hf⟩ ⟨g, hg⟩
        refine ⟨f + g, ?_⟩
        change π (⟨x, hx⟩ + ⟨y, hy⟩) = algebraMap F K (f + g)
        rw [map_add, hf, hg, map_add]
      · rintro x y hx hy ⟨f, hf⟩ ⟨g, hg⟩
        refine ⟨f * g, ?_⟩
        change π (⟨x, hx⟩ * ⟨y, hy⟩) = algebraMap F K (f * g)
        rw [map_mul, hf, hg, map_mul]
    have hrange : LinearMap.range (Algebra.linearMap F K) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro k
      obtain ⟨a, rfl⟩ := hπsurj k
      obtain ⟨f, hf⟩ := hP a
      exact ⟨f, hf.symm⟩
    have hle : Module.finrank F K ≤ 1 := by
      have h1 : Module.finrank F (LinearMap.range (Algebra.linearMap F K)) ≤
          Module.finrank F F := LinearMap.finrank_range_le (Algebra.linearMap F K)
      rw [hrange, Module.finrank_self] at h1
      simpa using h1
    omega
  have hpi_ne_zero : ∀ (s : GL (fepomepι n) F) (hs : s ∈ S), π (sA s hs) ≠ 0 := by
    intro s hs hzero
    have hse : (s : Matrix (fepomepι n) (fepomepι n) F) * e = 0 :=
      (hπker (sA s hs)).mp hzero
    have he0 : e = 0 := by
      calc e = 1 * e := (one_mul e).symm
        _ = ((↑(s⁻¹) : Matrix (fepomepι n) (fepomepι n) F) *
              (s : Matrix (fepomepι n) (fepomepι n) F)) * e := by rw [Units.inv_mul]
        _ = (↑(s⁻¹) : Matrix (fepomepι n) (fepomepι n) F) *
              ((s : Matrix (fepomepι n) (fepomepι n) F) * e) := by rw [mul_assoc]
        _ = 0 := by rw [hse, mul_zero]
    exact he.2.2.1 he0
  let G : Subgroup Kˣ :=
    Subgroup.closure (fepomep_selfDual_blockGroup_sUnitSet n S K π)
  haveI : Fintype G := Fintype.ofFinite G
  have hGne : G ≠ ⊥ := by
    intro hbot
    obtain ⟨s, hs, hpi1⟩ := hexlam
    have hne : π (sA s hs) ≠ 0 := hpi_ne_zero s hs
    let u : Kˣ := Units.mk0 (π (sA s hs)) hne
    have hu : u ∈ fepomep_selfDual_blockGroup_sUnitSet n S K π :=
      ⟨s, hs, by rw [Units.val_mk0]⟩
    have humem : u ∈ G := Subgroup.subset_closure hu
    have humem' : u ∈ (⊥ : Subgroup Kˣ) := by rwa [hbot] at humem
    have hu1 : u = 1 := Subgroup.mem_bot.mp humem'
    have hpi : π (sA s hs) = 1 := by
      have h1 := congrArg (fun v : Kˣ => (v : K)) hu1
      simpa [u, Units.val_mk0] using h1
    exact hpi1 hpi
  have hgen_odd : ∀ u ∈ fepomep_selfDual_blockGroup_sUnitSet n S K π,
      Odd (orderOf u) := by
    intro u hu
    rcases hu with ⟨s, hs, hus⟩
    have hpowA : (sA s hs) ^ orderOf s = 1 := by
      apply Subtype.ext
      show ((sA s hs : fepomepA n F S) :
        Matrix (fepomepι n) (fepomepι n) F) ^ orderOf s = 1
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    have hpow : (π (sA s hs)) ^ orderOf s = 1 := by
      rw [← map_pow, hpowA, map_one]
    have hdvd : orderOf (π (sA s hs)) ∣ orderOf s :=
      orderOf_dvd_iff_pow_eq_one.mpr hpow
    have hoddpi : Odd (orderOf (π (sA s hs))) := Odd.of_dvd_nat (hodd s hs) hdvd
    rw [← orderOf_units (y := u), hus]
    exact hoddpi
  have hoddG : ∀ κ ∈ G, Odd (orderOf κ) := by
    intro κ hκ
    change κ ∈ Subgroup.closure (fepomep_selfDual_blockGroup_sUnitSet n S K π) at hκ
    induction hκ using Subgroup.closure_induction with
    | mem y hy => exact hgen_odd y hy
    | one => simpa [orderOf_one] using (odd_one : Odd (1 : ℕ))
    | mul a b _ _ ha hb =>
        have hlcm : Odd (Nat.lcm (orderOf a) (orderOf b)) :=
          Odd.of_dvd_nat (ha.mul hb) (Nat.lcm_dvd_mul _ _)
        exact Odd.of_dvd_nat hlcm (Commute.orderOf_mul_dvd_lcm (mul_comm a b))
    | inv a _ ha => simpa [orderOf_inv] using ha
  have hOddCard : Odd (Nat.card G) := by
    by_contra h
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
    obtain ⟨κ, hκord⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 h
    have hoddκ : Odd (orderOf κ) :=
      Subgroup.orderOf_coe κ ▸ hoddG (κ : Kˣ) κ.property
    rw [hκord] at hoddκ
    exact absurd hoddκ (by decide)
  have hpol : ∀ u v : W,
      QuadraticMap.polar (fepomepQ n F) (g u : fepomepι n → F)
        (g v : fepomepι n → F) =
      QuadraticMap.polar (fepomepQ n F) (u : fepomepι n → F) (v : fepomepι n → F) :=
    fepomep_selfDual_blockGroup_descentPolarPreserved n hn f hc S hSU hS hodd hε hJε
      he heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ
      hinjρ H hHinv hHtr ι₀ hι₀ hτeq g hg
  let ν : W → F := fun y => fepomepQ n F (g y : fepomepι n → F) -
      fepomepQ n F (y : fepomepι n → F)
  have hνadd : ∀ u v : W, ν (u + v) = ν u + ν v := by
    intro u v
    dsimp [ν]
    rw [map_add g u v, Submodule.coe_add]
    rw [QuadraticMap.map_add (fepomepQ n F),
      QuadraticMap.map_add (fepomepQ n F), hpol u v]
    abel
  have hνzero : ν 0 = 0 := by
    simp [ν]
  let νH : W →+ F :=
    { toFun := ν, map_zero' := hνzero, map_add' := hνadd }
  have hT : (∑ κ : G, ((κ : Kˣ) : K)) = (0 : K) :=
    FiniteField.sum_subgroup_units_eq_zero (G := G) hGne
  have hmap : νH (∑ κ : G, ((κ : Kˣ) : K) • x) =
      ∑ κ : G, νH (((κ : Kˣ) : K) • x) := by
    simpa using map_sum νH (fun κ : G => ((κ : Kˣ) : K) • x) Finset.univ
  have hsum_smul : (∑ κ : G, ((κ : Kˣ) : K) • x) =
      (∑ κ : G, ((κ : Kˣ) : K)) • x := by
    rw [Finset.sum_smul]
  have hL : νH (∑ κ : G, ((κ : Kˣ) : K) • x) = 0 := by
    rw [hsum_smul, hT, zero_smul]
    exact map_zero νH
  have hR : (∑ κ : G, νH (((κ : Kˣ) : K) • x)) = (Nat.card G : F) • ν x := by
    have hstep : (∑ κ : G, νH (((κ : Kˣ) : K) • x)) = ∑ _κ : G, ν x := by
      refine Finset.sum_congr rfl ?_
      intro κ _
      dsimp [νH, ν]
      exact hκ (κ : Kˣ) κ.property x
    calc (∑ κ : G, νH (((κ : Kˣ) : K) • x))
        = ∑ _κ : G, ν x := hstep
      _ = Fintype.card G • ν x := by
          rw [Finset.sum_const, Finset.card_univ]
      _ = (Nat.card G : F) • ν x := by
          rw [nsmul_eq_mul, Nat.card_eq_fintype_card, smul_eq_mul]
  have hstar : (Nat.card G : F) • ν x = 0 := by
    rw [← hR, ← hmap, hL]
  have hcG : (Nat.card G : F) ≠ 0 := by
    intro hzero
    have h2 : 2 ∣ Nat.card G := (CharP.cast_eq_zero_iff F 2 (Nat.card G)).mp hzero
    exact (Nat.not_even_iff_odd.mpr hOddCard) (even_iff_two_dvd.mpr h2)
  have hνx : ν x = 0 := by
    have hmul : (Nat.card G : F) * ν x = 0 := by
      simpa [nsmul_eq_mul] using hstar
    exact (mul_eq_zero.mp hmul).resolve_left hcG
  rw [← sub_eq_zero]
  change ν x = 0
  exact hνx

private lemma fepomep_selfDual_blockGroup_descentQuadPreserved
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (g : W ≃ₗ[K] W)
    (hg : ∀ x y : W, H (g x) (g y) = H x y)
    :
    ∀ x : W, fepomepQ n F (g x : fepomepι n → F) =
      fepomepQ n F (x : fepomepι n → F) := by
  intro x
  have hκ := fepomep_selfDual_blockGroup_descentQClosureInvariant n hn f hc S hSU hS hodd hε hJε
      he heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ hinjρ H
          hHinv hHtr ι₀ hι₀ hτeq g hg
  exact fepomep_selfDual_blockGroup_descentQZero n hn f hc S hSU hS hodd hε hJε he heε hself hd4
      l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ hinjρ H hHinv hHtr ι₀ hι₀
          hτeq g hg hκ x

private lemma fepomep_selfDual_blockGroup_descentBlockExtension
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (g : W ≃ₗ[K] W)
    (hg : ∀ x y : W, H (g x) (g y) = H x y)
    (hgQ : ∀ x : W, fepomepQ n F (g x : fepomepι n → F) =
      fepomepQ n F (x : fepomepι n → F)) :
    ∃ E : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F),
      (∀ w : W, E (w : fepomepι n → F) = (g w : fepomepι n → F)) ∧
      (∀ v : fepomepι n → F, E ((1 - ε).mulVec v) = (1 - ε).mulVec v) := by
  classical
  let p : (fepomepι n → F) →ₗ[F] (fepomepι n → F) := Matrix.mulVecLin e
  have heps : e * (1 - ε) = 0 := by
    rw [← hself, Matrix.mul_sub, Matrix.mul_one, he.2.1.eq, sub_self]
  have hidem : IsIdempotentElem p := by
    change IsIdempotentElem (Matrix.mulVecLin e)
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, he.2.1.eq]
  have hproj : LinearMap.IsProj (LinearMap.range p) p :=
    (LinearMap.isProj_range_iff_isIdempotentElem p).mpr hidem
  have hcompl : IsCompl W (LinearMap.ker p) := by
    have h2 := hproj.isCompl
    have hr : LinearMap.range p = W := by
      rw [show p = Matrix.mulVecLin e from rfl]
      exact hW.symm
    rwa [hr] at h2
  let gF : W ≃ₗ[F] W := g.restrictScalars F
  let e0 : (W × (LinearMap.ker p)) ≃ₗ[F] (fepomepι n → F) :=
    Submodule.prodEquivOfIsCompl W (LinearMap.ker p) hcompl
  let g' : (W × (LinearMap.ker p)) ≃ₗ[F] (W × (LinearMap.ker p)) :=
    LinearEquiv.prodCongr gF (LinearEquiv.refl F (LinearMap.ker p))
  let E : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F) := e0.symm.trans (g'.trans e0)
  refine ⟨E, ?_, ?_⟩
  · intro w
    change E (w : fepomepι n → F) = (g w : fepomepι n → F)
    change e0 (g' (e0.symm (w : fepomepι n → F))) = (g w : fepomepι n → F)
    dsimp only [e0]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left W (LinearMap.ker p) hcompl w]
    dsimp only [g']
    rw [LinearEquiv.prodCongr_apply]
    simp [gF]
  · intro v
    have hx : p ((1 - ε).mulVec v) = 0 := by
      dsimp only [p]
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, heps]
      simp
    have hxmem : (1 - ε).mulVec v ∈ LinearMap.ker p := LinearMap.mem_ker.mpr hx
    change E ((1 - ε).mulVec v) = (1 - ε).mulVec v
    change e0 (g' (e0.symm ((1 - ε).mulVec v))) = (1 - ε).mulVec v
    dsimp only [e0]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right W (LinearMap.ker p) hcompl
      ⟨(1 - ε).mulVec v, hxmem⟩]
    dsimp only [g']
    rw [LinearEquiv.prodCongr_apply]
    simp [gF]

private lemma fepomep_selfDual_blockGroup_descentExtensionOmega
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (g : W ≃ₗ[K] W)
    (hg : ∀ x y : W, H (g x) (g y) = H x y)
    (hgQ : ∀ x : W, fepomepQ n F (g x : fepomepι n → F) =
      fepomepQ n F (x : fepomepι n → F))
    (E : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (hEw : ∀ w : W, E (w : fepomepι n → F) = (g w : fepomepι n → F))
    (hEfix : ∀ v : fepomepι n → F, E ((1 - ε).mulVec v) = (1 - ε).mulVec v) :
    E ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (fepomepQ n F)
      (Spin.nondegenerate_polarBilin_quadPlus n F) := by
  classical
  have hEfix' : ∀ x : fepomepι n → F, E ((1 - e).mulVec x) = (1 - e).mulVec x := by
    intro x
    rw [hself]
    exact hEfix x
  have hpol0 : ∀ x y : fepomepι n → F,
      QuadraticMap.polar (fepomepQ n F) (e.mulVec x) ((1 - e).mulVec y) = 0 := by
    intro x y
    rw [hself]
    exact fepomep_polar_eps_compl n hε.2.1 hε.2.2.2.1 x y
  have hEapply : ∀ x : fepomepι n → F,
      E x = (g ⟨e.mulVec x, by rw [hW]; exact ⟨x, rfl⟩⟩ : fepomepι n → F) +
        (1 - e).mulVec x := by
    intro x
    have hxdec : e.mulVec x + (1 - e).mulVec x = x := by
      rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    calc E x = E (e.mulVec x + (1 - e).mulVec x) := by
          conv_lhs => rw [← hxdec]
      _ = E (e.mulVec x) + E ((1 - e).mulVec x) := by rw [map_add E]
      _ = E ((⟨e.mulVec x, by rw [hW]; exact ⟨x, rfl⟩⟩ : W) : fepomepι n → F) +
            E ((1 - e).mulVec x) := rfl
      _ = (g ⟨e.mulVec x, by rw [hW]; exact ⟨x, rfl⟩⟩ : fepomepι n → F) +
            (1 - e).mulVec x := by rw [hEw, hEfix']
  have hcommE : CFSG.RankThree.OrthogonalInvolutions.commSpace E =
      (CFSG.RankThree.OrthogonalInvolutions.commSpace (g.restrictScalars F)).map
        W.subtype := by
    ext x
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_commSpace, Submodule.mem_map]
    constructor
    · rintro ⟨v, hv⟩
      let w : W := ⟨e.mulVec v, by rw [hW]; exact ⟨v, rfl⟩⟩
      have hwv : (w : fepomepι n → F) = e.mulVec v := rfl
      have hsub : (g w : fepomepι n → F) - (w : fepomepι n → F) = x := by
        rw [← hv, hEapply v]
        have hdiff : (1 - e).mulVec v = v - e.mulVec v := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        rw [hdiff, hwv]
        abel
      refine ⟨g w - w, CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mpr
        ⟨w, rfl⟩, ?_⟩
      change (g w : fepomepι n → F) - (w : fepomepι n → F) = x
      exact hsub
    · rintro ⟨y, hy, rfl⟩
      rw [CFSG.RankThree.OrthogonalInvolutions.mem_commSpace] at hy
      obtain ⟨w, hw⟩ := hy
      refine ⟨(w : fepomepι n → F), ?_⟩
      rw [hEw w, ← hw]
      rfl
  refine (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup).mpr ⟨?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    let w : W := ⟨e.mulVec v, by rw [hW]; exact ⟨v, rfl⟩⟩
    have hwv : (w : fepomepι n → F) = e.mulVec v := rfl
    have hvdec : e.mulVec v + (1 - e).mulVec v = v := by
      rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    have hgw_fix : e.mulVec (g w : fepomepι n → F) = (g w : fepomepι n → F) := by
      have hmem : (g w : fepomepι n → F) ∈ LinearMap.range (Matrix.mulVecLin e) := by
        rw [← hW]; exact (g w).2
      obtain ⟨y, hy⟩ := hmem
      have h2 : Matrix.mulVecLin e ((g w : fepomepι n → F)) = (g w : fepomepι n → F) := by
        rw [← hy]
        show Matrix.mulVecLin e (Matrix.mulVecLin e y) = Matrix.mulVecLin e y
        rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, he.2.1.eq]
      rwa [Matrix.mulVecLin_apply] at h2
    have hcross : QuadraticMap.polar (fepomepQ n F) (g w : fepomepι n → F)
        ((1 - e).mulVec v) = 0 := by
      rw [← hgw_fix]
      exact hpol0 (g w : fepomepι n → F) v
    calc fepomepQ n F (E v) =
          fepomepQ n F ((g w : fepomepι n → F) + (1 - e).mulVec v) := by
            rw [hEapply v]
      _ = fepomepQ n F (g w : fepomepι n → F) + fepomepQ n F ((1 - e).mulVec v) +
            QuadraticMap.polar (fepomepQ n F) (g w : fepomepι n → F) ((1 - e).mulVec v) :=
            QuadraticMap.map_add (fepomepQ n F) _ _
      _ = fepomepQ n F (g w : fepomepι n → F) + fepomepQ n F ((1 - e).mulVec v) := by
            rw [hcross, add_zero]
      _ = fepomepQ n F (w : fepomepι n → F) + fepomepQ n F ((1 - e).mulVec v) := by
            rw [hgQ w]
      _ = fepomepQ n F (e.mulVec v) + fepomepQ n F ((1 - e).mulVec v) := by
            rw [hwv]
      _ = fepomepQ n F v := by
            conv_rhs => rw [← hvdec]
            rw [QuadraticMap.map_add (fepomepQ n F), hpol0 v v, add_zero]
  · have hfin : Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace E) =
        Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace
          (g.restrictScalars F)) := by
      rw [hcommE]
      exact Submodule.finrank_map_subtype_eq W
        (CFSG.RankThree.OrthogonalInvolutions.commSpace (g.restrictScalars F))
    have hdvd : Module.finrank F K ∣
        Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace E) := by
      rw [hfin]
      have hcomp : CFSG.RankThree.OrthogonalInvolutions.commSpace (g.restrictScalars F) =
          (CFSG.RankThree.OrthogonalInvolutions.commSpace g).restrictScalars F := rfl
      rw [hcomp]
      haveI : Module.Free K ↥(CFSG.RankThree.OrthogonalInvolutions.commSpace g) :=
        Module.Free.of_divisionRing K ↥(CFSG.RankThree.OrthogonalInvolutions.commSpace g)
      exact ⟨Module.finrank K ↥(CFSG.RankThree.OrthogonalInvolutions.commSpace g),
        (Module.finrank_mul_finrank F K
          ↥(CFSG.RankThree.OrthogonalInvolutions.commSpace g)).symm⟩
    have h2l : Module.finrank F K = 2 * l := by rw [hπdeg, hl]
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨l * k, ?_⟩
    rw [hk, h2l]
    ring

private lemma fepomep_selfDual_blockGroup_descentOmegaLift
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (g : W ≃ₗ[K] W)
    (hg : ∀ x y : W, H (g x) (g y) = H x y)
    (E : (fepomepι n → F) ≃ₗ[F] (fepomepι n → F))
    (hEw : ∀ w : W, E (w : fepomepι n → F) = (g w : fepomepι n → F))
    (hEfix : ∀ v : fepomepι n → F, E ((1 - ε).mulVec v) = (1 - ε).mulVec v)
    (hEΩ : E ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (fepomepQ n F)
      (Spin.nondegenerate_polarBilin_quadPlus n F)) :
    ∃ u : glBlockCentralizer (fepomepJ n F) S ε, ρ u = g := by
  classical
  obtain ⟨h, hh⟩ :=
    CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus hn hEΩ
  have hrange : E ∈ (Spin.spinAction (fepomepQ n F)).range := ⟨h, hh⟩
  have hcomm : ∀ s ∈ S, ∀ v : fepomepι n → F,
      E ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec v) =
        (s : Matrix (fepomepι n) (fepomepι n) F).mulVec (E v) := by
    intro s hs v
    let as : fepomepA n F S :=
      ⟨(s : Matrix (fepomepι n) (fepomepι n) F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
    have hse : (s : Matrix (fepomepι n) (fepomepι n) F) * ε =
        ε * (s : Matrix (fepomepι n) (fepomepι n) F) :=
      fepomep_dualPair_eps_comm n S hS hε.1 s hs
    have hse1 : (s : Matrix (fepomepι n) (fepomepι n) F) * (1 - ε) =
        (1 - ε) * (s : Matrix (fepomepι n) (fepomepι n) F) := by
      rw [mul_sub, hse, sub_mul, mul_one, one_mul]
    have hWε : W = LinearMap.range (Matrix.mulVecLin ε) := by rw [hW, hself]
    have hmemεv : Matrix.mulVec ε v ∈ W := by rw [hWε]; exact ⟨v, rfl⟩
    let w0 : W := ⟨Matrix.mulVec ε v, hmemεv⟩
    have hdec : Matrix.mulVec ε v + Matrix.mulVec (1 - ε) v = v := by
      rw [← Matrix.add_mulVec]
      have : ε + (1 - ε) = 1 := by abel
      rw [this, Matrix.one_mulVec]
    have hsv : (s : Matrix (fepomepι n) (fepomepι n) F).mulVec v =
        (s : Matrix (fepomepι n) (fepomepι n) F).mulVec (Matrix.mulVec ε v) +
          (s : Matrix (fepomepι n) (fepomepι n) F).mulVec (Matrix.mulVec (1 - ε) v) := by
      conv_lhs => rw [← hdec]
      rw [Matrix.mulVec_add]
    have hsv1ε : (s : Matrix (fepomepι n) (fepomepι n) F).mulVec (Matrix.mulVec (1 - ε) v) =
        Matrix.mulVec (1 - ε) ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hse1]
    have hEv : E v = (g w0 : fepomepι n → F) + Matrix.mulVec (1 - ε) v := by
      calc E v = E (Matrix.mulVec ε v + Matrix.mulVec (1 - ε) v) := by
            conv_lhs => rw [← hdec]
        _ = E (Matrix.mulVec ε v) + E (Matrix.mulVec (1 - ε) v) := by rw [map_add E]
        _ = (g w0 : fepomepι n → F) + Matrix.mulVec (1 - ε) v := by
            rw [show Matrix.mulVec ε v = (w0 : fepomepι n → F) from rfl, hEw, hEfix]
    have h2 : E ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec (Matrix.mulVec ε v)) =
        (g (π as • w0) : fepomepι n → F) := by
      rw [show Matrix.mulVec ε v = (w0 : fepomepι n → F) from rfl, ← hK as w0]
      exact hEw (π as • w0)
    have h3 : E ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec (Matrix.mulVec (1 - ε) v)) =
        Matrix.mulVec (1 - ε) ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec v) := by
      rw [hsv1ε, hEfix]
    have hsw : (s : Matrix (fepomepι n) (fepomepι n) F).mulVec (g w0 : fepomepι n → F) =
        (g (π as • w0) : fepomepι n → F) := by
      rw [← hK as (g w0)]
      exact (congrArg Subtype.val (g.map_smul (π as) w0)).symm
    have hL : E ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec v) =
        (g (π as • w0) : fepomepι n → F) +
          Matrix.mulVec (1 - ε) ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec v) := by
      calc E ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec v)
          = E ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec (Matrix.mulVec ε v) +
                (s : Matrix (fepomepι n) (fepomepι n) F).mulVec
                  (Matrix.mulVec (1 - ε) v)) := by
              conv_lhs => rw [hsv]
        _ = E ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec (Matrix.mulVec ε v)) +
              E ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec
                (Matrix.mulVec (1 - ε) v)) := by
              rw [map_add E]
        _ = (g (π as • w0) : fepomepι n → F) +
              Matrix.mulVec (1 - ε) ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec v) := by
              rw [h2, h3]
    have hR : (s : Matrix (fepomepι n) (fepomepι n) F).mulVec (E v) =
        (g (π as • w0) : fepomepι n → F) +
          Matrix.mulVec (1 - ε) ((s : Matrix (fepomepι n) (fepomepι n) F).mulVec v) := by
      rw [hEv, Matrix.mulVec_add, hsw, hsv1ε]
    rw [hL, hR]
  have hA1 : (((1 : GL (Fin (Module.finrank K W)) K) :
      Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
      (fun x => x ^ (2 ^ (l * f)))).transpose *
      ((1 : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) = 1 := by
    ext i j
    simp
  have hmap :=
    fepomep_selfDual_extension_mem_map (n := n) (hn := hn) (f := f) (l := l)
      (S := S) (hSU := hSU) (hS := hS) (hε := hε) (he := he) (heε := heε) (hself := hself)
      (K := K) (π := π) (hπsurj := hπsurj) (hπker := hπker) (hπdeg := hπdeg)
      (W := W) (hW := hW) (Φ := Φ) (A := 1) (hA := hA1) E hcomm hEfix hrange
  rw [Subgroup.mem_map] at hmap
  obtain ⟨u, hu_mem, hu_eq⟩ := hmap
  refine ⟨⟨u, hu_mem⟩, ?_⟩
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  rw [hρ ⟨u, hu_mem⟩ w]
  rw [show ((fepomepJ n F ((⟨u, hu_mem⟩ :
        glBlockCentralizer (fepomepJ n F) S ε) : ↥(spinGroup (fepomepQ n F))) :
      GL (fepomepι n) F) : Matrix (fepomepι n) (fepomepι n) F) =
      (Spin.spinMatrix (fepomepQ n F) u :
        Matrix (fepomepι n) (fepomepι n) F) from rfl]
  rw [Spin.spinMatrix_mulVec, hu_eq]
  exact hEw w

private lemma fepomep_selfDual_blockGroup_descentHIsometrySurjective
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (g : W ≃ₗ[K] W)
    (hg : ∀ x y : W, H (g x) (g y) = H x y)
    :
    ∃ u : glBlockCentralizer (fepomepJ n F) S ε, ρ u = g := by
  have hgQ := fepomep_selfDual_blockGroup_descentQuadPreserved n hn f hc S hSU hS hodd hε hJε he
      heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ hinjρ H hHinv
          hHtr ι₀ hι₀ hτeq g hg
  obtain ⟨E, hEw, hEfix⟩ := fepomep_selfDual_blockGroup_descentBlockExtension n hn f hc S hSU hS
      hodd hε hJε he heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK
          Φ hinjρ H hHinv hHtr ι₀ hι₀ hτeq g hg hgQ
  have hEΩ := fepomep_selfDual_blockGroup_descentExtensionOmega n hn f hc S hSU hS hodd hε hJε
      he heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ hinjρ H
          hHinv hHtr ι₀ hι₀ hτeq g hg hgQ E hEw hEfix
  exact fepomep_selfDual_blockGroup_descentOmegaLift n hn f hc S hSU hS hodd hε hJε he heε hself
      hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ hinjρ H hHinv hHtr ι₀
          hι₀ hτeq g hg E hEw hEfix hEΩ

private lemma fepomep_selfDual_blockGroup_descentJSurjective
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (A : GL (Fin (Module.finrank K W)) K)
    (hA : (((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
        (fun x => x ^ (2 ^ (l * f)))).transpose *
      (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) *
      ((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) =
    (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1))))) :
    ∃ u : glBlockCentralizer (fepomepJ n F) S ε,
      ∀ w : W, (ρ u w : W) = Φ.symm (Matrix.mulVec ((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Φ w)) := by
  have hgA : ∀ x y : W,
      H (Φ.symm (Matrix.mulVec ((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Φ x)))
        (Φ.symm (Matrix.mulVec ((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Φ y))) = H x y :=
    fepomep_selfDual_blockGroup_descentJIsometry n hn f hc S hSU hS hodd hε hJε he heε hself hd4
        l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ hinjρ H hHinv hHtr ι₀ hι₀
            hτeq A hA
  let Am : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K :=
    (A : GL (Fin (Module.finrank K W)) K)
  have hInj : Function.Injective (Matrix.mulVecLin Am) := by
    change Function.Injective (fun v => Matrix.mulVec Am v)
    exact (Matrix.mulVec_injective_iff_isUnit).mpr A.isUnit
  let Alin : (Fin (Module.finrank K W) → K) ≃ₗ[K] (Fin (Module.finrank K W) → K) :=
    LinearEquiv.ofBijective (Matrix.mulVecLin Am)
      ⟨hInj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hInj⟩
  let g : W ≃ₗ[K] W := Φ.trans (Alin.trans Φ.symm)
  have hgdef : ∀ w : W, g w = Φ.symm (Matrix.mulVec Am (Φ w)) := by
    intro w
    simp [g, Alin]
    change Matrix.mulVecLin Am (Φ w) = Matrix.mulVec Am (Φ w)
    rfl
  obtain ⟨u, hu⟩ := fepomep_selfDual_blockGroup_descentHIsometrySurjective n hn f hc S hSU hS
      hodd hε hJε he heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK
          Φ hinjρ H hHinv hHtr ι₀ hι₀ hτeq g (by
    intro x y
    rw [hgdef x, hgdef y]
    exact hgA x y)
  exact ⟨u, fun w => by rw [hu]; exact hgdef w⟩

private lemma fepomep_selfDual_blockGroup_descentJRangeGeData
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f))) :
    ∀ A : GL (Fin (Module.finrank K W)) K,
      (((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
          (fun x => x ^ (2 ^ (l * f)))).transpose *
        (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) *
        ((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) =
      (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) →
      A ∈ ι₀.range := by
  intro A hA
  obtain ⟨u, hu⟩ := fepomep_selfDual_blockGroup_descentJSurjective n hn f hc S hSU hS hodd hε
      hJε he heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ hinjρ
          H hHinv hHtr ι₀ hι₀ hτeq A hA
  refine ⟨u, ?_⟩
  ext i j
  have e1 : (Matrix.mulVec ((ι₀ u : GL (Fin (Module.finrank K W)) K) :
      Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single j 1)) i =
      ((ι₀ u : GL (Fin (Module.finrank K W)) K) :
      Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) i j := by
    simp [Matrix.mulVec, Pi.single_apply]
  rw [← e1]
  have h1 := congrFun (hι₀ u j) i
  rw [h1, hu (Φ.symm (Pi.single j 1))]
  simp [Matrix.mulVec, Pi.single_apply, LinearEquiv.apply_symm_apply]

private lemma fepomep_selfDual_blockGroup_descentJRangeGe
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f))) :
    ∀ A : GL (Fin (Module.finrank K W)) K,
      (((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
          (fun x => x ^ (2 ^ (l * f)))).transpose *
        (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) *
        ((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) =
      (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) →
      A ∈ ι₀.range := by
  intro A hA
  exact fepomep_selfDual_blockGroup_descentJRangeGeData n hn f hc S hSU hS hodd hε hJε
    he heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ
    hinjρ H hHinv hHtr ι₀ hι₀ hτeq A hA

private lemma fepomep_selfDual_blockGroup_descentCoordinateUnitary
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hinjρ : Function.Injective ρ)
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (hHtr : ∀ v w : W, Algebra.trace F K (H v w) =
      QuadraticMap.polar (fepomepQ n F) (v : fepomepι n → F) (w : fepomepι n → F))
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : ∀ (g : glBlockCentralizer (fepomepJ n F) S ε) (i : Fin (Module.finrank K W)),
      Matrix.mulVec ((ι₀ g : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) (Pi.single i 1) =
        Φ (ρ g (Φ.symm (Pi.single i 1))))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f))) :
    ∀ A : GL (Fin (Module.finrank K W)) K,
      A ∈ ι₀.range ↔
      (((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
          (fun x => x ^ (2 ^ (l * f)))).transpose *
        (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) *
        ((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) =
      (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) := by
  intro A
  exact ⟨fepomep_selfDual_blockGroup_descentJRangeLe n hn f hc S hSU hS hodd hε hJε he
      heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW hK ρ hρ hinjρ H
      hHinv Φ ι₀ hι₀ hτeq A,
    fepomep_selfDual_blockGroup_descentJRangeGe n hn f hc S hSU hS hodd hε hJε he
      heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ hinjρ H
      hHinv hHtr ι₀ hι₀ hτeq A⟩

private lemma fepomep_selfDual_blockGroup_descentIdentityRange
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K))
    (hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)))
    (H : W →ₛₗ[τ.toRingHom] W →ₗ[K] K) (hHsymm : H.IsSymm) (hHnd : H.SeparatingLeft)
    (hHinv : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (x y : W),
      H (ρ u x) (ρ u y) = H x y)
    (ι₀ : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K)
    (hι₀ : Function.Injective ι₀)
    (hU₀ : ∀ A : GL (Fin (Module.finrank K W)) K,
      A ∈ ι₀.range ↔
      (((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
          (fun x => x ^ (2 ^ (l * f)))).transpose *
        (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))) *
        ((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) =
      (Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1))))) :
    ∃ ι : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K,
      Function.Injective ι ∧
      (∀ A : GL (Fin (Module.finrank K W)) K, A ∈ ι.range ↔
        (((A : GL (Fin (Module.finrank K W)) K) :
            Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
            (fun x => x ^ (2 ^ (l * f)))).transpose *
          ((A : GL (Fin (Module.finrank K W)) K) :
            Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) = 1) := by
  let σ : K →+* K := τ.toRingHom
  have hmap : (⇑σ : K → K) = fun x => x ^ (2 ^ (l * f)) := by
    funext x
    exact hτeq x
  let J : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K :=
    Matrix.of (fun i j => H (Φ.symm (Pi.single i 1)) (Φ.symm (Pi.single j 1)))
  obtain ⟨C, hC⟩ :=
    fepomep_selfDual_blockGroup_descentNormalization n hn f hc S hSU hS hodd hε hJε he
      heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne hτeq W hW H hHsymm
      hHnd Φ
  have hCσ : ((((C : GL (Fin (Module.finrank K W)) K) :
      Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map ⇑σ).transpose * J *
      ((C : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) = 1) := by
    rw [hmap]
    exact hC
  have hU₀σ : ∀ A : GL (Fin (Module.finrank K W)) K,
      A ∈ ι₀.range ↔ ((((A : GL (Fin (Module.finrank K W)) K) :
        Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map ⇑σ).transpose * J *
        ((A : GL (Fin (Module.finrank K W)) K) :
          Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) = J) := by
    intro A
    rw [hmap]
    exact hU₀ A
  simpa only [hmap] using
    fepomep_selfDual_blockGroup_descentTransport (τ := τ) (Module.finrank K W) σ J ι₀ hι₀ hU₀σ C hCσ

private lemma fepomep_selfDual_blockGroup_formDescentExists
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1)
    (W : Submodule F (fepomepι n → F)) (hW : W = LinearMap.range (Matrix.mulVecLin e))
    [Module K W] [IsScalarTower F K W] [FiniteDimensional K W]
    (ρ : glBlockCentralizer (fepomepJ n F) S ε →* (W ≃ₗ[K] W))
    (hρ : ∀ (u : glBlockCentralizer (fepomepJ n F) S ε) (w : W),
      ((ρ u w : W) : fepomepι n → F) =
        Matrix.mulVec ((fepomepJ n F (u : ↥(spinGroup (fepomepQ n F)))) :
          Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (hK : ∀ (a : fepomepA n F S) (w : W),
      ((π a • w : W) : fepomepι n → F) =
        Matrix.mulVec (a : Matrix (fepomepι n) (fepomepι n) F) (w : fepomepι n → F))
    (Φ : W ≃ₗ[K] (Fin (Module.finrank K W) → K)) :
    ∃ ι : glBlockCentralizer (fepomepJ n F) S ε →* GL (Fin (Module.finrank K W)) K,
      Function.Injective ι ∧
      (∀ A : GL (Fin (Module.finrank K W)) K, A ∈ ι.range ↔
        (((A : GL (Fin (Module.finrank K W)) K) :
            Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
            (fun x => x ^ (2 ^ (l * f)))).transpose *
          ((A : GL (Fin (Module.finrank K W)) K) :
            Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) = 1) := by
  classical
  have hinjρ : Function.Injective ρ :=
    fepomep_selfDual_blockAction_injective n hn S hSU hS hε he heε hself (by omega) K π
      hπsurj hπker hπdeg W hW hK ρ hρ
  have hτF : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a := by
    intro a
    have h := hτcompat (algebraMap F (fepomepA n F S) a)
    rw [π.commutes a] at h
    rw [(fepomep_formAdjAlgEquiv n hn S hSU hS).commutes a] at h
    rw [π.commutes a] at h
    exact h
  have hdeg : Module.finrank F K = 2 * l := by rw [hπdeg, hl]
  have hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)) :=
    fepomep_selfDual_tau_eq_frobenius f hc l hl2 hdeg τ hτF hτ2 hτne
  obtain ⟨H, hHsymm, hHnd, hHtr, hHinv⟩ :=
    fepomep_selfDual_blockGroup_descentHermitianForm n hn f hc S hSU hS hodd hε hJε he
      heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ
  obtain ⟨ι₀, hι₀inj, hι₀⟩ :=
    fepomep_selfDual_blockGroup_descentCoordinateMap n hn f hc S hSU hS hodd hε hJε he
      heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW hK ρ hρ hinjρ Φ
  have hU₀ := fepomep_selfDual_blockGroup_descentCoordinateUnitary n hn f hc S hSU hS hodd
    hε hJε he heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ
    hinjρ H hHinv hHtr ι₀ hι₀ hτeq
  exact fepomep_selfDual_blockGroup_descentIdentityRange n hn f hc S hSU hS hodd hε hJε he
    heε hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ hτeq H
    hHsymm hHnd hHinv ι₀ hι₀inj hU₀

private lemma fepomep_selfDual_blockGroup_su (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1) :
    ∃ m' : ℕ, 2 ≤ m' ∧ Nonempty
      (↥(⁅glBlockCentralizer (fepomepJ n F) S ε,
          glBlockCentralizer (fepomepJ n F) S ε⁆) ≃*
        CFSG.Open.StatedSU m' (2 ^ (l * f)) K) := by
  obtain ⟨W, hW, hmod, htower, hfin, hdim, hm1, hK⟩ :=
    fepomep_selfDual_blockModule n hn S hSU hS hε he heε hself K π hπsurj hπker hπdeg
  letI : Module K W := hmod
  letI : IsScalarTower F K W := htower
  letI : FiniteDimensional K W := hfin
  obtain ⟨ρ, hρ⟩ :=
    fepomep_selfDual_blockActionHom n hn S hSU hS hε he heε hself (by omega) K π hπsurj
      hπker hπdeg W hW hK
  obtain ⟨Φ⟩ := fepomep_selfDual_moduleMatrixEquiv n hn S hSU hS he K W hW
  obtain ⟨ι, hι, hU⟩ :=
    fepomep_selfDual_blockGroup_formDescentExists n hn f hc S hSU hS hodd hε hJε he heε
      hself hd4 l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ρ hρ hK Φ
  obtain ⟨hKcard, hm2, hne⟩ :=
    fepomep_selfDual_blockGroup_formRank n hn f hc S hSU hS hodd hε hJε he heε hself hd4 l hl
      hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW hK
  have hf : 1 ≤ f := by
    by_contra hf0
    have hfz : f = 0 := by omega
    have hcard2 : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
    rw [hc, hfz, pow_zero] at hcard2
    omega
  exact fepomep_selfDual_blockGroup_su_of_unitary n hn f hf S hSU hS hodd hε hJε he heε hself
      hd4
    l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne W hW ι hι hU hKcard hm2 hne

private lemma fepomep2_scalars_subgroupOf_statedSL_two_eq_bot {K : Type} [Field K] [CharP K 2] :
    (CFSG.Open.StatedScalars (Fin 2) K).subgroupOf (CFSG.Open.StatedSL 2 K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzscal : (z : GL (Fin 2) K) ∈ CFSG.Open.StatedScalars (Fin 2) K := hz
  rw [CFSG.Open.StatedAPI.statedScalars_eq_center] at hzscal
  obtain ⟨c, hc⟩ := (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar).mp hzscal
  have hdet : ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    (CFSG.Open.StatedAPI.mem_statedSL_iff).mp z.2
  have hc2 : c ^ 2 = 1 := by
    have h := hdet
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have hc1 : c = 1 := by
    rcases (sq_eq_one_iff.mp hc2) with h | h
    · exact h
    · rw [h]; exact CharTwo.neg_eq 1
  apply Subtype.ext
  apply Units.ext
  simp [← hc, hc1, Matrix.scalar_apply, Matrix.diagonal_one]

private lemma fepomep2_scalars_subgroupOf_statedSU_two_eq_bot {K : Type} [Field K] [CharP K 2]
    (q : ℕ) :
    (CFSG.Open.StatedScalars (Fin 2) K).subgroupOf (CFSG.Open.StatedSU 2 q K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzscal : (z : GL (Fin 2) K) ∈ CFSG.Open.StatedScalars (Fin 2) K := hz
  rw [CFSG.Open.StatedAPI.statedScalars_eq_center] at hzscal
  obtain ⟨c, hc⟩ := (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar).mp hzscal
  have hzSL : (z : GL (Fin 2) K) ∈ CFSG.Open.StatedSL 2 K :=
    CFSG.Open.StatedAPI.statedSU_le_statedSL 2 q K z.2
  have hdet : ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    (CFSG.Open.StatedAPI.mem_statedSL_iff).mp hzSL
  have hc2 : c ^ 2 = 1 := by
    have h := hdet
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have hc1 : c = 1 := by
    rcases (sq_eq_one_iff.mp hc2) with h | h
    · exact h
    · rw [h]; exact CharTwo.neg_eq 1
  apply Subtype.ext
  apply Units.ext
  simp [← hc, hc1, Matrix.scalar_apply, Matrix.diagonal_one]

private lemma fepomep_selfDual_SU2_to_SL2 {F : Type} [Field F] [CharP F 2] {f : ℕ}
    (d : ℕ) {K : Type} [Field K] [Finite K] [Algebra F K]
    (hKcard : Nat.card K = ((2 ^ f) ^ d) ^ 2) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'),
      Nat.card K' = (2 ^ f) ^ d ∧
      Nonempty (CFSG.Open.StatedProj (CFSG.Open.StatedSU 2 ((2 ^ f) ^ d) K) ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K')) := by
  classical
  haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K' : Type := ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d))
  haveI : CharP K' 2 := Subfield.charP (CFSG.LieType.Steinberg.fixedSubfield K 2 (f * d)) 2
  have hK' : Nat.card K = (2 ^ (f * d)) ^ 2 := by
    rw [hKcard, ← pow_mul 2 f d]
  have hcard : Nat.card K' = 2 ^ (f * d) :=
    CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := 2) (f := f * d) hK'
  refine ⟨K', inferInstance, inferInstance, ?_, ?_⟩
  · rw [hcard, pow_mul]
  · obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := K) (r := 2) (f := f * d) hK'
    rw [pow_mul] at e
    have eSL : ↥(CFSG.Open.StatedSL 2 K') ≃* CFSG.Open.StatedSU 2 ((2 ^ f) ^ d) K :=
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K').symm.trans e
    have hbotSL : (CFSG.Open.StatedScalars (Fin 2) K').subgroupOf
        (CFSG.Open.StatedSL 2 K') = ⊥ :=
      fepomep2_scalars_subgroupOf_statedSL_two_eq_bot
    have hbotSU : (CFSG.Open.StatedScalars (Fin 2) K).subgroupOf
        (CFSG.Open.StatedSU 2 ((2 ^ f) ^ d) K) = ⊥ :=
      fepomep2_scalars_subgroupOf_statedSU_two_eq_bot ((2 ^ f) ^ d)
    have projSU : CFSG.Open.StatedProj (CFSG.Open.StatedSU 2 ((2 ^ f) ^ d) K) ≃*
        CFSG.Open.StatedSU 2 ((2 ^ f) ^ d) K :=
      (QuotientGroup.quotientMulEquivOfEq hbotSU).trans QuotientGroup.quotientBot
    have projSL : CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K') ≃*
        ↥(CFSG.Open.StatedSL 2 K') :=
      (QuotientGroup.quotientMulEquivOfEq hbotSL).trans QuotientGroup.quotientBot
    exact ⟨projSU.trans (eSL.symm.trans projSL.symm)⟩

private lemma fepomep_selfDual_component_su_of_blockGroup (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (l : ℕ)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    {m' : ℕ} (hm' : 2 ≤ m')
    (φ : ↥(⁅glBlockCentralizer (fepomepJ n F) S ε,
        glBlockCentralizer (fepomepJ n F) S ε⁆) ≃*
      CFSG.Open.StatedSU m' (2 ^ (l * f)) K) :
    Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU m' (2 ^ (l * f)) K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Module.finrank F K = 2 * l := by rw [hπdeg, hl]
  have hKcard : Nat.card K = (2 ^ (l * f)) ^ 2 := by
    rw [fepomep_blockField_card f (2 * l) hc hfin, ← pow_mul]
    congr 1
    ring
  have hf1 : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    subst f
    rw [pow_zero] at hc
    have h2 : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
    omega
  have hlf2 : 2 ≤ l * f := by
    have h := Nat.mul_le_mul hl2 hf1
    simpa using h
  have hq4 : 4 ≤ 2 ^ (l * f) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (l * f) := Nat.pow_le_pow_right (by norm_num) hlf2
  have hpow2 : 2 ^ (l * f) ≠ 2 := by
    intro h2
    have hle : 2 ^ 2 ≤ 2 ^ (l * f) := Nat.pow_le_pow_right (by norm_num) hlf2
    omega
  have hSUq : CFSG.Open.IsQuasisimple ↥(CFSG.Open.StatedSU m' (2 ^ (l * f)) K) ∧
      Subgroup.center ↥(CFSG.Open.StatedSU m' (2 ^ (l * f)) K) =
        (CFSG.Open.StatedScalars (Fin m') K).subgroupOf
          (CFSG.Open.StatedSU m' (2 ^ (l * f)) K) := by
    by_cases hm3 : 3 ≤ m'
    · have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
        (f := l * f) (n := m') hKcard hm3 (by intro hcon; exact hpow2 (congrArg Prod.snd hcon))
      exact ⟨⟨hq.1.1.commutator_eq_top, hq.1.2.1⟩, hq.2⟩
    · have hm2 : m' = 2 := by omega
      subst hm2
      have hexp : 2 ^ (l * f) = (2 ^ f) ^ l := by rw [← pow_mul, mul_comm]
      have hKcardL : Nat.card K = ((2 ^ f) ^ l) ^ 2 := by rw [hKcard, hexp]
      haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
      have hperf : Group.IsPerfect ↥(CFSG.Open.StatedSU 2 (2 ^ (l * f)) K) :=
        CFSG.RankThree.SubgroupLists.isPerfect_statedSU_two (r := 2) (f := l * f) hKcard hq4
      obtain ⟨K', hK'field, hK'finite, hK'card, ⟨ePSU₀⟩⟩ :=
        fepomep_selfDual_SU2_to_SL2 (F := F) (f := f) l (K := K) hKcardL
      letI : Field K' := hK'field
      letI : Finite K' := hK'finite
      have ePSU : CFSG.Open.StatedProj (CFSG.Open.StatedSU 2 (2 ^ (l * f)) K) ≃*
          CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K') := by
        rw [hexp]
        exact ePSU₀
      have hK'4 : 4 ≤ Nat.card K' := by rw [hK'card, ← hexp]; exact hq4
      haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K') :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK'4
      have hsimpleSL : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K')) :=
        MulEquiv.isSimpleGroup
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K').symm
      haveI : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K')) := hsimpleSL
      have hsimpleSU : IsSimpleGroup
          (CFSG.Open.StatedProj (CFSG.Open.StatedSU 2 (2 ^ (l * f)) K)) :=
        MulEquiv.isSimpleGroup ePSU
      have hSUq'' := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperf hsimpleSU
      exact ⟨⟨hSUq''.1.1.commutator_eq_top, hSUq''.1.2.1⟩, hSUq''.2⟩
  let H := ⁅glBlockCentralizer (fepomepJ n F) S ε,
    glBlockCentralizer (fepomepJ n F) S ε⁆
  have hHq : CFSG.Open.IsQuasisimple H := CFSG.Open.IsQuasisimple.of_mulEquiv φ hSUq.1
  have hsub : CFSG.Open.IsSubnormal (J'.subgroupOf H) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib (CFSG.Assembly.IsSubnormal.subgroupOf hJε.2.1)
  haveI : Group.IsPerfect J' := ⟨hJε.2.2.1⟩
  haveI : Group.IsPerfect (J'.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJε.1).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJε.1).symm.surjective
  have hJeq : J' = H := by
    rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
      hHq (J'.subgroupOf H) hsub with hbot | htop
    · exfalso
      have hJ'bot : J' = ⊥ := by
        have hdisj : Disjoint J' H := Subgroup.subgroupOf_eq_bot.mp hbot
        rwa [disjoint_iff, inf_eq_left.mpr hJε.1] at hdisj
      have hnt : Nontrivial J' := CFSG.ComponentClassification.Quasisimple.nontrivial hJε.2.2
      rw [hJ'bot] at hnt
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
    · exact le_antisymm hJε.1 (Subgroup.subgroupOf_eq_top.mp htop)
  let φJ : ↥J' ≃* ↥(CFSG.Open.StatedSU m' (2 ^ (l * f)) K) := hJeq.symm ▸ φ
  exact ⟨(QuotientGroup.congr (Subgroup.center ↥J')
      (Subgroup.center ↥(CFSG.Open.StatedSU m' (2 ^ (l * f)) K)) φJ
      (Subgroup.map_center_eq φJ)).trans
    (QuotientGroup.quotientMulEquivOfEq hSUq.2)⟩

private lemma fepomep_selfDual_component_su (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1) :
    ∃ m' : ℕ, 2 ≤ m' ∧ Nonempty
      (↥J' ⧸ Subgroup.center ↥J' ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSU m' (2 ^ (l * f)) K)) := by
  obtain ⟨m', hm', ⟨φ⟩⟩ :=
    fepomep_selfDual_blockGroup_su n hn f hc S hSU hS hodd hε hJε he heε hself hd4 l hl hl2
      K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne
  exact ⟨m', hm',
    fepomep_selfDual_component_su_of_blockGroup n hn f hc S hSU hS hodd hε hJε he heε hself l
      K hπdeg hl hl2 hm' φ⟩

private lemma fepomep_selfDual_model (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n)
    (f : ℕ) (hc : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e) (hself : e = ε)
    (hd4 : 4 ≤ blockDegree (fepomepA n F S) e)
    (l : ℕ) (hl : blockDegree (fepomepA n F S) e = 2 * l) (hl2 : 2 ≤ l)
    (K : Type) [Field K] [Finite K] [Algebra F K]
    (π : fepomepA n F S →ₐ[F] K) (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (fepomepι n) (fepomepι n) F) * e = 0)
    (hπdeg : Module.finrank F K = blockDegree (fepomepA n F S) e)
    (τ : K ≃+* K)
    (hτcompat : ∀ a : fepomepA n F S, τ (π a) =
      π (fepomep_formAdjAlgEquiv n hn S hSU hS a))
    (hτ2 : τ ^ 2 = 1) (hτne : τ ≠ 1) :
    (∃ m' : ℕ, 3 ≤ m' ∧ CFSG.Open.StatedClassicalModel
        (↥J' ⧸ Subgroup.center ↥J') .PSU m' 2 (l * f)) ∨
      CFSG.Open.StatedClassicalModel (↥J' ⧸ Subgroup.center ↥J') .PSL 2 2 (l * f) := by
  obtain ⟨m', hm'2, ⟨φ⟩⟩ :=
    fepomep_selfDual_component_su n hn f hc S hSU hS hodd hε hJε he heε hself hd4 l hl hl2
      K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne
  have hKcard : Nat.card K = (2 ^ (l * f)) ^ 2 := by
    rw [fepomep_blockField_card f _ hc hπdeg, hl, ← pow_mul]
    congr 1
    ring
  have hlf2 : 2 ≤ l * f := by
    have h := Nat.mul_le_mul hl2 hf
    simpa using h
  have hpow2 : 2 ^ (l * f) ≠ 2 := by
    intro h2
    have hle : 2 ^ 2 ≤ 2 ^ (l * f) := Nat.pow_le_pow_right (by norm_num) hlf2
    omega
  have hpow3 : 2 ^ (l * f) ≠ 3 := by
    intro h3
    have hle : 2 ^ 2 ≤ 2 ^ (l * f) := Nat.pow_le_pow_right (by norm_num) hlf2
    omega
  by_cases hm3 : 3 ≤ m'
  · have hadm : CFSG.Open.StatedLieAdmissible .PSU m' 2 (l * f) :=
      ⟨Nat.prime_two, by omega, hm3, fun h => hpow2 (congrArg Prod.snd h)⟩
    refine Or.inl ?_
    refine ⟨m', hm3, hadm, K, ‹Field K›, ‹Finite K›, hKcard, ?_⟩
    exact ⟨φ⟩
  · have hm2 : m' = 2 := by omega
    have hexp : (2 ^ f) ^ l = 2 ^ (l * f) := by rw [← pow_mul, mul_comm f l]
    have hKcardL : Nat.card K = ((2 ^ f) ^ l) ^ 2 := by rw [hKcard, hexp]
    obtain ⟨K', hK'field, hK'finite, hK'card, ⟨eSL⟩⟩ :=
      fepomep_selfDual_SU2_to_SL2 (F := F) (f := f) l (K := K) hKcardL
    rw [hexp] at eSL
    subst hm2
    have hK'card' : Nat.card K' = 2 ^ (l * f) := by rw [hK'card, hexp]
    have hadm : CFSG.Open.StatedLieAdmissible .PSL 2 2 (l * f) :=
      ⟨Nat.prime_two, by omega, by omega, fun h => hpow2 (congrArg Prod.snd h),
        fun h => hpow3 (congrArg Prod.snd h)⟩
    refine Or.inr ?_
    refine ⟨hadm, K', hK'field, hK'finite, hK'card', ?_⟩
    exact ⟨φ.trans eSL⟩

private lemma fepomep_component_model (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n) (f : ℕ)
    (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (fepomepι n) F))
    (hSU : ∀ s ∈ S, s ∈ (fepomepJ n F).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (fepomepQ n F))}
    {ε e : Matrix (fepomepι n) (fepomepι n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (fepomepG n F) (fepomepA n F S) ε)
    (hJε : IsComponentOf J' ⁅glBlockCentralizer (fepomepJ n F) S ε,
      glBlockCentralizer (fepomepJ n F) S ε⁆)
    (he : IsPrimIdemIn (fepomepA n F S) e) (heε : e * ε = e)
    (hdeg : (e = ε ∧ 4 ≤ blockDegree (fepomepA n F S) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (fepomepA n F S) e)) :
    ∃ (t' : StatedLieTag) (m' f' : ℕ), f < f' ∧
      t' ∈ CFSG.Blueprint.classicalTags ∧
      CFSG.Open.StatedClassicalModel (↥J' ⧸ Subgroup.center ↥J') t' m' 2 f' := by
  classical
  have hf : 1 ≤ f := by
    haveI : Fintype F := Fintype.ofFinite F
    have h2 : 2 ≤ Fintype.card F :=
      Fintype.one_lt_card_iff.mpr (exists_pair_ne F)
    have h2' : 2 ≤ Nat.card F := by rwa [Nat.card_eq_fintype_card]
    by_contra h
    have h0 : f = 0 := by omega
    subst f
    rw [pow_zero] at hc
    omega
  rcases hdeg with ⟨hself, hd4⟩ | ⟨hne, hd2⟩
  · obtain ⟨K, hKfield, hKalg, hKfinite, π, hπsurj, hπker, hπdeg⟩ :=
      exists_blockField hS hodd he
    letI : Field K := hKfield
    letI : Algebra F K := hKalg
    letI : Finite K := hKfinite
    obtain ⟨l, hl, hl2, τ, hτcompat, hτ2, hτne⟩ :=
      fepomep_selfDual_hermitian n hn f hc S hSU hS hodd hε he heε hself hd4 K π
        hπsurj hπker hπdeg
    rcases fepomep_selfDual_model n hn f hc hf S hSU hS hodd hε hJε he heε hself hd4
        l hl hl2 K π hπsurj hπker hπdeg τ hτcompat hτ2 hτne with ⟨m', hm'3, hmod⟩ | hmod
    · refine ⟨.PSU, m', l * f, ?_, ?_, hmod⟩
      · have hl1 : 1 < l := by omega
        have hf0 : 0 < f := by omega
        simpa using Nat.mul_lt_mul_of_pos_right hl1 hf0
      · decide
    · refine ⟨.PSL, 2, l * f, ?_, ?_, hmod⟩
      · have hl1 : 1 < l := by omega
        have hf0 : 0 < f := by omega
        simpa using Nat.mul_lt_mul_of_pos_right hl1 hf0
      · decide
  · obtain ⟨K, hKfield, hKalg, hKfinite, π, hπsurj, hπker, hπdeg⟩ :=
      exists_blockField hS hodd he
    letI : Field K := hKfield
    letI : Algebra F K := hKalg
    letI : Finite K := hKfinite
    obtain ⟨m', hm'2, hmod⟩ :=
      fepomep_dualPair_model n hn f hc hf S hSU hS hodd hε hJε he heε hne hd2 K π
        hπsurj hπker hπdeg
    refine ⟨.PSL, m', blockDegree (fepomepA n F S) e * f, ?_, ?_, hmod⟩
    · have hd1 : 1 < blockDegree (fepomepA n F S) e := by omega
      have hf0 : 0 < f := by omega
      simpa using Nat.mul_lt_mul_of_pos_right hd1 hf0
    · decide

theorem ggSixLSevenFieldExtCase_POmegaPlus (n : ℕ) (F : Type) [Field F]
    (hn : 3 ≤ n) (f : ℕ) (hc : Nat.card F = 2 ^ f) {X : Type} [Group X] [Finite X]
    (ψ : ↥(spinGroup (Spin.quadPlus n F)) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {J' : Subgroup ↥(spinGroup (Spin.quadPlus n F))}
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε, glBlockCentralizer
      (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e)) :
    GGSixLSevenFieldExtCase (J'.map ψ) .POmegaPlus f := by
  classical
  haveI hFin : Finite F := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  haveI hChar : CharP F 2 := by
    haveI : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = 2 ^ f := by
      rw [← Nat.card_eq_fintype_card]; exact hc
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow hcard
  obtain ⟨t', m', f', hlt, ht', hmod⟩ :=
    fepomep_component_model n hn f hc S hSU hS hodd hε hJε he heε hdeg
  have hperf : _root_.commutator ↥J' = ⊤ := hJε.2.2.1
  obtain ⟨ξ⟩ := fepomep_quotientCenter ψ hψ hperf
  have hmod' : CFSG.Open.StatedClassicalModel
      (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) t' m' 2 f' :=
    fepomep_statedClassicalModel_congr ξ t' m' 2 f' hmod
  exact fepomep_fieldExtCase_of_model f (J'.map ψ) hlt ht' hmod'

end CFSG.StandardType.ClassicalPosition