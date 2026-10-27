module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.RankThree.PartOne.AUTSL.OmegaForm
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockRankDvd
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGSixTCBlockField
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW35
public import CFSG.GroupTheory.InvolutionClassProducts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

private noncomputable abbrev bmst_gram (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f)) :
    Matrix N N (GaloisField 2 f) :=
  LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)

private noncomputable abbrev bmst_toLin (N : Type) [Fintype N] [DecidableEq N]
    (F : Type) [Field F] : GL N F ≃* (N → F) ≃ₗ[F] (N → F) :=
  CFSG.ClassicalGroups.Orthogonal.toLinEquiv N F

private abbrev bmst_memH (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (H : Subgroup (GL N (GaloisField 2 f))) : Prop :=
  ∀ A : GL N (GaloisField 2 f), A ∈ H ↔
    Matrix.transpose (A : Matrix N N (GaloisField 2 f)) * bmst_gram f Q *
      (A : Matrix N N (GaloisField 2 f)) = bmst_gram f Q

private lemma bmst_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma bmst_toBilin_eq (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f)) :
    Matrix.toBilin' (bmst_gram f Q) = QuadraticMap.polarBilin Q := by
  have hmat : (LinearMap.toMatrix₂' (GaloisField 2 f))
      (Matrix.toBilin' (bmst_gram f Q)) = bmst_gram f Q := by
    ext i j
    rw [LinearMap.toMatrix₂'_apply, Matrix.toBilin'_apply', single_dotProduct,
      Matrix.mulVec_single]
    simp
  exact (LinearMap.toMatrix₂' (GaloisField 2 f)).injective hmat

private lemma bmst_polar_eq_dot (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (x y : N → GaloisField 2 f) :
    QuadraticMap.polar Q x y = x ⬝ᵥ (bmst_gram f Q).mulVec y := by
  rw [← QuadraticMap.polarBilin_apply_apply Q x y, ← bmst_toBilin_eq f Q,
    Matrix.toBilin'_apply']

private lemma bmst_dot_comm (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (x y : N → GaloisField 2 f) :
    x ⬝ᵥ (bmst_gram f Q).mulVec y = y ⬝ᵥ (bmst_gram f Q).mulVec x := by
  rw [← bmst_polar_eq_dot f Q x y, ← bmst_polar_eq_dot f Q y x]
  exact QuadraticMap.polar_comm Q x y

private lemma bmst_dot_self (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (x : N → GaloisField 2 f) :
    x ⬝ᵥ (bmst_gram f Q).mulVec x = 0 := by
  rw [← bmst_polar_eq_dot f Q x x, QuadraticMap.polar_self]
  rw [nsmul_eq_mul, CharP.cast_eq_zero (GaloisField 2 f) 2, zero_mul]

private lemma bmst_isometry_transpose_mul (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    {A : GL N (GaloisField 2 f)}
    (hA : ∀ v, Q ((A : Matrix N N (GaloisField 2 f)).mulVec v) = Q v) :
    Matrix.transpose (A : Matrix N N (GaloisField 2 f)) * bmst_gram f Q *
      (A : Matrix N N (GaloisField 2 f)) = bmst_gram f Q := by
  exact CFSG.RankThree.PartOne.AUTSL.gram_of_isometry Q (bmst_gram f Q)
    (fun v w => bmst_polar_eq_dot f Q v w)
    (A : Matrix N N (GaloisField 2 f)) hA

private lemma bmst_isUnit_det (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) : IsUnit (bmst_gram f Q).det := by
  rw [isUnit_iff_ne_zero, ← Matrix.nondegenerate_iff_det_ne_zero,
    ← Matrix.nondegenerate_toBilin'_iff, bmst_toBilin_eq f Q]
  exact hnd

private lemma bmst_spinMatrix_mem_H (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    (x : ↥(spinGroup Q)) : Spin.spinMatrix Q x ∈ H :=
  (hH (Spin.spinMatrix Q x)).mpr
    (bmst_isometry_transpose_mul f Q (Spin.spinMatrix_mem Q x))

private noncomputable def bmst_spToSp (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H) :
    ↥(spinGroup Q) →* ↥H :=
  (Spin.spinMatrix Q).codRestrict H (bmst_spinMatrix_mem_H f Q H hH)

private lemma bmst_spToSp_coe (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    (x : ↥(spinGroup Q)) :
    ((bmst_spToSp f Q H hH x : ↥H) : GL N (GaloisField 2 f)) = Spin.spinMatrix Q x :=
  rfl

private lemma bmst_spToSp_injective (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    (hinj : Function.Injective (Spin.spinMatrix Q)) :
    Function.Injective (bmst_spToSp f Q H hH) := by
  intro x y h
  exact hinj (congrArg Subtype.val h)

private lemma bmst_blockDegree_eq_two (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (S : Set (GL N (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix N N (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmst_gram f Q) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 2 := by
  have hSG : ∀ s ∈ S, Matrix.transpose (s : Matrix N N (GaloisField 2 f)) *
      bmst_gram f Q * (s : Matrix N N (GaloisField 2 f)) = bmst_gram f Q := by
    intro s hs
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hSU s hs)
    exact bmst_isometry_transpose_mul f Q (Spin.spinMatrix_mem Q x)
  rcases blockDegree_eq_one_or_even_of_formAdj_eq (bmst_isUnit_det f Q hnd) hS hodd hSG
    he hadj with h | h
  · omega
  · obtain ⟨m, hm⟩ := h
    omega

private lemma bmst_fixed_eq_zero (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (S : Set (GL N (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix N N (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmst_gram f Q) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 2)
    {w : N → GaloisField 2 f} (hw : Matrix.mulVec e w = w)
    (hfix : ∀ s ∈ S, (s : Matrix N N (GaloisField 2 f)).mulVec w = w) : w = 0 := by
  classical
  by_contra hw0
  let A : Subalgebra (GaloisField 2 f) (Matrix N N (GaloisField 2 f)) :=
    Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
  obtain ⟨K, hKfield, hKalg, hKfin, hKmod, hKtower, π, hπsurj, hπker, hπdeg, hact⟩ :=
    TableCRes.exists_blockModule (S := S) (e := e) hS hodd he
  letI : Field K := hKfield
  letI : Algebra (GaloisField 2 f) K := hKalg
  letI : Finite K := hKfin
  letI : Module K ↥(TableCRes.blockSpace e) := hKmod
  haveI : IsScalarTower (GaloisField 2 f) K ↥(TableCRes.blockSpace e) := hKtower
  haveI : FiniteDimensional (GaloisField 2 f) K := Module.Finite.of_finite
  have hwmem : w ∈ TableCRes.blockSpace e := by
    unfold TableCRes.blockSpace
    exact LinearMap.mem_range.mpr ⟨w, by rw [Matrix.mulVecLin_apply, hw]⟩
  let wK : ↥(TableCRes.blockSpace e) := ⟨w, hwmem⟩
  have hwK : wK ≠ 0 := by
    intro h
    exact hw0 (congrArg Subtype.val h)
  have hsmul : ∀ k : K, k ≠ 0 → k • wK ≠ 0 := fun k hk => smul_ne_zero hk hwK
  have hs_action : ∀ s (hs : s ∈ S),
      π (⟨(s : Matrix N N (GaloisField 2 f)),
        Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : A) = 1 := by
    intro s hs
    let a : A := ⟨(s : Matrix N N (GaloisField 2 f)),
      Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
    have ha_coe : (↑a : Matrix N N (GaloisField 2 f)) = (s : Matrix N N (GaloisField 2 f)) := rfl
    suffices h0 : (π a - 1) • wK = 0 by
      have hk : π a - 1 = 0 := by
        by_contra hne
        exact (hsmul (π a - 1) hne) h0
      exact sub_eq_zero.mp hk
    rw [sub_smul]
    have h3 : π a • wK = wK := by
      apply Subtype.ext
      rw [hact a wK]
      simpa [wK, ha_coe] using hfix s hs
    rw [h3, one_smul, sub_self]
  have hspan : Submodule.span (GaloisField 2 f) ({1} : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, rfl⟩ := hπsurj x
    have hmem : ∀ b : A, π b ∈ (⊥ : Subalgebra (GaloisField 2 f) K) := by
      intro b
      refine Algebra.adjoin_induction
        (p := fun z hz => π (⟨z, hz⟩ : A) ∈ (⊥ : Subalgebra (GaloisField 2 f) K))
        ?_ ?_ ?_ ?_ b.2
      · rintro z ⟨s, hs, rfl⟩
        have hz : π (⟨(s : Matrix N N (GaloisField 2 f)),
            Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : A) = 1 := hs_action s hs
        simpa only [hz] using Subalgebra.one_mem (⊥ : Subalgebra (GaloisField 2 f) K)
      · intro r
        have hzmem : (algebraMap (GaloisField 2 f) (Matrix N N (GaloisField 2 f))) r ∈ A :=
          Subalgebra.algebraMap_mem _ r
        have heq : (⟨(algebraMap (GaloisField 2 f) (Matrix N N (GaloisField 2 f))) r,
            hzmem⟩ : A) = algebraMap (GaloisField 2 f) A r := Subtype.ext rfl
        rw [heq, AlgHom.commutes]
        exact Subalgebra.algebraMap_mem (⊥ : Subalgebra (GaloisField 2 f) K) r
      · intro y z hy hz ihy ihz
        have hyz : y + z ∈ A := Subalgebra.add_mem _ hy hz
        have heq : (⟨y + z, hyz⟩ : A) = ⟨y, hy⟩ + ⟨z, hz⟩ := Subtype.ext rfl
        rw [heq, map_add]
        exact Subalgebra.add_mem _ ihy ihz
      · intro y z hy hz ihy ihz
        have hyz : y * z ∈ A := Subalgebra.mul_mem _ hy hz
        have heq : (⟨y * z, hyz⟩ : A) = ⟨y, hy⟩ * ⟨z, hz⟩ := Subtype.ext rfl
        rw [heq, map_mul]
        exact Subalgebra.mul_mem _ ihy ihz
    have hxbot := hmem a
    rw [Algebra.mem_bot] at hxbot
    obtain ⟨c, hc⟩ := hxbot
    rw [← hc, Algebra.algebraMap_eq_smul_one]
    exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
  have hfin : Module.finrank (GaloisField 2 f) K = 1 :=
    (finrank_eq_one_iff_of_nonzero (1 : K) one_ne_zero).mpr hspan
  have hdeg2 : Module.finrank (GaloisField 2 f) K = 2 := hπdeg.trans hdeg
  rw [hfin] at hdeg2
  omega

private lemma bmst_quad_preserved (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    (S : Set (GL N (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix N N (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmst_gram f Q) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 2)
    {u : GL N (GaloisField 2 f)}
    (hHmem : u ∈ H) (hcomm : ∀ s ∈ S, Commute u s)
    (hfix : (u : Matrix N N (GaloisField 2 f)) * (1 - e) = 1 - e) :
    ∀ v, Q ((u : Matrix N N (GaloisField 2 f)).mulVec v) = Q v := by
  classical
  have hGu : Matrix.transpose (u : Matrix N N (GaloisField 2 f)) * bmst_gram f Q *
      (u : Matrix N N (GaloisField 2 f)) = bmst_gram f Q := (hH u).mp hHmem
  have hB : ∀ x y, (u : Matrix N N (GaloisField 2 f)).mulVec x ⬝ᵥ
      (bmst_gram f Q).mulVec ((u : Matrix N N (GaloisField 2 f)).mulVec y) =
      x ⬝ᵥ (bmst_gram f Q).mulVec y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, hGu]
  have hpol : ∀ x y, QuadraticMap.polar Q ((u : Matrix N N (GaloisField 2 f)).mulVec x)
      ((u : Matrix N N (GaloisField 2 f)).mulVec y) = QuadraticMap.polar Q x y := by
    intro x y
    rw [bmst_polar_eq_dot f Q, bmst_polar_eq_dot f Q]
    exact hB x y
  let ν : (N → GaloisField 2 f) →+ GaloisField 2 f :=
    { toFun := fun x => Q ((u : Matrix N N (GaloisField 2 f)).mulVec x) - Q x
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [Matrix.mulVec_add,
          QuadraticMap.map_add (⇑Q) ((u : Matrix N N (GaloisField 2 f)).mulVec x)
            ((u : Matrix N N (GaloisField 2 f)).mulVec y),
          QuadraticMap.map_add (⇑Q) x y, hpol x y]
        abel }
  let Γ : Subgroup (GL N (GaloisField 2 f)) := Subgroup.closure S
  haveI : Finite ↥Γ := inferInstance
  letI : Fintype ↥Γ := Fintype.ofFinite ↥Γ
  have hΓcomm : ∀ x ∈ Γ, ∀ y ∈ Γ, Commute x y := by
    intro x hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · intro a ha y hy
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
      · intro b hb; exact hS a ha b hb
      · exact Commute.one_right a
      · intro b c hb hc ihb ihc; exact ihb.mul_right ihc
      · intro b hb ihb; exact ihb.inv_right
    · intro y hy; exact Commute.one_left y
    · intro a b ha hb iha ihb y hy
      exact (iha y hy).mul_left (ihb y hy)
    · intro a ha iha y hy
      exact (iha y hy).inv_left
  have hoddΓel : ∀ g ∈ Γ, Odd (orderOf g) := by
    intro g hg
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
    · intro s hs; exact hodd s hs
    · rw [orderOf_one]; exact odd_one
    · intro x y hx hy ihx ihy
      exact CFSG.GroupTheory.odd_orderOf_mul_of_commute (hΓcomm x hx y hy) ihx ihy
    · intro x hx ihx; rwa [orderOf_inv]
  have hoddΓ : Odd (Nat.card ↥Γ) :=
    CFSG.ComponentClassification.GrSLit.odd_card_of_forall_odd_orderOf hoddΓel
  have hodd_nsmul : ∀ n : ℕ, Odd n → ∀ a : GaloisField 2 f, n • a = a := by
    intro n hn a
    obtain ⟨k, hk⟩ := hn
    rw [hk, add_nsmul]
    have h2 : (2 * k) • a = 0 := by
      rw [mul_nsmul]
      have h3 : (2 : ℕ) • a = 0 := by
        rw [nsmul_eq_mul, CharP.cast_eq_zero (GaloisField 2 f) 2, zero_mul]
      rw [h3, nsmul_zero]
    rw [h2, zero_add, one_nsmul]
  set T : Matrix N N (GaloisField 2 f) :=
    ∑ g : ↥Γ, ((g : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) with hT
  have hTsum : ∀ x, T.mulVec x =
      ∑ g : ↥Γ, (((g : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f))).mulVec x := by
    intro x
    rw [hT]
    simpa using Matrix.sum_mulVec (Finset.univ : Finset ↥Γ)
      (fun g : ↥Γ => ((g : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f))) x
  have hsT : ∀ s ∈ S, (s : Matrix N N (GaloisField 2 f)) * T = T := by
    intro s hs
    let sΓ : ↥Γ := ⟨s, Subgroup.subset_closure hs⟩
    let ee : ↥Γ ≃ ↥Γ :=
      { toFun := fun g => sΓ * g
        invFun := fun g => sΓ⁻¹ * g
        left_inv := fun g => by simp
        right_inv := fun g => by simp }
    have hsum := Equiv.sum_comp ee
      (fun g : ↥Γ => ((g : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)))
    calc (s : Matrix N N (GaloisField 2 f)) * T
        = ∑ g : ↥Γ, (s : Matrix N N (GaloisField 2 f)) *
            ((g : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) := by
          rw [hT, Matrix.mul_sum]
      _ = ∑ g : ↥Γ, (((ee g : ↥Γ) : GL N (GaloisField 2 f)) :
            Matrix N N (GaloisField 2 f)) := by
          apply Finset.sum_congr rfl
          intro g _
          rfl
      _ = ∑ g : ↥Γ, ((g : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) := hsum
      _ = T := by rw [hT]
  have hgen_comm : ∀ g ∈ Γ, Commute (((g : GL N (GaloisField 2 f)) :
      Matrix N N (GaloisField 2 f))) e := by
    intro g hg
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
    · intro s hs
      exact bmst_adjoin_comm hS (s : Matrix N N (GaloisField 2 f))
        (Algebra.subset_adjoin ⟨s, hs, rfl⟩) e he.1
    · exact Commute.one_left e
    · intro x y hx hy ihx ihy; exact ihx.mul_left ihy
    · intro x hx ihx
      have hx1 : ((x⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) *
          ((x : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hx2 : ((x : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) *
          ((x⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      show ((x⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) * e =
        e * ((x⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f))
      calc ((x⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) * e
          = ((x⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) *
              (e * ((x : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f))) *
              ((x⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) := by
            rw [mul_assoc, mul_assoc, hx2, mul_one]
          _ = ((x⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) *
              (((x : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) * e) *
              ((x⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) := by
            rw [← ihx.eq]
          _ = e * ((x⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) := by
            rw [← mul_assoc, hx1, one_mul]
  have hTe : e * T = T * e := by
    rw [hT, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro g _
    exact (hgen_comm g g.2).eq.symm
  have hνinv : ∀ g ∈ Γ, ∀ x, ν ((((g : GL N (GaloisField 2 f)) :
      Matrix N N (GaloisField 2 f))).mulVec x) = ν x := by
    intro g hg
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
    · intro s hs x
      have hsiso : ∀ v, Q (((s : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec v)
          = Q v := by
        obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (hSU s hs)
        rw [← hy]
        exact Spin.spinMatrix_mem Q y
      have hus : ((u : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) *
          ((s : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) =
          ((s : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) *
          ((u : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) := by
        simpa only [Units.val_mul] using
          congrArg (fun z : GL N (GaloisField 2 f) => (z : Matrix N N (GaloisField 2 f)))
            (hcomm s hs).eq
      show Q (((u : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec
          (((s : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec x)) -
          Q (((s : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec x) =
          Q (((u : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec x) - Q x
      rw [Matrix.mulVec_mulVec, hus, ← Matrix.mulVec_mulVec,
        hsiso (((u : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec x),
        hsiso x]
    · intro x
      show Q (((u : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec
          ((1 : Matrix N N (GaloisField 2 f)).mulVec x)) -
          Q ((1 : Matrix N N (GaloisField 2 f)).mulVec x) =
          Q (((u : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec x) - Q x
      rw [Matrix.one_mulVec]
    · intro a b ha hb iha ihb x
      rw [show ν ((((a * b : GL N (GaloisField 2 f))) : Matrix N N (GaloisField 2 f)).mulVec x) =
          ν (((a : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec
            (((b : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec x)) from by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]]
      rw [iha (((b : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec x), ihb x]
    · intro a ha iha x
      have h := iha (((a⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec x)
      rw [Matrix.mulVec_mulVec, show ((a : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) *
          ((a⁻¹ : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)) = 1 from by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one], Matrix.one_mulVec] at h
      exact h.symm
  have hνzeroW : ∀ x, e.mulVec x = x → ν x = 0 := by
    intro x hx
    have hTx0 : T.mulVec x = 0 := by
      apply bmst_fixed_eq_zero f Q S hSU hS hodd he hadj hdeg
      · show e.mulVec (T.mulVec x) = T.mulVec x
        rw [Matrix.mulVec_mulVec, hTe, ← Matrix.mulVec_mulVec, hx]
      · intro s hs
        show ((s : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec (T.mulVec x) =
          T.mulVec x
        rw [Matrix.mulVec_mulVec, hsT s hs]
    have h1 : ν (T.mulVec x) = ν x := by
      rw [hTsum, map_sum]
      rw [Finset.sum_congr rfl (fun g _ => hνinv g.1 g.2 x)]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hodd_nsmul (Nat.card ↥Γ) hoddΓ (ν x)
    rw [hTx0, map_zero] at h1
    exact h1.symm
  intro v
  have hv : v = e.mulVec v + (1 - e).mulVec v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have h1 : ν (e.mulVec v) = 0 :=
    hνzeroW (e.mulVec v) (by rw [Matrix.mulVec_mulVec, he.2.1.eq])
  have h2 : ν ((1 - e).mulVec v) = 0 := by
    show Q (((u : GL N (GaloisField 2 f)) : Matrix N N (GaloisField 2 f)).mulVec
      ((1 - e).mulVec v)) - Q ((1 - e).mulVec v) = 0
    rw [Matrix.mulVec_mulVec, hfix, sub_self]
  have hνv : ν v = 0 := by
    rw [hv, map_add, h1, h2, add_zero]
  exact sub_eq_zero.mp hνv

private lemma bmst_dickson_even (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (S : Set (GL N (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix N N (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmst_gram f Q) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 2)
    {u : GL N (GaloisField 2 f)}
    (hcomm : ∀ s ∈ S, Commute u s)
    (hfix : (u : Matrix N N (GaloisField 2 f)) * (1 - e) = 1 - e) :
    Even (Module.finrank (GaloisField 2 f) ↥(LinearMap.range
      ((u : Matrix N N (GaloisField 2 f)) - 1).mulVecLin)) := by
  have hgS : u ∈ Subgroup.centralizer S :=
    Subgroup.mem_centralizer_iff.mpr fun s hs => (hcomm s hs).eq.symm
  have hge : u ∈ glFixing (1 - e) := hfix
  have h := blockDegree_dvd_rank_sub_one_of_glFixing hS hodd he hgS hge
  rw [hdeg,
    Matrix.rank_eq_finrank_range_toLin ((u : Matrix N N (GaloisField 2 f)) - 1)
      (Pi.basisFun (GaloisField 2 f) N) (Pi.basisFun (GaloisField 2 f) N)] at h
  exact even_iff_two_dvd.mpr h

private lemma bmst_toLin_apply (N : Type) [Fintype N] [DecidableEq N]
    (F : Type) [Field F] (A : GL N F) (v : N → F) :
    (bmst_toLin N F A) v = (A : Matrix N N F).mulVec v :=
  CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply A v

private lemma bmst_commSpace_toLin (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (A : GL N (GaloisField 2 f)) :
    CFSG.RankThree.OrthogonalInvolutions.commSpace (bmst_toLin N (GaloisField 2 f) A) =
      LinearMap.range ((A : Matrix N N (GaloisField 2 f)) - 1).mulVecLin := by
  unfold CFSG.RankThree.OrthogonalInvolutions.commSpace
  congr 1
  apply LinearMap.ext
  intro v
  simp [bmst_toLin_apply, Matrix.sub_mulVec]

private lemma bmst_block_mem_range (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hΩ : (Spin.spinAction Q).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd)
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    (S : Set (GL N (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix N N (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmst_gram f Q) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {u : GL N (GaloisField 2 f)}
    (hHmem : u ∈ H) (hcomm : ∀ s ∈ S, Commute u s)
    (hfix : (u : Matrix N N (GaloisField 2 f)) * (1 - e) = 1 - e) :
    u ∈ (Spin.spinMatrix Q).range := by
  have hdeg := bmst_blockDegree_eq_two f Q hnd S hSU hS hodd he hadj hdeg₁ hdeg₂
  have hquad := bmst_quad_preserved f Q H hH S hSU hS hodd he hadj hdeg hHmem hcomm hfix
  have hdick := bmst_dickson_even f Q S hSU hS hodd he hadj hdeg hcomm hfix
  have hmem : (bmst_toLin N (GaloisField 2 f)) u ∈
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd := by
    rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup]
    refine ⟨?_, ?_⟩
    · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      rw [bmst_toLin_apply]
      exact hquad v
    · rw [bmst_commSpace_toLin]
      exact hdick
  rw [← hΩ] at hmem
  obtain ⟨h, hh⟩ := hmem
  refine ⟨h, ?_⟩
  apply (bmst_toLin N (GaloisField 2 f)).injective
  calc bmst_toLin N (GaloisField 2 f) (Spin.spinMatrix Q h)
      = Spin.spinAction Q h := Spin.toLinEquiv_spinMatrix Q h
    _ = bmst_toLin N (GaloisField 2 f) u := hh

private lemma bmst_blockCentralizer_map_eq (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hΩ : (Spin.spinAction Q).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd)
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    (S : Set (GL N (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix N N (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmst_gram f Q) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4) :
    (glBlockCentralizer (Spin.spinMatrix Q) S e).map (bmst_spToSp f Q H hH) =
      glBlockCentralizer H.subtype S e := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [glBlockCentralizer, Subgroup.mem_comap] at hy ⊢
    change ((bmst_spToSp f Q H hH y : ↥H) : GL N (GaloisField 2 f)) ∈
      Subgroup.centralizer S ⊓ glFixing (1 - e)
    rw [bmst_spToSp_coe]
    exact hy
  · intro u hu
    rw [glBlockCentralizer, Subgroup.mem_comap] at hu
    obtain ⟨hcent, hfix⟩ := hu
    have hcomm : ∀ s ∈ S, Commute (H.subtype u) s := by
      intro s hs
      exact ((Subgroup.mem_centralizer_iff.mp hcent) s hs).symm
    obtain ⟨y, hy⟩ := bmst_block_mem_range f Q hnd hΩ H hH S hSU hS hodd he hadj
      hdeg₁ hdeg₂ u.2 hcomm hfix
    refine Subgroup.mem_map.mpr ⟨y, ?_, ?_⟩
    · rw [glBlockCentralizer, Subgroup.mem_comap]
      exact ⟨by rw [hy]; exact hcent, by rw [hy]; exact hfix⟩
    · exact Subtype.ext (by rw [bmst_spToSp_coe]; exact hy)

private lemma bmst_component_transport (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hinj : Function.Injective (Spin.spinMatrix Q))
    (hΩ : (Spin.spinAction Q).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd)
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    (S : Set (GL N (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix N N (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmst_gram f Q) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(spinGroup Q)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix Q) S e,
        glBlockCentralizer (Spin.spinMatrix Q) S e⁆) :
    IsComponentOf (J'.map (bmst_spToSp f Q H hH))
      ⁅glBlockCentralizer H.subtype S e, glBlockCentralizer H.subtype S e⁆ := by
  have h := isComponentOf_map_of_injective (bmst_spToSp f Q H hH)
    (bmst_spToSp_injective f Q H hH hinj) hJe
  rw [Subgroup.map_commutator, bmst_blockCentralizer_map_eq f Q hnd hΩ H hH S hSU hS hodd
    he hadj hdeg₁ hdeg₂] at h
  exact h

private lemma bmst_altGen_mulVec (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (c : GaloisField 2 f) (v w x : N → GaloisField 2 f) :
    (1 + c • (Matrix.vecMulVec v ((bmst_gram f Q).mulVec w) +
      Matrix.vecMulVec w ((bmst_gram f Q).mulVec v))).mulVec x =
      x + c • ((x ⬝ᵥ (bmst_gram f Q).mulVec w) • v +
        (x ⬝ᵥ (bmst_gram f Q).mulVec v) • w) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  have hop : ∀ (a : GaloisField 2 f) (u : N → GaloisField 2 f),
      MulOpposite.op a • u = a • u := fun a u => by funext i; simp [op_smul_eq_mul, mul_comm]
  rw [hop, hop, dotProduct_comm ((bmst_gram f Q).mulVec w) x,
    dotProduct_comm ((bmst_gram f Q).mulVec v) x]

private lemma bmst_altMatrix_mul_self (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    {v w : N → GaloisField 2 f}
    (hvw : v ⬝ᵥ (bmst_gram f Q).mulVec w = 0) :
    (Matrix.vecMulVec v ((bmst_gram f Q).mulVec w) +
        Matrix.vecMulVec w ((bmst_gram f Q).mulVec v)) *
      (Matrix.vecMulVec v ((bmst_gram f Q).mulVec w) +
        Matrix.vecMulVec w ((bmst_gram f Q).mulVec v)) = 0 := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
  rw [dotProduct_comm ((bmst_gram f Q).mulVec w) v, hvw,
    dotProduct_comm ((bmst_gram f Q).mulVec w) w, bmst_dot_self f Q,
    dotProduct_comm ((bmst_gram f Q).mulVec v) v, bmst_dot_self f Q,
    dotProduct_comm ((bmst_gram f Q).mulVec v) w]
  rw [bmst_dot_comm f Q w v, hvw]
  simp

private lemma bmst_altGen_isometry (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    {v w : N → GaloisField 2 f}
    (hvw : v ⬝ᵥ (bmst_gram f Q).mulVec w = 0)
    (hle : altSiegelGroup (bmst_gram f Q) v w ≤ (Spin.spinMatrix Q).range)
    (c : GaloisField 2 f) (x : N → GaloisField 2 f) :
    Q ((1 + c • (Matrix.vecMulVec v ((bmst_gram f Q).mulVec w) +
        Matrix.vecMulVec w ((bmst_gram f Q).mulVec v))).mulVec x) = Q x := by
  let A : Matrix N N (GaloisField 2 f) :=
    Matrix.vecMulVec v ((bmst_gram f Q).mulVec w) +
      Matrix.vecMulVec w ((bmst_gram f Q).mulVec v)
  have hAA : A * A = 0 := bmst_altMatrix_mul_self f Q hvw
  let M : Matrix N N (GaloisField 2 f) := 1 + c • A
  have hMM : M * M = 1 := by
    have hM : M = 1 + c • A := rfl
    have hmul : (c • A) * (c • A) = 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hAA]
      simp
    rw [hM, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      hmul, add_zero]
    rw [add_assoc, Matrix.one_mul, ← add_smul]
    have hc2 : c + c = 0 := by
      calc c + c = (2 : GaloisField 2 f) * c := (two_mul c).symm
        _ = 0 := by simp [CharTwo.two_eq_zero]
    rw [hc2, zero_smul, add_zero]
  let g : GL N (GaloisField 2 f) := Units.mkOfMulEqOne M M hMM
  have hg : g ∈ altSiegelGroup (bmst_gram f Q) v w :=
    Subgroup.subset_closure ⟨c, by rw [Units.val_mkOfMulEqOne]⟩
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (hle hg)
  have hyM : (Spin.spinMatrix Q y : Matrix N N (GaloisField 2 f)) = M := by
    rw [hy, Units.val_mkOfMulEqOne]
  have h := Spin.spinMatrix_mem Q y x
  rwa [hyM] at h

private lemma bmst_singular_of_altSiegel (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    {a₁ a₂ b₁ b₂ : N → GaloisField 2 f}
    (hB₁ : a₁ ⬝ᵥ (bmst_gram f Q).mulVec b₁ = 1)
    (hB₂ : a₂ ⬝ᵥ (bmst_gram f Q).mulVec b₂ = 1)
    (haa : a₁ ⬝ᵥ (bmst_gram f Q).mulVec a₂ = 0)
    (hbb : b₁ ⬝ᵥ (bmst_gram f Q).mulVec b₂ = 0)
    (hab : a₁ ⬝ᵥ (bmst_gram f Q).mulVec b₂ = 0)
    (hba : a₂ ⬝ᵥ (bmst_gram f Q).mulVec b₁ = 0)
    (hle₁ : altSiegelGroup (bmst_gram f Q) a₁ a₂ ≤ (Spin.spinMatrix Q).range)
    (hle₂ : altSiegelGroup (bmst_gram f Q) b₁ b₂ ≤ (Spin.spinMatrix Q).range) :
    Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0 := by
  have key : ∀ (v w x₁ x₂ : N → GaloisField 2 f),
      altSiegelGroup (bmst_gram f Q) v w ≤ (Spin.spinMatrix Q).range →
      v ⬝ᵥ (bmst_gram f Q).mulVec w = 0 →
      x₁ ⬝ᵥ (bmst_gram f Q).mulVec w = 1 →
      x₁ ⬝ᵥ (bmst_gram f Q).mulVec v = 0 →
      x₂ ⬝ᵥ (bmst_gram f Q).mulVec w = 0 →
      x₂ ⬝ᵥ (bmst_gram f Q).mulVec v = 1 →
      Q v = 0 ∧ Q w = 0 := by
    intro v w x₁ x₂ hle hvw h₁w h₁v h₂w h₂v
    have hv0 : Q v = 0 := by
      have h := bmst_altGen_isometry f Q hvw hle 1 x₁
      rw [bmst_altGen_mulVec f Q, h₁w, h₁v] at h
      simp only [one_smul, zero_smul, add_zero, zero_add, smul_zero] at h
      have hp : QuadraticMap.polar Q x₁ v = 0 := by
        rw [bmst_polar_eq_dot f Q, h₁v]
      have h2 := QuadraticMap.map_add (⇑Q) x₁ v
      rw [h2, hp, add_zero] at h
      exact add_left_cancel (by rw [add_zero]; exact h)
    have hw0 : Q w = 0 := by
      have h := bmst_altGen_isometry f Q hvw hle 1 x₂
      rw [bmst_altGen_mulVec f Q, h₂w, h₂v] at h
      simp only [one_smul, zero_smul, add_zero, zero_add, smul_zero] at h
      have hp : QuadraticMap.polar Q x₂ w = 0 := by
        rw [bmst_polar_eq_dot f Q, h₂w]
      have h2 := QuadraticMap.map_add (⇑Q) x₂ w
      rw [h2, hp, add_zero] at h
      exact add_left_cancel (by rw [add_zero]; exact h)
    exact ⟨hv0, hw0⟩
  obtain ⟨ha₁, ha₂⟩ := key a₁ a₂ b₂ b₁ hle₁ haa
    (by rw [bmst_dot_comm f Q b₂ a₂]; exact hB₂)
    (by rw [bmst_dot_comm f Q b₂ a₁]; exact hab)
    (by rw [bmst_dot_comm f Q b₁ a₂]; exact hba)
    (by rw [bmst_dot_comm f Q b₁ a₁]; exact hB₁)
  obtain ⟨hb₁, hb₂⟩ := key b₁ b₂ a₂ a₁ hle₂ hbb hB₂ hba hab hB₁
  exact ⟨ha₁, ha₂, hb₁, hb₂⟩

private lemma bmst_altGen_apply (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (c : GaloisField 2 f) {v w : N → GaloisField 2 f}
    (hv : Q v = 0) (hw : Q w = 0)
    (hpol : QuadraticMap.polar Q v w = 0) (x : N → GaloisField 2 f) :
    (1 + c • (Matrix.vecMulVec v ((bmst_gram f Q).mulVec w) +
      Matrix.vecMulVec w ((bmst_gram f Q).mulVec v))).mulVec x =
      CFSG.ClassicalGroups.Orthogonal.eichler Q v (c • w) x := by
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hv
    (by rw [QuadraticMap.polar_smul_right, hpol, smul_zero]) x]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  have hop : ∀ (a : GaloisField 2 f) (u : N → GaloisField 2 f),
      MulOpposite.op a • u = a • u := fun a u => by funext i; simp [op_smul_eq_mul, mul_comm]
  rw [hop, hop, QuadraticMap.polar_smul_right, QuadraticMap.map_smul, hw, bmst_polar_eq_dot f Q,
    bmst_polar_eq_dot f Q]
  simp only [dotProduct_comm, smul_add, smul_smul, smul_zero, zero_mul, mul_zero, add_zero]
  rw [sub_eq_add_neg]
  have hneg : ∀ u : N → GaloisField 2 f, -u = u := fun u => by
    funext i; exact CharTwo.neg_eq (u i)
  rw [hneg]
  module

private lemma bmst_altSiegel_eq_siegel (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    {v w : N → GaloisField 2 f}
    (hv : Q v = 0) (hw : Q w = 0)
    (hpol : QuadraticMap.polar Q v w = 0) :
    (altSiegelGroup (bmst_gram f Q) v w).map (bmst_toLin N (GaloisField 2 f)).toMonoidHom =
      siegelGroup Q v w := by
  rw [altSiegelGroup, MonoidHom.map_closure, siegelGroup]
  congr 1
  ext y
  constructor
  · rintro ⟨g, ⟨c, hc⟩, rfl⟩
    refine ⟨c, ?_⟩
    apply LinearEquiv.ext
    intro x
    change (bmst_toLin N (GaloisField 2 f) g) x = _
    rw [bmst_toLin_apply, hc]
    exact bmst_altGen_apply f Q c hv hw hpol x
  · rintro ⟨c, rfl⟩
    refine ⟨(bmst_toLin N (GaloisField 2 f)).symm
      (CFSG.ClassicalGroups.Orthogonal.eichler Q v (c • w)), ⟨c, ?_⟩, ?_⟩
    · apply Matrix.toLin'.injective
      rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
      apply LinearMap.ext
      intro x
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, ← bmst_toLin_apply,
        MulEquiv.apply_symm_apply]
      exact (bmst_altGen_apply f Q c hv hw hpol x).symm
    · exact MulEquiv.apply_symm_apply (bmst_toLin N (GaloisField 2 f)) _

private lemma bmst_exists_lift
    (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    (hinj : Function.Injective (Spin.spinMatrix Q))
    {t' : StatedLieTag} {m g' : ℕ}
    {ι₀ : (ggU t' m g').K →* ↥H}
    (hle : ι₀.range ≤ (bmst_spToSp f Q H hH).range) :
    ∃ ι : (ggU t' m g').K →* ↥(spinGroup Q),
      ∀ y, bmst_spToSp f Q H hH (ι y) = ι₀ y := by
  classical
  let g : (ggU t' m g').K → ↥(spinGroup Q) := fun y =>
    (MonoidHom.mem_range.mp (hle (MonoidHom.mem_range.mpr ⟨y, rfl⟩))).choose
  have hg : ∀ y, bmst_spToSp f Q H hH (g y) = ι₀ y := fun y =>
    (MonoidHom.mem_range.mp (hle (MonoidHom.mem_range.mpr ⟨y, rfl⟩))).choose_spec
  refine ⟨{ toFun := g
            map_one' := (bmst_spToSp_injective f Q H hH hinj) (by rw [hg 1, map_one, map_one])
            map_mul' := fun x y => (bmst_spToSp_injective f Q H hH hinj) (by
              simp only [hg, map_mul]) }, hg⟩

private lemma bmst_transfer
    (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    (hinj : Function.Injective (Spin.spinMatrix Q))
    (hcent : Subgroup.center ↥(spinGroup Q) = ⊥)
    {t' : StatedLieTag} {m g' : ℕ} {J' : Subgroup ↥(spinGroup Q)}
    {ι₀ : (ggU t' m g').K →* ↥H}
    (hrange : ι₀.range = J'.map (bmst_spToSp f Q H hH))
    (hcent₀ : ∀ y, ι₀ y ∈ Subgroup.center ↥H → y ∈ Subgroup.center (ggU t' m g').K) :
    ∃ ι : (ggU t' m g').K →* ↥(spinGroup Q),
      (∀ y, bmst_spToSp f Q H hH (ι y) = ι₀ y) ∧ ι.range = J' ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup Q) → y ∈ Subgroup.center (ggU t' m g').K) := by
  have hle : ι₀.range ≤ (bmst_spToSp f Q H hH).range := by
    rw [hrange]
    exact Subgroup.map_le_range (bmst_spToSp f Q H hH) J'
  obtain ⟨ι, hι⟩ := bmst_exists_lift f Q H hH hinj hle
  refine ⟨ι, hι, ?_, ?_⟩
  · apply le_antisymm
    · rintro x ⟨y, rfl⟩
      have hmem : bmst_spToSp f Q H hH (ι y) ∈ J'.map (bmst_spToSp f Q H hH) := by
        rw [hι y, ← hrange]
        exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
      obtain ⟨j, hj, hjeq⟩ := hmem
      rwa [← bmst_spToSp_injective f Q H hH hinj hjeq]
    · intro j hj
      have hmem : bmst_spToSp f Q H hH j ∈ J'.map (bmst_spToSp f Q H hH) :=
        Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
      rw [← hrange] at hmem
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
      exact ⟨y, bmst_spToSp_injective f Q H hH hinj (by rw [hι y, hy])⟩
  · intro y hy
    have hy1 : ι y = 1 := by
      have h := hy
      rw [hcent, Subgroup.mem_bot] at h
      exact h
    apply hcent₀
    rw [← hι y, hy1, map_one]
    exact Subgroup.one_mem _

private lemma bmst_map_spinAction
    (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    {t' : StatedLieTag} {m g' : ℕ}
    (ι₀ : (ggU t' m g').K →* ↥H)
    (ι : (ggU t' m g').K →* ↥(spinGroup Q))
    (hι : ∀ y, bmst_spToSp f Q H hH (ι y) = ι₀ y)
    (X : Subgroup (ggU t' m g').K) :
    (X.map ι).map (Spin.spinAction Q) =
      ((X.map ι₀).map H.subtype).map
        (bmst_toLin N (GaloisField 2 f)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hz
    have h1 : (H.subtype (ι₀ y) : GL N (GaloisField 2 f)) = Spin.spinMatrix Q (ι y) := by
      rw [← hι y]
      rfl
    refine ⟨(H.subtype (ι₀ y) : GL N (GaloisField 2 f)), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨ι₀ y, Subgroup.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩
    · rw [h1]
      exact Spin.toLinEquiv_spinMatrix Q (ι y)
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨y, hy, rfl⟩ := hw
    have h1 : (H.subtype (ι₀ y) : GL N (GaloisField 2 f)) = Spin.spinMatrix Q (ι y) := by
      rw [← hι y]
      rfl
    refine ⟨ι y, Subgroup.mem_map.mpr ⟨y, hy, rfl⟩, ?_⟩
    rw [h1]
    exact (Spin.toLinEquiv_spinMatrix Q (ι y)).symm

private lemma bmst_map_map_spinAction (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (H : Subgroup (GL N (GaloisField 2 f))) (hH : bmst_memH f Q H)
    (H' : Subgroup ↥(spinGroup Q)) :
    ((H'.map (bmst_spToSp f Q H hH)).map H.subtype).map
        (bmst_toLin N (GaloisField 2 f)).toMonoidHom =
      H'.map (Spin.spinAction Q) := by
  have hcomp : (bmst_toLin N (GaloisField 2 f)).toMonoidHom.comp
      (H.subtype.comp (bmst_spToSp f Q H hH)) = Spin.spinAction Q := by
    apply MonoidHom.ext
    intro y
    simp only [MonoidHom.comp_apply]
    rw [Subgroup.subtype_apply, bmst_spToSp_coe]
    exact Spin.toLinEquiv_spinMatrix Q y
  rw [Subgroup.map_map, Subgroup.map_map, MonoidHom.comp_assoc, hcomp]

@[expose]
def BMSTPSpModel
    (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (G : Matrix N N (GaloisField 2 f)) (H : Subgroup (GL N (GaloisField 2 f))) : Prop :=
  ∀ (S : Set (GL (N) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ H)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (N) (N) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      G e =
      e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(H)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (H.subtype) S (e),
      glBlockCentralizer (H.subtype) S (e)⁆),
    ∃ (t' : StatedLieTag) (m g' : ℕ)
      (ι : (ggU t' m g').K →* ↥(H))
      (β₀ : Fin (ggU t' m g').D.rank → ℤ), GGPosTag t' ∧ 1 ≤ g' ∧ GGLongRoot (ggU t' m g').D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(H) → y ∈ Subgroup.center
        (ggU t' m g').K) ∧ ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : (N) → (GaloisField 2 f),
        a₁ ⬝ᵥ Matrix.mulVec
          G
          b₁ = 1 ∧ a₂ ⬝ᵥ Matrix.mulVec
          G
          b₂ = 1 ∧
        (a₁ ⬝ᵥ Matrix.mulVec
          G
          a₂ = 0 ∧ b₁ ⬝ᵥ Matrix.mulVec
          G
          b₂ = 0 ∧
          a₁ ⬝ᵥ Matrix.mulVec
            G b₂ = 0 ∧ a₂ ⬝ᵥ Matrix.mulVec
            G b₁ = 0) ∧
        (((ggU t' m g').D.rootGroup β₀).map ι).map
        (H.subtype) = altSiegelGroup
        G a₁
        a₂ ∧
        (((ggU t' m g').D.rootGroup (-β₀)).map ι).map
        (H.subtype) = altSiegelGroup
        G b₁
        b₂

@[expose]
def BMSTPSpModelExplicit
    (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (G : Matrix N N (GaloisField 2 f)) (H : Subgroup (GL N (GaloisField 2 f))) : Prop :=
  ∀ (S : Set (GL (N) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ H)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (N) (N) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      G e =
      e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(H)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (H.subtype) S (e),
      glBlockCentralizer (H.subtype) S (e)⁆),
    ∃ (r : ℕ)
      (ι : (ggU .PSU r (max f 1)).K →* ↥(H))
      (β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ),
      2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) ∧
      GGLongRoot (ggU .PSU r (max f 1)).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(H) → y ∈ Subgroup.center
        (ggU .PSU r (max f 1)).K) ∧ ι.range = J' ∧
      (Function.Injective ι ∧ 2 ≤ r ∧ (2 ^ max f 1 ≠ 2 ∨ 4 ≤ r)) ∧
      ∃ a₁ a₂ b₁ b₂ : (N) → (GaloisField 2 f),
        a₁ ⬝ᵥ Matrix.mulVec
          G
          b₁ = 1 ∧ a₂ ⬝ᵥ Matrix.mulVec
          G
          b₂ = 1 ∧
        (a₁ ⬝ᵥ Matrix.mulVec
          G
          a₂ = 0 ∧ b₁ ⬝ᵥ Matrix.mulVec
          G
          b₂ = 0 ∧
          a₁ ⬝ᵥ Matrix.mulVec
            G b₂ = 0 ∧ a₂ ⬝ᵥ Matrix.mulVec
            G b₁ = 0) ∧
        (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map
        (H.subtype) = altSiegelGroup
        G a₁
        a₂ ∧
        (((ggU .PSU r (max f 1)).D.rootGroup (-β₀)).map ι).map
        (H.subtype) = altSiegelGroup
        G b₁
        b₂

@[expose]
def BMSTPSpClosureExplicit
    (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (G : Matrix N N (GaloisField 2 f)) (H : Subgroup (GL N (GaloisField 2 f))) : Prop :=
  ∀ (S : Set (GL (N) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ H)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (N) (N) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      G e =
      e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(H)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (H.subtype) S (e),
      glBlockCentralizer (H.subtype) S (e)⁆),
    ∃ (r : ℕ) (ι : (ggU .PSU r (max f 1)).K →* ↥(H)),
      2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) ∧
      (∀ y, ι y ∈ Subgroup.center ↥(H) → y ∈ Subgroup.center
          (ggU .PSU r (max f 1)).K) ∧
      ι.range = J' ∧
      (∀ a₁ a₂ : (N) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 → LinearIndependent
          (GaloisField 2 f) ![a₁, a₂] → a₁ ⬝ᵥ Matrix.mulVec G a₂ = 0 → altSiegelGroup
          G
          a₁ a₂ ≤ J'.map H.subtype →
        ∃ (β : Fin (ggU .PSU r (max f 1)).D.rank → ℤ) (u : (ggU .PSU r (max f 1)).K),
            β ∈ (ggU .PSU r (max f 1)).D.roots ∧
            GGLongRoot (ggU .PSU r (max f 1)).D β ∧
          ((((ggU .PSU r (max f 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
              H.subtype = altSiegelGroup G a₁ a₂)

theorem bmst_model_of_psp_explicit_inj
    (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hinj : Function.Injective (Spin.spinMatrix Q))
    (hΩ : (Spin.spinAction Q).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd)
    (hcent : Subgroup.center ↥(spinGroup Q) = ⊥)
    (H : Subgroup (GL N (GaloisField 2 f)))
    (hH : ∀ A : GL N (GaloisField 2 f), A ∈ H ↔
      Matrix.transpose (A : Matrix N N (GaloisField 2 f)) *
        LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q) * (A : Matrix N N
            (GaloisField 2 f)) =
        LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q))
    (psp : BMSTPSpModelExplicit f
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)) H)
    (S : Set (GL N (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (N) (N) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin Q)) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(spinGroup Q)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix Q) S (e),
      glBlockCentralizer (Spin.spinMatrix Q) S (e)⁆) :
    ∃ (r : ℕ)
      (ι : (ggU .PSU r (max f 1)).K →* ↥(spinGroup Q))
      (β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ),
      2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) ∧
      GGLongRoot (ggU .PSU r (max f 1)).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup Q) → y ∈
        Subgroup.center (ggU .PSU r (max f 1)).K) ∧ ι.range = J' ∧
      (Function.Injective ι ∧ 2 ≤ r ∧ (2 ^ max f 1 ≠ 2 ∨ 4 ≤ r)) ∧
      ∃ a₁ a₂ b₁ b₂ : (N) → (GaloisField 2 f),
        (Q a₁ = 0 ∧
          Q a₂ = 0 ∧
          Q b₁ = 0 ∧
          Q b₂ = 0) ∧
        QuadraticMap.polar Q a₁ b₁ = 1 ∧ QuadraticMap.polar
          Q a₂ b₂ = 1 ∧
        (QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar
          Q b₁ b₂ = 0 ∧
          QuadraticMap.polar Q a₁ b₂ = 0 ∧
            QuadraticMap.polar Q a₂ b₁ = 0) ∧
        (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map
        (Spin.spinAction Q) = siegelGroup
        Q a₁ a₂ ∧
        (((ggU .PSU r (max f 1)).D.rootGroup (-β₀)).map ι).map
        (Spin.spinAction Q) = siegelGroup
        Q b₁ b₂ := by
  have hSUH : ∀ s ∈ S, s ∈ H := by
    intro s hs
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hSU s hs)
    exact bmst_spinMatrix_mem_H f Q H hH x
  have hJeSp : IsComponentOf (J'.map (bmst_spToSp f Q H hH))
      ⁅glBlockCentralizer H.subtype S e, glBlockCentralizer H.subtype S e⁆ :=
    bmst_component_transport f Q hnd hinj hΩ H hH S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  obtain ⟨r, ι₀, β₀, hrank, hlong, hcent₀, hrange₀, ⟨hinj₀, hr2, hnq⟩, a₁, a₂, b₁, b₂,
    hB₁, hB₂, horth, hX, hX'⟩ :=
    psp S hSUH hS hodd he hadj hdeg₁ hdeg₂ hJeSp
  obtain ⟨haa, hbb, hab, hba⟩ := horth
  obtain ⟨ι, hι, hrange, hcent⟩ :=
    bmst_transfer f Q H hH hinj hcent hrange₀ hcent₀
  have hinjι : Function.Injective ι := fun y y' h => hinj₀ (by rw [← hι, ← hι, h])
  have hle₁ : altSiegelGroup (bmst_gram f Q) a₁ a₂ ≤ (Spin.spinMatrix Q).range := by
    rw [← hX]
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨y, _, rfl⟩ := hz
    exact ⟨ι y, by rw [← bmst_spToSp_coe f Q H hH, hι y]; rfl⟩
  have hle₂ : altSiegelGroup (bmst_gram f Q) b₁ b₂ ≤ (Spin.spinMatrix Q).range := by
    rw [← hX']
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨y, _, rfl⟩ := hz
    exact ⟨ι y, by rw [← bmst_spToSp_coe f Q H hH, hι y]; rfl⟩
  have hQframe := bmst_singular_of_altSiegel f Q hB₁ hB₂ haa hbb hab hba hle₁ hle₂
  have hB₁' : QuadraticMap.polar Q a₁ b₁ = 1 := by
    rw [bmst_polar_eq_dot]; exact hB₁
  have hB₂' : QuadraticMap.polar Q a₂ b₂ = 1 := by
    rw [bmst_polar_eq_dot]; exact hB₂
  have hOrth : QuadraticMap.polar Q a₁ a₂ = 0 ∧
      QuadraticMap.polar Q b₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₂ b₁ = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [bmst_polar_eq_dot] <;> assumption
  have hX₁ : (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map
      (Spin.spinAction Q) = siegelGroup Q a₁ a₂ := by
    rw [bmst_map_spinAction f Q H hH ι₀ ι hι ((ggU .PSU r (max f 1)).D.rootGroup β₀), hX,
      bmst_altSiegel_eq_siegel f Q hQframe.1 hQframe.2.1 hOrth.1]
  have hX₂ : (((ggU .PSU r (max f 1)).D.rootGroup (-β₀)).map ι).map
      (Spin.spinAction Q) = siegelGroup Q b₁ b₂ := by
    rw [bmst_map_spinAction f Q H hH ι₀ ι hι ((ggU .PSU r (max f 1)).D.rootGroup (-β₀)), hX',
      bmst_altSiegel_eq_siegel f Q hQframe.2.2.1 hQframe.2.2.2 hOrth.2.1]
  exact ⟨r, ι, β₀, hrank, hlong, hcent, hrange, ⟨hinjι, hr2, hnq⟩, a₁, a₂, b₁, b₂,
    hQframe, hB₁', hB₂', hOrth, hX₁, hX₂⟩

theorem bmst_model_of_psp_explicit
    (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hinj : Function.Injective (Spin.spinMatrix Q))
    (hΩ : (Spin.spinAction Q).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd)
    (hcent : Subgroup.center ↥(spinGroup Q) = ⊥)
    (H : Subgroup (GL N (GaloisField 2 f)))
    (hH : ∀ A : GL N (GaloisField 2 f), A ∈ H ↔
      Matrix.transpose (A : Matrix N N (GaloisField 2 f)) *
        LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q) * (A : Matrix N N
            (GaloisField 2 f)) =
        LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q))
    (psp : BMSTPSpModelExplicit f
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)) H)
    (S : Set (GL N (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (N) (N) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin Q)) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(spinGroup Q)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix Q) S (e),
      glBlockCentralizer (Spin.spinMatrix Q) S (e)⁆) :
    ∃ (r : ℕ)
      (ι : (ggU .PSU r (max f 1)).K →* ↥(spinGroup Q))
      (β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ),
      2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) ∧
      GGLongRoot (ggU .PSU r (max f 1)).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup Q) → y ∈
        Subgroup.center (ggU .PSU r (max f 1)).K) ∧ ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : (N) → (GaloisField 2 f),
        (Q a₁ = 0 ∧
          Q a₂ = 0 ∧
          Q b₁ = 0 ∧
          Q b₂ = 0) ∧
        QuadraticMap.polar Q a₁ b₁ = 1 ∧ QuadraticMap.polar
          Q a₂ b₂ = 1 ∧
        (QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar
          Q b₁ b₂ = 0 ∧
          QuadraticMap.polar Q a₁ b₂ = 0 ∧
            QuadraticMap.polar Q a₂ b₁ = 0) ∧
        (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map
        (Spin.spinAction Q) = siegelGroup
        Q a₁ a₂ ∧
        (((ggU .PSU r (max f 1)).D.rootGroup (-β₀)).map ι).map
        (Spin.spinAction Q) = siegelGroup
        Q b₁ b₂ := by
  obtain ⟨r, ι, β₀, hrank, hlong, hcentι, hrange, -, rest⟩ :=
    bmst_model_of_psp_explicit_inj f Q hnd hinj hΩ hcent H hH psp S hSU hS hodd he hadj hdeg₁ hdeg₂
      hJe
  exact ⟨r, ι, β₀, hrank, hlong, hcentι, hrange, rest⟩

theorem bmst_closure_of_psp_explicit
    (f : ℕ) {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm (GaloisField 2 f) (N → GaloisField 2 f))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hinj : Function.Injective (Spin.spinMatrix Q))
    (hΩ : (Spin.spinAction Q).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd)
    (hcent : Subgroup.center ↥(spinGroup Q) = ⊥)
    (H : Subgroup (GL N (GaloisField 2 f)))
    (hH : ∀ A : GL N (GaloisField 2 f), A ∈ H ↔
      Matrix.transpose (A : Matrix N N (GaloisField 2 f)) *
        LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q) * (A : Matrix N N
            (GaloisField 2 f)) =
        LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q))
    (psp : BMSTPSpClosureExplicit f
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)) H)
    (S : Set (GL N (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (N) (N) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin Q)) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(spinGroup Q)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix Q) S (e),
      glBlockCentralizer (Spin.spinMatrix Q) S (e)⁆) :
    ∃ (r : ℕ) (ι : (ggU .PSU r (max f 1)).K →* ↥(spinGroup Q)),
      2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup Q) → y ∈
          Subgroup.center (ggU .PSU r (max f 1)).K) ∧
      ι.range = J' ∧
      (∀ a₁ a₂ : ((N) → GaloisField 2 f), a₁ ≠ 0 → a₂ ≠ 0 →
          LinearIndependent (GaloisField 2 f) ![a₁, a₂] → Q
          a₁ = 0 → Q a₂ = 0 →
        QuadraticMap.polar Q a₁ a₂ = 0 → siegelGroup
            Q a₁ a₂ ≤ J'.map (Spin.spinAction
            Q) →
        ∃ (β : Fin (ggU .PSU r (max f 1)).D.rank → ℤ) (u : (ggU .PSU r (max f 1)).K),
            β ∈ (ggU .PSU r (max f 1)).D.roots ∧
            GGLongRoot (ggU .PSU r (max f 1)).D β ∧
          ((((ggU .PSU r (max f 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
              (Spin.spinAction Q) = siegelGroup
              Q a₁ a₂) := by
  have hSUH : ∀ s ∈ S, s ∈ H := by
    intro s hs
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hSU s hs)
    exact bmst_spinMatrix_mem_H f Q H hH x
  have hJeSp : IsComponentOf (J'.map (bmst_spToSp f Q H hH))
      ⁅glBlockCentralizer H.subtype S e, glBlockCentralizer H.subtype S e⁆ :=
    bmst_component_transport f Q hnd hinj hΩ H hH S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  obtain ⟨r, ι₀, hrank, hcent₀, hrange₀, hclos⟩ :=
    psp S hSUH hS hodd he hadj hdeg₁ hdeg₂ hJeSp
  obtain ⟨ι, hι, hrange, hcent⟩ :=
    bmst_transfer f Q H hH hinj hcent hrange₀ hcent₀
  refine ⟨r, ι, hrank, hcent, hrange, ?_⟩
  intro a₁ a₂ ha₁ ha₂ hli hQ₁ hQ₂ hpol hle
  have hmapJ : J'.map (Spin.spinAction Q) =
      ((J'.map (bmst_spToSp f Q H hH)).map H.subtype).map
        (bmst_toLin N (GaloisField 2 f)).toMonoidHom :=
    (bmst_map_map_spinAction f Q H hH J').symm
  have hle' : siegelGroup Q a₁ a₂ ≤
      ((J'.map (bmst_spToSp f Q H hH)).map H.subtype).map
        (bmst_toLin N (GaloisField 2 f)).toMonoidHom := by
    rw [← hmapJ]; exact hle
  have hsiegel : (altSiegelGroup (bmst_gram f Q) a₁ a₂).map
      (bmst_toLin N (GaloisField 2 f)).toMonoidHom = siegelGroup Q a₁ a₂ :=
    bmst_altSiegel_eq_siegel f Q hQ₁ hQ₂ hpol
  have hleH : altSiegelGroup (bmst_gram f Q) a₁ a₂ ≤
      (J'.map (bmst_spToSp f Q H hH)).map H.subtype := by
    rw [← hsiegel] at hle'
    intro x hx
    have hx' : (bmst_toLin N (GaloisField 2 f)).toMonoidHom x ∈
        (altSiegelGroup (bmst_gram f Q) a₁ a₂).map
          (bmst_toLin N (GaloisField 2 f)).toMonoidHom := ⟨x, hx, rfl⟩
    have hmem := hle' hx'
    obtain ⟨y, hy, hyx⟩ := hmem
    rwa [(bmst_toLin N (GaloisField 2 f)).injective hyx] at hy
  have hpol' : a₁ ⬝ᵥ Matrix.mulVec (bmst_gram f Q) a₂ = 0 := by
    rw [← bmst_polar_eq_dot]; exact hpol
  obtain ⟨β, u, hroot, hlong, heq⟩ :=
    hclos a₁ a₂ ha₁ ha₂ hli hpol' hleH
  refine ⟨β, u, hroot, hlong, ?_⟩
  rw [bmst_map_spinAction f Q H hH ι₀ ι hι
        (((ggU .PSU r (max f 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom),
      heq, bmst_altSiegel_eq_siegel f Q hQ₁ hQ₂ hpol]

section LinearModelAtTwo

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open Matrix

local notation "F₂" => GaloisField 2 1
local notation "F₄" => GaloisField 2 2
local notation "SU₂" => SU (unitaryInvolution F₄ 2 1)

@[expose] def BMSTPSpLinearModelAtTwo
    {N : Type} [Fintype N] [DecidableEq N]
    (G : Matrix N N F₂) (H : Subgroup (GL N F₂)) : Prop :=
  ∀ (S : Set (GL N F₂)), (∀ s ∈ S, s ∈ H) →
    (∀ s ∈ S, ∀ s' ∈ S, Commute s s') → (∀ s ∈ S, Odd (orderOf s)) →
    ∀ {e : Matrix N N F₂}, IsPrimIdemIn (Algebra.adjoin F₂ (Units.val '' S)) e →
      formAdj (RingHom.id F₂) G e = e →
      2 ≤ blockDegree (Algebra.adjoin F₂ (Units.val '' S)) e →
      blockDegree (Algebra.adjoin F₂ (Units.val '' S)) e < 4 →
      ∀ {J : Subgroup H}, IsComponentOf J ⁅glBlockCentralizer H.subtype S e,
        glBlockCentralizer H.subtype S e⁆ →
        ∃ (m : ℕ) (_ : Algebra F₂ F₄) (ι : SU₂ m →* H)
          (E : (Fin m → F₄) →ₗ[F₂] (N → F₂)) (C : Submodule F₂ (N → F₂)),
          4 ≤ m ∧ Function.Injective ι ∧ ι.range = J ∧ Function.Injective E ∧
          (∀ g x, ((ι g : GL N F₂) : Matrix N N F₂) *ᵥ E x =
            E (natRep (SU₂ m) g x)) ∧
          (∀ g w, w ∈ C → ((ι g : GL N F₂) : Matrix N N F₂) *ᵥ w = w) ∧
          (∀ z, ∃ x, ∃ w ∈ C, z = E x + w) ∧
          (∀ g, g ^ 2 = 1 → ∀ z, z ⬝ᵥ G.mulVec
            ((((ι g : GL N F₂) : Matrix N N F₂) *ᵥ z) - z) = 0)

theorem bmst_linear_model_of_psp_at_two
    {N : Type} [Fintype N] [DecidableEq N]
    (Q : QuadraticForm F₂ (N → F₂)) (hnd : Q.polarBilin.Nondegenerate)
    (hinj : Function.Injective (Spin.spinMatrix Q))
    (hΩ : (Spin.spinAction Q).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd)
    (hcent : Subgroup.center (spinGroup Q) = ⊥)
    (H : Subgroup (GL N F₂))
    (hH : ∀ A : GL N F₂, A ∈ H ↔
      Matrix.transpose (A : Matrix N N F₂) * LinearMap.toMatrix₂' F₂ Q.polarBilin *
        (A : Matrix N N F₂) = LinearMap.toMatrix₂' F₂ Q.polarBilin)
    (psp : BMSTPSpLinearModelAtTwo (LinearMap.toMatrix₂' F₂ Q.polarBilin) H)
    (S : Set (GL N F₂)) (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix Q).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix N N F₂} (he : IsPrimIdemIn (Algebra.adjoin F₂ (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id F₂) (LinearMap.toMatrix₂' F₂ Q.polarBilin) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin F₂ (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin F₂ (Units.val '' S)) e < 4)
    {J : Subgroup (spinGroup Q)}
    (hJ : IsComponentOf J ⁅glBlockCentralizer (Spin.spinMatrix Q) S e,
      glBlockCentralizer (Spin.spinMatrix Q) S e⁆) :
    ∃ (m : ℕ) (_ : Algebra F₂ F₄) (ι : SU₂ m →* spinGroup Q)
      (E : (Fin m → F₄) →ₗ[F₂] (N → F₂)) (C : Submodule F₂ (N → F₂)),
      4 ≤ m ∧ Function.Injective ι ∧ ι.range = J ∧ Function.Injective E ∧
      (∀ g x, Spin.spinAction Q (ι g) (E x) = E (natRep (SU₂ m) g x)) ∧
      (∀ g w, w ∈ C → Spin.spinAction Q (ι g) w = w) ∧
      (∀ z, ∃ x, ∃ w ∈ C, z = E x + w) ∧
      (∀ g, g ^ 2 = 1 → ∀ z, Q.polarBilin z (Spin.spinAction Q (ι g) z - z) = 0) := by
  have hSUH : ∀ s ∈ S, s ∈ H := by
    intro s hs
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hSU s hs)
    exact bmst_spinMatrix_mem_H 1 Q H hH x
  have hJSp : IsComponentOf (J.map (bmst_spToSp 1 Q H hH))
      ⁅glBlockCentralizer H.subtype S e, glBlockCentralizer H.subtype S e⁆ :=
    bmst_component_transport 1 Q hnd hinj hΩ H hH S hSU hS hodd he hadj hdeg₁ hdeg₂ hJ
  obtain ⟨m, A, ι₀, E, C, hm, hι₀, hRange₀, hE, hAct₀, hFix₀, hSplit, hAlt₀⟩ :=
    psp S hSUH hS hodd he hadj hdeg₁ hdeg₂ hJSp
  let : Algebra F₂ F₄ := A
  have hcent₀ : ∀ y, ι₀ y ∈ Subgroup.center H → y ∈ Subgroup.center (SU₂ m) := by
    intro y hy
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro z
    apply hι₀
    simpa only [map_mul] using hy (ι₀ z)
  obtain ⟨ι, hι, hRange, _⟩ := bmst_transfer (t' := .PSU) (m := m) (g' := 1)
    1 Q H hH hinj hcent hRange₀ hcent₀
  have hMat (g : SU₂ m) : Spin.spinMatrix Q (ι g) = (ι₀ g : GL N F₂) := by
    calc
      Spin.spinMatrix Q (ι g) = (bmst_spToSp 1 Q H hH (ι g) : GL N F₂) :=
        (bmst_spToSp_coe 1 Q H hH (ι g)).symm
      _ = (ι₀ g : GL N F₂) := congrArg Subtype.val (hι g)
  have hVec (g : SU₂ m) (x : N → F₂) :
      Spin.spinAction Q (ι g) x = ((ι₀ g : GL N F₂) : Matrix N N F₂) *ᵥ x :=
    (Spin.spinMatrix_mulVec Q (ι g) x).symm.trans
      (congrArg (fun A : GL N F₂ => (A : Matrix N N F₂) *ᵥ x) (hMat g))
  refine ⟨m, A, ι, E, C, hm, ?_, hRange, hE, ?_, ?_, hSplit, ?_⟩
  · intro x y hxy
    apply hι₀
    exact (hι x).symm.trans
      ((congrArg (bmst_spToSp 1 Q H hH) hxy).trans (hι y))
  · intro g x
    exact (hVec g (E x)).trans (hAct₀ g x)
  · intro g w hw
    exact (hVec g w).trans (hFix₀ g w hw)
  · intro g hg z
    change QuadraticMap.polar Q z (Spin.spinAction Q (ι g) z - z) = 0
    calc
      QuadraticMap.polar Q z (Spin.spinAction Q (ι g) z - z) =
          QuadraticMap.polar Q z ((((ι₀ g : GL N F₂) : Matrix N N F₂) *ᵥ z) - z) :=
        congrArg (fun x : N → F₂ => QuadraticMap.polar Q z (x - z)) (hVec g z)
      _ = z ⬝ᵥ (bmst_gram 1 Q).mulVec
          ((((ι₀ g : GL N F₂) : Matrix N N F₂) *ᵥ z) - z) := bmst_polar_eq_dot 1 Q _ _
      _ = 0 := hAlt₀ g hg z

end LinearModelAtTwo

end CFSG.StandardType.ClassicalPosition
