module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSURoot
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import TauCeti.RingTheory.Norm.Quadratic
public import CFSG.RankThree.PartTwo.Sec21.Item223Of
public import CFSG.Fischer.Classification.PartII.Herm.Classify
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangHerm
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.TraceTransfer
import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSU
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec21.Item226Steps
public import CFSG.RankThree.PartTwo.Sec21.Item229
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

open scoped commutatorElement

open Matrix

private noncomputable def bmSTS_J (n f : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
  Matrix.fromBlocks 0 1 (-1) 0

private lemma bmSTS_neg_one_matrix_eq_one {ι F : Type} [DecidableEq ι] [Field F] [CharP F 2] :
    (-1 : Matrix ι ι F) = 1 := by
  ext i j
  rw [Matrix.neg_apply, CharTwo.neg_eq]

private lemma bmSTS_J_mul_self (n f : ℕ) : bmSTS_J n f * bmSTS_J n f = 1 := by
  rw [bmSTS_J, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, zero_add,
    add_zero, Matrix.mul_neg, neg_zero]
  rw [bmSTS_neg_one_matrix_eq_one, Matrix.fromBlocks_one]

private lemma bmSTS_J_det (n f : ℕ) : IsUnit (bmSTS_J n f).det :=
  Matrix.isUnit_det_of_right_inverse (bmSTS_J_mul_self n f)

private theorem bmSTS_degree_two
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 2 := by
  have hSG : ∀ s ∈ S, Matrix.transpose (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) * bmSTS_J n f *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = bmSTS_J n f := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff).1 (hSU s hs)
    simpa [bmSTS_J] using h
  rcases blockDegree_eq_one_or_even_of_formAdj_eq (G := bmSTS_J n f) (S := S) (e := e)
      (bmSTS_J_det n f) hS hodd hSG he hadj with h | h
  · omega
  · obtain ⟨k, hk⟩ := h
    omega

private lemma bmSTS_B_self (n f : ℕ) (v : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    v ⬝ᵥ Matrix.mulVec (bmSTS_J n f) v = 0 := by
  rw [bmSTS_J, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, bmSTS_neg_one_matrix_eq_one, zero_add,
    add_zero]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
  have hcomm : (∑ i, v (Sum.inl i) * v (Sum.inr i)) =
      ∑ i, v (Sum.inr i) * v (Sum.inl i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  rw [hcomm]
  exact CharTwo.add_self_eq_zero _

private theorem bmSTS_blockSelfAdjoint
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4) :
    e * e = e ∧ Matrix.transpose e * bmSTS_J n f = bmSTS_J n f * e := by
  refine ⟨he.2.1.eq, ?_⟩
  have h := hadj
  rw [formAdj] at h
  rw [show e.map (⇑(RingHom.id (GaloisField 2 f))) = e from Matrix.map_id e] at h
  have hJJ : bmSTS_J n f * (bmSTS_J n f)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (bmSTS_J_det n f)
  have h1 : bmSTS_J n f * ((bmSTS_J n f)⁻¹ * Matrix.transpose e * bmSTS_J n f) =
      Matrix.transpose e * bmSTS_J n f := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [← h1, h]

private lemma bmSTS_mulVec_dotProduct_of_transpose_mul_eq {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] {G E : Matrix ι ι F} (hE : Matrix.transpose E * G = G * E)
    (x y : ι → F) :
    Matrix.mulVec E x ⬝ᵥ Matrix.mulVec G y = x ⬝ᵥ Matrix.mulVec G (Matrix.mulVec E y) := by
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hE,
    ← Matrix.mulVec_mulVec]

private lemma bmSTS_mulVec_eq_self_of_mem_range {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {E : Matrix ι ι F} (hE : E * E = E) {x : ι → F}
    (hx : x ∈ LinearMap.range (Matrix.mulVecLin E)) : Matrix.mulVec E x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hE]

private lemma bmSTS_eq_zero_of_forall_dotProduct_mulVec_eq_zero {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] {G : Matrix ι ι F} (hG : IsUnit G) {y : ι → F}
    (hy : ∀ z, z ⬝ᵥ Matrix.mulVec G y = 0) : y = 0 := by
  have h1 : Matrix.mulVec G y = 0 := dotProduct_eq_zero_iff.mp fun z => by
    rw [dotProduct_comm]
    exact hy z
  exact Matrix.mulVec_injective_iff_isUnit.mpr hG (h1.trans (Matrix.mulVec_zero G).symm)

private lemma bmSTS_eq_zero_of_forall_dotProduct_mulVec_eq_zero' {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] {G : Matrix ι ι F} (hG : IsUnit G) {x : ι → F}
    (hx : ∀ z, x ⬝ᵥ Matrix.mulVec G z = 0) : x = 0 := by
  have h1 : Matrix.vecMul x G = 0 := dotProduct_eq_zero_iff.mp fun z => by
    rw [← Matrix.dotProduct_mulVec]
    exact hx z
  exact Matrix.vecMul_injective_iff_isUnit.mpr hG (h1.trans (Matrix.zero_vecMul G).symm)

private theorem bmSTS_blockRestrictNondegenerate
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4) :
    ((Matrix.toBilin' (bmSTS_J n f)).restrict
      (LinearMap.range (Matrix.mulVecLin e))).Nondegenerate := by
  obtain ⟨hE2, hE⟩ := bmSTS_blockSelfAdjoint n f S hSU hS hodd he hadj hdeg₁ hdeg₂
  have hJunit : IsUnit (bmSTS_J n f) :=
    (Matrix.isUnit_iff_isUnit_det (bmSTS_J n f)).mpr (bmSTS_J_det n f)
  refine ⟨fun x hx => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩
  · refine bmSTS_eq_zero_of_forall_dotProduct_mulVec_eq_zero' hJunit fun z => ?_
    have h1 := hx ⟨Matrix.mulVec e z, z, rfl⟩
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      Matrix.toBilin'_apply'] at h1
    rw [← bmSTS_mulVec_eq_self_of_mem_range hE2 x.2,
      bmSTS_mulVec_dotProduct_of_transpose_mul_eq hE]
    exact h1
  · refine bmSTS_eq_zero_of_forall_dotProduct_mulVec_eq_zero hJunit fun z => ?_
    have h1 := hy ⟨Matrix.mulVec e z, z, rfl⟩
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      Matrix.toBilin'_apply'] at h1
    rw [← bmSTS_mulVec_eq_self_of_mem_range hE2 y.2,
      ← bmSTS_mulVec_dotProduct_of_transpose_mul_eq hE]
    exact h1

private theorem bmSTS_blockRangeNeBot
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4) :
    LinearMap.range (Matrix.mulVecLin e) ≠ ⊥ := by
  intro h
  have hzero : Matrix.mulVecLin e = 0 := LinearMap.range_eq_bot.mp h
  apply he.2.2.1
  ext i j
  have h1 := congrFun (DFunLike.congr_fun hzero (Pi.single j 1)) i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h1

private theorem bmSTS_charP_two
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2) :
    (2 : K) = 0 := by
  have h2F : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero _ _
  rw [show (2 : K) = algebraMap (GaloisField 2 f) K (2 : GaloisField 2 f) from
    (map_natCast (algebraMap (GaloisField 2 f) K) 2).symm, h2F, map_zero]

private theorem bmSTS_tau_eq_canonical
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (τ : K ≃+* K) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hτlin : ∀ c : GaloisField 2 f,
      τ (algebraMap (GaloisField 2 f) K c) = algebraMap (GaloisField 2 f) K c) :
    ∃ (σ : K ≃ₐ[GaloisField 2 f] K), σ ≠ 1 ∧ (∀ a : K, τ a = σ a) ∧
      (∀ a : K, σ a * a + a * σ a = 0) := by
  haveI : Algebra.IsQuadraticExtension (GaloisField 2 f) K :=
    Algebra.IsQuadraticExtension.mk hKrank
  let τ' : K ≃ₐ[GaloisField 2 f] K := { τ with commutes' := fun c => hτlin c }
  have hτ'ne : τ' ≠ 1 := by
    intro h
    apply hτne
    ext x
    exact congrFun (congrArg (fun e : K ≃ₐ[GaloisField 2 f] K => (e : K → K)) h) x
  obtain ⟨σ, hσne⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one (GaloisField 2 f) K
  have hτσ : τ' = σ := by
    rcases Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq (GaloisField 2 f) K hσne τ' with
      h | h
    · exact absurd h hτ'ne
    · exact h
  refine ⟨σ, hσne, fun a => ?_, fun a => ?_⟩
  · change τ' a = σ a
    exact congrFun (congrArg (fun e : K ≃ₐ[GaloisField 2 f] K => (e : K → K)) hτσ) a
  · have h2 : (2 : K) = 0 := bmSTS_charP_two n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank
    rw [mul_comm a (σ a), ← two_mul, h2, zero_mul]

private theorem bmSTS_charP
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2) :
    CharP K 2 := by
  exact charP_of_injective_ringHom (f := algebraMap (GaloisField 2 f) K)
    (FaithfulSMul.algebraMap_injective (GaloisField 2 f) K) 2

private theorem bmSTS_tauFrobeniusPow
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (τ : K ≃+* K) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hchar : CharP K 2) :
    ∃ i : ℕ, ∀ x : K, τ x = x ^ 2 ^ i := by
  letI : Algebra (ZMod 2) K := (ZMod.castHom (dvd_refl 2) K).toAlgebra
  let τ' : K ≃ₐ[ZMod 2] K :=
    { τ with
      commutes' := fun n => by
        change τ ((n.val : K)) = (n.val : K)
        exact map_natCast τ n.val }
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 K τ'
  refine ⟨i, fun x => ?_⟩
  have h := hi x
  rw [Nat.card_eq_fintype_card, ZMod.card] at h
  exact h

private theorem bmSTS_powTwoTwoI_eq_self
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (τ : K ≃+* K) (hτ2 : ∀ a : K, τ (τ a) = a)
    (i : ℕ) (hi : ∀ x : K, τ x = x ^ 2 ^ i) :
    ∀ x : K, x ^ (2 ^ i * 2 ^ i) = x := by
  intro x
  rw [pow_mul, ← hi x, ← hi (τ x)]
  exact hτ2 x

private theorem bmSTS_card_F
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2) :
    f ≠ 0 → Nat.card (GaloisField 2 f) = 2 ^ f := by
  exact GaloisField.card 2 f

private theorem bmSTS_card_K
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2) :
    Nat.card K = Nat.card (GaloisField 2 f) ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := GaloisField 2 f), hKrank]

private theorem bmSTS_powTwo_mul (i : ℕ) : 2 ^ i * 2 ^ i = 2 ^ (2 * i) := by
  rw [← pow_add, two_mul]

private theorem bmSTS_units_pow_eq_one
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (i : ℕ) (hi2 : ∀ x : K, x ^ (2 ^ i * 2 ^ i) = x) :
    ∀ g : Kˣ, g ^ (2 ^ (2 * i) - 1) = 1 := by
  intro g
  have h1 : g ^ (2 ^ i * 2 ^ i) = g := by
    ext
    rw [Units.val_pow_eq_pow_val, hi2 (g : K)]
  rw [← bmSTS_powTwo_mul i]
  have hm : 1 ≤ 2 ^ i * 2 ^ i := by
    have hpos : 0 < 2 ^ i * 2 ^ i := by positivity
    omega
  have h3 : g ^ (2 ^ i * 2 ^ i - 1) * g = g := by
    rw [← pow_succ, Nat.sub_add_cancel hm, h1]
  exact mul_right_cancel (h3.trans (one_mul g).symm)

private theorem bmSTS_card_units_dvd
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (m : ℕ) (hm : ∀ g : Kˣ, g ^ m = 1) :
    Nat.card K - 1 ∣ m := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [← Nat.card_units K, ← hg]
  exact orderOf_dvd_iff_pow_eq_one.mpr (hm g)

private theorem bmSTS_exponent_dvd
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (i : ℕ) (hi2 : ∀ x : K, x ^ (2 ^ i * 2 ^ i) = x) :
    Nat.card K - 1 ∣ 2 ^ (2 * i) - 1 := by
  have hm := bmSTS_units_pow_eq_one n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank i hi2
  rw [← bmSTS_powTwo_mul i] at hm
  have h := bmSTS_card_units_dvd n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank
    (2 ^ i * 2 ^ i - 1) hm
  simpa [bmSTS_powTwo_mul i] using h

private theorem bmSTS_card_K_eq
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (hf : 0 < f) :
    Nat.card K = 2 ^ (2 * f) := by
  have hfne : f ≠ 0 := by omega
  have h1 : Nat.card (GaloisField 2 f) = 2 ^ f :=
    bmSTS_card_F n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank hfne
  rw [bmSTS_card_K n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank, h1, ← pow_mul, mul_comm f 2]

private theorem bmSTS_card_K_sub_one
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (hcard : Nat.card K = 2 ^ (2 * f)) :
    Nat.card K - 1 = 2 ^ (2 * f) - 1 := by
  rw [hcard]

private theorem bmSTS_modEq_one_of_dvd (a b : ℕ) (h : 2 ^ a - 1 ∣ 2 ^ b - 1) :
    2 ^ b ≡ 1 [MOD 2 ^ a - 1] := by
  exact ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow (n := b))).mpr h).symm

private theorem bmSTS_modEq_pow_self (a : ℕ) : 2 ^ a ≡ 1 [MOD 2 ^ a - 1] := by
  exact ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow (n := a))).mpr (dvd_refl (2 ^ a - 1))).symm

private theorem bmSTS_modEq_mod (a b : ℕ) (h : 2 ^ b ≡ 1 [MOD 2 ^ a - 1]) :
    2 ^ (b % a) ≡ 1 [MOD 2 ^ a - 1] := by
  have h2 : (2 ^ a) ^ (b / a) ≡ 1 [MOD 2 ^ a - 1] := by
    simpa using (bmSTS_modEq_pow_self a).pow (b / a)
  have h3 : (2 ^ a) ^ (b / a) * 2 ^ (b % a) ≡ 2 ^ (b % a) [MOD 2 ^ a - 1] := by
    simpa using h2.mul (Nat.ModEq.refl (2 ^ (b % a)))
  have h4 : 2 ^ b ≡ 2 ^ (b % a) [MOD 2 ^ a - 1] := by
    have hb : b = a * (b / a) + b % a := by
      conv_lhs => rw [← Nat.div_add_mod b a]
    conv_lhs => rw [hb, pow_add, pow_mul]
    exact h3
  exact h4.symm.trans h

private theorem bmSTS_pow_sub_one_dvd_mod (a b : ℕ) (h : 2 ^ a - 1 ∣ 2 ^ b - 1) :
    2 ^ a - 1 ∣ 2 ^ (b % a) - 1 := by
  have h1 : 1 ≡ 2 ^ (b % a) [MOD 2 ^ a - 1] :=
    (bmSTS_modEq_mod a b (bmSTS_modEq_one_of_dvd a b h)).symm
  exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow (n := b % a))).mp h1

private theorem bmSTS_pow_eq_one_of_dvd_of_lt (a r : ℕ) (hr : r < a)
    (h : 2 ^ a - 1 ∣ 2 ^ r - 1) : 2 ^ r = 1 := by
  by_contra hne
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hpos : 0 < 2 ^ r - 1 := by omega
  have hle := Nat.le_of_dvd hpos h
  have hlt : 2 ^ r < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) hr
  omega

private theorem bmSTS_pow_two_eq_one (r : ℕ) (h : 2 ^ r = 1) : r = 0 := by
  by_contra hr
  have h2 : 1 < 2 ^ r := Nat.one_lt_two_pow hr
  omega

private theorem bmSTS_pow_sub_one_dvd_arith (a b : ℕ) (h : 2 ^ a - 1 ∣ 2 ^ b - 1) :
    a ∣ b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have h0 : 2 ^ b - 1 = 0 := by
      have : 0 ∣ 2 ^ b - 1 := by simpa using h
      rwa [zero_dvd_iff] at this
    have hb : 2 ^ b = 1 := le_antisymm (Nat.sub_eq_zero_iff_le.mp h0) Nat.one_le_two_pow
    have hb0 : b = 0 := bmSTS_pow_two_eq_one b hb
    subst hb0
    exact dvd_zero 0
  · have hmod := bmSTS_pow_sub_one_dvd_mod a b h
    have hlt : b % a < a := Nat.mod_lt b ha
    have h1 := bmSTS_pow_eq_one_of_dvd_of_lt a (b % a) hlt hmod
    exact Nat.dvd_of_mod_eq_zero (bmSTS_pow_two_eq_one (b % a) h1)

private theorem bmSTS_card_K_minus_one_eq
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (hf : 0 < f) :
    Nat.card K - 1 = 2 ^ (2 * f) - 1 := by
  exact bmSTS_card_K_sub_one n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank
    (bmSTS_card_K_eq n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank hf)

private theorem bmSTS_mul_two_dvd (f i : ℕ) (h : 2 * f ∣ 2 * i) : f ∣ i :=
  (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < (2 : ℕ))).mp h

private theorem bmSTS_powTwo_sub_one_dvd_pos
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (i : ℕ) (hf : 0 < f) (hdvd : Nat.card K - 1 ∣ 2 ^ (2 * i) - 1) :
    f ∣ i := by
  rw [bmSTS_card_K_minus_one_eq n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank hf] at hdvd
  exact bmSTS_mul_two_dvd f i (bmSTS_pow_sub_one_dvd_arith (2 * f) (2 * i) hdvd)

private theorem bmSTS_powTwo_sub_one_dvd_pos'
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (i : ℕ) (hf : 0 < f) (hdvd : Nat.card K - 1 ∣ 2 ^ (2 * i) - 1) :
    max f 1 ∣ i := by
  rw [show max f 1 = f from by omega]
  exact bmSTS_powTwo_sub_one_dvd_pos n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank i hf hdvd

private theorem bmSTS_powTwo_sub_one_dvd_zero
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (i : ℕ) (hf : f = 0) (hdvd : Nat.card K - 1 ∣ 2 ^ (2 * i) - 1) :
    max f 1 ∣ i := by
  rw [hf]
  exact one_dvd i

private theorem bmSTS_powTwo_sub_one_dvd
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (i : ℕ) (hcard : Nat.card K = Nat.card (GaloisField 2 f) ^ 2)
    (hdvd : Nat.card K - 1 ∣ 2 ^ (2 * i) - 1) :
    max f 1 ∣ i := by
  rcases Nat.eq_zero_or_pos f with hf | hf
  · exact bmSTS_powTwo_sub_one_dvd_zero n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank i hf hdvd
  · exact bmSTS_powTwo_sub_one_dvd_pos' n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank i hf hdvd

private theorem bmSTS_dvd_of_pow_eq_self
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (i : ℕ) (hi2 : ∀ x : K, x ^ (2 ^ i * 2 ^ i) = x) :
    max f 1 ∣ i := by
  exact bmSTS_powTwo_sub_one_dvd n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank i
    (bmSTS_card_K n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank)
    (bmSTS_exponent_dvd n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank i hi2)

private theorem bmSTS_baseFrobenius
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2) :
    ∀ c : GaloisField 2 f, c ^ 2 ^ f = c := by
  intro c
  rcases Nat.eq_zero_or_pos f with hf | hf
  · subst hf
    simp
  · haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    have hq : Fintype.card (GaloisField 2 f) = 2 ^ f := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 f (ne_of_gt hf)
    rw [← hq]
    exact FiniteField.pow_card c

private theorem bmSTS_card_galoisField_max (f : ℕ) :
    Nat.card (GaloisField 2 f) = 2 ^ max f 1 := by
  rcases Nat.eq_zero_or_pos f with hf | hf
  · subst hf
    have h : max 0 1 = 1 := by omega
    rw [h]
    exact CFSG.RankThree.PartTwo.Sec21.natCard_galoisField_two_zero
  · have h : max f 1 = f := by omega
    rw [h]
    exact GaloisField.card 2 f (ne_of_gt hf)

private theorem bmSTS_base_pow_two_max (f : ℕ) (c : GaloisField 2 f) :
    c ^ 2 ^ max f 1 = c := by
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have h : c ^ Nat.card (GaloisField 2 f) = c := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  rwa [bmSTS_card_galoisField_max f] at h

private theorem bmSTS_basePowFrobenius
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (i : ℕ) (hfi : max f 1 ∣ i) (hc : ∀ c : GaloisField 2 f, c ^ 2 ^ f = c) :
    ∀ c : GaloisField 2 f,
      (algebraMap (GaloisField 2 f) K c) ^ 2 ^ i = algebraMap (GaloisField 2 f) K c := by
  intro c
  obtain ⟨k, rfl⟩ := hfi
  rw [← map_pow]
  congr 1
  rw [pow_mul]
  have hbase : c ^ 2 ^ max f 1 = c := bmSTS_base_pow_two_max f c
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, hbase]

private theorem bmSTS_frobeniusPow_fixes_base
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (τ : K ≃+* K) (hτ2 : ∀ a : K, τ (τ a) = a)
    (i : ℕ) (hi : ∀ x : K, τ x = x ^ 2 ^ i) :
    ∀ c : GaloisField 2 f,
      τ (algebraMap (GaloisField 2 f) K c) = algebraMap (GaloisField 2 f) K c := by
  have hfi := bmSTS_dvd_of_pow_eq_self n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank i
    (bmSTS_powTwoTwoI_eq_self n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 i hi)
  have hc := bmSTS_baseFrobenius n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank
  intro c
  rw [hi (algebraMap (GaloisField 2 f) K c)]
  exact bmSTS_basePowFrobenius n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank i hfi hc c

private theorem bmSTS_tauFixesBase
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    [FiniteDimensional (GaloisField 2 f) K] [Algebra.IsSeparable (GaloisField 2 f) K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (τ : K ≃+* K) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K) :
    ∀ c : GaloisField 2 f,
      τ (algebraMap (GaloisField 2 f) K c) = algebraMap (GaloisField 2 f) K c := by
  have hchar := bmSTS_charP n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank
  obtain ⟨i, hi⟩ :=
    bmSTS_tauFrobeniusPow n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne hchar
  exact bmSTS_frobeniusPow_fixes_base n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 i hi

private theorem bmSTS_blockEmbeddingEV_PSU_unitaryInvolution
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution τ :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang.isUnitaryInvolution_of_involution
    (by intro h; exact hτne (by rw [h]; rfl))
    (by ext x; exact hτ2 x)

private theorem bmSTS_blockEmbeddingEV_PSU_isHermForm
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    CFSG.Fischer.Classification.Herm.IsHermForm τ (fun x y => h x y) := by
  have hxy : ∀ x y : W, h x y = τ (h y x) := fun x y => by
    rw [← hτ2 (h x y), ← hsymm x y]
  refine CFSG.Fischer.Classification.Herm.IsHermForm.mk ?_ ?_ hsymm
  · intro x x' y
    rw [hxy (x + x') y, (h y).map_add, map_add, ← hxy x y, ← hxy x' y]
  · intro c x y
    rw [hxy (c • x) y, (h y).map_smul, smul_eq_mul, map_mul, ← hxy x y]

private noncomputable def bmSTS_blockEmbeddingEV_PSU_hermEquiv
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    W ≃ₗ[GaloisField 2 f] (Fin m' → K) := by
  haveI : FiniteDimensional K W := FiniteDimensional.of_finrank_pos (by omega)
  exact LinearEquiv.restrictScalars (GaloisField 2 f)
    (Classical.choose (CFSG.Fischer.Classification.exists_linearEquiv_herm_of_form
      (bmSTS_blockEmbeddingEV_PSU_unitaryInvolution n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
      (bmSTS_blockEmbeddingEV_PSU_isHermForm n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
      hnd hrank))

private theorem bmSTS_finrank_galoisField_max (f : ℕ) :
    Module.finrank (ZMod 2) (GaloisField 2 f) = max f 1 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := GaloisField 2 f)
  rw [bmSTS_card_galoisField_max f] at h
  have hz : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hz] at h
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h.symm

private theorem bmSTS_finrank_galoisField_twoMax (f : ℕ) :
    Module.finrank (ZMod 2) (GaloisField 2 (2 * max f 1)) = 2 * max f 1 :=
  (bmSTS_finrank_galoisField_max (2 * max f 1)).trans (by omega)

private theorem bmSTS_blockEmbeddingEV_PSU_baseAlgebra (f : ℕ) :
    Nonempty (Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))) := by
  have hdiv : Module.finrank (ZMod 2) (GaloisField 2 f) ∣
      Module.finrank (ZMod 2) (GaloisField 2 (2 * max f 1)) := by
    rw [bmSTS_finrank_galoisField_max f, bmSTS_finrank_galoisField_twoMax f]
    exact dvd_mul_left (max f 1) 2
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
    (K := GaloisField 2 f) (L := GaloisField 2 (2 * max f 1)) hdiv
  exact ⟨φ.toRingHom.toAlgebra⟩

private noncomputable instance bmSTS_baseAlgInst (f : ℕ) :
    Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) :=
  Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)

private theorem bmSTS_natCard_of_finrank_two (f : ℕ) (K : Type) [Field K]
    [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2) :
    Nat.card K = 2 ^ (2 * max f 1) := by
  have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 f) (V := K)
  rw [bmSTS_card_galoisField_max f, hKrank] at h
  rw [h, ← pow_mul, mul_comm]

private theorem bmSTS_natCard_galoisField_twoMax (f : ℕ) :
    Nat.card (GaloisField 2 (2 * max f 1)) = 2 ^ (2 * max f 1) :=
  GaloisField.card 2 (2 * max f 1) (by omega)

private noncomputable def bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv
    (f : ℕ) (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))] :
    K ≃ₐ[GaloisField 2 f] GaloisField 2 (2 * max f 1) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 (2 * max f 1)) := Fintype.ofFinite _
  have hcardNat : Nat.card K = Nat.card (GaloisField 2 (2 * max f 1)) := by
    rw [bmSTS_natCard_of_finrank_two f K hKrank, bmSTS_natCard_galoisField_twoMax f]
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 (2 * max f 1)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardNat
  let p : Polynomial (GaloisField 2 f) := Polynomial.X ^ Fintype.card K - Polynomial.X
  letI : Polynomial.IsSplittingField (GaloisField 2 f) K p := by
    dsimp only [p]
    exact FiniteField.isSplittingField_sub K (GaloisField 2 f)
  letI : Polynomial.IsSplittingField (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) p := by
    dsimp only [p]
    rw [hcard]
    exact FiniteField.isSplittingField_sub (GaloisField 2 (2 * max f 1)) (GaloisField 2 f)
  exact (Polynomial.IsSplittingField.algEquiv (K := GaloisField 2 f) (L := K) p).trans
    (Polynomial.IsSplittingField.algEquiv (K := GaloisField 2 f)
      (L := GaloisField 2 (2 * max f 1)) p).symm

private noncomputable def bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv
    (f m' : ℕ) (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))] :
    (Fin m' → K) ≃ₗ[GaloisField 2 f] (Fin m' → GaloisField 2 (2 * max f 1)) :=
  LinearEquiv.piCongrRight
    (fun _ : Fin m' => (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).toLinearEquiv)

private theorem bmSTS_natCard_galoisField_twoMax_sq (f : ℕ) :
    Nat.card (GaloisField 2 (2 * max f 1)) = (2 ^ max f 1) ^ 2 := by
  rw [bmSTS_natCard_galoisField_twoMax f, ← pow_mul]
  congr 1
  omega

private noncomputable def bmSTS_antidiagConj (m' f : ℕ) :
    GL (Fin m') (GaloisField 2 (2 * max f 1)) :=
  (Unitary.exists_wittMatrix (F := GaloisField 2 (2 * max f 1)) (p := 2) (f := max f 1)
    (bmSTS_natCard_galoisField_twoMax_sq f) m').choose

private theorem bmSTS_antidiagConj_spec (m' f : ℕ) :
    Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
        (bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
      (bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) =
      Unitary.antidiag m' :=
  (Unitary.exists_wittMatrix (F := GaloisField 2 (2 * max f 1)) (p := 2) (f := max f 1)
    (bmSTS_natCard_galoisField_twoMax_sq f) m').choose_spec

private noncomputable def bmSTS_blockEmbeddingEV_PSU_suAction
    (m' f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (g : (ggU .PSU m' (max f 1)).K) :
    (Fin m' → GaloisField 2 (2 * max f 1)) →ₗ[GaloisField 2 f]
      (Fin m' → GaloisField 2 (2 * max f 1)) := by
  let σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have e : ggU .PSU m' (max f 1) =
      ⟨Unitary.SU σ m',
        Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte, σ]
  have hK : (ggU .PSU m' (max f 1)).K = ↥(Unitary.SU σ m') := congrArg LieUniversal.K e
  let g' : ↥(Unitary.SU σ m') := hK ▸ g
  exact (Matrix.mulVecLin ((Unitary.conjEquiv (bmSTS_antidiagConj m' f)
      (bmSTS_antidiagConj_spec m' f) g').1 :
        Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))).restrictScalars
    (GaloisField 2 f)

private noncomputable def bmSTS_blockEmbeddingEV_PSU_stdActionMap
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    (ggU .PSU m' (max f 1)).K → (Fin m' → K) →ₗ[GaloisField 2 f] (Fin m' → K) := by
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) :=
    Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)
  exact fun g => (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm.toLinearMap.comp
    ((bmSTS_blockEmbeddingEV_PSU_suAction m' f g).comp
      (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).toLinearMap)

private theorem bmSTS_mulVecLin_GL_injective {m : ℕ} {F : Type} [Field F]
    (M : GL (Fin m) F) :
    Function.Injective ((Matrix.mulVecLin (M : Matrix (Fin m) (Fin m) F)).restrictScalars F) := by
  intro a b hab
  rw [← Matrix.GeneralLinearGroup.coe_toLin] at hab
  exact (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv.injective hab

private theorem bmSTS_blockEmbeddingEV_PSU_stdActionInjective
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ g : (ggU .PSU m' (max f 1)).K,
      Function.Injective (bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁
        hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) := by
  intro g
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) :=
    Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)
  have hinj : Function.Injective (bmSTS_blockEmbeddingEV_PSU_suAction m' f g) := by
    simp only [bmSTS_blockEmbeddingEV_PSU_suAction]
    exact bmSTS_mulVecLin_GL_injective _
  have hmap : bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g =
      (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm.toLinearMap.comp
        ((bmSTS_blockEmbeddingEV_PSU_suAction m' f g).comp
          (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).toLinearMap) := rfl
  rw [hmap]
  exact ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm.injective).comp
    (hinj.comp (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).injective)

private theorem bmSTS_mulVecLin_GL_surjective {m : ℕ} {F : Type} [Field F]
    (M : GL (Fin m) F) :
    Function.Surjective ((Matrix.mulVecLin (M : Matrix (Fin m) (Fin m) F)).restrictScalars F) := by
  intro b
  refine ⟨(Matrix.GeneralLinearGroup.toLin M).toLinearEquiv.symm b, ?_⟩
  rw [← Matrix.GeneralLinearGroup.coe_toLin]
  exact (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv.apply_symm_apply b

private theorem bmSTS_blockEmbeddingEV_PSU_stdActionSurjective
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ g : (ggU .PSU m' (max f 1)).K,
      Function.Surjective (bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁
        hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) := by
  intro g
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) :=
    Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)
  have hsurj : Function.Surjective (bmSTS_blockEmbeddingEV_PSU_suAction m' f g) := by
    simp only [bmSTS_blockEmbeddingEV_PSU_suAction]
    exact bmSTS_mulVecLin_GL_surjective _
  have hmap : bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g =
      (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm.toLinearMap.comp
        ((bmSTS_blockEmbeddingEV_PSU_suAction m' f g).comp
          (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).toLinearMap) := rfl
  rw [hmap]
  exact ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm.surjective).comp
    (hsurj.comp (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).surjective)

private noncomputable def bmSTS_blockEmbeddingEV_PSU_stdAction
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    (ggU .PSU m' (max f 1)).K → (Fin m' → K) ≃ₗ[GaloisField 2 f] (Fin m' → K) :=
  fun g => LinearEquiv.ofBijective
    (bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g)
    ⟨bmSTS_blockEmbeddingEV_PSU_stdActionInjective n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g,
      bmSTS_blockEmbeddingEV_PSU_stdActionSurjective n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g⟩

private noncomputable def bmSTS_blockEmbeddingEV_PSU_blockAction
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    (ggU .PSU m' (max f 1)).K → W ≃ₗ[GaloisField 2 f] W :=
  fun g => (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).trans
    ((bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).trans
      (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm)

private noncomputable def bmSTS_linearEquiv_to_GL (f : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : (ι → GaloisField 2 f) ≃ₗ[GaloisField 2 f] (ι → GaloisField 2 f)) :
    GL ι (GaloisField 2 f) :=
  (Matrix.GeneralLinearGroup.toLin (R := GaloisField 2 f) (n := ι)).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv T)

private noncomputable def bmSTS_blockEmbeddingEV_PSU_blockExtendEquiv
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K) :
    ((Fin n ⊕ Fin n) → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      ((Fin n ⊕ Fin n) → GaloisField 2 f) := by
  have hee : e * e = e := he.2.1
  have hL : IsIdempotentElem (Matrix.mulVecLin e :
      ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
        ((Fin n ⊕ Fin n) → GaloisField 2 f)) := by
    show (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e
    rw [← Matrix.mulVecLin_mul, hee]
  have hcompl := LinearMap.IsIdempotentElem.isCompl hL
  let φ : W ≃ₗ[GaloisField 2 f] LinearMap.range (Matrix.mulVecLin e) :=
    (LinearEquiv.ofInjective eW heWinj).trans (LinearEquiv.ofEq _ _ heW)
  let Ae : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[GaloisField 2 f]
      LinearMap.range (Matrix.mulVecLin e) :=
    (φ.symm.trans (bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
      K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g)).trans φ
  exact (Submodule.prodEquivOfIsCompl _ _ hcompl).symm.trans
    ((Ae.prodCongr (LinearEquiv.refl (GaloisField 2 f) _)).trans
      (Submodule.prodEquivOfIsCompl _ _ hcompl))

private noncomputable def bmSTS_blockEmbeddingEV_PSU_blockExtend
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    (ggU .PSU m' (max f 1)).K → GL (Fin n ⊕ Fin n) (GaloisField 2 f) :=
  fun g => bmSTS_linearEquiv_to_GL f
    (bmSTS_blockEmbeddingEV_PSU_blockExtendEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g)

private theorem bmSTS_blockExtend_orthogonal
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ a : (Fin n ⊕ Fin n) → GaloisField 2 f,
      a ∈ LinearMap.range (Matrix.mulVecLin e) →
      ∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
        b ∈ LinearMap.ker (Matrix.mulVecLin e) →
        Matrix.toBilin' (bmSTS_J n f) a b = 0 := by
  intro a ha b hb
  have hee : e * e = e := he.2.1
  have hmap : e.map (⇑(RingHom.id (GaloisField 2 f))) = e := Matrix.map_id e
  have h' : (bmSTS_J n f)⁻¹ * Matrix.transpose e * bmSTS_J n f = e := by
    simpa only [formAdj, hmap] using hadj
  have hJinv : (bmSTS_J n f)⁻¹ = bmSTS_J n f :=
    Matrix.inv_eq_left_inv (bmSTS_J_mul_self n f)
  rw [hJinv] at h'
  have hEJ : Matrix.transpose e * bmSTS_J n f = bmSTS_J n f * e := by
    calc Matrix.transpose e * bmSTS_J n f
        = (bmSTS_J n f * bmSTS_J n f) * (Matrix.transpose e * bmSTS_J n f) := by
          rw [bmSTS_J_mul_self, Matrix.one_mul]
      _ = bmSTS_J n f * (bmSTS_J n f * Matrix.transpose e * bmSTS_J n f) := by
          simp only [Matrix.mul_assoc]
      _ = bmSTS_J n f * e := by rw [h']
  have ha' : Matrix.mulVec e a = a := bmSTS_mulVec_eq_self_of_mem_range hee ha
  have hb' : Matrix.mulVec e b = 0 := by
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hb
  rw [Matrix.toBilin'_apply', ← ha',
    bmSTS_mulVec_dotProduct_of_transpose_mul_eq hEJ a b, hb']
  simp

private theorem bmSTS_blockExtend_orthogonal'
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
      b ∈ LinearMap.ker (Matrix.mulVecLin e) →
      ∀ a : (Fin n ⊕ Fin n) → GaloisField 2 f,
        a ∈ LinearMap.range (Matrix.mulVecLin e) →
        Matrix.toBilin' (bmSTS_J n f) b a = 0 := by
  intro b hb a ha
  have hee : e * e = e := he.2.1
  have hmap : e.map (⇑(RingHom.id (GaloisField 2 f))) = e := Matrix.map_id e
  have h' : (bmSTS_J n f)⁻¹ * Matrix.transpose e * bmSTS_J n f = e := by
    simpa only [formAdj, hmap] using hadj
  have hJinv : (bmSTS_J n f)⁻¹ = bmSTS_J n f :=
    Matrix.inv_eq_left_inv (bmSTS_J_mul_self n f)
  rw [hJinv] at h'
  have hEJ : Matrix.transpose e * bmSTS_J n f = bmSTS_J n f * e := by
    calc Matrix.transpose e * bmSTS_J n f
        = (bmSTS_J n f * bmSTS_J n f) * (Matrix.transpose e * bmSTS_J n f) := by
          rw [bmSTS_J_mul_self, Matrix.one_mul]
      _ = bmSTS_J n f * (bmSTS_J n f * Matrix.transpose e * bmSTS_J n f) := by
          simp only [Matrix.mul_assoc]
      _ = bmSTS_J n f * e := by rw [h']
  have ha' : Matrix.mulVec e a = a := bmSTS_mulVec_eq_self_of_mem_range hee ha
  have hb' : Matrix.mulVec e b = 0 := by
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hb
  rw [Matrix.toBilin'_apply', ← ha', Matrix.mulVec_mulVec, ← hEJ, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hb']
  simp

private theorem bmSTS_blockExtend_decompose
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ a c : (Fin n ⊕ Fin n) → GaloisField 2 f,
      a ∈ LinearMap.range (Matrix.mulVecLin e) → c ∈ LinearMap.range (Matrix.mulVecLin e) →
      ∀ b d : (Fin n ⊕ Fin n) → GaloisField 2 f,
        b ∈ LinearMap.ker (Matrix.mulVecLin e) → d ∈ LinearMap.ker (Matrix.mulVecLin e) →
        Matrix.toBilin' (bmSTS_J n f) (a + b) (c + d) =
          Matrix.toBilin' (bmSTS_J n f) a c + Matrix.toBilin' (bmSTS_J n f) b d := by
  intro a c ha hc b d hb hd
  have h1 := bmSTS_blockExtend_orthogonal n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
    heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace a ha d hd
  have h2 := bmSTS_blockExtend_orthogonal' n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
    heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace b hb c hc
  simp only [map_add, LinearMap.add_apply]
  rw [h1, h2]
  ring

private theorem bmSTS_prodEquiv_prodCongr_apply {ι F : Type} [Field F]
    (p q : Submodule F (ι → F)) (hcompl : IsCompl p q) (Ae : p ≃ₗ[F] p) (x : ι → F) :
    ((Submodule.prodEquivOfIsCompl p q hcompl).symm.trans
      ((Ae.prodCongr (LinearEquiv.refl F q)).trans
        (Submodule.prodEquivOfIsCompl p q hcompl))) x =
      ↑(Ae ((Submodule.prodEquivOfIsCompl p q hcompl).symm x).1) +
      ↑((Submodule.prodEquivOfIsCompl p q hcompl).symm x).2 := by
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    Submodule.coe_prodEquivOfIsCompl']

private theorem bmSTS_ofInjective_trans_ofEq_coe {W E F : Type} [Field F]
    [AddCommGroup W] [Module F W] [AddCommGroup E] [Module F E]
    (f : W →ₗ[F] E) (hf : Function.Injective f) (g : E →ₗ[F] E)
    (h : LinearMap.range f = LinearMap.range g) (x : W) :
    (((LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ h)) x : E) = f x := by
  simp only [LinearEquiv.trans_apply, LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply]

private theorem bmSTS_ofInjective_trans_ofEq_symm {W E F : Type} [Field F]
    [AddCommGroup W] [Module F W] [AddCommGroup E] [Module F E]
    (f : W →ₗ[F] E) (hf : Function.Injective f) (g : E →ₗ[F] E)
    (h : LinearMap.range f = LinearMap.range g) (x : W) (hx : f x ∈ LinearMap.range g) :
    ((LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ h)).symm ⟨f x, hx⟩ = x := by
  have hcoe : (((LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ h)) x : E) = f x :=
    bmSTS_ofInjective_trans_ofEq_coe f hf g h x
  have hsub : ((LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ h)) x =
      (⟨f x, hx⟩ : LinearMap.range g) := Subtype.ext hcoe
  have := ((LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ h)).symm_apply_apply x
  rwa [hsub] at this

private theorem bmSTS_linearEquiv_to_GL_mulVecLin (f : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (T : (ι → GaloisField 2 f) ≃ₗ[GaloisField 2 f] (ι → GaloisField 2 f)) :
    Matrix.mulVecLin ((bmSTS_linearEquiv_to_GL f T : GL ι (GaloisField 2 f)) :
      Matrix ι ι (GaloisField 2 f)) = T.toLinearMap := by
  simp only [bmSTS_linearEquiv_to_GL]
  rw [← Matrix.GeneralLinearGroup.coe_toLin, MulEquiv.apply_symm_apply]
  rfl

private theorem bmSTS_blockExtend_apply
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K) :
    (∀ w : W,
      Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
        hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w) =
      eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) w)) ∧
    (∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
      b ∈ LinearMap.ker (Matrix.mulVecLin e) →
      Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
        hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) b = b) := by
  have hee : e * e = e := he.2.1
  have hL : IsIdempotentElem (Matrix.mulVecLin e :
      ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
        ((Fin n ⊕ Fin n) → GaloisField 2 f)) := by
    show (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e
    rw [← Matrix.mulVecLin_mul, hee]
  have hcompl := LinearMap.IsIdempotentElem.isCompl hL
  let φ : W ≃ₗ[GaloisField 2 f] LinearMap.range (Matrix.mulVecLin e) :=
    (LinearEquiv.ofInjective eW heWinj).trans (LinearEquiv.ofEq _ _ heW)
  let B : W ≃ₗ[GaloisField 2 f] W :=
    bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  let Ae : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[GaloisField 2 f]
      LinearMap.range (Matrix.mulVecLin e) := (φ.symm.trans B).trans φ
  let pr := Submodule.prodEquivOfIsCompl _ _ hcompl
  let Tg : ((Fin n ⊕ Fin n) → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      ((Fin n ⊕ Fin n) → GaloisField 2 f) :=
    pr.symm.trans ((Ae.prodCongr (LinearEquiv.refl (GaloisField 2 f) _)).trans pr)
  have hTg : bmSTS_blockEmbeddingEV_PSU_blockExtendEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂
      hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g = Tg := rfl
  have hM : Matrix.mulVecLin
      ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = Tg.toLinearMap := by
    rw [bmSTS_blockEmbeddingEV_PSU_blockExtend, hTg]
    exact bmSTS_linearEquiv_to_GL_mulVecLin f Tg
  have hTapply (x : (Fin n ⊕ Fin n) → GaloisField 2 f) :
      Tg x = ↑(Ae (pr.symm x).1) + ↑(pr.symm x).2 :=
    bmSTS_prodEquiv_prodCongr_apply (LinearMap.range (Matrix.mulVecLin e))
      (LinearMap.ker (Matrix.mulVecLin e)) hcompl Ae x
  refine ⟨?_, ?_⟩
  · intro w
    have hmem : eW w ∈ LinearMap.range (Matrix.mulVecLin e) := by
      rw [← heW]
      exact LinearMap.mem_range_self eW w
    have hpr : pr.symm (eW w) = (⟨eW w, hmem⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hcompl ⟨eW w, hmem⟩
    have hAe : (Ae ⟨eW w, hmem⟩ : (Fin n ⊕ Fin n) → GaloisField 2 f) = eW (B w) := by
      simp only [Ae, φ, LinearEquiv.trans_apply]
      rw [bmSTS_ofInjective_trans_ofEq_symm eW heWinj (Matrix.mulVecLin e) heW w hmem]
      exact bmSTS_ofInjective_trans_ofEq_coe eW heWinj (Matrix.mulVecLin e) heW (B w)
    have hval := hTapply (eW w)
    rw [hpr] at hval
    simp only [Submodule.coe_zero, add_zero] at hval
    rw [hAe] at hval
    change Matrix.mulVecLin
      ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w) = eW (B w)
    rw [hM]
    exact hval
  · intro b hb
    have hpr : pr.symm b = (0, (⟨b, hb⟩ : LinearMap.ker (Matrix.mulVecLin e))) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right _ _ hcompl ⟨b, hb⟩
    have hval := hTapply b
    rw [hpr] at hval
    simp only [map_zero, Submodule.coe_zero, zero_add] at hval
    change Matrix.mulVecLin
      ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b = b
    rw [hM]
    exact hval

private theorem bmSTS_suAction_isometry
    (m' f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (g : (ggU .PSU m' (max f 1)).K) :
    ∀ u v : Fin m' → GaloisField 2 (2 * max f 1),
      CFSG.ClassicalGroups.Unitary.herm
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1))
          (bmSTS_blockEmbeddingEV_PSU_suAction m' f g u)
          (bmSTS_blockEmbeddingEV_PSU_suAction m' f g v) =
        CFSG.ClassicalGroups.Unitary.herm
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)) u v := by
  intro u v
  let σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have e : ggU .PSU m' (max f 1) =
      ⟨Unitary.SU σ m',
        Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte, σ]
  have hK : (ggU .PSU m' (max f 1)).K = ↥(Unitary.SU σ m') := congrArg LieUniversal.K e
  let g' : ↥(Unitary.SU σ m') := hK ▸ g
  let M : ↥(Unitary.SUid σ m') :=
    Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) g'
  have haction : ∀ w : Fin m' → GaloisField 2 (2 * max f 1),
      bmSTS_blockEmbeddingEV_PSU_suAction m' f g w = M • w := by
    intro w
    simp only [bmSTS_blockEmbeddingEV_PSU_suAction]
    exact rfl
  rw [haction u, haction v]
  exact CFSG.ClassicalGroups.Unitary.herm_smul_smul σ M u v

private theorem bmSTS_herm_stdModuleEquiv
    (f m' : ℕ) (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (τ : K ≃+* K) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (u v : Fin m' → GaloisField 2 (2 * max f 1)) :
    CFSG.ClassicalGroups.Unitary.herm τ
        ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm u)
        ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm v) =
      (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm
        (CFSG.ClassicalGroups.Unitary.herm
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)) u v) := by
  have hcompat : ∀ c : K,
      (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank) (τ c) =
        CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
          ((bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank) c) := by
    intro c
    have hKcard : Nat.card K = 2 ^ (2 * max f 1) := bmSTS_natCard_of_finrank_two f K hKrank
    have hτne1 : τ ≠ 1 := by
      intro h
      exact hτne (by rw [h]; rfl)
    have hτ2mul : τ * τ = 1 := by
      ext x
      exact hτ2 x
    obtain ⟨-, hpow⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution_prime
        Nat.prime_two (by omega) hKcard hτne1 hτ2mul
    rw [hpow c, map_pow, CFSG.LieType.BorelTits.unitaryInvolution_apply]
    congr 1
    rw [Nat.mul_div_cancel_left (max f 1) (by norm_num : 0 < 2)]
  rw [CFSG.ClassicalGroups.Unitary.herm_def, CFSG.ClassicalGroups.Unitary.herm_def, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hu : ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm u) i =
      (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm (u i) := by
    simp only [bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv, LinearEquiv.piCongrRight_symm,
      LinearEquiv.piCongrRight_apply, AlgEquiv.toLinearEquiv_symm]
    rfl
  have hv : ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm v) i =
      (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm (v i) := by
    simp only [bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv, LinearEquiv.piCongrRight_symm,
      LinearEquiv.piCongrRight_apply, AlgEquiv.toLinearEquiv_symm]
    rfl
  rw [hu, hv, map_mul]
  congr 1
  have hc := hcompat ((bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm (u i))
  rw [AlgEquiv.apply_symm_apply] at hc
  have hc' := congrArg (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm hc
  rwa [AlgEquiv.symm_apply_apply] at hc'

private theorem bmSTS_stdAction_isometry
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K) :
    ∀ x y : Fin m' → K,
      CFSG.ClassicalGroups.Unitary.herm τ
          (bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
            h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x)
          (bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
            h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g y) =
        CFSG.ClassicalGroups.Unitary.herm τ x y := by
  intro x y
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) :=
    Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)
  let C : (Fin m' → K) ≃ₗ[GaloisField 2 f] (Fin m' → GaloisField 2 (2 * max f 1)) :=
    bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
  have hxy : ∀ z : Fin m' → K,
      bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g z =
        C.symm (bmSTS_blockEmbeddingEV_PSU_suAction m' f g (C z)) := fun z => rfl
  rw [hxy x, hxy y]
  calc CFSG.ClassicalGroups.Unitary.herm τ
        (C.symm (bmSTS_blockEmbeddingEV_PSU_suAction m' f g (C x)))
        (C.symm (bmSTS_blockEmbeddingEV_PSU_suAction m' f g (C y)))
      = (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm
          (CFSG.ClassicalGroups.Unitary.herm
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            (bmSTS_blockEmbeddingEV_PSU_suAction m' f g (C x))
            (bmSTS_blockEmbeddingEV_PSU_suAction m' f g (C y))) :=
          bmSTS_herm_stdModuleEquiv f m' K hKrank τ hτ2 hτne
            (bmSTS_blockEmbeddingEV_PSU_suAction m' f g (C x))
            (bmSTS_blockEmbeddingEV_PSU_suAction m' f g (C y))
    _ = (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm
          (CFSG.ClassicalGroups.Unitary.herm
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            (C x) (C y)) := by
          rw [bmSTS_suAction_isometry m' f g (C x) (C y)]
    _ = CFSG.ClassicalGroups.Unitary.herm τ (C.symm (C x)) (C.symm (C y)) :=
          (bmSTS_herm_stdModuleEquiv f m' K hKrank τ hτ2 hτne (C x) (C y)).symm
    _ = CFSG.ClassicalGroups.Unitary.herm τ x y := by
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

private theorem bmSTS_blockAction_isometry
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K) :
    ∀ x y : W,
      h (bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
          h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x)
        (bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
          h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g y) = h x y := by
  intro x y
  let Φ : W ≃ₗ[GaloisField 2 f] (Fin m' → K) :=
    bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace
  let A : (Fin m' → K) ≃ₗ[GaloisField 2 f] (Fin m' → K) :=
    bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  let B : W ≃ₗ[GaloisField 2 f] W :=
    bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  haveI : FiniteDimensional K W := FiniteDimensional.of_finrank_pos (by omega)
  have hspec := Classical.choose_spec (CFSG.Fischer.Classification.exists_linearEquiv_herm_of_form
      (bmSTS_blockEmbeddingEV_PSU_unitaryInvolution n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
      (bmSTS_blockEmbeddingEV_PSU_isHermForm n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
      hnd hrank)
  have hherm : ∀ a b : W, CFSG.ClassicalGroups.Unitary.herm τ (Φ a) (Φ b) = h a b := by
    intro a b
    simpa only [Φ, bmSTS_blockEmbeddingEV_PSU_hermEquiv, LinearEquiv.restrictScalars_apply]
      using hspec a b
  have hx : Φ (B x) = A (Φ x) := by
    simp only [B, A, Φ, bmSTS_blockEmbeddingEV_PSU_blockAction, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
  have hy : Φ (B y) = A (Φ y) := by
    simp only [B, A, Φ, bmSTS_blockEmbeddingEV_PSU_blockAction, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
  calc h (B x) (B y)
      = CFSG.ClassicalGroups.Unitary.herm τ (Φ (B x)) (Φ (B y)) := (hherm (B x) (B y)).symm
    _ = CFSG.ClassicalGroups.Unitary.herm τ (A (Φ x)) (A (Φ y)) := by rw [hx, hy]
    _ = CFSG.ClassicalGroups.Unitary.herm τ (Φ x) (Φ y) :=
          bmSTS_stdAction_isometry n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
            heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g _ _
    _ = h x y := hherm x y

private theorem bmSTS_Ae_isometry
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K) :
    ∀ w w' : W,
      Matrix.toBilin' (bmSTS_J n f)
          (eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K
            τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) w))
          (eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K
            τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) w')) =
        Matrix.toBilin' (bmSTS_J n f) (eW w) (eW w') := by
  intro w w'
  let B : W ≃ₗ[GaloisField 2 f] W :=
    bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  have hD : h (B w) (B w') = h w w' :=
    bmSTS_blockAction_isometry n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
      heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g w w'
  have htr : ∀ x y : W, eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW y) =
      Algebra.trace (GaloisField 2 f) K (h x y) := by
    intro x y
    simpa using htrace x y 1
  have hgoal : Matrix.toBilin' (bmSTS_J n f) (eW (B w)) (eW (B w')) =
      Matrix.toBilin' (bmSTS_J n f) (eW w) (eW w') := by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', htr (B w) (B w'), htr w w', hD]
  exact hgoal

private theorem bmSTS_blockExtend_form_of_components
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K)
    (horth : ∀ a : (Fin n ⊕ Fin n) → GaloisField 2 f,
      a ∈ LinearMap.range (Matrix.mulVecLin e) →
      ∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
        b ∈ LinearMap.ker (Matrix.mulVecLin e) →
        Matrix.toBilin' (bmSTS_J n f) a b = 0)
    (hdec : ∀ a c : (Fin n ⊕ Fin n) → GaloisField 2 f,
      a ∈ LinearMap.range (Matrix.mulVecLin e) → c ∈ LinearMap.range (Matrix.mulVecLin e) →
      ∀ b d : (Fin n ⊕ Fin n) → GaloisField 2 f,
        b ∈ LinearMap.ker (Matrix.mulVecLin e) → d ∈ LinearMap.ker (Matrix.mulVecLin e) →
        Matrix.toBilin' (bmSTS_J n f) (a + b) (c + d) =
          Matrix.toBilin' (bmSTS_J n f) a c + Matrix.toBilin' (bmSTS_J n f) b d)
    (happly : (∀ w : W,
      Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
        hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w) =
      eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) w)) ∧
    (∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
      b ∈ LinearMap.ker (Matrix.mulVecLin e) →
      Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
        hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) b = b))
    (hiso : ∀ w w' : W,
      Matrix.toBilin' (bmSTS_J n f)
          (eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K
            τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) w))
          (eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K
            τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) w')) =
        Matrix.toBilin' (bmSTS_J n f) (eW w) (eW w')) :
    ∀ x y : (Fin n ⊕ Fin n) → GaloisField 2 f,
      Matrix.toBilin' (bmSTS_J n f)
          (Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
            hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
              GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) x)
          (Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
            hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
              GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) y) =
        Matrix.toBilin' (bmSTS_J n f) x y := by
  intro x y
  have hee : e * e = e := he.2.1
  have hL : IsIdempotentElem (Matrix.mulVecLin e :
      ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
        ((Fin n ⊕ Fin n) → GaloisField 2 f)) := by
    show (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e
    rw [← Matrix.mulVecLin_mul, hee]
  have hcompl := LinearMap.IsIdempotentElem.isCompl hL
  let pr := Submodule.prodEquivOfIsCompl _ _ hcompl
  let a := (pr.symm x).1
  let b := (pr.symm x).2
  let c := (pr.symm y).1
  let d := (pr.symm y).2
  let M : GL (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  let A : W ≃ₗ[GaloisField 2 f] W :=
    bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  change Matrix.toBilin' (bmSTS_J n f)
      (Matrix.mulVec (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) x)
      (Matrix.mulVec (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) y) =
    Matrix.toBilin' (bmSTS_J n f) x y
  have hap1 : ∀ w : W,
      Matrix.mulVec (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w) =
        eW (A w) := happly.1
  have hap2 : ∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
      b ∈ LinearMap.ker (Matrix.mulVecLin e) →
      Matrix.mulVec (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b = b :=
    happly.2
  have hiso' : ∀ w w' : W,
      Matrix.toBilin' (bmSTS_J n f) (eW (A w)) (eW (A w')) =
        Matrix.toBilin' (bmSTS_J n f) (eW w) (eW w') := hiso
  have hx : x = ↑a + ↑b := by
    rw [← pr.apply_symm_apply x, Submodule.coe_prodEquivOfIsCompl']
  have hy : y = ↑c + ↑d := by
    rw [← pr.apply_symm_apply y, Submodule.coe_prodEquivOfIsCompl']
  obtain ⟨w, hw⟩ : ∃ w, eW w = ↑a := by
    have h : ↑a ∈ LinearMap.range eW := by rw [heW]; exact a.property
    exact LinearMap.mem_range.mp h
  obtain ⟨w', hw'⟩ : ∃ w', eW w' = ↑c := by
    have h : ↑c ∈ LinearMap.range eW := by rw [heW]; exact c.property
    exact LinearMap.mem_range.mp h
  have hMx : Matrix.mulVec (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) x =
      eW (A w) + ↑b := by
    rw [hx, Matrix.mulVec_add, hap2 ↑b b.property, ← hw, hap1 w]
  have hMy : Matrix.mulVec (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) y =
      eW (A w') + ↑d := by
    rw [hy, Matrix.mulVec_add, hap2 ↑d d.property, ← hw', hap1 w']
  rw [hMx, hMy]
  have hAr : eW (A w) ∈ LinearMap.range (Matrix.mulVecLin e) := by
    rw [← heW]; exact ⟨A w, rfl⟩
  have hAr' : eW (A w') ∈ LinearMap.range (Matrix.mulVecLin e) := by
    rw [← heW]; exact ⟨A w', rfl⟩
  have hwr : eW w ∈ LinearMap.range (Matrix.mulVecLin e) := by
    rw [← heW]; exact ⟨w, rfl⟩
  have hwr' : eW w' ∈ LinearMap.range (Matrix.mulVecLin e) := by
    rw [← heW]; exact ⟨w', rfl⟩
  rw [hdec (eW (A w)) (eW (A w')) hAr hAr' ↑b ↑d b.property d.property, hiso' w w',
    ← hdec (eW w) (eW w') hwr hwr' ↑b ↑d b.property d.property]
  rw [hw, hw', ← hx, ← hy]

private theorem bmSTS_blockExtend_form
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K) :
    ∀ x y : (Fin n ⊕ Fin n) → GaloisField 2 f,
      Matrix.toBilin' (bmSTS_J n f)
          (Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
            hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
              GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) x)
          (Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
            hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
              GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) y) =
        Matrix.toBilin' (bmSTS_J n f) x y :=
  bmSTS_blockExtend_form_of_components n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
    heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
    (bmSTS_blockExtend_orthogonal n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)
    (bmSTS_blockExtend_decompose n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)
    (bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g)
    (bmSTS_Ae_isometry n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g)

private theorem bmSTS_blockEmbeddingEV_PSU_blockSymp
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ g : (ggU .PSU m' (max f 1)).K,
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g ∈
      CFSG.Open.StatedSp n (GaloisField 2 f) := by
  intro g
  let M : GL (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  change M ∈ Subgroup.closure (fun A : GL (Fin n ⊕ Fin n) (GaloisField 2 f) =>
      Matrix.transpose (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        bmSTS_J n f * (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        bmSTS_J n f)
  apply Subgroup.subset_closure
  have hform := bmSTS_blockExtend_form n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
    heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  have hcomp : Matrix.toBilin' (Matrix.transpose (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) * bmSTS_J n f * (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f))) = Matrix.toBilin' (bmSTS_J n f) := by
    rw [← Matrix.toBilin'_comp]
    apply LinearMap.BilinForm.ext
    intro x y
    exact hform x y
  exact Matrix.toBilin'.injective hcomp

private noncomputable def bmSTS_blockEmbeddingEV_PSU_blockFun
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    (ggU .PSU m' (max f 1)).K → ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) :=
  fun g => ⟨bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
    h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g,
    bmSTS_blockEmbeddingEV_PSU_blockSymp n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g⟩

private lemma bmSTS_cast_one_eq_one {A B : LieUniversal} (e : A = B) :
    (congrArg LieUniversal.K e) ▸ (1 : A.K) = (1 : B.K) := by
  cases e
  rfl

private lemma bmSTS_cast_mul {A B : LieUniversal} (e : A = B) (g g' : A.K) :
    (congrArg LieUniversal.K e) ▸ (g * g') =
      ((congrArg LieUniversal.K e) ▸ g) * ((congrArg LieUniversal.K e) ▸ g') := by
  cases e
  rfl

private lemma bmSTS_conj_mul {F : Type} [Field F] {A B : Type} [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] (φ : A ≃ₗ[F] B) (X Y : A ≃ₗ[F] A) :
    (φ.symm.trans (X.trans φ)) * (φ.symm.trans (Y.trans φ)) =
      φ.symm.trans ((X * Y).trans φ) := by
  apply LinearEquiv.ext
  intro x
  simp only [LinearEquiv.mul_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

private lemma bmSTS_prodCongr_mul_refl {F : Type} [Field F] {M N : Type}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (A B : M ≃ₗ[F] M) :
    (A.prodCongr (LinearEquiv.refl F N)) * (B.prodCongr (LinearEquiv.refl F N)) =
      (A * B).prodCongr (LinearEquiv.refl F N) := by
  apply LinearEquiv.ext
  rintro ⟨m, n⟩
  simp only [LinearEquiv.mul_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]

private theorem bmSTS_suAction_mul
    (m' f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (g g' : (ggU .PSU m' (max f 1)).K) :
    bmSTS_blockEmbeddingEV_PSU_suAction m' f (g * g') =
      (bmSTS_blockEmbeddingEV_PSU_suAction m' f g).comp
        (bmSTS_blockEmbeddingEV_PSU_suAction m' f g') := by
  let σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have e : ggU .PSU m' (max f 1) =
      ⟨Unitary.SU σ m',
        Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte, σ]
  have hK : (ggU .PSU m' (max f 1)).K = ↥(Unitary.SU σ m') := congrArg LieUniversal.K e
  let A : ↥(Unitary.SU σ m') →
      (Fin m' → GaloisField 2 (2 * max f 1)) →ₗ[GaloisField 2 f]
        (Fin m' → GaloisField 2 (2 * max f 1)) := fun x =>
    (Matrix.mulVecLin ((Unitary.conjEquiv (bmSTS_antidiagConj m' f)
      (bmSTS_antidiagConj_spec m' f) x).1 :
        Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))).restrictScalars
      (GaloisField 2 f)
  change A (hK ▸ (g * g')) = (A (hK ▸ g)).comp (A (hK ▸ g'))
  have hcast : hK ▸ (g * g') = (hK ▸ g) * (hK ▸ g') := bmSTS_cast_mul e g g'
  rw [hcast]
  dsimp only [A]
  rw [map_mul]
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mulVecLin_mul,
    LinearMap.restrictScalars_comp]

private theorem bmSTS_stdActionMap_mul
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ g g' : (ggU .PSU m' (max f 1)).K,
      bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (g * g') =
      (bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).comp
        (bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
          h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g') := by
  intro g g'
  dsimp only [bmSTS_blockEmbeddingEV_PSU_stdActionMap]
  rw [bmSTS_suAction_mul]
  ext x
  simp

private theorem bmSTS_stdAction_mul
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ g g' : (ggU .PSU m' (max f 1)).K,
      bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (g * g') =
      bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g *
      bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g' := by
  intro g g'
  apply LinearEquiv.ext
  intro x
  simp only [bmSTS_blockEmbeddingEV_PSU_stdAction, LinearEquiv.ofBijective_apply,
    LinearEquiv.mul_apply, bmSTS_stdActionMap_mul, LinearMap.comp_apply]
  rfl

private theorem bmSTS_blockAction_mul
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ g g' : (ggU .PSU m' (max f 1)).K,
      bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (g * g') =
      bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g *
      bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g' := by
  intro g g'
  apply LinearEquiv.ext
  intro x
  simp only [bmSTS_blockEmbeddingEV_PSU_blockAction, LinearEquiv.trans_apply,
    LinearEquiv.mul_apply]
  rw [bmSTS_stdAction_mul, LinearEquiv.mul_apply]
  simp

private theorem bmSTS_blockExtendEquiv_mul
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ g g' : (ggU .PSU m' (max f 1)).K,
      bmSTS_blockEmbeddingEV_PSU_blockExtendEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (g * g') =
      bmSTS_blockEmbeddingEV_PSU_blockExtendEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g *
      bmSTS_blockEmbeddingEV_PSU_blockExtendEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g' := by
  intro g g'
  have hee : e * e = e := he.2.1
  have hL : IsIdempotentElem (Matrix.mulVecLin e :
      ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
        ((Fin n ⊕ Fin n) → GaloisField 2 f)) := by
    show (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e
    rw [← Matrix.mulVecLin_mul, hee]
  have hcompl := LinearMap.IsIdempotentElem.isCompl hL
  let φ : W ≃ₗ[GaloisField 2 f] LinearMap.range (Matrix.mulVecLin e) :=
    (LinearEquiv.ofInjective eW heWinj).trans (LinearEquiv.ofEq _ _ heW)
  let pc : (LinearMap.range (Matrix.mulVecLin e) ×
      LinearMap.ker (Matrix.mulVecLin e)) ≃ₗ[GaloisField 2 f]
        ((Fin n ⊕ Fin n) → GaloisField 2 f) :=
    Submodule.prodEquivOfIsCompl _ _ hcompl
  have hblock : ∀ g : (ggU .PSU m' (max f 1)).K,
      bmSTS_blockEmbeddingEV_PSU_blockExtendEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g =
      pc.symm.trans (((φ.symm.trans
        ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
          h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).trans φ)).prodCongr
        (LinearEquiv.refl (GaloisField 2 f)
          (LinearMap.ker (Matrix.mulVecLin e)))).trans pc) := by
    intro g
    rfl
  rw [hblock (g * g'), hblock g, hblock g']
  rw [bmSTS_blockAction_mul]
  rw [← bmSTS_conj_mul φ _ _]
  rw [← bmSTS_prodCongr_mul_refl]
  rw [← bmSTS_conj_mul pc _ _]

private theorem bmSTS_suAction_one
    (m' f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))] :
    bmSTS_blockEmbeddingEV_PSU_suAction m' f (1 : (ggU .PSU m' (max f 1)).K) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  let σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have e : ggU .PSU m' (max f 1) =
      ⟨Unitary.SU σ m',
        Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte, σ]
  have hK : (ggU .PSU m' (max f 1)).K = ↥(Unitary.SU σ m') := congrArg LieUniversal.K e
  let g' : ↥(Unitary.SU σ m') := hK ▸ (1 : (ggU .PSU m' (max f 1)).K)
  let M : ↥(Unitary.SUid σ m') :=
    Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) g'
  have hg' : g' = 1 := by
    show hK ▸ (1 : (ggU .PSU m' (max f 1)).K) = (1 : ↥(Unitary.SU σ m'))
    exact bmSTS_cast_one_eq_one e
  have hM : M = 1 := by
    show Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) g' = 1
    rw [hg', map_one]
  have haction : bmSTS_blockEmbeddingEV_PSU_suAction m' f
      (1 : (ggU .PSU m' (max f 1)).K) v = M • v := by
    simp only [bmSTS_blockEmbeddingEV_PSU_suAction]
    exact rfl
  rw [haction, hM, one_smul]
  rfl

private theorem bmSTS_linearEquiv_to_GL_refl (f : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] :
    bmSTS_linearEquiv_to_GL f (LinearEquiv.refl (GaloisField 2 f) (ι → GaloisField 2 f)) = 1 := by
  simp only [bmSTS_linearEquiv_to_GL]
  rw [show LinearMap.GeneralLinearGroup.ofLinearEquiv
      (LinearEquiv.refl (GaloisField 2 f) (ι → GaloisField 2 f)) = 1 from rfl]
  exact map_one _

private theorem bmSTS_linearEquiv_to_GL_mul (f : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (T S : (ι → GaloisField 2 f) ≃ₗ[GaloisField 2 f] (ι → GaloisField 2 f)) :
    bmSTS_linearEquiv_to_GL f (T * S) =
      bmSTS_linearEquiv_to_GL f T * bmSTS_linearEquiv_to_GL f S := by
  simp only [bmSTS_linearEquiv_to_GL]
  rw [LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]
  exact map_mul _ _ _

private lemma bmSTS_refl_prodCongr {F : Type} [Field F] {M N : Type}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N] :
    (LinearEquiv.refl F M).prodCongr (LinearEquiv.refl F N) =
      LinearEquiv.refl F (M × N) := by
  apply LinearEquiv.ext
  rintro ⟨a, b⟩
  rfl

private theorem bmSTS_blockEmbeddingEV_PSU_blockOne
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    bmSTS_blockEmbeddingEV_PSU_blockFun n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace 1 = 1 := by
  apply Subtype.ext
  change bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
    h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
    (1 : (ggU .PSU m' (max f 1)).K) = 1
  rw [bmSTS_blockEmbeddingEV_PSU_blockExtend]
  have hstdMap : bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂
      hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
      (1 : (ggU .PSU m' (max f 1)).K) = LinearMap.id := by
    letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) :=
      Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)
    simp only [bmSTS_blockEmbeddingEV_PSU_stdActionMap]
    rw [bmSTS_suAction_one]
    apply LinearMap.ext
    intro x
    simp
  have hstdAction : bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂
      hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
      (1 : (ggU .PSU m' (max f 1)).K) =
      LinearEquiv.refl (GaloisField 2 f) (Fin m' → K) := by
    apply LinearEquiv.ext
    intro x
    simp only [bmSTS_blockEmbeddingEV_PSU_stdAction, hstdMap]
    rfl
  have hblockAction : bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁
      hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
      (1 : (ggU .PSU m' (max f 1)).K) = LinearEquiv.refl (GaloisField 2 f) W := by
    simp only [bmSTS_blockEmbeddingEV_PSU_blockAction]
    rw [hstdAction]
    simp
  have hblockExtendEquiv : bmSTS_blockEmbeddingEV_PSU_blockExtendEquiv n f S hSU hS hodd he hadj
      hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
      (1 : (ggU .PSU m' (max f 1)).K) =
      LinearEquiv.refl (GaloisField 2 f) ((Fin n ⊕ Fin n) → GaloisField 2 f) := by
    simp only [bmSTS_blockEmbeddingEV_PSU_blockExtendEquiv]
    rw [hblockAction]
    rw [LinearEquiv.trans_refl, LinearEquiv.symm_trans_self, bmSTS_refl_prodCongr,
      LinearEquiv.refl_trans, LinearEquiv.symm_trans_self]
  rw [hblockExtendEquiv]
  exact bmSTS_linearEquiv_to_GL_refl f

private theorem bmSTS_blockEmbeddingEV_PSU_blockMul
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ g g' : (ggU .PSU m' (max f 1)).K,
      bmSTS_blockEmbeddingEV_PSU_blockFun n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (g * g') =
      bmSTS_blockEmbeddingEV_PSU_blockFun n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g *
      bmSTS_blockEmbeddingEV_PSU_blockFun n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g' := by
  intro g g'
  apply Subtype.ext
  change bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
    h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (g * g') =
    bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g *
    bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g'
  simp only [bmSTS_blockEmbeddingEV_PSU_blockExtend]
  rw [bmSTS_blockExtendEquiv_mul]
  rw [bmSTS_linearEquiv_to_GL_mul]

private noncomputable def bmSTS_blockEmbeddingEV_PSU_hom
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    (ggU .PSU m' (max f 1)).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) :=
  { toFun := bmSTS_blockEmbeddingEV_PSU_blockFun n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
    map_one' := bmSTS_blockEmbeddingEV_PSU_blockOne n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
    map_mul' := bmSTS_blockEmbeddingEV_PSU_blockMul n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace }

private theorem bmSTS_blockEmbeddingEV_PSU_hom_injective
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    Function.Injective
      (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace) := by
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) :=
    Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)
  have hker : ∀ x : (ggU .PSU m' (max f 1)).K,
      bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x = 1 → x = 1 := by
    intro x hx
    have hExt : bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x = 1 := by
      have hx' := congrArg Subtype.val hx
      change bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x = 1 at hx'
      exact hx'
    have hBA : bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x =
        LinearEquiv.refl (GaloisField 2 f) W := by
      apply LinearEquiv.ext
      intro w
      have hw := (bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x).1 w
      rw [hExt] at hw
      have hw' : eW w =
          eW (bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
            h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x w) := by
        simpa using hw
      exact (heWinj hw').symm
    have hStdA : bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x =
        LinearEquiv.refl (GaloisField 2 f) (Fin m' → K) := by
      apply LinearEquiv.ext
      intro v
      let C := bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace
      have hblk := hBA
      simp only [bmSTS_blockEmbeddingEV_PSU_blockAction] at hblk
      change C.trans ((bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂
          hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x).trans C.symm) =
          LinearEquiv.refl (GaloisField 2 f) W at hblk
      have hv := congrArg (fun (T : W ≃ₗ[GaloisField 2 f] W) => T (C.symm v)) hblk
      have hc : C.symm (bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂
          hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x v) =
          C.symm v := by
        simpa only [LinearEquiv.trans_apply, C.apply_symm_apply, LinearEquiv.refl_apply] using hv
      simpa only [LinearEquiv.refl_apply] using C.symm.injective hc
    have hStdMap : bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x = LinearMap.id := by
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun (T : (Fin m' → K) ≃ₗ[GaloisField 2 f] (Fin m' → K)) => T v) hStdA
      change bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace x v = v at hv
      simpa only [LinearMap.id_apply] using hv
    have hsu : bmSTS_blockEmbeddingEV_PSU_suAction m' f x = LinearMap.id := by
      apply LinearMap.ext
      intro u
      let C := bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
      obtain ⟨v, rfl⟩ := C.surjective u
      have hmap := hStdMap
      simp only [bmSTS_blockEmbeddingEV_PSU_stdActionMap] at hmap
      change C.symm.toLinearMap.comp
          ((bmSTS_blockEmbeddingEV_PSU_suAction m' f x).comp C.toLinearMap) = LinearMap.id at hmap
      have hv := congrArg (fun (f : (Fin m' → K) →ₗ[GaloisField 2 f] (Fin m' → K)) => f v) hmap
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply] at hv
      have hc := congrArg (fun y => C y) hv
      simpa only [C.apply_symm_apply, LinearMap.id_apply] using hc
    let σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
      CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
    have hf : 1 ≤ max f 1 := le_max_right f 1
    have heq : ggU .PSU m' (max f 1) =
        ⟨Unitary.SU σ m', Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte, σ]
    have hK : (ggU .PSU m' (max f 1)).K = ↥(Unitary.SU σ m') := congrArg LieUniversal.K heq
    let x' : ↥(Unitary.SU σ m') := hK ▸ x
    have hmat : ((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        x').1 : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) = 1 := by
      apply Matrix.mulVec_injective
      funext v
      have hv := congrArg (fun (f : (Fin m' → GaloisField 2 (2 * max f 1)) →ₗ[GaloisField 2 f]
          (Fin m' → GaloisField 2 (2 * max f 1))) => f v) hsu
      simpa only [x', bmSTS_blockEmbeddingEV_PSU_suAction, LinearMap.restrictScalars_apply,
        Matrix.mulVecLin_apply, LinearMap.id_apply, Matrix.one_mulVec] using hv
    have hM : Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) x' = 1 :=
      Subtype.ext (Units.ext hmat)
    have hx' : x' = 1 := by
      apply (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)).injective
      rw [hM, map_one]
    have hone : hK ▸ (1 : (ggU .PSU m' (max f 1)).K) = 1 := bmSTS_cast_one_eq_one heq
    have hx'' : hK ▸ x = 1 := by simpa only [x'] using hx'
    refine (Equiv.cast hK).injective ?_
    change hK ▸ x = hK ▸ (1 : (ggU .PSU m' (max f 1)).K)
    rw [hx'', hone]
  intro g g' h
  exact eq_of_mul_inv_eq_one
    (hker (g * g'⁻¹) (by rw [map_mul, map_inv, h, mul_inv_cancel]))

private theorem bmSTS_blockExtend_mul_one_sub_e
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K) :
    ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) * (1 - e) = 1 - e := by
  have hker : ∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
      b ∈ LinearMap.range (Matrix.mulVecLin (1 - e)) →
      Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
        hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) b = b := by
    intro b hb
    obtain ⟨v, rfl⟩ := hb
    have hbker : Matrix.mulVecLin (1 - e) v ∈ LinearMap.ker (Matrix.mulVecLin e) := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, IsIdempotentElem.mul_one_sub_self he.2.1, Matrix.zero_mulVec]
    exact (bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).2 _ hbker
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec]
  exact hker (Matrix.mulVec (1 - e) v)
    (by simpa only [Matrix.mulVecLin_apply] using
      LinearMap.mem_range_self (Matrix.mulVecLin (1 - e)) v)

private theorem bmSTS_blockExtend_commute_S
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g)
    (g : (ggU .PSU m' (max f 1)).K) :
    bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g ∈
        Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact (hcommS g s hs).symm

private theorem bmSTS_blockEmbeddingEV_PSU_hom_range_le_centralizer
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range ≤
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e) := by
  intro u hu
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hu
  rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · change bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g ∈ Subgroup.centralizer S
    exact bmSTS_blockExtend_commute_S n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hcommS g
  · change ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) * (1 - e) = 1 - e
    exact bmSTS_blockExtend_mul_one_sub_e n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g

private theorem bmSTS_fieldAut_invol_eq_pow {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ q : ℕ, q * q = Nat.card K ∧ ∀ x : K, σ x = x ^ q := by
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite K p
  haveI hpF : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right hp0⟩
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Fintype (ZMod p) := Fintype.ofFinite _
  have hcard : p ^ Module.finrank (ZMod p) K = Nat.card K :=
    FiniteField.pow_finrank_eq_natCard p K
  have hcomm : ∀ x : ZMod p, σ (algebraMap (ZMod p) K x) = algebraMap (ZMod p) K x := by
    intro x
    have h : σ.toRingHom.comp (algebraMap (ZMod p) K) = algebraMap (ZMod p) K :=
      RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x
  obtain ⟨τ, hτdef⟩ : ∃ τ : K ≃ₐ[ZMod p] K, ∀ x, τ x = σ x :=
    ⟨AlgEquiv.ofRingEquiv (f := σ) hcomm, fun x => rfl⟩
  have hτ2 : τ * τ = 1 := by
    ext x
    have h := congrArg (fun g : K ≃+* K => g x) hσ2
    rw [AlgEquiv.mul_apply, hτdef, hτdef]
    exact h
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hσ1
    ext x
    have h' := congrArg (fun g : K ≃ₐ[ZMod p] K => g x) h
    rw [← hτdef]
    exact h'
  obtain ⟨φ, hφdef⟩ : ∃ φ : K ≃ₐ[ZMod p] K,
      φ = FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K := ⟨_, rfl⟩
  have hord : orderOf φ = Module.finrank (ZMod p) K := by
    rw [hφdef]
    exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) K
  obtain ⟨a, ha⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) K).2 τ
  obtain ⟨j, hjτ⟩ : ∃ j : ℕ, φ ^ j = τ := ⟨a.1, by rw [hφdef]; exact ha⟩
  have h1 : φ ^ (j * 2) = 1 := by
    rw [pow_mul, hjτ, sq, hτ2]
  have h2 : ¬ orderOf φ ∣ j := by
    intro hd
    apply hτ1
    rw [← hjτ, orderOf_dvd_iff_pow_eq_one.mp hd]
  have h3 : orderOf φ ∣ j * 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
  rw [hord] at h2 h3
  obtain ⟨k, hk⟩ : 2 ∣ Module.finrank (ZMod p) K := by
    by_contra hodd
    have hc : Nat.Coprime (Module.finrank (ZMod p) K) 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    exact h2 (hc.dvd_of_dvd_mul_right h3)
  have h5 : k ∣ j := by
    have h3' : 2 * k ∣ 2 * j := by
      rw [← hk, mul_comm 2 j]
      exact h3
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3'
  obtain ⟨t, rfl⟩ := h5
  have ht : Odd t := by
    rcases Nat.even_or_odd t with ⟨s, hs⟩ | ht
    · exfalso
      apply h2
      refine ⟨s, ?_⟩
      rw [hk, hs]
      ring
    · exact ht
  obtain ⟨s, rfl⟩ := ht
  have hφf : φ ^ Module.finrank (ZMod p) K = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one φ
  have hτk : τ = φ ^ k := by
    rw [← hjτ]
    have hexp : k * (2 * s + 1) = k + Module.finrank (ZMod p) K * s := by
      rw [hk]
      ring
    rw [hexp, pow_add, pow_mul, hφf, one_pow, mul_one]
  have hiter : ∀ (n : ℕ) (x : K), (φ ^ n) x = x ^ (p ^ n) := by
    intro n x
    rw [hφdef, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]
  refine ⟨p ^ k, ?_, fun x => ?_⟩
  · rw [← hcard, hk, two_mul, pow_add]
  · have h : τ x = (φ ^ k) x := by rw [hτk]
    rw [← hτdef, h, hiter]

private theorem bmSTS_SUid_two_isPerfect
    (f : ℕ)
    (σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1))
    (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ)
    (hcard : Nat.card (GaloisField 2 (2 * max f 1)) = (2 ^ max f 1) ^ 2)
    (hq : 4 ≤ 2 ^ max f 1) :
    Group.IsPerfect (Unitary.SUid σ 2) := by
  have hσ2 : σ * σ = 1 := RingEquiv.ext fun c => hσ.invol c
  have hσ1 : σ ≠ 1 := by
    obtain ⟨c, hc⟩ := hσ.exists_ne
    intro h
    exact hc (DFunLike.congr_fun h c)
  obtain ⟨q, hq2, hpow⟩ := bmSTS_fieldAut_invol_eq_pow hσ2 hσ1
  have hq' : q = 2 ^ max f 1 := by
    rw [hcard, pow_two] at hq2
    exact Nat.mul_self_inj.mp hq2
  have hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1) := by
    ext x
    rw [hpow x, hq', CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [hσeq]
  haveI hchar : CharP (GaloisField 2 (2 * max f 1)) 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq hcard
  obtain ⟨e⟩ := CFSG.SectionRank.EvenCover.nonempty_sl2_mulEquiv_SUid_two
    (K := GaloisField 2 (2 * max f 1)) (f := max f 1) hcard
  have h4 : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hcard]
    exact hq
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card
    (CFSG.LieType.Steinberg.fixedSubfield (GaloisField 2 (2 * max f 1)) 2 (max f 1)) h4
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

private theorem bmSTS_blockEmbeddingEV_PSU_hom_range_perfect
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range ≤
      ⁅(bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range,
        (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range⁆ := by
  let ι₀ := bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
    heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
  change ι₀.range ≤ ⁅ι₀.range, ι₀.range⁆
  haveI hperfRange : Group.IsPerfect ↥ι₀.range := by
    let σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
      CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
    have hcard : Nat.card (GaloisField 2 (2 * max f 1)) = (2 ^ max f 1) ^ 2 :=
      bmSTS_natCard_galoisField_twoMax_sq f
    haveI hchar : CharP (GaloisField 2 (2 * max f 1)) 2 :=
      CFSG.ClassicalGroups.Unitary.charP_of_card_sq hcard
    have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ :=
      CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hcard
    haveI hperfSUid : Group.IsPerfect (Unitary.SUid σ m') := by
      by_cases h3 : 3 ≤ m'
      · refine CFSG.ClassicalGroups.Unitary.isPerfect_SUid hσ h3 ?_
        intro hm3eq
        have hq2 : 2 ^ max f 1 ≠ 2 := by
          rcases hnq with hq | h4
          · exact hq
          · omega
        have hne := CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hcard hq2
        simpa [σ] using hne
      · have hm2 : m' = 2 := by omega
        have h4 : 4 ≤ 2 ^ max f 1 := by
          rcases hnq with hne | h4
          · have hle : 1 ≤ max f 1 := le_max_right f 1
            have hne1 : max f 1 ≠ 1 := by
              intro h1
              exact hne (by rw [h1]; norm_num)
            have h2 : 2 ≤ max f 1 := by omega
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ max f 1 := Nat.pow_le_pow_right (by norm_num) h2
          · omega
        rw [hm2]
        exact bmSTS_SUid_two_isPerfect f σ hσ hcard h4
    have hperfSU : Group.IsPerfect (Unitary.SU σ m') :=
      let e := (Unitary.conjEquiv (bmSTS_antidiagConj m' f)
        (bmSTS_antidiagConj_spec m' f)).symm
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    haveI hperfD : Group.IsPerfect (ggU .PSU m' (max f 1)).K := by
      have hf : 1 ≤ max f 1 := le_max_right f 1
      have e : ggU .PSU m' (max f 1) =
          ⟨Unitary.SU σ m',
            Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
        simp only [ggU, lieUniversal, hf, ↓reduceDIte, σ]
      rw [e]
      exact hperfSU
    exact Group.IsPerfect.range ι₀
  exact le_of_eq (Subgroup.commutator_eq_self (H := ι₀.range)).symm

private theorem bmSTS_blockEmbeddingEV_PSU_hom_range_le_derived
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range ≤
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆ := by
  have h1 := bmSTS_blockEmbeddingEV_PSU_hom_range_le_centralizer n f S hSU hS hodd he hadj
    hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hcommS
  have h2 := bmSTS_blockEmbeddingEV_PSU_hom_range_perfect n f S hSU hS hodd he hadj
    hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace
  exact h2.trans (Subgroup.commutator_mono h1 h1)

private theorem bmSTS_commutator_mem_ker_of_commutative
    {G A : Type*} [Group G] [CommGroup A] (φ : G →* A) (x y : G) :
    ⁅x, y⁆ ∈ φ.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (mul_comm (φ x) (φ y))

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_fixes_ker
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
    (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e) :
    ∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
      b ∈ LinearMap.ker (Matrix.mulVecLin e) →
      Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) b = b := by
  intro b hb
  have hz : (⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) ∈
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e :=
    Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator hx hy)
  have hmat : (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) * (1 - e) = 1 - e :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hz)).2
  have hb0 : Matrix.mulVec e b = 0 := by
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hb
  have hb' : Matrix.mulVec (1 - e) b = b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hb0, sub_zero]
  calc Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) b
      = Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (Matrix.mulVec (1 - e) b) := by rw [hb']
    _ = Matrix.mulVec ((((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) * (1 - e)) b := by rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (1 - e) b := by rw [hmat]
    _ = b := hb'

private lemma bmSTS_mulVec_mem_range_of_commute
    {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {e A : Matrix ι ι F} (h : Commute A e) :
    ∀ v : ι → F, v ∈ LinearMap.range (Matrix.mulVecLin e) →
      Matrix.mulVec A v ∈ LinearMap.range (Matrix.mulVecLin e) := by
  rintro v ⟨w, rfl⟩
  refine ⟨Matrix.mulVec A w, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h.eq]

private lemma bmSTS_units_commutator_commute
    {M : Type*} [Monoid M] {e : M} (a b : Mˣ)
    (ha : Commute (a : M) e) (hb : Commute (b : M) e) :
    Commute (((a * b * a⁻¹ * b⁻¹ : Mˣ) : M)) e := by
  have hai : Commute ((a⁻¹ : Mˣ) : M) e := by simpa using ha.units_inv_left
  have hbi : Commute ((b⁻¹ : Mˣ) : M) e := by simpa using hb.units_inv_left
  simpa only [Units.val_mul] using ((ha.mul_left hb).mul_left hai).mul_left hbi

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_stabilizes_range
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
    (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e) :
    ∀ v : (Fin n ⊕ Fin n) → GaloisField 2 f,
      v ∈ LinearMap.range (Matrix.mulVecLin e) →
      Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) v ∈ LinearMap.range (Matrix.mulVecLin e) := by
  have hmat_comm : ∀ z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)),
      z ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e →
      ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e =
      e * ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
    intro z hz
    obtain ⟨hzS, -⟩ := Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hz)
    have hgen : ∀ s ∈ Units.val '' S,
        ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * s =
        s * ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
      rintro s ⟨u, hu, rfl⟩
      have h := (Subgroup.mem_centralizer_iff.mp hzS) u hu
      have h' := congrArg
        (fun w : GL (Fin n ⊕ Fin n) (GaloisField 2 f) =>
          (w : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) h
      have h'' : ((u : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
          ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
          ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
          ((u : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
        simpa using h'
      exact h''.symm
    exact Algebra.adjoin_induction
      (p := fun a _ => ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * a =
        a * ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))
      hgen (fun r => (Algebra.commute_algebraMap_right r
        ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))).eq)
      (fun a b _ _ ha hb => by rw [mul_add, add_mul, ha, hb])
      (fun a b _ _ ha hb => (Commute.mul_right ha hb).eq) he
  have hxmat : Commute
      (((x : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e := hmat_comm x hx
  have hymat : Commute
      (((y : GL (Fin n ⊕ Fin n) (GaloisField 2 f))) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e := hmat_comm y hy
  have hzu : Commute
      ((((x : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (x : GL (Fin n ⊕ Fin n) (GaloisField 2 f))⁻¹ *
        (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f))⁻¹ : GL (Fin n ⊕ Fin n)
          (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) e :=
    bmSTS_units_commutator_commute (x : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
      (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) hxmat hymat
  have hz : (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      ((((x : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (x : GL (Fin n ⊕ Fin n) (GaloisField 2 f))⁻¹ *
        (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f))⁻¹ : GL (Fin n ⊕ Fin n)
          (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) := by
    congr 1
  rw [hz]
  exact bmSTS_mulVec_mem_range_of_commute hzu

private lemma bmSTS_exists_linearMap_of_stabilizes_range
    {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (eW : W →ₗ[F] V) (heWinj : Function.Injective eW)
    (R : Submodule F V) (heW : LinearMap.range eW = R)
    (A : V →ₗ[F] V) (hstab : ∀ v ∈ R, A v ∈ R) :
    ∃ T : W →ₗ[F] W, ∀ w : W, eW (T w) = A (eW w) := by
  let f : W →ₗ[F] R := eW.codRestrict R (fun w => by
    rw [← heW]
    exact ⟨w, rfl⟩)
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply heWinj
    have h := congrArg (Subtype.val) hab
    simpa only [f, LinearMap.codRestrict_apply] using h
  have hf_surj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    rw [← heW] at hv
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, Subtype.ext (by simpa only [f, LinearMap.codRestrict_apply] using hw)⟩
  let φ : W ≃ₗ[F] R := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let g : R →ₗ[F] R := (A.comp R.subtype).codRestrict R (fun v => hstab (v : V) v.2)
  let T : W →ₗ[F] W := (φ.symm : R →ₗ[F] W).comp (g.comp (φ : W →ₗ[F] R))
  refine ⟨T, fun w => ?_⟩
  have hφw : ((φ w : R) : V) = eW w := rfl
  have hg : ((g (φ w) : R) : V) = A (eW w) := by
    change A ((φ w : R) : V) = A (eW w)
    rw [hφw]
  have hT : ((φ (T w) : R) : V) = A (eW w) := by
    have h1 : φ (T w) = g (φ w) := by
      change φ (φ.symm (g (φ w))) = g (φ w)
      exact LinearEquiv.apply_symm_apply φ (g (φ w))
    rw [h1]
    exact hg
  have hφT : ((φ (T w) : R) : V) = eW (T w) := rfl
  rw [← hφT]
  exact hT

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_exists
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
      ∀ y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        ∃ T : W →ₗ[GaloisField 2 f] W,
          ∀ w : W,
            eW (T w) =
              Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
                GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) (eW w) := by
  intro x hx y hy
  let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    ((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) : GL (Fin n ⊕ Fin n)
      (GaloisField 2 f))
  have hstab : ∀ v : (Fin n ⊕ Fin n) → GaloisField 2 f,
      v ∈ LinearMap.range (Matrix.mulVecLin e) →
      (Matrix.mulVecLin M) v ∈ LinearMap.range (Matrix.mulVecLin e) := by
    intro v hv
    simpa only [Matrix.mulVecLin_apply, M] using
      bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_stabilizes_range
        n f S he.1 x y hx hy v hv
  obtain ⟨T, hT⟩ := bmSTS_exists_linearMap_of_stabilizes_range eW heWinj
    (LinearMap.range (Matrix.mulVecLin e)) heW (Matrix.mulVecLin M) hstab
  exact ⟨T, fun w => by simpa only [Matrix.mulVecLin_apply, M] using hT w⟩

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_isKLinear
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
      ∀ y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        ∀ T : W →ₗ[GaloisField 2 f] W,
          (∀ w : W,
            eW (T w) =
              Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
                GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) (eW w)) →
          (∀ w w' : W, h (T w) (T w') = h w w') →
          ∀ (c : K) (w : W), T (c • w) = c • T w := by
  intro x hx y hy T hT hiso c w
  haveI : FiniteDimensional (GaloisField 2 f) K := Module.Finite.of_finite
  haveI : FiniteDimensional K W := FiniteDimensional.of_finrank_pos (by omega)
  haveI : FiniteDimensional (GaloisField 2 f) W :=
    FiniteDimensional.trans (GaloisField 2 f) K W
  have hsmul : ∀ (c : K) (u v : W), h (c • u) v = τ c * h u v := by
    intro c u v
    rw [← hτ2 (h (c • u) v), ← hsymm (c • u) v, (h v).map_smul, smul_eq_mul,
      map_mul, hsymm u v, hτ2]
  have hsub_fst : ∀ (u u' v : W), h (u - u') v = h u v - h u' v := by
    intro u u' v
    rw [← hτ2 (h (u - u') v), ← hsymm (u - u') v, (h v).map_sub, map_sub,
      hsymm u v, hsymm u' v, hτ2, hτ2]
  have hinj : Function.Injective T := by
    intro a b hab
    have hsub : T (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hzero : a - b = 0 := by
      apply hnd
      intro y
      calc h (a - b) y = h (T (a - b)) (T y) := (hiso (a - b) y).symm
        _ = h 0 (T y) := by rw [hsub]
        _ = 0 := by
              have h0 := hsub_fst a a (T y)
              rw [sub_self] at h0
              rw [h0, sub_self]
    exact sub_eq_zero.mp hzero
  have hsurj : Function.Surjective T := LinearMap.surjective_of_injective hinj
  have hz : T (c • w) - c • T w = 0 := by
    apply hnd
    intro y
    obtain ⟨y', rfl⟩ := hsurj y
    have hsplit := hsub_fst (T (c • w)) (c • T w) (T y')
    rw [hsplit, hiso, hsmul c (T w) (T y'), hiso w y', ← hsmul c w y']
    exact sub_self _
  exact sub_eq_zero.mp hz

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_isometry
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w) :
    ∀ x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
      ∀ y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        ∀ T : W →ₗ[GaloisField 2 f] W,
          (∀ w : W,
            eW (T w) =
              Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
                GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) (eW w)) →
          ∀ w w' : W, h (T w) (T w') = h w w' := by
  intro x hx y hy T hT w w'
  let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    ((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) : GL (Fin n ⊕ Fin n)
      (GaloisField 2 f))
  have hKlin : ∀ (c : K) (w : W), T (c • w) = c • T w :=
    hKlinRep x y hx hy T hT
  have hJ : ∀ u v : (Fin n ⊕ Fin n) → GaloisField 2 f,
      Matrix.mulVec M u ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (Matrix.mulVec M v) =
        u ⬝ᵥ Matrix.mulVec (bmSTS_J n f) v := by
    intro u v
    have hM : Matrix.transpose M * bmSTS_J n f * M = bmSTS_J n f := by
      have h := (CFSG.Open.StatedAPI.mem_statedSp_iff).1
        ((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))).2)
      simpa only [M, bmSTS_J] using h
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hM, ← Matrix.dotProduct_mulVec]
  have hb : ∀ u v : W, Algebra.trace (GaloisField 2 f) K (h (T u) (T v)) =
      Algebra.trace (GaloisField 2 f) K (h u v) := by
    intro u v
    have hu := htrace (T u) (T v) 1
    have hv := htrace u v 1
    simp only [one_smul, one_mul] at hu hv
    rw [← hu, ← hv, hT u, hT v, hJ]
  have hzero : h (T w) (T w') - h w w' = 0 := by
    apply (traceForm_nondegenerate (GaloisField 2 f) K).1
    intro c
    rw [Algebra.traceForm_apply, mul_comm (h (T w) (T w') - h w w') c, mul_sub, map_sub]
    have h2 : c * h (T w) (T w') = h (T w) (T (c • w')) := by
      rw [hKlin c w', map_smul, smul_eq_mul]
    have h3 : c * h w w' = h w (c • w') := by
      rw [map_smul, smul_eq_mul]
    rw [h2, h3, hb w (c • w'), sub_self]
  exact sub_eq_zero.mp hzero

private theorem
    bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_isCommutator
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW)
    (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
    (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (Tk : W →ₗ[K] W)
    (hTk : ∀ w : W,
      eW (Tk w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) :
    ∃ A B : W ≃ₗ[K] W, Tk = (↑(A * B * A⁻¹ * B⁻¹) : W →ₗ[K] W) := by
  obtain ⟨ρ, hρ⟩ := hKlinRepC
  let xC : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e := ⟨x, hx⟩
  let yC : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e := ⟨y, hy⟩
  refine ⟨ρ xC, ρ yC, ?_⟩
  apply LinearMap.ext
  intro w
  apply heWinj
  rw [hTk w]
  have hh : (ρ xC * ρ yC * (ρ xC)⁻¹ * (ρ yC)⁻¹ : W ≃ₗ[K] W) =
      ρ (xC * yC * xC⁻¹ * yC⁻¹) := by
    simp only [map_mul, map_inv]
  have hcoe : (((xC * yC * xC⁻¹ * yC⁻¹ : _) :
        ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))) = ⁅x, y⁆ := by
    simp only [xC, yC, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_mk]
  rw [hh, hρ (xC * yC * xC⁻¹ * yC⁻¹) w, hcoe]

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_det_eq_one
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    [Module.Free K W] [Module.Finite K W] :
    ∀ x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
      ∀ y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        ∀ (T : W →ₗ[GaloisField 2 f] W) (Tk : W →ₗ[K] W),
          (∀ w : W, Tk w = T w) →
          (∀ w : W,
            eW (T w) =
              Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
                GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) (eW w)) →
          (∀ (c : K) (w : W), T (c • w) = c • T w) →
          (∀ w w' : W, h (T w) (T w') = h w w') →
          LinearMap.det Tk = 1 := by
  intro x hx y hy T Tk hTk_eq hT hKlin hiso
  have hTk : ∀ w : W,
      eW (Tk w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w) := by
    intro w
    rw [hTk_eq w]
    exact hT w
  obtain ⟨A, B, hAB⟩ :=
    bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_isCommutator
      n f S he K W eW heW heWinj x y hx hy hKlinRepC Tk hTk
  have hdet : LinearEquiv.det (A * B * A⁻¹ * B⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
  calc LinearMap.det Tk
      = LinearMap.det (↑(A * B * A⁻¹ * B⁻¹) : W →ₗ[K] W) := by rw [hAB]
    _ = ↑(LinearEquiv.det (A * B * A⁻¹ * B⁻¹)) := (LinearEquiv.coe_det _).symm
    _ = 1 := by rw [hdet, Units.val_one]

private theorem bmSTS_blockEmbeddingEV_PSU_blockAction_surjective_of_isometry_det_one
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    [Module.Free K W] [Module.Finite K W] :
    ∀ (Tk : W →ₗ[K] W),
      Function.Bijective Tk →
      (∀ w w' : W, h (Tk w) (Tk w') = h w w') →
      LinearMap.det Tk = 1 →
      ∃ g : (ggU .PSU m' (max f 1)).K,
        ∀ w : W,
          eW (Tk w) =
            eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁
              hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank
              htrace g) w) := by
  intro Tk hbij hTk_iso hdet
  haveI : FiniteDimensional K W := FiniteDimensional.of_finrank_pos (by omega)
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) :=
    Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)
  let e : K ≃ₐ[GaloisField 2 f] GaloisField 2 (2 * max f 1) :=
    bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank
  let C : (Fin m' → K) ≃ₗ[GaloisField 2 f] (Fin m' → GaloisField 2 (2 * max f 1)) :=
    bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
  let σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  have hunit := bmSTS_blockEmbeddingEV_PSU_unitaryInvolution n f S hSU hS hodd he hadj hdeg₁
    hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace
  have hhform := bmSTS_blockEmbeddingEV_PSU_isHermForm n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
    K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace
  let E : W ≃ₗ[K] (Fin m' → K) := Classical.choose
    (CFSG.Fischer.Classification.exists_linearEquiv_herm_of_form hunit hhform hnd hrank)
  have hE : ∀ a b : W, CFSG.ClassicalGroups.Unitary.herm τ (E a) (E b) = h a b :=
    Classical.choose_spec
      (CFSG.Fischer.Classification.exists_linearEquiv_herm_of_form hunit hhform hnd hrank)
  let Tke : W ≃ₗ[K] W := LinearEquiv.ofBijective Tk hbij
  let A0 : (Fin m' → K) ≃ₗ[K] (Fin m' → K) := (E.symm.trans Tke).trans E
  have hA0 : ∀ x, A0 x = E (Tk (E.symm x)) := fun _ => rfl
  have hA0iso : ∀ x y, CFSG.ClassicalGroups.Unitary.herm τ (A0 x) (A0 y) =
      CFSG.ClassicalGroups.Unitary.herm τ x y := by
    intro x y
    calc CFSG.ClassicalGroups.Unitary.herm τ (A0 x) (A0 y)
        = CFSG.ClassicalGroups.Unitary.herm τ (E (Tk (E.symm x))) (E (Tk (E.symm y))) := by
            rw [hA0 x, hA0 y]
      _ = h (Tk (E.symm x)) (Tk (E.symm y)) := hE _ _
      _ = h (E.symm x) (E.symm y) := hTk_iso _ _
      _ = CFSG.ClassicalGroups.Unitary.herm τ (E (E.symm x)) (E (E.symm y)) := (hE _ _).symm
      _ = CFSG.ClassicalGroups.Unitary.herm τ x y := by
            rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hdetA0 : LinearMap.det A0.toLinearMap = 1 := by
    rw [show A0.toLinearMap = (E : W →ₗ[K] (Fin m' → K)) ∘ₗ Tke.toLinearMap ∘ₗ
        E.symm.toLinearMap from rfl, LinearMap.det_conj Tke.toLinearMap E]
    exact hdet
  let N : Matrix (Fin m') (Fin m') K := LinearMap.toMatrix' A0.toLinearMap
  have hNdet : N.det = 1 := by rw [LinearMap.det_toMatrix', hdetA0]
  have hNmul : ∀ x : Fin m' → K, Matrix.mulVec N x = A0 x := fun x =>
    LinearMap.toMatrix'_mulVec A0.toLinearMap x
  let M : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)) :=
    N.map (e : K →+* GaloisField 2 (2 * max f 1))
  have hMdet : M.det = 1 := by
    change ((e : K →+* GaloisField 2 (2 * max f 1)).mapMatrix N).det = 1
    rw [← RingHom.map_det (e : K →+* GaloisField 2 (2 * max f 1)) N, hNdet, map_one]
  have hC_apply : ∀ a : Fin m' → K, C a = e ∘ a := fun _ => rfl
  have hMv : ∀ a : Fin m' → K, Matrix.mulVec M (C a) = C (A0 a) := by
    intro a
    calc Matrix.mulVec M (C a)
        = Matrix.mulVec (N.map (e : K →+* GaloisField 2 (2 * max f 1))) (e ∘ a) := by
            rw [hC_apply a]
      _ = e ∘ (Matrix.mulVec N a) := by
            funext i
            exact (RingHom.map_mulVec (e : K →+* GaloisField 2 (2 * max f 1)) N a i).symm
      _ = e ∘ (A0 a) := by rw [hNmul a]
      _ = C (A0 a) := (hC_apply (A0 a)).symm
  have hC_herm : ∀ a b : Fin m' → K,
      CFSG.ClassicalGroups.Unitary.herm σ (C a) (C b) =
        e (CFSG.ClassicalGroups.Unitary.herm τ a b) := by
    intro a b
    refine (?_ : e (CFSG.ClassicalGroups.Unitary.herm τ a b) =
      CFSG.ClassicalGroups.Unitary.herm σ (C a) (C b)).symm
    calc e (CFSG.ClassicalGroups.Unitary.herm τ a b)
        = e (CFSG.ClassicalGroups.Unitary.herm τ (C.symm (C a)) (C.symm (C b))) := by
            rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      _ = e (e.symm (CFSG.ClassicalGroups.Unitary.herm σ (C a) (C b))) :=
            congrArg e (bmSTS_herm_stdModuleEquiv f m' K hKrank τ hτ2 hτne (C a) (C b))
      _ = CFSG.ClassicalGroups.Unitary.herm σ (C a) (C b) := by simp
  have hMiso : ∀ x y : Fin m' → GaloisField 2 (2 * max f 1),
      CFSG.ClassicalGroups.Unitary.herm σ (Matrix.mulVec M x) (Matrix.mulVec M y) =
        CFSG.ClassicalGroups.Unitary.herm σ x y := by
    intro x y
    have hx : x = C (C.symm x) := (LinearEquiv.apply_symm_apply C x).symm
    have hy : y = C (C.symm y) := (LinearEquiv.apply_symm_apply C y).symm
    rw [hx, hy, hMv (C.symm x), hMv (C.symm y)]
    calc CFSG.ClassicalGroups.Unitary.herm σ (C (A0 (C.symm x))) (C (A0 (C.symm y)))
        = e (CFSG.ClassicalGroups.Unitary.herm τ (A0 (C.symm x)) (A0 (C.symm y))) :=
            hC_herm _ _
      _ = e (CFSG.ClassicalGroups.Unitary.herm τ (C.symm x) (C.symm y)) := by rw [hA0iso]
      _ = CFSG.ClassicalGroups.Unitary.herm σ (C (C.symm x)) (C (C.symm y)) :=
            (hC_herm _ _).symm
  let Msu : ↥(Unitary.SUid σ m') := CFSG.ClassicalGroups.Unitary.mkSU σ M hMdet hMiso
  let P := bmSTS_antidiagConj m' f
  have hP := bmSTS_antidiagConj_spec m' f
  let g'' : ↥(Unitary.SU σ m') := (Unitary.conjEquiv P hP).symm Msu
  have hconj : Unitary.conjEquiv P hP g'' = Msu :=
    MulEquiv.apply_symm_apply (Unitary.conjEquiv P hP) Msu
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have heq : ggU .PSU m' (max f 1) =
      ⟨Unitary.SU σ m', Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte, σ]
  have hK : (ggU .PSU m' (max f 1)).K = ↥(Unitary.SU σ m') := congrArg LieUniversal.K heq
  let g : (ggU .PSU m' (max f 1)).K := hK.symm ▸ g''
  have hcast : hK ▸ g = g'' := by
    dsimp only [g]
    exact eq_of_heq ((cast_heq hK (cast hK.symm g'')).trans (cast_heq hK.symm g''))
  have hsu : bmSTS_blockEmbeddingEV_PSU_suAction m' f g =
      (Matrix.mulVecLin (Msu : GL (Fin m') (GaloisField 2 (2 * max f 1)))).restrictScalars
        (GaloisField 2 f) := by
    simp only [bmSTS_blockEmbeddingEV_PSU_suAction]
    rw [hcast, hconj]
  have hmap : bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g =
      C.symm.toLinearMap.comp ((bmSTS_blockEmbeddingEV_PSU_suAction m' f g).comp C.toLinearMap) :=
    rfl
  have hstd : ∀ x : Fin m' → K,
      bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x = A0 x := by
    intro x
    change bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x = A0 x
    rw [hmap, LinearMap.comp_apply, LinearMap.comp_apply, hsu]
    change C.symm (Matrix.mulVec M (C x)) = A0 x
    rw [hMv x, LinearEquiv.symm_apply_apply]
  have hΦ : ∀ w : W,
      bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace w = E w := by
    intro w
    rfl
  have hblock : ∀ w : W,
      (bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) w = Tk w := by
    intro w
    change (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
      ((bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g)
        ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) w)) = Tk w
    rw [hstd ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) w)]
    rw [hΦ w, hA0 (E w), LinearEquiv.symm_apply_apply, ← hΦ (Tk w),
      LinearEquiv.symm_apply_apply]
  exact ⟨g, fun w => (congrArg eW (hblock w)).symm⟩

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_eq_blockAction
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w)) :
    ∀ x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
      ∀ y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        ∀ T : W →ₗ[GaloisField 2 f] W,
          (∀ w : W,
            eW (T w) =
              Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
                GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) (eW w)) →
          (∀ (c : K) (w : W), T (c • w) = c • T w) →
          (∀ w w' : W, h (T w) (T w') = h w w') →
          ∃ g : (ggU .PSU m' (max f 1)).K,
            ∀ w : W,
              eW (T w) =
                eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁
                  hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank
                  htrace g) w) := by
  intro x hx y hy T hT hKlin hiso
  haveI : FiniteDimensional K W := FiniteDimensional.of_finrank_pos (by omega)
  haveI : Module.Free K W := Module.Free.of_divisionRing K W
  let Tk : W →ₗ[K] W :=
    { toFun := T
      map_add' := T.map_add'
      map_smul' := hKlin }
  have hTk_apply : ∀ w : W, Tk w = T w := fun _ => rfl
  have hTk_iso : ∀ w w' : W, h (Tk w) (Tk w') = h w w' := by
    intro w w'
    rw [hTk_apply w, hTk_apply w']
    exact hiso w w'
  have hdet : LinearMap.det Tk = 1 :=
    bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_det_eq_one
      n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
      hrank hm' hKrank htrace hKlinRepC x hx y hy T Tk hTk_apply hT hKlin hiso
  have hsub_fst : ∀ (u u' v : W), h (u - u') v = h u v - h u' v := by
    intro u u' v
    rw [← hτ2 (h (u - u') v), ← hsymm (u - u') v, (h v).map_sub, map_sub,
      hsymm u v, hsymm u' v, hτ2, hτ2]
  have hinj : Function.Injective Tk := by
    intro a b hab
    have hsub : Tk (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hzero : a - b = 0 := by
      apply hnd
      intro y
      calc h (a - b) y = h (Tk (a - b)) (Tk y) := (hTk_iso (a - b) y).symm
        _ = h 0 (Tk y) := by rw [hsub]
        _ = 0 := by
              have h0 := hsub_fst a a (Tk y)
              rw [sub_self] at h0
              rw [h0, sub_self]
    exact sub_eq_zero.mp hzero
  have hsurj : Function.Surjective Tk := LinearMap.surjective_of_injective hinj
  obtain ⟨g, hg⟩ :=
    bmSTS_blockEmbeddingEV_PSU_blockAction_surjective_of_isometry_det_one
      n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
      hrank hm' hKrank htrace Tk ⟨hinj, hsurj⟩ hTk_iso hdet
  exact ⟨g, fun w => by rw [← hTk_apply w]; exact hg w⟩

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_mem_range
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w) :
    ∀ x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
      ∀ y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        ∃ g : (ggU .PSU m' (max f 1)).K,
          ∀ w : W,
            Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
              GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) (eW w) =
              eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) w) := by
  intro x hx y hy
  obtain ⟨T, hT⟩ :=
    bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_exists
      n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
      hrank hm' hKrank htrace x hx y hy
  have hiso :=
    bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_isometry
      n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
      hrank hm' hKrank htrace hKlinRep x hx y hy T hT
  obtain ⟨g, hg⟩ :=
    bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_eq_blockAction
      n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
      hrank hm' hKrank htrace hKlinRepC x hx y hy T hT
      (bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_isKLinear
        n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
        hrank hm' hKrank htrace x hx y hy T hT hiso)
      hiso
  exact ⟨g, fun w => (hT w).symm.trans (hg w)⟩

private theorem bmSTS_blockEmbeddingEV_PSU_eq_blockExtend_of_fixes_ker_of_range_action
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K)
    (z : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hzker : ∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
      b ∈ LinearMap.ker (Matrix.mulVecLin e) → Matrix.mulVec z b = b)
    (hzrange : ∀ w : W, Matrix.mulVec z (eW w) =
      eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) w)) :
    z = bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g := by
  have hM := bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
    heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  obtain ⟨hMrange, hMker⟩ := hM
  apply Units.ext
  apply Matrix.mulVec_injective
  funext v
  let a := Matrix.mulVec e v
  let b := v - Matrix.mulVec e v
  have hbker : b ∈ LinearMap.ker (Matrix.mulVecLin e) := by
    dsimp only [b]
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      he.2.1, sub_self]
  have hdecomp : v = a + b := by
    dsimp only [a, b]
    abel
  have hamem : a ∈ LinearMap.range (Matrix.mulVecLin e) := by
    dsimp only [a]
    simpa only [Matrix.mulVecLin_apply] using
      LinearMap.mem_range_self (Matrix.mulVecLin e) v
  rw [← heW] at hamem
  obtain ⟨w, hw⟩ := hamem
  let B := bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
    h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  have hz_e : Matrix.mulVec z a = eW (B w) := by
    rw [← hw]
    exact hzrange w
  have hM_e : Matrix.mulVec (bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
      hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) a =
      eW (B w) := by
    rw [← hw]
    exact hMrange w
  rw [hdecomp]
  simp only [Matrix.mulVec_add, hzker b hbker, hMker b hbker, hz_e, hM_e]

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_mem_range
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    ∀ x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
      ∀ y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
        ⁅x, y⁆ ∈ (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range := by
  intro x hx y hy
  have hker := bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_fixes_ker
    n f S x y hx hy
  obtain ⟨g, hg⟩ :=
    bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_mem_range
      n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
      hrank hm' hKrank htrace hKlinRepC hKlinRep x hx y hy
  have heq := bmSTS_blockEmbeddingEV_PSU_eq_blockExtend_of_fixes_ker_of_range_action
    n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
    hrank hm' hKrank htrace g (⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) hker hg
  exact ⟨g, Subtype.ext heq.symm⟩

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutator_closure_le_range
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    Subgroup.closure
        {z | ∃ x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
          ∃ y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e,
            ⁅x, y⁆ = z} ≤
      (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range := by
  refine (Subgroup.closure_le _).mpr (fun z hz => ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  exact bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_mem_range
    n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
    hrank hm' hm3 hnq hKrank htrace hKlinRepC hKlinRep hcommS x hx y hy

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutator_le_range
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    _root_.commutator
        ↥(glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)) ≤
      (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range.subgroupOf
      (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)) := by
  have hB := bmSTS_blockEmbeddingEV_PSU_centralizer_commutator_closure_le_range
    n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
    hrank hm' hm3 hnq hKrank htrace hKlinRepC hKlinRep hcommS
  rw [← Subgroup.comap_subtype, ← Subgroup.map_le_iff_le_comap,
    Subgroup.map_subtype_commutator]
  exact (Subgroup.commutator_def _ _).trans_le hB

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_range_normal
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    ((bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range.subgroupOf
      (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e))).Normal := by
  exact Subgroup.Normal.of_commutator_le _
    (bmSTS_blockEmbeddingEV_PSU_centralizer_commutator_le_range
      n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace hKlinRepC hKlinRep hcommS)

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_quotient_commutative
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g)
    [hN : ((bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range.subgroupOf
      (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e))).Normal] :
    IsMulCommutative
      (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e) ⧸
        (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range.subgroupOf
        (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e))) := by
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (bmSTS_blockEmbeddingEV_PSU_centralizer_commutator_le_range n f S hSU hS hodd he hadj hdeg₁
      hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace
      hKlinRepC hKlinRep hcommS)

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_quotient_iso
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    ∃ (_ : ((bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range.subgroupOf
        (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e))).Normal),
      IsMulCommutative
        (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e) ⧸
          (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
            eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range.subgroupOf
          (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e))) := by
  haveI hN : ((bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range.subgroupOf
      (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e))).Normal :=
    bmSTS_blockEmbeddingEV_PSU_centralizer_range_normal n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
      K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace
      hKlinRepC hKlinRep hcommS
  exact ⟨hN, bmSTS_blockEmbeddingEV_PSU_centralizer_quotient_commutative n f S hSU hS hodd he hadj
    hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace
    hKlinRepC hKlinRep hcommS⟩

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_quotient_iso_units
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    ∃ (A : Type) (_ : CommGroup A)
      (φ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e) →* A),
      φ.ker = (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range.subgroupOf
        (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)) := by
  obtain ⟨hN, hcomm⟩ :=
    bmSTS_blockEmbeddingEV_PSU_centralizer_quotient_iso n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
      K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace
      hKlinRepC hKlinRep hcommS
  let N := (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range.subgroupOf
    (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e))
  haveI : N.Normal := hN
  letI : CommGroup
      (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e) ⧸ N) :=
    { QuotientGroup.Quotient.group N with
      mul_comm := fun a b => hcomm.is_comm.comm a b }
  exact ⟨glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e) ⧸ N,
    inferInstance, QuotientGroup.mk' N, QuotientGroup.ker_mk' N⟩

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_abelian_quotient
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    ∃ (A : Type) (_ : CommGroup A)
      (φ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e) →* A),
      φ.ker = (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range.subgroupOf
        (glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)) := by
  obtain ⟨A, hA, φ, hφ⟩ :=
    bmSTS_blockEmbeddingEV_PSU_centralizer_quotient_iso_units n f S hSU hS hodd he hadj hdeg₁ hdeg₂
      hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace
      hKlinRepC hKlinRep hcommS
  exact ⟨A, hA, φ, hφ⟩

private theorem bmSTS_blockEmbeddingEV_PSU_centralizer_commutator_mem_range
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    ∀ x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      ∀ y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
        ⁅x, y⁆ ∈ (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range := by
  intro x hx y hy
  obtain ⟨A, hA, φ, hφ⟩ := bmSTS_blockEmbeddingEV_PSU_centralizer_abelian_quotient n f S hSU hS
    hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq
    hKrank htrace hKlinRepC hKlinRep hcommS
  letI : CommGroup A := hA
  let C := glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)
  have hker : ⁅(⟨x, hx⟩ : C), (⟨y, hy⟩ : C)⁆ ∈ φ.ker :=
    bmSTS_commutator_mem_ker_of_commutative φ (⟨x, hx⟩ : C) (⟨y, hy⟩ : C)
  rw [hφ] at hker
  simpa [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    using Subgroup.mem_subgroupOf.mp hker

private theorem bmSTS_blockEmbeddingEV_PSU_derived_le_hom_range
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆ ≤
    (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range := by
  exact Subgroup.commutator_le.mpr
    (bmSTS_blockEmbeddingEV_PSU_centralizer_commutator_mem_range n f S hSU hS hodd he hadj hdeg₁
      hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace
      hKlinRepC hKlinRep hcommS)

private theorem bmSTS_blockEmbeddingEV_PSU_hom_range_eq_derived
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range =
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆ := by
  refine le_antisymm ?_ ?_
  · exact bmSTS_blockEmbeddingEV_PSU_hom_range_le_derived n f S hSU hS hodd he hadj hdeg₁ hdeg₂
      hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace hcommS
  · exact bmSTS_blockEmbeddingEV_PSU_derived_le_hom_range n f S hSU hS hodd he hadj hdeg₁ hdeg₂
      hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace
      hKlinRepC hKlinRep hcommS

private theorem bmSTS_blockEmbeddingEV_PSU_props
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    (∀ y, bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace y ∈
      Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSU m' (max f 1)).K) ∧
    (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range =
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆ := by
  have hinj := bmSTS_blockEmbeddingEV_PSU_hom_injective n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
    K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
  refine ⟨?_, ?_⟩
  · intro y hy
    have hcenter : Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) = ⊥ := by
      rw [CFSG.LieType.Universal.Symplectic.center_eq n (GaloisField 2 f),
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
    rw [hcenter, Subgroup.mem_bot] at hy
    have hy1 : y = 1 := hinj (by simpa using hy)
    rw [hy1]
    exact Subgroup.one_mem _
  · exact bmSTS_blockEmbeddingEV_PSU_hom_range_eq_derived n f S hSU hS hodd he hadj hdeg₁ hdeg₂
      hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace
      hKlinRepC hKlinRep hcommS

private theorem bmSTS_quasisimple_nontrivial {Q : Type*} [Group Q]
    (hQ : CFSG.Assembly.IsQuasisimple Q) : Nontrivial Q := by
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨x, y, hxy⟩ := hsimple.exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨a, b, fun hab => hxy (by rw [hab])⟩

private theorem bmSTS_SU_one_eq_bot (F : Type*) [Field F] (σ : F ≃+* F) :
    Unitary.SU σ 1 = ⊥ := by
  apply le_antisymm _ bot_le
  intro A hA
  rw [Subgroup.mem_bot]
  have hdet : (A : Matrix (Fin 1) (Fin 1) F).det = 1 := hA.1
  have hentry : (A : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
    rwa [Matrix.det_fin_one] at hdet
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simpa using hentry

private theorem bmSTS_subsingleton_ggU_PSU_one
    (f : ℕ) :
    Subsingleton (ggU .PSU 1 (max f 1)).K := by
  let σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have hSU : Unitary.SU σ 1 = ⊥ := bmSTS_SU_one_eq_bot _ σ
  have hG : ggU .PSU 1 (max f 1) =
      ⟨Unitary.SU σ 1,
        Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) 1⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte, σ]
  rw [hG]
  change Subsingleton ↥(Unitary.SU σ 1)
  rw [hSU]
  exact ⟨fun a b => Subtype.ext (by
    rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩

private theorem bmSTS_explicit_data_hm3
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w)
    (hcommS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) :
    2 ≤ m' := by
  by_contra hcon
  have hm1 : m' = 1 := by omega
  let ι₀ := bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
    eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
  haveI : Subsingleton (ggU .PSU m' (max f 1)).K := by
    rw [hm1]
    exact bmSTS_subsingleton_ggU_PSU_one f
  have hrange_bot : ι₀.range = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨g, rfl⟩ := hx
    rw [Subsingleton.elim g 1]
    exact map_one ι₀
  let C := glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
  have hmem : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ ι₀.range := by
    intro x hx y hy
    have hker := bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_fixes_ker
      n f S x y hx hy
    obtain ⟨g, hg⟩ :=
      bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_mem_range
        n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
        hrank hm' hKrank htrace hKlinRepC hKlinRep x hx y hy
    have heq := bmSTS_blockEmbeddingEV_PSU_eq_blockExtend_of_fixes_ker_of_range_action
      n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
      hrank hm' hKrank htrace g (⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) hker hg
    exact ⟨g, Subtype.ext heq.symm⟩
  have hCCle : ⁅C, C⁆ ≤ ι₀.range := Subgroup.commutator_le.mpr hmem
  have hCCbot : ⁅C, C⁆ = ⊥ := le_antisymm (hCCle.trans (le_of_eq hrange_bot)) bot_le
  have hJbot : J' = ⊥ := le_antisymm (hJe.1.trans (le_of_eq hCCbot)) bot_le
  haveI hnt : Nontrivial ↥J' := bmSTS_quasisimple_nontrivial hJe.2.2
  haveI hss : Subsingleton ↥J' := by rw [hJbot]; infer_instance
  exact not_nontrivial_iff_subsingleton.mpr hss hnt

private theorem bmSTS_not_solvable_of_isComponentOf
    {X : Type} [Group X] {J' K : Subgroup X} (h : IsComponentOf J' K) :
    ¬ Group.IsSolvable ↥J' := by
  intro hs
  haveI : Nontrivial ↥J' := bmSTS_quasisimple_nontrivial h.2.2
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J').ne h.2.2.1

private theorem bmSTS_explicit_data_hnq
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
    (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w) :
    2 ^ max f 1 ≠ 2 ∨ 4 ≤ m' := by
  by_contra h
  push_neg at h
  obtain ⟨hq, hmle⟩ := h
  have hsmall : ∀ k, 1 ≤ k → k ≤ 3 → 2 ^ max f 1 = 2 →
      Group.IsSolvable ((ggU .PSU k (max f 1)).K) := by
    intro k hk1 hk3 hqk
    interval_cases k
    · haveI : Subsingleton (ggU .PSU 1 (max f 1)).K :=
        bmSTS_subsingleton_ggU_PSU_one f
      infer_instance
    · have hf : 1 ≤ max f 1 := le_max_right f 1
      have e : ggU .PSU 2 (max f 1) =
          ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
              (GaloisField 2 (2 * max f 1)) 2 (max f 1)) 2,
            Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) 2⟩ := by
        simp only [ggU, lieUniversal, hf, ↓reduceDIte]
      rw [e]
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : CharP (GaloisField 2 (2 * max f 1)) 2 :=
        CFSG.ClassicalGroups.Unitary.charP_of_card_sq (bmSTS_natCard_galoisField_twoMax_sq f)
      have hcard := CFSG.LieType.Steinberg.card_SU_two (F := GaloisField 2 (2 * max f 1))
        (p := 2) (f := max f 1) (bmSTS_natCard_galoisField_twoMax_sq f)
      refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
      rw [hcard, hqk]
      norm_num [Nat.primeFactors]
    · have hf : 1 ≤ max f 1 := le_max_right f 1
      have e : ggU .PSU 3 (max f 1) =
          ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
              (GaloisField 2 (2 * max f 1)) 2 (max f 1)) 3,
            Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) 3⟩ := by
        simp only [ggU, lieUniversal, hf, ↓reduceDIte]
      rw [e]
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : CharP (GaloisField 2 (2 * max f 1)) 2 :=
        CFSG.ClassicalGroups.Unitary.charP_of_card_sq (bmSTS_natCard_galoisField_twoMax_sq f)
      have hcard := CFSG.LieType.Steinberg.card_SU_three (F := GaloisField 2 (2 * max f 1))
        (p := 2) (f := max f 1) (bmSTS_natCard_galoisField_twoMax_sq f)
      refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
      rw [hcard, hqk]
      norm_num [Nat.primeFactors]
  have hsolve : Group.IsSolvable ((ggU .PSU m' (max f 1)).K) := hsmall m' hm' (by omega) hq
  let C := glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
  let ι₀ := bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
    eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
  have hmem : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ ι₀.range := by
    intro x hx y hy
    have hker := bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_fixes_ker
      n f S x y hx hy
    obtain ⟨g, hg⟩ :=
      bmSTS_blockEmbeddingEV_PSU_centralizer_commutatorElement_range_action_mem_range
        n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
        hrank hm' hKrank htrace hKlinRepC hKlinRep x hx y hy
    have heq := bmSTS_blockEmbeddingEV_PSU_eq_blockExtend_of_fixes_ker_of_range_action
      n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd
      hrank hm' hKrank htrace g (⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) hker hg
    exact ⟨g, Subtype.ext heq.symm⟩
  have hCCle : ⁅C, C⁆ ≤ ι₀.range := Subgroup.commutator_le.mpr hmem
  haveI : Group.IsSolvable ((ggU .PSU m' (max f 1)).K) := hsolve
  have hsolve_range : Group.IsSolvable ↥ι₀.range :=
    Group.isSolvable_of_surjective ι₀.rangeRestrict_surjective
  haveI : Group.IsSolvable ↥ι₀.range := hsolve_range
  have hCCsolv : Group.IsSolvable ↥⁅C, C⁆ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCCle)
  haveI : Group.IsSolvable ↥⁅C, C⁆ := hCCsolv
  have hJsolv : Group.IsSolvable ↥J' :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJe.1)
  exact bmSTS_not_solvable_of_isComponentOf hJe hJsolv

private lemma bmSTS_blockAction
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :
    ∃ actA : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f]
        Module.End (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)),
      ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
        (w : LinearMap.range (Matrix.mulVecLin e)),
        (actA a w : (Fin n ⊕ Fin n) → GaloisField 2 f) =
          Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) w := by
  classical
  let F := GaloisField 2 f
  let A := Algebra.adjoin F (Units.val '' S)
  let W : Submodule F ((Fin n ⊕ Fin n) → F) := LinearMap.range (Matrix.mulVecLin e)
  have hpair : (Units.val '' S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).Pairwise
      Commute := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ _
    exact (hS s hs s' hs').map (Units.coeHom (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpair
  have hcomm : ∀ a : A, (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * e =
      e * (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    intro a
    exact congrArg Subtype.val (mul_comm a (⟨e, he.1⟩ : A))
  let actA : A →ₐ[F] Module.End F W :=
  { toFun := fun a =>
      ((Matrix.mulVecLin (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).comp W.subtype).codRestrict
        W (fun v => by
          rw [LinearMap.comp_apply, Submodule.coe_subtype]
          obtain ⟨u, hu⟩ := v.2
          rw [← hu]
          refine ⟨Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) u, ?_⟩
          calc Matrix.mulVecLin e (Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) u)
              = Matrix.mulVec e
                  (Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) u) := rfl
            _ = Matrix.mulVec (e * (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) u :=
                  Matrix.mulVec_mulVec u e (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            _ = Matrix.mulVec ((a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * e) u := by
                  rw [hcomm a]
            _ = Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
                  (Matrix.mulVec e u) :=
                  (Matrix.mulVec_mulVec u (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e).symm
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
      rw [show algebraMap F ((Fin n ⊕ Fin n) → F) c = fun _ => c from rfl,
        Matrix.diagonal_const_mulVec] }
  refine ⟨actA, ?_⟩
  intro a w
  rfl

private lemma bmSTS_blockAction_ker
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (_hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (_he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) * e = 0)
    (actA : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f]
      Module.End (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)))
    (hact : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
      (w : LinearMap.range (Matrix.mulVecLin e)),
      (actA a w : (Fin n ⊕ Fin n) → GaloisField 2 f) =
        Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) w) :
    RingHom.ker (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+* K) ≤
      RingHom.ker (actA : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →+*
        Module.End (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e))) := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  have hae : (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e = 0 :=
    (hπker a).mp ha
  refine LinearMap.ext fun w => Subtype.ext ?_
  change (actA a w : (Fin n ⊕ Fin n) → GaloisField 2 f) = 0
  rw [hact a w]
  obtain ⟨v, hv⟩ := w.2
  rw [← hv, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec v (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e, hae,
    Matrix.zero_mulVec]

private lemma bmSTS_blockKModuleAction
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) * e = 0) :
    ∃ (W : Submodule (GaloisField 2 f) ((Fin n ⊕ Fin n) → GaloisField 2 f))
      (_ : Module K W) (_ : IsScalarTower (GaloisField 2 f) K W),
      W = LinearMap.range (Matrix.mulVecLin e) ∧
      (∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) (w : W),
        (Submodule.subtype W) ((π a) • w) =
          Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
            ((Submodule.subtype W) w)) := by
  classical
  let F := GaloisField 2 f
  let A := Algebra.adjoin F (Units.val '' S)
  have hpair : (Units.val '' S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).Pairwise
      Commute := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ _
    exact (hS s hs s' hs').map (Units.coeHom (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpair
  obtain ⟨actA, hactA⟩ := bmSTS_blockAction n f S hS he
  have hker : RingHom.ker (π : A →+* K) ≤
      RingHom.ker (actA : A →+* Module.End F (LinearMap.range (Matrix.mulVecLin e))) :=
    bmSTS_blockAction_ker n f S hS he K π hπker actA hactA
  have hp : Function.Surjective (π : A →+* K) := fun k => hπsurj k
  let ψ : K →+* Module.End F (LinearMap.range (Matrix.mulVecLin e)) :=
    (Ideal.Quotient.lift (RingHom.ker (π : A →+* K))
      (actA : A →+* Module.End F (LinearMap.range (Matrix.mulVecLin e)))
      (fun a ha => RingHom.mem_ker.mp (hker ha))).comp
      (RingHom.quotientKerEquivOfSurjective (f := (π : A →+* K)) hp).symm.toRingHom
  have hψ : ∀ a : A, ψ (π a) = actA a := fun a => by
    change (Ideal.Quotient.lift (RingHom.ker (π : A →+* K))
      (actA : A →+* Module.End F (LinearMap.range (Matrix.mulVecLin e)))
      (fun a ha => RingHom.mem_ker.mp (hker ha)))
      ((RingHom.quotientKerEquivOfSurjective (f := (π : A →+* K)) hp).symm
        ((π : A →+* K) a)) = actA a
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    rfl
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.compHom (LinearMap.range (Matrix.mulVecLin e)) ψ
  have htower : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)) :=
    ⟨fun c k w => by
    change (ψ (c • k)) w = c • ((ψ k) w)
    obtain ⟨a, rfl⟩ := hπsurj k
    rw [← map_smul π c a, hψ (c • a), hψ a, map_smul]
    rfl⟩
  refine ⟨LinearMap.range (Matrix.mulVecLin e), inferInstance, htower, rfl, ?_⟩
  intro a w
  change (ψ (π a) (w : LinearMap.range (Matrix.mulVecLin e)) :
      (Fin n ⊕ Fin n) → GaloisField 2 f) =
    Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) w
  rw [hψ a, hactA a w]

private theorem bmSTS_explicit_data_canonicalKAction
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    :
    ∃ (K : Type) (_ : Field K) (_ : Algebra (GaloisField 2 f) K) (_ : Finite K)
      (hKrank : Module.finrank (GaloisField 2 f) K = 2)
      (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
      (hπsurj : Function.Surjective π)
      (W : Submodule (GaloisField 2 f) ((Fin n ⊕ Fin n) → GaloisField 2 f))
      (_ : Module K W) (_ : IsScalarTower (GaloisField 2 f) K W),
      W = LinearMap.range (Matrix.mulVecLin e) ∧
      (∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) (w : W),
        (Submodule.subtype W) ((π a) • w) =
          Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
            ((Submodule.subtype W) w)) := by
  obtain ⟨K, hKf, hKa, hKfin, π, hπsurj, hπker, hπrank⟩ :=
    exists_blockField (F := GaloisField 2 f) hS hodd he
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 f) K := hKa
  have hKrank : Module.finrank (GaloisField 2 f) K = 2 :=
    hπrank.trans (bmSTS_degree_two n f S hSU hS hodd he hadj hdeg₁ hdeg₂)
  obtain ⟨W, hWmod, hWtower, hWeq, hact⟩ :=
    bmSTS_blockKModuleAction n f S hS he K π hπsurj hπker
  exact ⟨K, hKf, hKa, hKfin, hKrank, π, hπsurj, W, hWmod, hWtower, hWeq, hact⟩

private lemma bmSTS_J_transpose (n f : ℕ) :
    Matrix.transpose (bmSTS_J n f) = bmSTS_J n f := by
  rw [bmSTS_J, bmSTS_neg_one_matrix_eq_one, Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero, Matrix.transpose_one]

private lemma bmSTS_form_symm (n f : ℕ) (x y : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) y =
      y ⬝ᵥ Matrix.mulVec (bmSTS_J n f) x := by
  have h := Matrix.dotProduct_transpose_mulVec (bmSTS_J n f) x y
  rwa [bmSTS_J_transpose] at h

private lemma bmSTS_adjoint_dotProduct (n f : ℕ)
    (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (x y : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    Matrix.mulVec b x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) y =
      x ⬝ᵥ Matrix.mulVec (bmSTS_J n f)
        (Matrix.mulVec (formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) b) y) := by
  have hJ : bmSTS_J n f * formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) b =
      Matrix.transpose b * bmSTS_J n f := by
    rw [formAdj, show b.map (⇑(RingHom.id (GaloisField 2 f))) = b from Matrix.map_id b]
    rw [← Matrix.mul_assoc (bmSTS_J n f) ((bmSTS_J n f)⁻¹ * Matrix.transpose b)
          (bmSTS_J n f),
      ← Matrix.mul_assoc (bmSTS_J n f) (bmSTS_J n f)⁻¹ (Matrix.transpose b),
      Matrix.mul_nonsing_inv (bmSTS_J n f) (bmSTS_J_det n f), Matrix.one_mul]
  have hR : x ⬝ᵥ Matrix.mulVec (bmSTS_J n f)
        (Matrix.mulVec (formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) b) y) =
      Matrix.mulVec b x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) y := by
    rw [Matrix.mulVec_mulVec, hJ, ← Matrix.mulVec_mulVec]
    nth_rewrite 1 [Matrix.dotProduct_mulVec]
    rw [Matrix.vecMul_transpose]
  exact hR.symm

private lemma bmSTS_smul_eq_zero_of_forall (K W : Type) [Field K] [AddCommGroup W]
    [Module K W] [Nontrivial W] {k : K} (h : ∀ w : W, k • w = 0) : k = 0 := by
  by_contra hk
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  apply hw
  calc w = 1 • w := (one_smul K w).symm
    _ = (k⁻¹ * k) • w := by rw [inv_mul_cancel₀ hk]
    _ = k⁻¹ • (k • w) := by rw [mul_smul]
    _ = k⁻¹ • 0 := by rw [h w]
    _ = 0 := smul_zero k⁻¹

private theorem bmSTS_explicit_data_traceTransferForm
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (W : Submodule (GaloisField 2 f) ((Fin n ⊕ Fin n) → GaloisField 2 f))
    [Module K W] [IsScalarTower (GaloisField 2 f) K W]
    (hWeq : W = LinearMap.range (Matrix.mulVecLin e))
    (hact : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) (w : W),
      (Submodule.subtype W) ((π a) • w) =
        Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          ((Submodule.subtype W) w))
    :
    ∃ (τ : K ≃+* K) (h : W → W →ₗ[K] K) (m' : ℕ),
      (∀ a : K, τ (τ a) = a) ∧ τ ≠ RingHom.id K ∧
      (∀ c : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K c) =
        algebraMap (GaloisField 2 f) K c) ∧
      (∀ x y : W, h y x = τ (h x y)) ∧
      (∀ x : W, (∀ y : W, h x y = 0) → x = 0) ∧
      Module.finrank K W = m' ∧ 1 ≤ m' ∧
      (∀ (x y : W) (c : K),
        (Submodule.subtype W) x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) ((Submodule.subtype W) (c • y)) =
          Algebra.trace (GaloisField 2 f) K (c * h x y)) := by
  classical
  let F := GaloisField 2 f
  let J := bmSTS_J n f
  let A := Algebra.adjoin F (Units.val '' S)
  have hpair : (Units.val '' S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).Pairwise
      Commute := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ _
    exact (hS s hs s' hs').map (Units.coeHom (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpair
  have hJdet : IsUnit J.det := by simpa only [J] using bmSTS_J_det n f
  have hJsymm : Matrix.transpose J = J := by simpa only [J] using bmSTS_J_transpose n f
  have hadj' : formAdj (RingHom.id F) J e = e := by simpa only [J, F] using hadj
  have hGh : Matrix.transpose (J.map (RingHom.id F)) = J := by
    rw [show J.map (⇑(RingHom.id F)) = J from Matrix.map_id J]
    exact hJsymm
  have hSG : ∀ s ∈ S, Matrix.transpose (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * J *
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = J := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff).1 (hSU s hs)
    simpa [J, bmSTS_J] using h
  have hSU' : ∀ s ∈ S, Matrix.transpose
      (((s : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map
        (RingHom.id F)) * J * ((s : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = J := by
    intro s hs
    rw [show (((s : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map (⇑(RingHom.id F))) =
        ((s : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      from Matrix.map_id _]
    exact hSG s hs
  have hφmem : ∀ a : A, formAdj (RingHom.id F) J
      (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ∈ A :=
    fun a => Geo.formAdj_mem_adjoin (RingHom.id F) hJdet hSU' a.2
  let φA : A →+* A :=
    { toFun := fun a => ⟨formAdj (RingHom.id F) J
          (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F), hφmem a⟩
      map_one' := by
        apply Subtype.ext
        change formAdj (RingHom.id F) J (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1
        exact Geo.formAdj_one (RingHom.id F) hJdet
      map_mul' := by
        intro a b
        apply Subtype.ext
        change formAdj (RingHom.id F) J
            ((a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
              (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) =
          formAdj (RingHom.id F) J (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            formAdj (RingHom.id F) J (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        rw [Geo.formAdj_mul (RingHom.id F) hJdet]
        exact congrArg Subtype.val (mul_comm
          (⟨formAdj (RingHom.id F) J (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F),
              hφmem b⟩ : A)
          (⟨formAdj (RingHom.id F) J (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F),
              hφmem a⟩ : A))
      map_zero' := by
        apply Subtype.ext
        change formAdj (RingHom.id F) J (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 0
        simp [formAdj]
      map_add' := by
        intro a b
        apply Subtype.ext
        change formAdj (RingHom.id F) J
            ((a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) +
              (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) =
          formAdj (RingHom.id F) J (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) +
            formAdj (RingHom.id F) J (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        rw [Geo.formAdj_add (RingHom.id F)] }
  have hφA_coe : ∀ a : A, ((φA a : A) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      formAdj (RingHom.id F) J (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := fun a => rfl
  have hφA2 : ∀ a : A, φA (φA a) = a := by
    intro a
    apply Subtype.ext
    change formAdj (RingHom.id F) J
        (formAdj (RingHom.id F) J (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) =
      (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    exact Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hJdet hGh
      (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  have hφA_algebraMap : ∀ c : F, φA (algebraMap F A c) = algebraMap F A c := by
    intro c
    apply Subtype.ext
    change formAdj (RingHom.id F) J
        (algebraMap F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) c) =
      algebraMap F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) c
    rw [Algebra.algebraMap_eq_smul_one, Geo.formAdj_smul, Geo.formAdj_one (RingHom.id F) hJdet,
      RingHom.id_apply]
  have hWne : W ≠ ⊥ := by
    rw [hWeq]
    exact bmSTS_blockRangeNeBot n f S hSU hS hodd he hadj hdeg₁ hdeg₂
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWne
  have hker : ∀ a : A, π a = 0 ↔ (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * e = 0 := by
    intro a
    constructor
    · intro ha
      apply Matrix.ext_of_mulVec_single
      intro j
      have hw : Matrix.mulVec e (Pi.single j 1) ∈ W := by
        rw [hWeq]
        exact ⟨Pi.single j 1, rfl⟩
      have h1 := hact a ⟨Matrix.mulVec e (Pi.single j 1), hw⟩
      rw [ha, zero_smul, map_zero] at h1
      change (0 : (Fin n ⊕ Fin n) → F) =
        (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec
          (Matrix.mulVec e (Pi.single j 1)) at h1
      rw [Matrix.mulVec_mulVec] at h1
      rw [Matrix.zero_mulVec]
      exact h1.symm
    · intro hae
      apply bmSTS_smul_eq_zero_of_forall K W
      intro w
      apply Submodule.subtype_injective W
      have h1 := hact a w
      have hw : ((w : W) : (Fin n ⊕ Fin n) → F) ∈ LinearMap.range (Matrix.mulVecLin e) := by
        rw [← hWeq]
        exact w.2
      obtain ⟨v, hv⟩ := hw
      have hv' : Matrix.mulVec e v = (Submodule.subtype W) w := hv
      rw [h1, ← hv', Matrix.mulVec_mulVec, hae, Matrix.zero_mulVec, map_zero]
  have hkerφ : ∀ a : A, π a = 0 → π (φA a) = 0 := by
    intro a ha
    have hae : (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * e = 0 := (hker a).mp ha
    have hcomm : (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * e =
        e * (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
      have h := congrArg Subtype.val (mul_comm a (⟨e, he.1⟩ : A))
      simpa only [Subalgebra.coe_mul, Subtype.coe_mk] using h
    have hea : e * (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 0 := by
      rw [← hcomm]
      exact hae
    have h1 : formAdj (RingHom.id F) J
        (e * (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) = 0 := by
      rw [hea]
      simp [formAdj]
    rw [Geo.formAdj_mul (RingHom.id F) hJdet, hadj'] at h1
    exact (hker (φA a)).mpr (by rw [hφA_coe]; exact h1)
  let I : Ideal A := RingHom.ker (π : A →+* K)
  have hp : Function.Surjective (π : A →+* K) := fun k => hπsurj k
  let e1 : A ⧸ I ≃+* K := RingHom.quotientKerEquivOfSurjective (f := (π : A →+* K)) hp
  let φbar : A ⧸ I →+* A ⧸ I := Ideal.Quotient.lift I ((Ideal.Quotient.mk I).comp φA)
    (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hkerφ a (RingHom.mem_ker.mp ha))
  have hφbar_mk : ∀ a : A, φbar (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (φA a) := by
    intro a
    change (Ideal.Quotient.lift I ((Ideal.Quotient.mk I).comp φA) _)
      (Ideal.Quotient.mk I a) = _
    rw [Ideal.Quotient.lift_mk]
    rfl
  have hφbar2 : ∀ x, φbar (φbar x) = x := by
    have hcomp : (φbar.comp φbar).comp (Ideal.Quotient.mk I) =
        (RingHom.id (A ⧸ I)).comp (Ideal.Quotient.mk I) := by
      ext a
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [hφbar_mk a, hφbar_mk (φA a), hφA2 a]
    have h : φbar.comp φbar = RingHom.id (A ⧸ I) := Ideal.Quotient.ringHom_ext hcomp
    intro x
    exact RingHom.congr_fun h x
  let φbarE : A ⧸ I ≃+* A ⧸ I :=
    { toFun := φbar
      invFun := φbar
      left_inv := hφbar2
      right_inv := hφbar2
      map_mul' := φbar.map_mul
      map_add' := φbar.map_add }
  let τe : K ≃+* K := e1.symm.trans (φbarE.trans e1)
  have hsymm1 : ∀ a : A, e1.symm ((π : A →+* K) a) = Ideal.Quotient.mk I a := fun a =>
    RingHom.quotientKerEquivOfSurjective_symm_apply (f := (π : A →+* K)) hp a
  have hfwd1 : ∀ a : A, e1 (Ideal.Quotient.mk I a) = (π : A →+* K) a := fun a =>
    RingHom.quotientKerEquivOfSurjective_apply_mk (f := (π : A →+* K)) hp a
  have hτe_π : ∀ a : A, (τe : K →+* K) (π a) = π (φA a) := by
    intro a
    change e1 (φbar (e1.symm ((π : A →+* K) a))) = (π : A →+* K) (φA a)
    rw [hsymm1 a, hφbar_mk a, hfwd1 (φA a)]
  have hτe2 : ∀ a : K, τe (τe a) = a := by
    intro a
    obtain ⟨b, rfl⟩ := hπsurj a
    rw [show τe (π b) = π (φA b) from hτe_π b,
      show τe (π (φA b)) = π (φA (φA b)) from hτe_π (φA b), hφA2 b]
  let gen (s : GL (Fin n ⊕ Fin n) F) (hs : s ∈ S) : A :=
    ⟨(s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F),
      Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
  have hτene : τe ≠ RingHom.id K := by
    intro hid
    have hfix : ∀ a : A, π (φA a) = π a := by
      intro a
      have h := DFunLike.congr_fun hid (π a)
      rw [hτe_π a] at h
      simpa using h
    have hgen1 : ∀ s (hs : s ∈ S), π (gen s hs) = 1 := by
      intro s hs
      have hφval : ((φA (gen s hs) : A) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          ((s⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
        rw [hφA_coe]
        exact Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hJdet s (hSU' s hs)
      have hxyeq : φA (gen s hs) * gen s hs = 1 := by
        apply Subtype.ext
        rw [Subalgebra.coe_mul, hφval]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rfl
      have hmul : π (φA (gen s hs)) * π (gen s hs) = 1 := by
        rw [← map_mul, hxyeq, map_one]
      have hsq : (π (gen s hs)) ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [← hfix (gen s hs)]
        exact hmul
      have h2K : (2 : K) = 0 :=
        bmSTS_charP_two n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact h
      · rw [h]
        have hneg : (-1 : K) = 1 := by
          rw [neg_eq_iff_add_eq_zero, show (1 : K) + 1 = 2 from by norm_num, h2K]
        exact hneg
    have hbot : (⊥ : Subalgebra F K) = ⊤ := by
      rw [Algebra.eq_top_iff]
      intro k
      obtain ⟨a, rfl⟩ := hπsurj k
      have h := Algebra.adjoin_induction (R := F) (s := Units.val '' S)
        (p := fun x hx => π (⟨x, hx⟩ : A) ∈ (⊥ : Subalgebra F K))
        (fun x hx => by
          rcases hx with ⟨s, hs, rfl⟩
          rw [hgen1 s hs]
          exact Subalgebra.one_mem _)
        (fun r => by
          change π (algebraMap F A r) ∈ (⊥ : Subalgebra F K)
          rw [π.commutes r]
          exact Subalgebra.algebraMap_mem _ r)
        (fun x y hx hy ihx ihy => by
          have hxy : π (⟨x + y, add_mem hx hy⟩ : A) =
              π (⟨x, hx⟩ : A) + π (⟨y, hy⟩ : A) := by
            rw [← map_add]
            rfl
          rw [hxy]
          exact Subalgebra.add_mem _ ihx ihy)
        (fun x y hx hy ihx ihy => by
          have hxy : π (⟨x * y, mul_mem hx hy⟩ : A) =
              π (⟨x, hx⟩ : A) * π (⟨y, hy⟩ : A) := by
            rw [← map_mul]
            rfl
          rw [hxy]
          exact Subalgebra.mul_mem _ ihx ihy)
        a.2
      simpa using h
    have hfr : Module.finrank F K = 1 := by
      have hspan : Submodule.span F ({1} : Set K) = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro k
        have hk : k ∈ (⊥ : Subalgebra F K) := by
          rw [hbot]
          exact Algebra.mem_top
        rw [Algebra.mem_bot] at hk
        obtain ⟨c, hc⟩ := hk
        rw [Submodule.mem_span_singleton]
        exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
      rw [← finrank_top, ← hspan]
      exact finrank_span_singleton one_ne_zero
    rw [hfr] at hKrank
    omega
  let B : W →ₗ[F] W →ₗ[F] F := (Matrix.toBilin' J).restrict W
  have hBh : ∀ x y : W, B y x = (RingEquiv.refl F) (B x y) := by
    intro x y
    rw [RingEquiv.refl_apply]
    simp only [B, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      Matrix.toBilin'_apply']
    exact bmSTS_form_symm n f ((Submodule.subtype W) y) ((Submodule.subtype W) x)
  have hτσ : ∀ c : F, τe (algebraMap F K c) = algebraMap F K ((RingEquiv.refl F) c) := by
    intro c
    rw [RingEquiv.refl_apply, ← π.commutes c]
    rw [show τe (π (algebraMap F A c)) = π (φA (algebraMap F A c)) from
      hτe_π (algebraMap F A c), hφA_algebraMap c, π.commutes c]
  have hτadj : ∀ (a : K) (x y : W), B (a • x) y = B x ((τe : K →+* K) a • y) := by
    intro a x y
    obtain ⟨b, rfl⟩ := hπsurj a
    rw [hτe_π b]
    simp only [B, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      Matrix.toBilin'_apply']
    change (Submodule.subtype W) ((π b) • x) ⬝ᵥ Matrix.mulVec J ((Submodule.subtype W) y) =
      (Submodule.subtype W) x ⬝ᵥ Matrix.mulVec J
        ((Submodule.subtype W) ((π (φA b)) • y))
    rw [hact b x, hact (φA b) y, hφA_coe]
    exact bmSTS_adjoint_dotProduct n f (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      ((Submodule.subtype W) x) ((Submodule.subtype W) y)
  letI : FiniteDimensional F K := Module.Finite.of_finite
  haveI : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hEx : ∀ x : W, ∃! hx : W →ₗ[K] K,
      ∀ (y : W) (c : K), B x (c • y) = Algebra.trace F K (c * hx y) :=
    fun x => existsUnique_traceTransfer (K := F) (A := K) (W := W) B x
  let h : W → W →ₗ[K] K := fun x => (hEx x).choose
  have hspec : ∀ (x y : W) (c : K), B x (c • y) = Algebra.trace F K (c * h x y) :=
    fun x y c => (hEx x).choose_spec.1 y c
  have htr := traceTransfer_herm (K := F) (A := K) (W := W) (RingEquiv.refl F) B h hspec hBh
    (τe : K ≃+* K) hτσ hτe2 hτadj
  have hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0 := by
    intro x hx
    have hBxy : ∀ y : W, B x y = 0 := by
      intro y
      have h1 := hspec x y 1
      rw [one_smul] at h1
      rw [h1, hx y, mul_zero, map_zero]
    have hBnd : B.Nondegenerate := by
      have h0 := bmSTS_blockRestrictNondegenerate n f S hSU hS hodd he hadj hdeg₁ hdeg₂
      rw [← hWeq] at h0
      exact h0
    exact hBnd.1 x hBxy
  have htraceFinal : ∀ (x y : W) (c : K),
      (Submodule.subtype W) x ⬝ᵥ Matrix.mulVec J ((Submodule.subtype W) (c • y)) =
        Algebra.trace F K (c * h x y) := by
    intro x y c
    rw [← hspec x y c]
    simp only [B, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      Matrix.toBilin'_apply', Submodule.subtype_apply]
  exact ⟨τe, h, Module.finrank K W, hτe2, hτene, (fun c => by simpa using hτσ c), htr.2, hnd, rfl,
    Module.finrank_pos, htraceFinal⟩

private lemma bmSTS_centralizer_matrix_commute_adjoin
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hz : z ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e) :
    ∀ a ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S),
      ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * a =
      a * ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
  obtain ⟨hzS, -⟩ := Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hz)
  have hgen : ∀ s ∈ Units.val '' S,
      ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * s =
        s * ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
    rintro s ⟨u, hu, rfl⟩
    have h := (Subgroup.mem_centralizer_iff.mp hzS) u hu
    have h' := congrArg
      (fun w : GL (Fin n ⊕ Fin n) (GaloisField 2 f) =>
        (w : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) h
    simpa using h'.symm
  intro a ha
  exact Algebra.adjoin_induction
    (p := fun a _ => ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * a =
      a * ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))
    hgen (fun r => (Algebra.commute_algebraMap_right r
      ((z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))).eq)
    (fun a b _ _ ha hb => by rw [mul_add, add_mul, ha, hb])
    (fun a b _ _ ha hb => (Commute.mul_right ha hb).eq) ha

private lemma bmSTS_blockCentralizer_KLin
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K]
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (W : Submodule (GaloisField 2 f) ((Fin n ⊕ Fin n) → GaloisField 2 f))
    [Module K W] [IsScalarTower (GaloisField 2 f) K W]
    (hWeq : W = LinearMap.range (Matrix.mulVecLin e))
    (hact : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) (w : W),
      (Submodule.subtype W) ((π a) • w) =
        Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          ((Submodule.subtype W) w))
    (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e) :
    ∃ φ : W →ₗ[K] W,
      ∀ w : W,
        (Submodule.subtype W) (φ w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
            ((Submodule.subtype W) w) := by
  classical
  let Mz : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    ((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f))
  change ∃ φ : W →ₗ[K] W,
    ∀ w : W, (Submodule.subtype W) (φ w) = Matrix.mulVec Mz ((Submodule.subtype W) w)
  have hcomm : ∀ a ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S), Mz * a = a * Mz := by
    intro a ha
    exact bmSTS_centralizer_matrix_commute_adjoin n f S z.1 z.2 a ha
  let funw : W → W := fun w =>
    ⟨Matrix.mulVec Mz (w : (Fin n ⊕ Fin n) → GaloisField 2 f),
      hWeq.symm ▸ bmSTS_mulVec_mem_range_of_commute
        (show Commute Mz e from hcomm e he.1) (w : (Fin n ⊕ Fin n) → GaloisField 2 f)
        (hWeq ▸ w.2)⟩
  have hfunw : ∀ w : W,
      (Submodule.subtype W) (funw w) = Matrix.mulVec Mz ((Submodule.subtype W) w) :=
    fun w => rfl
  refine ⟨IsLinearMap.mk' funw ⟨?_, ?_⟩, ?_⟩
  · intro x y
    apply Subtype.ext
    change (Submodule.subtype W) (funw (x + y)) =
      (Submodule.subtype W) (funw x + funw y)
    simp only [hfunw, map_add, Matrix.mulVec_add]
  · intro c x
    obtain ⟨a, ha⟩ := hπsurj c
    apply Subtype.ext
    rw [← ha]
    change (Submodule.subtype W) (funw ((π a) • x)) =
      (Submodule.subtype W) ((π a) • funw x)
    rw [hfunw ((π a) • x), hact a x, hact a (funw x), hfunw x]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hcomm (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a.2]
  · intro w
    exact hfunw w

private theorem bmSTS_explicit_data_hKlC
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (W : Submodule (GaloisField 2 f) ((Fin n ⊕ Fin n) → GaloisField 2 f))
    [Module K W] [IsScalarTower (GaloisField 2 f) K W]
    (hWeq : W = LinearMap.range (Matrix.mulVecLin e))
    (hact : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) (w : W),
      (Submodule.subtype W) ((π a) • w) =
        Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          ((Submodule.subtype W) w))
    :
    ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        (Submodule.subtype W) (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ((Submodule.subtype W) w)
    := by
  classical
  let C := glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
  let mat : C → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    fun z => (((z : C) : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f))
  have hmat_mul : ∀ z z' : C, mat (z * z') = mat z * mat z' := by
    intro z z'
    simp only [mat, Subgroup.coe_mul, Units.val_mul]
  have hmat_one : mat (1 : C) = 1 := by
    simp only [mat, Subgroup.coe_one, Units.val_one]
  have hmat_mulinv : ∀ z : C, mat z * mat (z⁻¹) = 1 := by
    intro z
    rw [← hmat_mul z z⁻¹, mul_inv_cancel, hmat_one]
  have hmat_invmul : ∀ z : C, mat (z⁻¹) * mat z = 1 := by
    intro z
    rw [← hmat_mul z⁻¹ z, inv_mul_cancel, hmat_one]
  let φ : C → (W →ₗ[K] W) := fun z =>
    Classical.choose (bmSTS_blockCentralizer_KLin n f S he K π hπsurj W hWeq hact z)
  have hφ : ∀ (z : C) (w : W),
      (Submodule.subtype W) (φ z w) = Matrix.mulVec (mat z) ((Submodule.subtype W) w) := by
    intro z w
    exact Classical.choose_spec
      (bmSTS_blockCentralizer_KLin n f S he K π hπsurj W hWeq hact z) w
  refine ⟨MonoidHom.mk' (fun z =>
      LinearEquiv.ofLinearMap (φ z) (φ z⁻¹) ?_ ?_) ?_, ?_⟩
  · apply LinearMap.ext
    intro w
    apply Subtype.ext
    change (Submodule.subtype W) (φ z (φ z⁻¹ w)) = (Submodule.subtype W) w
    rw [hφ z (φ z⁻¹ w), hφ z⁻¹ w]
    rw [Matrix.mulVec_mulVec, hmat_mulinv z, Matrix.one_mulVec]
  · apply LinearMap.ext
    intro w
    apply Subtype.ext
    change (Submodule.subtype W) (φ z⁻¹ (φ z w)) = (Submodule.subtype W) w
    rw [hφ z⁻¹ (φ z w), hφ z w]
    rw [Matrix.mulVec_mulVec, hmat_invmul z, Matrix.one_mulVec]
  · intro z z'
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [LinearEquiv.mul_apply]
    change (Submodule.subtype W) (φ (z * z') w) =
      (Submodule.subtype W) (φ z (φ z' w))
    rw [hφ (z * z') w, hmat_mul z z', hφ z (φ z' w), hφ z' w]
    rw [Matrix.mulVec_mulVec]
  · intro z w
    change (Submodule.subtype W) (φ z w) = Matrix.mulVec (mat z) ((Submodule.subtype W) w)
    exact hφ z w

private theorem bmSTS_explicit_data_hKl
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K]
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (heWinj : Function.Injective eW)
    (hKlC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
        →* (W ≃ₗ[K] W),
      ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (w : W),
        eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
          Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w)) :
    ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, eW (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w := by
  intro x y hx hy T hT c w
  obtain ⟨ρ, hρ⟩ := hKlC
  let xC : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e :=
    ⟨x, hx⟩
  let yC : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e :=
    ⟨y, hy⟩
  have hmem : ⁅x, y⁆ ∈
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e := by
    have hcoe : ((xC * yC * xC⁻¹ * yC⁻¹ :
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e) :
        ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) = ⁅x, y⁆ := by
      simp only [xC, yC, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_mk]
    simpa [← hcoe] using (xC * yC * xC⁻¹ * yC⁻¹).2
  let z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e :=
    ⟨⁅x, y⁆, hmem⟩
  have hTw : ∀ u : W, T u = ((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) u := by
    intro u
    apply heWinj
    rw [hT u, hρ z u]
  rw [hTw (c • w), hTw w, map_smul]

private theorem bmSTS_suAction_smul
    (m' f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (g : (ggU .PSU m' (max f 1)).K) :
    ∀ (a : GaloisField 2 (2 * max f 1))
      (x : Fin m' → GaloisField 2 (2 * max f 1)),
      bmSTS_blockEmbeddingEV_PSU_suAction m' f g (a • x) =
        a • bmSTS_blockEmbeddingEV_PSU_suAction m' f g x := by
  intro a x
  let σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have heq : ggU .PSU m' (max f 1) =
      ⟨Unitary.SU σ m',
        Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte, σ]
  have hK : (ggU .PSU m' (max f 1)).K = ↥(Unitary.SU σ m') := congrArg LieUniversal.K heq
  let g' : ↥(Unitary.SU σ m') := hK ▸ g
  let M : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)) :=
    (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) g').1
  have hM : ∀ x : Fin m' → GaloisField 2 (2 * max f 1),
      bmSTS_blockEmbeddingEV_PSU_suAction m' f g x = Matrix.mulVecLin M x := by
    intro x
    simp only [bmSTS_blockEmbeddingEV_PSU_suAction]
    exact rfl
  rw [hM (a • x), hM x]
  exact (Matrix.mulVecLin M).map_smul a x

private theorem bmSTS_stdActionMap_smul
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K) :
    ∀ (d : K) (v : Fin m' → K),
      bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g (d • v) =
      d • bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g v := by
  intro d v
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) :=
    Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)
  let C := bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
  let φ := bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank
  have hC1 : C (d • v) = φ d • C v := by
    funext i
    simp only [C, φ, bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv, LinearEquiv.piCongrRight_apply,
      AlgEquiv.toLinearEquiv_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  have hC2 : ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      C.symm (φ d • y) = d • C.symm y := by
    intro y
    funext i
    change φ.symm (φ d * y i) = d * φ.symm (y i)
    rw [map_mul (φ.symm) (φ d) (y i), AlgEquiv.symm_apply_apply]
  change C.symm (bmSTS_blockEmbeddingEV_PSU_suAction m' f g (C (d • v))) =
    d • C.symm (bmSTS_blockEmbeddingEV_PSU_suAction m' f g (C v))
  rw [hC1, bmSTS_suAction_smul m' f g (φ d) (C v), hC2]

private theorem bmSTS_blockAction_smul
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K) :
    ∀ (c : K) (w : W),
      bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g (c • w) =
      c • bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g w := by
  intro c w
  let Φ : W ≃ₗ[GaloisField 2 f] (Fin m' → K) :=
    bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace
  let A : (Fin m' → K) ≃ₗ[GaloisField 2 f] (Fin m' → K) :=
    bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  haveI : FiniteDimensional K W := FiniteDimensional.of_finrank_pos (by omega)
  let ΦK : W ≃ₗ[K] (Fin m' → K) :=
    Classical.choose (CFSG.Fischer.Classification.exists_linearEquiv_herm_of_form
      (bmSTS_blockEmbeddingEV_PSU_unitaryInvolution n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
      (bmSTS_blockEmbeddingEV_PSU_isHermForm n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
      hnd hrank)
  have hΦ : ∀ (d : K) (x : W), Φ (d • x) = d • Φ x := by
    intro d x
    have hΦeq : Φ = LinearEquiv.restrictScalars (GaloisField 2 f) ΦK := rfl
    rw [hΦeq]
    exact ΦK.map_smul d x
  have hΦsymm : ∀ (d : K) (x : Fin m' → K), Φ.symm (d • x) = d • Φ.symm x := by
    intro d x
    have hΦsymm_eq : Φ.symm = LinearEquiv.restrictScalars (GaloisField 2 f) ΦK.symm := rfl
    rw [hΦsymm_eq]
    exact ΦK.symm.map_smul d x
  have hA : A (c • Φ w) = c • A (Φ w) := by
    change bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g (c • Φ w) =
      c • bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g (Φ w)
    rw [bmSTS_stdActionMap_smul]
  change (Φ.trans (A.trans Φ.symm)) (c • w) = c • (Φ.trans (A.trans Φ.symm)) w
  simp only [LinearEquiv.trans_apply, hΦ, hA, hΦsymm]

private theorem bmSTS_explicit_data_hcS
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (π : Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →ₐ[GaloisField 2 f] K)
    (hπsurj : Function.Surjective π)
    (W : Submodule (GaloisField 2 f) ((Fin n ⊕ Fin n) → GaloisField 2 f))
    [Module K W] [IsScalarTower (GaloisField 2 f) K W]
    (hWeq : W = LinearMap.range (Matrix.mulVecLin e))
    (hact : ∀ (a : Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) (w : W),
      (Submodule.subtype W) ((π a) • w) =
        Matrix.mulVec (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          ((Submodule.subtype W) w))
    (τ : K ≃+* K) (h : W → W →ₗ[K] K) (m' : ℕ)
    (heW : LinearMap.range (Submodule.subtype W) = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective (Submodule.subtype W))
    (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (htrace : ∀ (x y : W) (c : K),
      (Submodule.subtype W) x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) ((Submodule.subtype W) (c • y)) =
        Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g := by
  intro g s hs
  classical
  let A := Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
  have hpair : (Units.val '' S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f))).Pairwise Commute := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩ _
    exact (hS u hu u' hu').map (Units.coeHom (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)))
  letI : CommRing A := Algebra.adjoinCommRingOfComm (GaloisField 2 f) (s := Units.val '' S) hpair
  let Tg : GL (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  let Me : ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
      ((Fin n ⊕ Fin n) → GaloisField 2 f) := Matrix.mulVecLin e
  let Mt : ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
      ((Fin n ⊕ Fin n) → GaloisField 2 f) := Matrix.mulVecLin (Tg : Matrix (Fin n ⊕ Fin n)
        (Fin n ⊕ Fin n) (GaloisField 2 f))
  let Ms : ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
      ((Fin n ⊕ Fin n) → GaloisField 2 f) := Matrix.mulVecLin (s : Matrix (Fin n ⊕ Fin n)
        (Fin n ⊕ Fin n) (GaloisField 2 f))
  let a₀ : A := ⟨(s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)),
    Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
  have hse : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e =
      e * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
    have h := congrArg Subtype.val (mul_comm a₀ (⟨e, he.1⟩ : A))
    simpa [a₀] using h
  have hpoint : ∀ v : (Fin n ⊕ Fin n) → GaloisField 2 f, Mt (Ms v) = Ms (Mt v) := by
    intro v
    have hMeMe : ∀ x, Me (Me x) = Me x := by
      intro x
      change Matrix.mulVec e (Matrix.mulVec e x) = Matrix.mulVec e x
      rw [Matrix.mulVec_mulVec, he.2.1]
    have hMsMe : ∀ x, Ms (Me x) = Me (Ms x) := by
      intro x
      change Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          (Matrix.mulVec e x) = Matrix.mulVec e (Matrix.mulVec (s : Matrix (Fin n ⊕ Fin n)
            (Fin n ⊕ Fin n) (GaloisField 2 f)) x)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hse]
    have hMs_ker : ∀ x, Me x = 0 → Me (Ms x) = 0 := by
      intro x hx
      rw [← hMsMe x, hx, map_zero]
    have hMt_range : ∀ w : ↥W, Mt ((Submodule.subtype W) w) =
        (Submodule.subtype W) (bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj
          hdeg₁ hdeg₂ hJe K τ W h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank
          hm' hKrank htrace g w) := by
      intro w
      exact (bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).1 w
    have hMt_ker : ∀ b, Me b = 0 → Mt b = b := by
      intro b hb
      exact (bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).2 b
        (LinearMap.mem_ker.mpr hb)
    have hMs_range : ∀ w : ↥W, Ms ((Submodule.subtype W) w) =
        (Submodule.subtype W) (π a₀ • w) := by
      intro w
      exact (hact a₀ w).symm
    have hBA : ∀ (c : K) (w : ↥W),
        bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
          h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
          (c • w) =
        c • bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
          W h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g w :=
      bmSTS_blockAction_smul n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
    have hker_v : Me (v - Me v) = 0 := by
      rw [map_sub, hMeMe v, sub_self]
    have hrange : Mt (Ms (Me v)) = Ms (Mt (Me v)) := by
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (by
        rw [heW]
        exact LinearMap.mem_range_self Me v)
      calc Mt (Ms (Me v))
          = Mt (Ms ((Submodule.subtype W) w)) := by rw [← hw]
        _ = Mt ((Submodule.subtype W) (π a₀ • w)) := by rw [hMs_range w]
        _ = (Submodule.subtype W) (bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he
              hadj hdeg₁ hdeg₂ hJe K τ W h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm
              hnd hrank hm' hKrank htrace g (π a₀ • w)) := hMt_range _
        _ = (Submodule.subtype W) (π a₀ • bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS
              hodd he hadj hdeg₁ hdeg₂ hJe K τ W h (Submodule.subtype W) m' heW heWinj hτ2 hτne
              hsymm hnd hrank hm' hKrank htrace g w) := by rw [hBA (π a₀) w]
        _ = Ms ((Submodule.subtype W) (bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd
              he hadj hdeg₁ hdeg₂ hJe K τ W h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm
              hnd hrank hm' hKrank htrace g w)) := (hMs_range _).symm
        _ = Ms (Mt ((Submodule.subtype W) w)) := by rw [hMt_range w]
        _ = Ms (Mt (Me v)) := by rw [hw]
    calc Mt (Ms v)
        = Mt (Ms (Me v + (v - Me v))) := by
            rw [show Me v + (v - Me v) = v by abel]
      _ = Mt (Ms (Me v) + Ms (v - Me v)) := by rw [map_add]
      _ = Mt (Ms (Me v)) + Mt (Ms (v - Me v)) := by rw [map_add]
      _ = Ms (Mt (Me v)) + Ms (v - Me v) := by
            rw [hrange, hMt_ker (Ms (v - Me v)) (hMs_ker (v - Me v) hker_v)]
      _ = Ms (Mt (Me v)) + Ms (Mt (v - Me v)) := by
            exact congrArg (fun z => Ms (Mt (Me v)) + Ms z)
              (hMt_ker (v - Me v) hker_v).symm
      _ = Ms (Mt (Me v) + Mt (v - Me v)) := by rw [← map_add]
      _ = Ms (Mt (Me v + (v - Me v))) := by rw [← map_add]
      _ = Ms (Mt v) := by rw [show Me v + (v - Me v) = v by abel]
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hpoint v

private theorem bmSTS_explicit_data
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra (GaloisField 2 f) K) (_ : Finite K)
      (hKrank : Module.finrank (GaloisField 2 f) K = 2)
      (τ : K ≃+* K)
      (W : Type) (_ : AddCommGroup W) (_ : Module K W)
      (_ : Module (GaloisField 2 f) W) (_ : IsScalarTower (GaloisField 2 f) K W)
      (h : W → W →ₗ[K] K)
      (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
      (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
      (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a)
      (hτne : τ ≠ RingHom.id K)
      (hτfix : ∀ c : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K c) =
        algebraMap (GaloisField 2 f) K c)
      (hsymm : ∀ x y : W, h y x = τ (h x y))
      (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
      (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
      (hm3 : 2 ≤ m')
      (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m')
      (htrace : ∀ (x y : W) (c : K),
        eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
        Algebra.trace (GaloisField 2 f) K (c * h x y))
      (hKlinRepC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
          →* (W ≃ₗ[K] W),
        ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
          (w : W),
          eW (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
            Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
              GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) (eW w))
      (hKlinRep : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
        (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
        (T : W →ₗ[GaloisField 2 f] W),
        (∀ w : W, eW (T w) =
          Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) (eW w)) →
        ∀ (c : K) (w : W), T (c • w) = c • T w),
      (∀ (g : (ggU .PSU m' (max f 1)).K)
        (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
        bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
          h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
        s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
          h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) := by
  classical
  obtain ⟨K, hKf, hKa, hKfin, hKrank, π, hπsurj, W, hWmodK, hWtower, hWeq, hact⟩ :=
    bmSTS_explicit_data_canonicalKAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 f) K := hKa
  letI : Finite K := hKfin
  letI : Module K W := hWmodK
  letI : IsScalarTower (GaloisField 2 f) K W := hWtower
  obtain ⟨τ, h, m', hτ2, hτne, hτfix, hsymm, hnd, hrank, hm', htrace⟩ :=
    bmSTS_explicit_data_traceTransferForm n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank π
      hπsurj W hWeq hact
  have heW : LinearMap.range (Submodule.subtype W) = LinearMap.range (Matrix.mulVecLin e) := by
    rw [Submodule.range_subtype, hWeq]
  have heWinj : Function.Injective (Submodule.subtype W) := fun a b hab => Subtype.ext hab
  have hKlC : ∃ ρ : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
          →* (W ≃ₗ[K] W),
        ∀ (z : glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
          (w : W),
          (Submodule.subtype W) (((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) w) =
            Matrix.mulVec (((z : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
              GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
              ((Submodule.subtype W) w) :=
    bmSTS_explicit_data_hKlC n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank π hπsurj W hWeq hact
  have hKl : ∀ (x y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (hx : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (hy : y ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e)
      (T : W →ₗ[GaloisField 2 f] W),
      (∀ w : W, (Submodule.subtype W) (T w) =
        Matrix.mulVec (((⁅x, y⁆ : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) ((Submodule.subtype W) w)) →
      ∀ (c : K) (w : W), T (c • w) = c • T w :=
    bmSTS_explicit_data_hKl n f S e K W (Submodule.subtype W) heWinj hKlC
  have hcS : ∀ (g : (ggU .PSU m' (max f 1)).K)
      (s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)), s ∈ S →
      bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g * s =
      s * bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :=
    bmSTS_explicit_data_hcS n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K hKrank π hπsurj W hWeq
      hact τ h m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace
  have hnq := bmSTS_explicit_data_hnq n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K hKrank τ W
    h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace hKlC hKl
  have hm3 : 2 ≤ m' := bmSTS_explicit_data_hm3 n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
    K hKrank τ W h (Submodule.subtype W) m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hnq htrace
      hKlC hKl hcS
  exact ⟨K, hKf, hKa, hKfin, hKrank, τ, W, (inferInstance : AddCommGroup W), hWmodK,
    (inferInstance : Module (GaloisField 2 f) W), hWtower, h, Submodule.subtype W, m', heW,
    heWinj, hτ2, hτne, hτfix, hsymm, hnd, hrank, hm', hm3, hnq, htrace, hKlC, hKl, hcS⟩

private theorem bmSTS_ggU_PSU_quasisimple
    (f m' : ℕ) (hm3 : 2 ≤ m')
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ m') :
    CFSG.IsQuasisimple ((ggU .PSU m' (max f 1)).K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have hunfold : ∀ k : ℕ, ggU .PSU k (max f 1) =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) k,
        Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) k⟩ := by
    intro k
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  by_cases hm3' : 3 ≤ m'
  · have hF : Nat.card (GaloisField 2 (2 * max f 1)) = (2 ^ max f 1) ^ 2 :=
      card_galoisField_two_mul 2 (max f 1) hf
    haveI : CharP (GaloisField 2 (2 * max f 1)) 2 :=
      CFSG.ClassicalGroups.Unitary.charP_of_card_sq hF
    have hSU := CFSG.LieType.Universal.Unitary.isQuasisimple_SU
      (F := GaloisField 2 (2 * max f 1)) (p := 2) (f := max f 1) (n := m') hF hm3'
      (by rintro h
          rcases hnq with hq | hm
          · exact hq (Prod.ext_iff.mp h).2
          · have h1 : m' = 3 := (Prod.ext_iff.mp h).1
            omega)
    rw [hunfold m']
    exact hSU
  · have hm2 : m' = 2 := by omega
    subst hm2
    have hq : 2 ^ max f 1 ≠ 2 := by
      rcases hnq with hq | hm
      · exact hq
      · exact absurd hm (by omega)
    let F := GaloisField 2 (2 * max f 1)
    have hF : Nat.card F = (2 ^ max f 1) ^ 2 := card_galoisField_two_mul 2 (max f 1) hf
    haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hF
    have h4 : 4 ≤ Nat.card (CFSG.LieType.Steinberg.fixedSubfield F 2 (max f 1)) := by
      rw [CFSG.LieType.Steinberg.card_fixedSubfield hF]
      have h2 : 2 ≤ max f 1 := by
        by_contra h
        have : max f 1 = 1 := by omega
        exact hq (by rw [this]; norm_num)
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ max f 1 := Nat.pow_le_pow_right (by norm_num) h2
    obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hF
    let e := CFSG.LieType.Steinberg.hypEquiv (F := F) (p := 2) (f := max f 1) hζ0 hζ
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2)
        (CFSG.LieType.Steinberg.fixedSubfield F 2 (max f 1))) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ h4
    haveI : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (CFSG.LieType.Steinberg.fixedSubfield F 2 (max f 1))) := inferInstance
    haveI : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (CFSG.LieType.Steinberg.fixedSubfield F 2 (max f 1))) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have hnc : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (CFSG.LieType.Steinberg.fixedSubfield F 2 (max f 1)), a * b ≠ b * a := by
      by_contra h
      push Not at h
      haveI : IsMulCommutative (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
          (CFSG.LieType.Steinberg.fixedSubfield F 2 (max f 1))) := ⟨⟨h⟩⟩
      exact Group.IsPerfect.not_isMulCommutative _ ‹_›
    have hSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2)
        (CFSG.LieType.Steinberg.fixedSubfield F 2 (max f 1))) :=
      ⟨CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ h4,
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4, hnc⟩
    have hSU : CFSG.IsQuasisimple
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 (max f 1)) 2) :=
      CFSG.IsQuasisimple.of_mulEquiv e.symm hSL
    rw [hunfold 2]
    exact hSU

private theorem bmSTS_derived_quasisimple
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆) :
    IsQuasisimple ↥⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆ := by
  obtain ⟨K, hKf, hKa, hKfin, hKrank, τ, W, hWadd, hWmodK, hWmodF, hWtower, h, eW, m', heW,
    heWinj, hτ2, hτne, hτfix, hsymm, hnd, hrank, hm', hm3, hnq, htrace, hKlinRepC, hKlinRep, hcommS⟩
        :=
    bmSTS_explicit_data n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 f) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWadd
  letI : Module K W := hWmodK
  letI : Module (GaloisField 2 f) W := hWmodF
  letI : IsScalarTower (GaloisField 2 f) K W := hWtower
  let C := glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e
  let ι₀ := bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
    heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
  have hrange : ι₀.range = ⁅C, C⁆ :=
    bmSTS_blockEmbeddingEV_PSU_hom_range_eq_derived n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace hKlinRepC hKlinRep
      hcommS
  have hinj : Function.Injective ι₀ :=
    bmSTS_blockEmbeddingEV_PSU_hom_injective n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
  have hKq : CFSG.IsQuasisimple ((ggU .PSU m' (max f 1)).K) :=
    bmSTS_ggU_PSU_quasisimple f m' hm3 hnq
  have hbij : Function.Bijective ι₀.rangeRestrict :=
    ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), ι₀.rangeRestrict_surjective⟩
  let φ : (ggU .PSU m' (max f 1)).K ≃* ↥⁅C, C⁆ :=
    (MulEquiv.ofBijective ι₀.rangeRestrict hbij).trans (MulEquiv.subgroupCongr hrange)
  exact CFSG.IsQuasisimple.of_mulEquiv φ.symm hKq

private theorem bmSTS_component_eq_of_quasisimple
    {G : Type*} [Group G] {N : Subgroup G} (hNq : CFSG.IsQuasisimple N)
    {J' : Subgroup G} (hJe : IsComponentOf J' N) : J' = N := by
  have hNo : CFSG.Open.IsQuasisimple N :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hNq
  have hJq : CFSG.Open.IsQuasisimple J' := hJe.2.2
  have hKq : CFSG.Open.IsQuasisimple ↥(J'.subgroupOf N) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJe.1) hJq
  letI : Group.IsPerfect ↥(J'.subgroupOf N) := ⟨hKq.1⟩
  have hKsub : CFSG.Open.IsSubnormal (J'.subgroupOf N) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hJe.1).mp
        (CFSG.Assembly.isSubnormal_iff_open.mp hJe.2.1))
  rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hNo
    (J'.subgroupOf N) hKsub with hbot | htop
  · exact absurd hbot ((Subgroup.nontrivial_iff_ne_bot _).mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hKq))
  · exact le_antisymm hJe.1 (Subgroup.subgroupOf_eq_top.mp htop)

private theorem bmSTS_component_eq
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆) :
    J' = ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆ := by
  have hNq : CFSG.IsQuasisimple
      ↥⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆ :=
    bmSTS_derived_quasisimple n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  exact bmSTS_component_eq_of_quasisimple hNq hJe

private theorem bmSTS_rangeEqJ'
    {G : Type} [Group G] {J' K : Subgroup G} {H : Type} [Group H] {ι : H →* G}
    (hrange : ι.range = K) (hJ' : J' = K) : ι.range = J' := by
  rw [hJ', hrange]

private theorem bmSTS_hom_action
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    (∀ (g : (ggU .PSU m' (max f 1)).K) (x : W),
      Matrix.mulVec ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
          heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g)) (eW x) =
      eW ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
        (bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
          m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
          ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
            eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) x)))) ∧
    (∀ (g : (ggU .PSU m' (max f 1)).K) (z : (Fin n ⊕ Fin n) → GaloisField 2 f),
      z ∈ LinearMap.range (Matrix.mulVecLin ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) - e)) →
      Matrix.mulVec ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
          heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g)) z = z) := by
  constructor
  · intro g x
    have happ := (bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).1 x
    change Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
        hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (eW x) =
      eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) x)
    exact happ
  · intro g z hz
    have hzker : z ∈ LinearMap.ker (Matrix.mulVecLin e) := by
      obtain ⟨v, rfl⟩ := hz
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, IsIdempotentElem.mul_one_sub_self he.2.1, Matrix.zero_mulVec]
    have happ := (bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).2 z hzker
    change Matrix.mulVec ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
        hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) z = z
    exact happ

private theorem bmSTS_rootPair_longRoot
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∃ β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ,
      GGLongRoot (ggU .PSU m' (max f 1)).D β₀ := by
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have e : ggU .PSU m' (max f 1) =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1))
          2 (max f 1)) m',
        Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  rw [e]
  obtain ⟨γ, hγ, hmax⟩ :=
    exists_maxHeight (D := Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m')
      (show 0 < m' / 2 by omega)
  exact ⟨γ, 1, γ, hγ, hmax, by rfl⟩

private theorem bmSTS_rootGroup_fixedTransvection
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (β₀ : Fin (n / 2) → ℤ)
    (hlong : GGLongRoot (Unitary.rootDatum hc n) β₀) :
    ∃ v₀ w₀ : Fin n → F,
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₀ i))
        (Unitary.antidiag n) ⬝ᵥ v₀ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₀ i))
        (Unitary.antidiag n) ⬝ᵥ w₀ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₀ i))
        (Unitary.antidiag n) ⬝ᵥ w₀ = 1 ∧
      ∃ u : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n),
        (((Unitary.rootDatum hc n).rootGroup β₀).map (MulAut.conj u).toMonoidHom).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) v₀ ∧
        (((Unitary.rootDatum hc n).rootGroup (-β₀)).map (MulAut.conj u).toMonoidHom).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) w₀ := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hlong
  have hβ : weylAction (Unitary.rootDatum hc n).isFiniteType w γ₀ ∈
      (Unitary.rootDatum hc n).roots :=
    weylAction_mem_roots (Unitary.rootDatum hc n).isFiniteType w hγ₀
  obtain ⟨v, w', hvv, hww, hvw, h1, h2⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_unitTransvGroup_eq_conj_rootGroup_SU
      hc n hβ ⟨w, γ₀, hγ₀, hmax, rfl⟩ 1
  exact ⟨v, w', hvv, hww, hvw, 1, h1, h2⟩

private noncomputable def bmSTS_transvectionModelElem
    (f : ℕ) {G W : Type} [Group G] [AddCommGroup W] [Module (GaloisField 2 f) W]
    (R : Subgroup G) (act : G → W → W) (T : W → W)
    (h : ∃ g ∈ R, ∀ x : W, act g x = T x) : G :=
  Classical.choose h

private lemma bmSTS_dotProduct_mulVec_comm (n f : ℕ)
    (x y : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    Matrix.mulVec (bmSTS_J n f) x ⬝ᵥ y =
      x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) y := by
  calc Matrix.mulVec (bmSTS_J n f) x ⬝ᵥ y
      = y ⬝ᵥ Matrix.mulVec (bmSTS_J n f) x := dotProduct_comm _ _
    _ = x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) y := (bmSTS_form_symm n f x y).symm

private theorem bmSTS_blockExtend_transvection_uniform
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (v : W) (v₀ : Fin m' → K)
    (hv : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm v₀)
    (hvv : h v v = 0) (ω : K) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hroot : ∀ c : GaloisField 2 f,
      ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ∀ x : W,
          bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
              h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x =
            x + (c • h v x) • v) :
    ∀ c : GaloisField 2 f,
      let g := bmSTS_transvectionModelElem f ((ggU .PSU m' (max f 1)).D.rootGroup β₀)
        (fun g x => bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂
          hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x)
        (fun x => x + (c • h v x) • v) (hroot c);
      g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ ∧
      (∀ x : W,
        bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
            h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x =
          x + (c • h v x) • v) ∧
      ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
            h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
              GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        1 + c • (Matrix.vecMulVec (eW v) (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) +
          Matrix.vecMulVec (eW (ω • v)) (Matrix.mulVec (bmSTS_J n f) (eW v))) := by
  intro c
  simp only [bmSTS_transvectionModelElem]
  obtain ⟨hgmem, hgact⟩ := Classical.choose_spec (hroot c)
  refine ⟨hgmem, hgact, ?_⟩
  haveI : FiniteDimensional (GaloisField 2 f) K := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (GaloisField 2 f) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsQuadraticExtension (GaloisField 2 f) K :=
    Algebra.IsQuadraticExtension.mk hKrank
  have hchar2 : (2 : K) = 0 :=
    bmSTS_charP_two n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank
  have hτlin := bmSTS_tauFixesBase n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne
  obtain ⟨σ, hσne, hτσ, -⟩ :=
    bmSTS_tau_eq_canonical n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne hτlin
  have hτtrace : ∀ z : K,
      algebraMap (GaloisField 2 f) K (Algebra.trace (GaloisField 2 f) K z) = z + τ z := by
    intro z
    have h := Algebra.IsQuadraticExtension.algebraMap_trace_eq_add (GaloisField 2 f) K hσne z
    rw [h, hτσ z]
  have hωω : ω + ω = 0 := by rw [← two_mul, hchar2, zero_mul]
  have hτω : τ ω = ω + 1 := by
    have h := hτtrace ω
    rw [hω, map_one, eq_comm] at h
    rw [← h, ← add_assoc, hωω, zero_add]
  have hkey : ∀ k : K,
      k = algebraMap (GaloisField 2 f) K (Algebra.trace (GaloisField 2 f) K (τ ω * k)) +
        algebraMap (GaloisField 2 f) K (Algebra.trace (GaloisField 2 f) K k) * ω := by
    intro k
    have h1 : algebraMap (GaloisField 2 f) K
        (Algebra.trace (GaloisField 2 f) K (τ ω * k)) = (ω + 1) * k + ω * τ k := by
      rw [hτtrace (τ ω * k)]
      have h2 : τ (τ ω * k) = ω * τ k := by rw [map_mul, hτ2 ω]
      rw [h2, hτω]
    have h3 : algebraMap (GaloisField 2 f) K (Algebra.trace (GaloisField 2 f) K k) = k + τ k :=
      hτtrace k
    rw [h1, h3]
    rw [show ((ω + 1) * k + ω * τ k) + (k + τ k) * ω =
        k + (2 : K) * (ω * k + ω * τ k) by ring]
    rw [hchar2, zero_mul, add_zero]
  have hkv : ∀ k : K,
      eW (k • v) = Algebra.trace (GaloisField 2 f) K (τ ω * k) • eW v +
        Algebra.trace (GaloisField 2 f) K k • eW (ω • v) := by
    intro k
    conv_lhs => rw [hkey k]
    rw [add_smul, mul_smul, algebraMap_smul, algebraMap_smul, map_add, map_smul, map_smul]
  have htrace1 : ∀ w : W, (Matrix.mulVec (bmSTS_J n f) (eW v)) ⬝ᵥ eW w =
      Algebra.trace (GaloisField 2 f) K (h v w) := by
    intro w
    rw [bmSTS_dotProduct_mulVec_comm]
    simpa using htrace v w 1
  have htrace2 : ∀ w : W, (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) ⬝ᵥ eW w =
      Algebra.trace (GaloisField 2 f) K (τ ω * h v w) := by
    intro w
    rw [bmSTS_dotProduct_mulVec_comm]
    have h := htrace (ω • v) w 1
    simp only [one_smul, one_mul] at h
    rw [h]
    congr 1
    rw [hsymm w (ω • v), map_smul, smul_eq_mul, map_mul, hsymm v w, hτ2]
  let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    (bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (Classical.choose (hroot c)) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f))
  let T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    1 + c • (Matrix.vecMulVec (eW v) (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) +
      Matrix.vecMulVec (eW (ω • v)) (Matrix.mulVec (bmSTS_J n f) (eW v)))
  change M = T
  have hMa : ∀ a : (Fin n ⊕ Fin n) → GaloisField 2 f,
      a ∈ LinearMap.range (Matrix.mulVecLin e) → Matrix.mulVec M a = Matrix.mulVec T a := by
    intro a ha
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (show a ∈ LinearMap.range eW by rw [heW]; exact ha)
    rw [← hw]
    have hM1 : Matrix.mulVec M (eW w) = eW w + c •
        (Algebra.trace (GaloisField 2 f) K (τ ω * h v w) • eW v +
          Algebra.trace (GaloisField 2 f) K (h v w) • eW (ω • v)) := by
      rw [show Matrix.mulVec M (eW w) = eW (w + (c • h v w) • v) by
        rw [(bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
          heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
          (Classical.choose (hroot c))).1 w, hgact w]]
      rw [map_add]
      congr 1
      rw [show (c • h v w) • v = c • ((h v w) • v) by
        rw [Algebra.smul_def, mul_smul, algebraMap_smul]]
      rw [map_smul, hkv (h v w)]
    have hT1 : Matrix.mulVec T (eW w) = eW w + c •
        (Algebra.trace (GaloisField 2 f) K (τ ω * h v w) • eW v +
          Algebra.trace (GaloisField 2 f) K (h v w) • eW (ω • v)) := by
      simp only [T, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        Matrix.vecMulVec_mulVec, op_smul_eq_smul]
      rw [htrace2 w, htrace1 w]
    rw [hM1, hT1]
  have hMb : ∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
      b ∈ LinearMap.ker (Matrix.mulVecLin e) → Matrix.mulVec M b = Matrix.mulVec T b := by
    intro b hb
    have hM2 : Matrix.mulVec M b = b :=
      (bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
        (Classical.choose (hroot c))).2 b hb
    have horth1 : (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) ⬝ᵥ b = 0 := by
      rw [bmSTS_dotProduct_mulVec_comm, ← Matrix.toBilin'_apply']
      exact bmSTS_blockExtend_orthogonal n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (eW (ω • v))
        (by rw [← heW]; exact ⟨ω • v, rfl⟩) b hb
    have horth2 : (Matrix.mulVec (bmSTS_J n f) (eW v)) ⬝ᵥ b = 0 := by
      rw [bmSTS_dotProduct_mulVec_comm, ← Matrix.toBilin'_apply']
      exact bmSTS_blockExtend_orthogonal n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (eW v)
        (by rw [← heW]; exact ⟨v, rfl⟩) b hb
    have hT1 : Matrix.mulVec T b = b + c • ((Matrix.mulVec (bmSTS_J n f) (eW (ω • v)) ⬝ᵥ b) • eW v +
        (Matrix.mulVec (bmSTS_J n f) (eW v) ⬝ᵥ b) • eW (ω • v)) := by
      simp only [T, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    rw [hM2, hT1, horth1, horth2, zero_smul, zero_smul, add_zero, smul_zero, add_zero]
  rw [Matrix.ext_iff_mulVec]
  intro x
  have hee : e * e = e := he.2.1
  have hL : IsIdempotentElem (Matrix.mulVecLin e :
      ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
        ((Fin n ⊕ Fin n) → GaloisField 2 f)) := by
    show (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e
    rw [← Matrix.mulVecLin_mul, hee]
  have hcompl := LinearMap.IsIdempotentElem.isCompl hL
  let pr := Submodule.prodEquivOfIsCompl _ _ hcompl
  let a := (pr.symm x).1
  let b := (pr.symm x).2
  have hx : x = (↑a : (Fin n ⊕ Fin n) → GaloisField 2 f) + ↑b := by
    rw [← pr.apply_symm_apply x, Submodule.coe_prodEquivOfIsCompl']
  rw [hx]
  rw [Matrix.mulVec_add M, Matrix.mulVec_add T]
  rw [hMa _ a.property, hMb _ b.property]

private theorem bmSTS_blockExtend_transvection_matrix
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (v : W) (ω : K) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (g : (ggU .PSU m' (max f 1)).K) (c : GaloisField 2 f)
    (hact : ∀ x : W,
      bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x =
      x + (c • h v x) • v) :
    ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + c • (Matrix.vecMulVec (eW v) (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) +
        Matrix.vecMulVec (eW (ω • v)) (Matrix.mulVec (bmSTS_J n f) (eW v))) := by
  haveI : FiniteDimensional (GaloisField 2 f) K := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (GaloisField 2 f) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsQuadraticExtension (GaloisField 2 f) K :=
    Algebra.IsQuadraticExtension.mk hKrank
  have hchar2 : (2 : K) = 0 :=
    bmSTS_charP_two n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank
  have hτlin := bmSTS_tauFixesBase n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne
  obtain ⟨σ, hσne, hτσ, -⟩ :=
    bmSTS_tau_eq_canonical n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne hτlin
  have hτtrace : ∀ z : K,
      algebraMap (GaloisField 2 f) K (Algebra.trace (GaloisField 2 f) K z) = z + τ z := by
    intro z
    have h := Algebra.IsQuadraticExtension.algebraMap_trace_eq_add (GaloisField 2 f) K hσne z
    rw [h, hτσ z]
  have hωω : ω + ω = 0 := by rw [← two_mul, hchar2, zero_mul]
  have hτω : τ ω = ω + 1 := by
    have h := hτtrace ω
    rw [hω, map_one, eq_comm] at h
    rw [← h, ← add_assoc, hωω, zero_add]
  have hkey : ∀ k : K,
      k = algebraMap (GaloisField 2 f) K (Algebra.trace (GaloisField 2 f) K (τ ω * k)) +
        algebraMap (GaloisField 2 f) K (Algebra.trace (GaloisField 2 f) K k) * ω := by
    intro k
    have h1 : algebraMap (GaloisField 2 f) K
        (Algebra.trace (GaloisField 2 f) K (τ ω * k)) = (ω + 1) * k + ω * τ k := by
      rw [hτtrace (τ ω * k)]
      have h2 : τ (τ ω * k) = ω * τ k := by rw [map_mul, hτ2 ω]
      rw [h2, hτω]
    have h3 : algebraMap (GaloisField 2 f) K (Algebra.trace (GaloisField 2 f) K k) = k + τ k :=
      hτtrace k
    rw [h1, h3]
    rw [show ((ω + 1) * k + ω * τ k) + (k + τ k) * ω =
        k + (2 : K) * (ω * k + ω * τ k) by ring]
    rw [hchar2, zero_mul, add_zero]
  have hkv : ∀ k : K,
      eW (k • v) = Algebra.trace (GaloisField 2 f) K (τ ω * k) • eW v +
        Algebra.trace (GaloisField 2 f) K k • eW (ω • v) := by
    intro k
    conv_lhs => rw [hkey k]
    rw [add_smul, mul_smul, algebraMap_smul, algebraMap_smul, map_add, map_smul, map_smul]
  have htrace1 : ∀ w : W, (Matrix.mulVec (bmSTS_J n f) (eW v)) ⬝ᵥ eW w =
      Algebra.trace (GaloisField 2 f) K (h v w) := by
    intro w
    rw [bmSTS_dotProduct_mulVec_comm]
    simpa using htrace v w 1
  have htrace2 : ∀ w : W, (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) ⬝ᵥ eW w =
      Algebra.trace (GaloisField 2 f) K (τ ω * h v w) := by
    intro w
    rw [bmSTS_dotProduct_mulVec_comm]
    have h := htrace (ω • v) w 1
    simp only [one_smul, one_mul] at h
    rw [h]
    congr 1
    rw [hsymm w (ω • v), map_smul, smul_eq_mul, map_mul, hsymm v w, hτ2]
  let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    (bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f))
  let T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    1 + c • (Matrix.vecMulVec (eW v) (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) +
      Matrix.vecMulVec (eW (ω • v)) (Matrix.mulVec (bmSTS_J n f) (eW v)))
  change M = T
  have hMa : ∀ a : (Fin n ⊕ Fin n) → GaloisField 2 f,
      a ∈ LinearMap.range (Matrix.mulVecLin e) → Matrix.mulVec M a = Matrix.mulVec T a := by
    intro a ha
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (show a ∈ LinearMap.range eW by rw [heW]; exact ha)
    rw [← hw]
    have hM1 : Matrix.mulVec M (eW w) = eW w + c •
        (Algebra.trace (GaloisField 2 f) K (τ ω * h v w) • eW v +
          Algebra.trace (GaloisField 2 f) K (h v w) • eW (ω • v)) := by
      rw [show Matrix.mulVec M (eW w) = eW (w + (c • h v w) • v) by
        rw [(bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
          heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).1 w, hact w]]
      rw [map_add]
      congr 1
      rw [show (c • h v w) • v = c • ((h v w) • v) by
        rw [Algebra.smul_def, mul_smul, algebraMap_smul]]
      rw [map_smul, hkv (h v w)]
    have hT1 : Matrix.mulVec T (eW w) = eW w + c •
        (Algebra.trace (GaloisField 2 f) K (τ ω * h v w) • eW v +
          Algebra.trace (GaloisField 2 f) K (h v w) • eW (ω • v)) := by
      simp only [T, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        Matrix.vecMulVec_mulVec, op_smul_eq_smul]
      rw [htrace2 w, htrace1 w]
    rw [hM1, hT1]
  have hMb : ∀ b : (Fin n ⊕ Fin n) → GaloisField 2 f,
      b ∈ LinearMap.ker (Matrix.mulVecLin e) → Matrix.mulVec M b = Matrix.mulVec T b := by
    intro b hb
    have hM2 : Matrix.mulVec M b = b :=
      (bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).2 b hb
    have horth1 : (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) ⬝ᵥ b = 0 := by
      rw [bmSTS_dotProduct_mulVec_comm, ← Matrix.toBilin'_apply']
      exact bmSTS_blockExtend_orthogonal n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (eW (ω • v))
        (by rw [← heW]; exact ⟨ω • v, rfl⟩) b hb
    have horth2 : (Matrix.mulVec (bmSTS_J n f) (eW v)) ⬝ᵥ b = 0 := by
      rw [bmSTS_dotProduct_mulVec_comm, ← Matrix.toBilin'_apply']
      exact bmSTS_blockExtend_orthogonal n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (eW v)
        (by rw [← heW]; exact ⟨v, rfl⟩) b hb
    have hT1 : Matrix.mulVec T b = b + c • ((Matrix.mulVec (bmSTS_J n f) (eW (ω • v)) ⬝ᵥ b) • eW v +
        (Matrix.mulVec (bmSTS_J n f) (eW v) ⬝ᵥ b) • eW (ω • v)) := by
      simp only [T, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    rw [hM2, hT1, horth1, horth2, zero_smul, zero_smul, add_zero, smul_zero, add_zero]
  rw [Matrix.ext_iff_mulVec]
  intro x
  have hee : e * e = e := he.2.1
  have hL : IsIdempotentElem (Matrix.mulVecLin e :
      ((Fin n ⊕ Fin n) → GaloisField 2 f) →ₗ[GaloisField 2 f]
        ((Fin n ⊕ Fin n) → GaloisField 2 f)) := by
    show (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e
    rw [← Matrix.mulVecLin_mul, hee]
  have hcompl := LinearMap.IsIdempotentElem.isCompl hL
  let pr := Submodule.prodEquivOfIsCompl _ _ hcompl
  let a := (pr.symm x).1
  let b := (pr.symm x).2
  have hx : x = (↑a : (Fin n ⊕ Fin n) → GaloisField 2 f) + ↑b := by
    rw [← pr.apply_symm_apply x, Submodule.coe_prodEquivOfIsCompl']
  rw [hx]
  rw [Matrix.mulVec_add M, Matrix.mulVec_add T]
  rw [hMa _ a.property, hMb _ b.property]

private theorem bmSTS_eW_pair_facts
    (n f : ℕ) {K : Type} [Field K] [Algebra (GaloisField 2 f) K]
    {W : Type} [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (heWinj : Function.Injective eW)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (v : W) (hv : v ≠ 0) (hvv : h v v = 0) (ω : K)
    (hω : Algebra.trace (GaloisField 2 f) K ω = 1) :
    eW v ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (ω • v)) = 0 ∧
    LinearIndependent (GaloisField 2 f) ![eW v, eW (ω • v)] ∧
    altSiegelGroup (bmSTS_J n f) (eW v) (eW (ω • v)) =
      Subgroup.closure {x : GL (Fin n ⊕ Fin n) (GaloisField 2 f) |
        ∃ c : GaloisField 2 f,
          (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
            1 + c • (Matrix.vecMulVec (eW v) (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) +
              Matrix.vecMulVec (eW (ω • v)) (Matrix.mulVec (bmSTS_J n f) (eW v)))} := by
  have htr_base : ∀ c : GaloisField 2 f,
      Algebra.trace (GaloisField 2 f) K (algebraMap (GaloisField 2 f) K c) = 0 := by
    intro c
    rw [Algebra.trace_algebraMap (R := GaloisField 2 f) (S := K) c, hKrank]
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  refine ⟨?_, ?_, rfl⟩
  · have horth := htrace v v ω
    rw [hvv, mul_zero, map_zero] at horth
    exact horth
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have hv0 : s • v + t • (ω • v) = 0 := by
      refine heWinj ?_
      rw [map_add, map_smul, map_smul, hst, map_zero]
    have hcoef : algebraMap (GaloisField 2 f) K s +
        algebraMap (GaloisField 2 f) K t * ω = 0 := by
      have h1 : (algebraMap (GaloisField 2 f) K s +
          algebraMap (GaloisField 2 f) K t * ω) • v = s • v + t • (ω • v) := by
        rw [add_smul, mul_smul, algebraMap_smul, algebraMap_smul]
      have h2 : (algebraMap (GaloisField 2 f) K s +
          algebraMap (GaloisField 2 f) K t * ω) • v = 0 := by rw [h1, hv0]
      rcases smul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hv
    by_cases ht : t = 0
    · have hs : s = 0 := by
        have hc := hcoef
        rw [ht, map_zero, zero_mul, add_zero] at hc
        exact (algebraMap (GaloisField 2 f) K).injective (by simpa using hc)
      exact ⟨hs, ht⟩
    · exfalso
      have htK : algebraMap (GaloisField 2 f) K t ≠ 0 := by
        intro h0
        exact ht ((algebraMap (GaloisField 2 f) K).injective (by simpa using h0))
      have hmul : algebraMap (GaloisField 2 f) K t * ω =
          -algebraMap (GaloisField 2 f) K s := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hcoef
      have hcancel : (algebraMap (GaloisField 2 f) K t)⁻¹ *
          (algebraMap (GaloisField 2 f) K t * ω) = ω := by
        rw [← mul_assoc, inv_mul_cancel₀ htK, one_mul]
      have homega : ω = (algebraMap (GaloisField 2 f) K t)⁻¹ *
          (-algebraMap (GaloisField 2 f) K s) := by
        rw [← hcancel, hmul]
      have hωeq : algebraMap (GaloisField 2 f) K (-(t⁻¹ * s)) = ω := by
        rw [homega, map_neg, map_mul, map_inv₀, mul_neg]
      have htr : Algebra.trace (GaloisField 2 f) K ω = 0 := by
        rw [← hωeq]
        exact htr_base (-(t⁻¹ * s))
      rw [hω] at htr
      exact one_ne_zero htr

private theorem bmSTS_rootGroupImage_altSiegel
    (n f : ℕ) {K : Type} [Field K] [Algebra (GaloisField 2 f) K]
    {W : Type} [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f))
    (heWinj : Function.Injective eW)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (v : W) (hv : v ≠ 0) (hvv : h v v = 0) (ω : K)
    (hω : Algebra.trace (GaloisField 2 f) K ω = 1) :
    eW v ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (ω • v)) = 0 ∧
    LinearIndependent (GaloisField 2 f) ![eW v, eW (ω • v)] ∧
    altSiegelGroup (bmSTS_J n f) (eW v) (eW (ω • v)) =
      Subgroup.closure {x : GL (Fin n ⊕ Fin n) (GaloisField 2 f) |
        ∃ c : GaloisField 2 f,
          (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
            1 + c • (Matrix.vecMulVec (eW v) (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) +
              Matrix.vecMulVec (eW (ω • v)) (Matrix.mulVec (bmSTS_J n f) (eW v)))} := by
  exact bmSTS_eW_pair_facts n f h eW heWinj htrace hKrank v hv hvv ω hω

private theorem bmSTS_Jfb_transpose {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

private theorem bmSTS_Jfb_mul_self {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, CharTwo.neg_eq]

private theorem bmSTS_mat_mul_inv {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) :
    (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

private theorem bmSTS_mat_inv_mul {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) :
    (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

private theorem bmSTS_mat_inv_eq {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) :
    (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u)ᵀ *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  have hsp : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u)ᵀ *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) =
      Matrix.fromBlocks 0 1 (-1) 0 :=
    (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2
  have h2 : ((Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u)ᵀ *
      Matrix.fromBlocks 0 1 (-1) 0) *
        (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ (Matrix.fromBlocks 0 1 (-1) 0), hsp, bmSTS_Jfb_mul_self]
  exact (left_inv_eq_right_inv h2 (bmSTS_mat_mul_inv u)).symm

private theorem bmSTS_transpose_inv_mul_J {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) :
    (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹)ᵀ *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) := by
  have htrans : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹)ᵀ =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    rw [bmSTS_mat_inv_eq, Matrix.transpose_mul, Matrix.transpose_mul, bmSTS_Jfb_transpose,
      Matrix.transpose_transpose]
    noncomm_ring
  rw [htrans]
  change ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *
      Matrix.fromBlocks 0 1 (-1) 0) * Matrix.fromBlocks 0 1 (-1) 0 =
    Matrix.fromBlocks 0 1 (-1) 0 * CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u
  rw [Matrix.mul_assoc ((Matrix.fromBlocks 0 1 (-1) 0) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u))
      (Matrix.fromBlocks 0 1 (-1) 0), bmSTS_Jfb_mul_self, Matrix.mul_one]

private theorem bmSTS_vecMul_eq_transpose_mulVec {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (z : Fin n ⊕ Fin n → F) :
    z ᵥ* A = Aᵀ *ᵥ z := by
  have h := Matrix.vecMul_transpose (A := Aᵀ) z
  rwa [Matrix.transpose_transpose] at h

private theorem bmSTS_conj_add_vecMulVec {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) (x y x' y' : Fin n ⊕ Fin n → F) (c : F)
    (h : GL (Fin n ⊕ Fin n) F)
    (hh : (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • (Matrix.vecMulVec x y + Matrix.vecMulVec x' y')) :
    (((MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • (Matrix.vecMulVec
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)
          (y ᵥ* (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹)) +
        Matrix.vecMulVec ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x')
          (y' ᵥ* (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹))) := by
  rw [show (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h =
      (u : GL (Fin n ⊕ Fin n) F) * h * (u : GL (Fin n ⊕ Fin n) F)⁻¹ from rfl]
  rw [Units.val_mul, Units.val_mul]
  change (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *
      (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) = _
  rw [hh]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, bmSTS_mat_mul_inv, zero_add]

private theorem bmSTS_conj_altSiegelGroup {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) (x y : Fin n ⊕ Fin n → F) :
    (altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)
        ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y) := by
  have hJU := bmSTS_transpose_inv_mul_J u
  rw [altSiegelGroup, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, ⟨c, hc⟩, rfl⟩
    refine ⟨c, ?_⟩
    change (((MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = _
    have e1 : (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y) ᵥ*
          (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) =
        Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y) := by
      rw [← Matrix.transpose_transpose
          (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹),
        Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hJU, ← Matrix.mulVec_mulVec]
    have e2 : (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x) ᵥ*
          (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) =
        Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x) := by
      rw [← Matrix.transpose_transpose
          (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹),
        Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hJU, ← Matrix.mulVec_mulVec]
    rw [bmSTS_conj_add_vecMulVec u x (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y)
        y (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x) c h hc, e1, e2]
  · rintro ⟨c, hg⟩
    refine ⟨(MulAut.conj (u : GL (Fin n ⊕ Fin n) F))⁻¹ g, ⟨c, ?_⟩, ?_⟩
    · have hle := bmSTS_conj_add_vecMulVec (u := u⁻¹)
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)
          (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y))
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y)
          (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)) c g hg
      have hcomp : (MulAut.conj (u : GL (Fin n ⊕ Fin n) F))⁻¹ =
          MulAut.conj ((u⁻¹ : ↥(CFSG.Open.StatedSp n F)) :
            GL (Fin n ⊕ Fin n) F) := (map_inv _ _).symm
      have e1 : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) *ᵥ
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, bmSTS_mat_inv_mul, Matrix.one_mulVec]
      have e2 : (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y)) ᵥ*
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F ((u⁻¹)⁻¹)) =
          Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y := by
        rw [show (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F (u⁻¹)⁻¹) =
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) from by rw [inv_inv],
          bmSTS_vecMul_eq_transpose_mulVec
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u),
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          show (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u)ᵀ *
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) =
            Matrix.fromBlocks 0 1 (-1) 0 from
          (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2]
      have e3 : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) *ᵥ
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y) = y := by
        rw [Matrix.mulVec_mulVec, bmSTS_mat_inv_mul, Matrix.one_mulVec]
      have e4 : (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)) ᵥ*
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F ((u⁻¹)⁻¹)) =
          Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x := by
        rw [show (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F (u⁻¹)⁻¹) =
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) from by rw [inv_inv],
          bmSTS_vecMul_eq_transpose_mulVec
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u),
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          show (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u)ᵀ *
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) =
            Matrix.fromBlocks 0 1 (-1) 0 from
          (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2]
      rw [← hcomp] at hle
      rw [hle, e1, e2, e3, e4]
    · change (MulAut.conj (u : GL (Fin n ⊕ Fin n) F))
          ((MulAut.conj (u : GL (Fin n ⊕ Fin n) F))⁻¹ g) = g
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

private theorem bmSTS_map_conj_subtype {n f : ℕ}
    (X : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
    ((X.map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
      ((X.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype).map
        (MulAut.conj ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u)).toMonoidHom) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private lemma bmSTS_conj_transvection {m' : ℕ} {F : Type} [Field F] (σ : F ≃+* F)
    (P : GL (Fin m') F)
    (hP : Unitary.conjTr σ (P : Matrix (Fin m') (Fin m') F) *
      (P : Matrix (Fin m') (Fin m') F) = Unitary.antidiag m')
    (c : F) (v : Fin m' → F) :
    (P : Matrix (Fin m') (Fin m') F) *
        (1 + c • Matrix.vecMulVec v
          (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag m'))) *
        ((P⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) =
      1 + c • Matrix.vecMulVec ((P : Matrix (Fin m') (Fin m') F) *ᵥ v)
        (fun i => σ (((P : Matrix (Fin m') (Fin m') F) *ᵥ v) i)) := by
  have hPP : (P : Matrix (Fin m') (Fin m') F) *
      ((P⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGinv : (Unitary.antidiag m' : Matrix (Fin m') (Fin m') F) *
      ((P⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) =
      Unitary.conjTr σ (P : Matrix (Fin m') (Fin m') F) := by
    rw [← hP, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hw : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag m') ᵥ*
      ((P⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) =
      fun i => σ (((P : Matrix (Fin m') (Fin m') F) *ᵥ v) i) := by
    rw [Matrix.vecMul_vecMul, hGinv, Unitary.conjTr, Matrix.vecMul_transpose]
    funext i
    exact (RingHom.map_mulVec σ.toRingHom (P : Matrix (Fin m') (Fin m') F) v i).symm
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hw]

private theorem bmSTS_suAction_transvection (m' f : ℕ)
    [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (c : GaloisField 2 (2 * max f 1)) (v₀ : Fin m' → GaloisField 2 (2 * max f 1))
    (hg : ((g : GL (Fin m') (GaloisField 2 (2 * max f 1))) :
        Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) =
      1 + c • Matrix.vecMulVec v₀
        (Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m'))) :
    ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      Matrix.mulVecLin ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f)
          (bmSTS_antidiagConj_spec m' f) g).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))) :
              Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) y =
        y + c • (CFSG.ClassicalGroups.Unitary.herm
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
          ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
            (GaloisField 2 (2 * max f 1))) *ᵥ v₀) y) •
          ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
            (GaloisField 2 (2 * max f 1))) *ᵥ v₀) := by
  intro y
  let P : GL (Fin m') (GaloisField 2 (2 * max f 1)) := bmSTS_antidiagConj m' f
  have hP : Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1))
      (P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
      (P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) =
      Unitary.antidiag m' := bmSTS_antidiagConj_spec m' f
  have hcoe : ((((Unitary.conjEquiv P hP g).1 : GL (Fin m')
      (GaloisField 2 (2 * max f 1)))) : Matrix (Fin m') (Fin m')
        (GaloisField 2 (2 * max f 1))) =
      (P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
        ((g : GL (Fin m') (GaloisField 2 (2 * max f 1))) :
          Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
        (((P⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1)))) :
          Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) := by
    have h := Unitary.coe_conjEquiv P hP g
    simpa only [Units.val_mul] using
      congrArg (fun u : GL (Fin m') (GaloisField 2 (2 * max f 1)) =>
        (u : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))) h
  change Matrix.mulVecLin ((((Unitary.conjEquiv P hP g).1 : GL (Fin m')
      (GaloisField 2 (2 * max f 1)))) : Matrix (Fin m') (Fin m')
        (GaloisField 2 (2 * max f 1))) y = _
  rw [hcoe, hg, bmSTS_conj_transvection (CFSG.LieType.BorelTits.unitaryInvolution
    (GaloisField 2 (2 * max f 1)) 2 (max f 1)) P hP c v₀]
  simp only [P, Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    CFSG.ClassicalGroups.Unitary.herm_def, dotProduct, Function.comp_apply,
    smul_smul, smul_eq_mul]

private theorem bmSTS_rootGroup_canonical_traceScalar
    {f : ℕ} (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2) :
    ∃ ω : K, Algebra.trace (GaloisField 2 f) K ω = 1 := by
  haveI : FiniteDimensional (GaloisField 2 f) K := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (GaloisField 2 f) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.trace_surjective (GaloisField 2 f) K 1

private theorem bmSTS_mem_unitTransvGroup_iff
    {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    (σ : F →+* F) (G : Matrix ι ι F) (v : ι → F)
    (hv : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ v = 0) (g : GL ι F) :
    g ∈ unitTransvGroup σ G v ↔
      ∃ c : F, σ c = c ∧
        (g : Matrix ι ι F) =
          1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) := by
  set φ : ι → F := Matrix.vecMul (fun i => σ (v i)) G with hφ
  set T : Matrix ι ι F := Matrix.vecMulVec v φ with hT
  have hv' : φ ⬝ᵥ v = 0 := by rw [hφ]; exact hv
  have hφT : Matrix.vecMul φ (Matrix.vecMulVec v φ) = 0 := by
    have h1 : Matrix.vecMul φ (Matrix.vecMulVec v φ) = (v ⬝ᵥ φ) • φ := by
      have h := Matrix.vecMul_transpose (A := (Matrix.vecMulVec v φ)ᵀ) φ
      rw [Matrix.transpose_transpose, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mulVec,
        op_smul_eq_smul] at h
      exact h
    rw [h1, dotProduct_comm, hv', zero_smul]
  have hsq : T * T = 0 := by
    rw [hT, Matrix.vecMulVec_mul, hφT]
    ext i j
    simp
  have hprod : ∀ c d : F, (1 + c • T) * (1 + d • T) = 1 + (c + d) • T := by
    intro c d
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_smul, hsq, smul_zero, add_zero]
    rw [add_assoc, ← add_smul]
  have hset : ({x : GL ι F | ∃ c : F, σ c = c ∧
      (x : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G)} :
        Set (GL ι F)) =
      {x : GL ι F | ∃ c : F, σ c = c ∧ (x : Matrix ι ι F) = 1 + c • T} := by
    ext x
    constructor <;> rintro ⟨c, hc, hx⟩
    · exact ⟨c, hc, by rw [hx, ← hφ, ← hT]⟩
    · exact ⟨c, hc, by rw [hx, hT, hφ]⟩
  rw [unitTransvGroup, hset]
  constructor
  · intro hg
    refine Subgroup.closure_induction
      (k := {x : GL ι F | ∃ c : F, σ c = c ∧ (x : Matrix ι ι F) = 1 + c • T})
      (p := fun x _ => ∃ c : F, σ c = c ∧ (x : Matrix ι ι F) = 1 + c • T) ?_ ?_ ?_ ?_ hg
    · rintro x ⟨c, hc, hx⟩
      exact ⟨c, hc, hx⟩
    · exact ⟨0, map_zero σ, by simp⟩
    · rintro x y _ _ ⟨c, hc, hx⟩ ⟨d, hd, hy⟩
      refine ⟨c + d, by rw [map_add, hc, hd], ?_⟩
      rw [Units.val_mul, hx, hy, hprod]
    · rintro x _ ⟨c, hc, hx⟩
      refine ⟨c, hc, ?_⟩
      have hx2 : x * x = 1 := by
        apply Units.ext
        rw [Units.val_mul, Units.val_one, hx, hprod c c]
        rw [show c + c = 0 from CharTwo.add_self_eq_zero c, zero_smul, add_zero]
      rw [inv_eq_of_mul_eq_one_right hx2, hx]
  · rintro ⟨c, hc, hx⟩
    exact Subgroup.subset_closure ⟨c, hc, hx⟩

private theorem bmSTS_fixed_eq_algebraMap
    {f : ℕ} (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (τ : K ≃+* K) (hτne : τ ≠ RingHom.id K)
    (hτlin : ∀ c : GaloisField 2 f,
      τ (algebraMap (GaloisField 2 f) K c) = algebraMap (GaloisField 2 f) K c)
    {c : K} (hc : τ c = c) :
    ∃ c_F : GaloisField 2 f, algebraMap (GaloisField 2 f) K c_F = c := by
  haveI : FiniteDimensional (GaloisField 2 f) K := Module.Finite.of_finite
  haveI : Algebra.IsQuadraticExtension (GaloisField 2 f) K :=
    Algebra.IsQuadraticExtension.mk hKrank
  let τ' : K ≃ₐ[GaloisField 2 f] K := { τ with commutes' := fun c => hτlin c }
  have hτ'ne : τ' ≠ 1 := by
    intro h
    apply hτne
    ext x
    exact congrFun (congrArg (fun e : K ≃ₐ[GaloisField 2 f] K => (e : K → K)) h) x
  obtain ⟨c_F, hc_F⟩ := Algebra.IsQuadraticExtension.mem_range_algebraMap_of_apply_eq
    (GaloisField 2 f) K hτ'ne (by change τ c = c; exact hc)
  exact ⟨c_F, hc_F⟩

private theorem bmSTS_antidiagConj_mulVec_isotropic
    (m' f : ℕ) (v₀ : Fin m' → GaloisField 2 (2 * max f 1)) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0) :
    ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀) ≠ 0 ∧
      CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1))
        ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀)
        ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀)
        = 0 := by
  set σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1) with hσ
  have hP : Unitary.conjTr σ
      (bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
      (bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) =
      Unitary.antidiag m' := by
    simpa only [hσ] using bmSTS_antidiagConj_spec m' f
  have hherm_mul : ∀ (M : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))
      (y : Fin m' → GaloisField 2 (2 * max f 1)),
      CFSG.ClassicalGroups.Unitary.herm σ (M *ᵥ v₀) y =
        CFSG.ClassicalGroups.Unitary.herm σ v₀ (Unitary.conjTr σ M *ᵥ y) := by
    intro M y
    rw [CFSG.ClassicalGroups.Unitary.herm_def, CFSG.ClassicalGroups.Unitary.herm_def]
    simp only [Matrix.mulVec, dotProduct, Unitary.conjTr, Matrix.transpose_apply,
      Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finset.sum_congr rfl fun i _ => by ring
  have hfinal : CFSG.ClassicalGroups.Unitary.herm σ v₀ (Unitary.antidiag m' *ᵥ v₀) = 0 := by
    rw [CFSG.ClassicalGroups.Unitary.herm_def]
    have hb : (∑ i, σ (v₀ i) * (Matrix.mulVec (Unitary.antidiag m') v₀) i) =
        Matrix.vecMul (fun i => σ (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ := by
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
      have hL : (∑ x, σ (v₀ x) * ∑ x_1, Unitary.antidiag m' x x_1 * v₀ x_1) =
          ∑ x, ∑ x_1, σ (v₀ x) * (Unitary.antidiag m' x x_1 * v₀ x_1) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
      rw [hL, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hb]
    exact hiso
  constructor
  · intro h0
    apply hv₀
    have hInvMul : (((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) :
        Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
        (bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h := congrArg (fun w : Fin m' → GaloisField 2 (2 * max f 1) =>
      (((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) :
        Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ w) h0
    rwa [Matrix.mulVec_mulVec, hInvMul, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  · have hherm := hherm_mul
      (bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))
      ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀)
    rw [Matrix.mulVec_mulVec, hP] at hherm
    rw [hherm]
    exact hfinal

private theorem bmSTS_stdAction_blockAction_transvection_fixed
    (n f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (g : (ggU .PSU m' (max f 1)).K)
    (a : Fin m' → K) (c : K)
    (ha : ∀ y : Fin m' → K,
      bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g y =
        y + c • CFSG.ClassicalGroups.Unitary.herm τ a y • a) :
    ∀ x : W, bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x =
      x + c • h
        ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
          m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm a) x •
        ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
          m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm a) := by
  haveI : FiniteDimensional K W := FiniteDimensional.of_finrank_pos (by rw [hrank]; omega)
  let Φ : W ≃ₗ[GaloisField 2 f] (Fin m' → K) :=
    bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace
  let Φ₀ : W ≃ₗ[K] (Fin m' → K) := Classical.choose
    (CFSG.Fischer.Classification.exists_linearEquiv_herm_of_form
      (bmSTS_blockEmbeddingEV_PSU_unitaryInvolution n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
          h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
      (bmSTS_blockEmbeddingEV_PSU_isHermForm n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) hnd hrank)
  have hΦ_symm_smul : ∀ (k : K) (y : Fin m' → K), Φ.symm (k • y) = k • Φ.symm y := by
    intro k y
    exact Φ₀.symm.map_smul k y
  have hherm : ∀ u v : W, CFSG.ClassicalGroups.Unitary.herm τ (Φ u) (Φ v) = h u v := by
    intro u v
    have hspec := Classical.choose_spec (CFSG.Fischer.Classification.exists_linearEquiv_herm_of_form
      (bmSTS_blockEmbeddingEV_PSU_unitaryInvolution n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
          h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
      (bmSTS_blockEmbeddingEV_PSU_isHermForm n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) hnd hrank)
    simpa only [Φ, bmSTS_blockEmbeddingEV_PSU_hermEquiv, LinearEquiv.restrictScalars_apply]
      using hspec u v
  intro x
  have h1 : Φ (bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x) =
      bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g (Φ x) := by
    show Φ (Φ.symm (bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
      K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g (Φ x))) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [← Φ.symm_apply_apply (bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁
    hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x), h1]
  rw [ha (Φ x), map_add, hΦ_symm_smul, hΦ_symm_smul]
  rw [show Φ.symm (Φ x) = x from Φ.symm_apply_apply x]
  rw [show CFSG.ClassicalGroups.Unitary.herm τ a (Φ x) = h (Φ.symm a) x from by
    nth_rewrite 1 [← LinearEquiv.apply_symm_apply Φ a]
    exact hherm (Φ.symm a) x]

private theorem bmSTS_conj_transvection_act
    {m' : ℕ} {F : Type} [Field F] (σ : F ≃+* F)
    (M : GL (Fin m') F) (C Cg : Matrix (Fin m') (Fin m') F)
    (a : Fin m' → F) (c : F)
    (hM : (M : Matrix (Fin m') (Fin m') F) * (M⁻¹ : Matrix (Fin m') (Fin m') F) = 1)
    (hM' : (M⁻¹ : Matrix (Fin m') (Fin m') F) * (M : Matrix (Fin m') (Fin m') F) = 1)
    (hiso : ∀ u v, CFSG.ClassicalGroups.Unitary.herm σ
      ((M : Matrix (Fin m') (Fin m') F) *ᵥ u) ((M : Matrix (Fin m') (Fin m') F) *ᵥ v) =
      CFSG.ClassicalGroups.Unitary.herm σ u v)
    (hC : ∀ y, Matrix.mulVec C y = y + c • CFSG.ClassicalGroups.Unitary.herm σ a y • a)
    (hCg : Cg = (M⁻¹ : Matrix (Fin m') (Fin m') F) * C * (M : Matrix (Fin m') (Fin m') F)) :
    ∀ y, Matrix.mulVecLin Cg y =
      y + c • CFSG.ClassicalGroups.Unitary.herm σ ((M⁻¹ : Matrix (Fin m') (Fin m') F) *ᵥ a) y •
        ((M⁻¹ : Matrix (Fin m') (Fin m') F) *ᵥ a) := by
  intro y
  rw [hCg, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hC (Matrix.mulVec (M : Matrix (Fin m') (Fin m') F) y), Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul]
  rw [show Matrix.mulVec (M⁻¹ : Matrix (Fin m') (Fin m') F)
      (Matrix.mulVec (M : Matrix (Fin m') (Fin m') F) y) = y from by
    rw [Matrix.mulVec_mulVec, hM', Matrix.one_mulVec]]
  rw [show Matrix.mulVec (M⁻¹ : Matrix (Fin m') (Fin m') F) a =
      (M⁻¹ : Matrix (Fin m') (Fin m') F) *ᵥ a from rfl]
  rw [smul_smul]
  rw [smul_smul]
  rw [show CFSG.ClassicalGroups.Unitary.herm σ a
      (Matrix.mulVec (M : Matrix (Fin m') (Fin m') F) y) =
      CFSG.ClassicalGroups.Unitary.herm σ ((M⁻¹ : Matrix (Fin m') (Fin m') F) *ᵥ a) y from by
    rw [show a = Matrix.mulVec (M : Matrix (Fin m') (Fin m') F)
        ((M⁻¹ : Matrix (Fin m') (Fin m') F) *ᵥ a) from by
      rw [show (M⁻¹ : Matrix (Fin m') (Fin m') F) *ᵥ a =
          Matrix.mulVec (M⁻¹ : Matrix (Fin m') (Fin m') F) a from rfl,
        Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]]
    simpa using hiso ((M⁻¹ : Matrix (Fin m') (Fin m') F) *ᵥ a) y]

private theorem bmSTS_conjEquiv_mul_inv (m' f : ℕ)
    [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (a b : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m')) :
    Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) (a * b * a⁻¹) =
      Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) a *
        Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) b *
          (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) a)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

private theorem bmSTS_mulVec_inv_nonzero_isotropic
    {m' : ℕ} {F : Type} [Field F] (σ : F ≃+* F)
    (Cu : GL (Fin m') F) (a : Fin m' → F) (ha0 : a ≠ 0)
    (haa : CFSG.ClassicalGroups.Unitary.herm σ a a = 0)
    (hiso : ∀ u v, CFSG.ClassicalGroups.Unitary.herm σ
      ((Cu : Matrix (Fin m') (Fin m') F) *ᵥ u) ((Cu : Matrix (Fin m') (Fin m') F) *ᵥ v) =
      CFSG.ClassicalGroups.Unitary.herm σ u v) :
    ((Cu⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ a ≠ 0 ∧
      CFSG.ClassicalGroups.Unitary.herm σ
        (((Cu⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ a)
        (((Cu⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ a) = 0 := by
  have hCa : (Cu : Matrix (Fin m') (Fin m') F) *ᵥ
      (((Cu⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · intro h0
    apply ha0
    rw [← hCa, h0, Matrix.mulVec_zero]
  · have h := hiso (((Cu⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ a)
      (((Cu⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ a)
    rw [hCa] at h
    rw [← h, haa]

private theorem bmSTS_suAction_transvection_fixed
    {m' f : ℕ} [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ : Fin m' → GaloisField 2 (2 * max f 1)) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1)) m').subtype) = unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
      (max f 1)) m')) (hgm : g ∈ rootG) :
    ∃ c : GaloisField 2 (2 * max f 1),
      CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1) c = c ∧
      ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
        Matrix.mulVecLin (((Unitary.conjEquiv (bmSTS_antidiagConj m' f)
          (bmSTS_antidiagConj_spec m' f) g).1 : GL (Fin m')
            (GaloisField 2 (2 * max f 1))) : Matrix (Fin m') (Fin m')
              (GaloisField 2 (2 * max f 1))) y =
          y + c • CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
              GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ :
              Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
              ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
                (GaloisField 2 (2 * max f 1))) *ᵥ v₀)) y •
            ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
              GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ :
              Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
              ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
                (GaloisField 2 (2 * max f 1))) *ᵥ v₀)) := by
  let σR : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  have hx : (u_SU * g * u_SU⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) ∈
      unitTransvGroup σR.toRingHom (Unitary.antidiag m') v₀ := by
    rw [← hu_SU]
    exact Subgroup.mem_map.mpr ⟨u_SU * g * u_SU⁻¹,
      Subgroup.mem_map.mpr ⟨g, hgm, rfl⟩, rfl⟩
  have hiff := bmSTS_mem_unitTransvGroup_iff σR.toRingHom (Unitary.antidiag m') v₀ hiso
    (u_SU * g * u_SU⁻¹)
  obtain ⟨c, hc, hmat⟩ := hiff.1 hx
  have hact : ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      Matrix.mulVecLin (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        (u_SU * g * u_SU⁻¹)).1 : GL (Fin m') (GaloisField 2 (2 * max f 1))) :
        Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) y =
      y + c • CFSG.ClassicalGroups.Unitary.herm σR
        ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
          (GaloisField 2 (2 * max f 1))) *ᵥ v₀) y •
        ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
          (GaloisField 2 (2 * max f 1))) *ᵥ v₀) :=
    bmSTS_suAction_transvection m' f (u_SU * g * u_SU⁻¹) c v₀ hmat
  let Cu : GL (Fin m') (GaloisField 2 (2 * max f 1)) :=
    (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1
  have hfac : Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) g =
      (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU)⁻¹ *
        Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
          (u_SU * g * u_SU⁻¹) *
        Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU := by
    have h := bmSTS_conjEquiv_mul_inv m' f u_SU g
    rw [h]
    group
  have hcoe : ((Cu⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) :
      Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) =
      ((Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))))⁻¹ := by
    simp only [Cu, Matrix.GeneralLinearGroup.coe_inv]
  have hCg : ((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) g).1 :
      Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) =
      (Cu⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
        ((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
          (u_SU * g * u_SU⁻¹)).1 :
          Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
        (Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) := by
    rw [hfac]
    simp only [Cu, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hcoe]
  have hisoCu : ∀ u v : Fin m' → GaloisField 2 (2 * max f 1),
      CFSG.ClassicalGroups.Unitary.herm σR
        ((Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ u)
        ((Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v) =
      CFSG.ClassicalGroups.Unitary.herm σR u v :=
    fun u v => CFSG.ClassicalGroups.Unitary.herm_smul_smul σR
      (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU) u v
  refine ⟨c, hc, ?_⟩
  exact bmSTS_conj_transvection_act σR Cu
    ((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
      (u_SU * g * u_SU⁻¹)).1 : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))
    ((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) g).1 :
      Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))
    ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
      (GaloisField 2 (2 * max f 1))) *ᵥ v₀) c (by simp) (by simp) hisoCu
    (fun z => by rw [← Matrix.mulVecLin_apply]; exact hact z) hCg

private theorem bmSTS_suAction_transvection_of_unitTransv
    {m' f : ℕ} [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ : Fin m' → GaloisField 2 (2 * max f 1))
    (g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
      (max f 1)) m'))
    (c : GaloisField 2 (2 * max f 1))
    (hc : CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1) c = c)
    (hmat : (u_SU * g * u_SU⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) =
      1 + c • Matrix.vecMulVec v₀ (Matrix.vecMul (fun i =>
        CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
          (v₀ i)) (Unitary.antidiag m'))) :
    ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      Matrix.mulVecLin (((Unitary.conjEquiv (bmSTS_antidiagConj m' f)
        (bmSTS_antidiagConj_spec m' f) g).1 : GL (Fin m')
          (GaloisField 2 (2 * max f 1))) : Matrix (Fin m') (Fin m')
            (GaloisField 2 (2 * max f 1))) y =
        y + c • CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * max f 1)) 2 (max f 1))
          ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ :
            Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
              (GaloisField 2 (2 * max f 1))) *ᵥ v₀)) y •
          ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ :
            Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
              (GaloisField 2 (2 * max f 1))) *ᵥ v₀)) := by
  let σR : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  have hact : ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      Matrix.mulVecLin (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        (u_SU * g * u_SU⁻¹)).1 : GL (Fin m') (GaloisField 2 (2 * max f 1))) :
        Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) y =
      y + c • CFSG.ClassicalGroups.Unitary.herm σR
        ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
          (GaloisField 2 (2 * max f 1))) *ᵥ v₀) y •
        ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
          (GaloisField 2 (2 * max f 1))) *ᵥ v₀) :=
    bmSTS_suAction_transvection m' f (u_SU * g * u_SU⁻¹) c v₀ hmat
  let Cu : GL (Fin m') (GaloisField 2 (2 * max f 1)) :=
    (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1
  have hfac : Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) g =
      (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU)⁻¹ *
        Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
          (u_SU * g * u_SU⁻¹) *
        Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU := by
    have h := bmSTS_conjEquiv_mul_inv m' f u_SU g
    rw [h]
    group
  have hcoe : ((Cu⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) :
      Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) =
      ((Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))))⁻¹ := by
    simp only [Cu, Matrix.GeneralLinearGroup.coe_inv]
  have hCg : ((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) g).1 :
      Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) =
      (Cu⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
        ((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
          (u_SU * g * u_SU⁻¹)).1 :
          Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
        (Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) := by
    rw [hfac]
    simp only [Cu, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hcoe]
  have hisoCu : ∀ u v : Fin m' → GaloisField 2 (2 * max f 1),
      CFSG.ClassicalGroups.Unitary.herm σR
        ((Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ u)
        ((Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v) =
      CFSG.ClassicalGroups.Unitary.herm σR u v :=
    fun u v => CFSG.ClassicalGroups.Unitary.herm_smul_smul σR
      (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU) u v
  exact bmSTS_conj_transvection_act σR Cu
    ((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
      (u_SU * g * u_SU⁻¹)).1 : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))
    ((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) g).1 :
      Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))
    ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
      (GaloisField 2 (2 * max f 1))) *ᵥ v₀) c (by simp) (by simp) hisoCu
    (fun z => by rw [← Matrix.mulVecLin_apply]; exact hact z) hCg

private theorem bmSTS_LieUniversal_transport_iff
    {A B : LieUniversal} (heq : A = B) (β : Fin A.D.rank → ℤ) :
    (∀ g : A.K, g ∈ A.D.rootGroup β →
        (congrArg LieUniversal.K heq) ▸ g ∈
          B.D.rootGroup ((congrArg (fun X : LieUniversal => Fin X.D.rank → ℤ) heq) ▸ β)) ∧
    (∀ g' ∈ B.D.rootGroup ((congrArg (fun X : LieUniversal => Fin X.D.rank → ℤ) heq) ▸ β),
        ∃ g ∈ A.D.rootGroup β, (congrArg LieUniversal.K heq) ▸ g = g') := by
  cases heq
  exact ⟨fun g hg => hg, fun g' hg' => ⟨g', hg', rfl⟩⟩

private theorem bmSTS_LieUniversal_transport_longRoot
    {A B : LieUniversal} (heq : A = B) (β : Fin A.D.rank → ℤ) (hβ : GGLongRoot A.D β) :
    GGLongRoot B.D ((congrArg (fun X : LieUniversal => Fin X.D.rank → ℤ) heq) ▸ β) := by
  cases heq
  exact hβ

private theorem bmSTS_ggU_K_eq
    (m' f : ℕ) :
    (ggU .PSU m' (max f 1)).K =
      ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1)) m') := by
  simp only [ggU, lieUniversal, le_max_right, ↓reduceDIte]

private theorem bmSTS_involution_fixes_base
    (n f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))] (S : Set (GL (Fin n ⊕ Fin n)
        (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG)
    (hrootG' : ∀ g' ∈ rootG, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ((bmSTS_ggU_K_eq m' f) ▸ g) = g') :
    ∀ c : GaloisField 2 f, (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1)) (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) = algebraMap
            (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c := by
  let σR : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
      CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  let φ : K ≃ₐ[GaloisField 2 f] (GaloisField 2 (2 * max f 1)) :=
      bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank
  have hcompat : ∀ x : K, φ (τ x) = σR (φ x) := by
    intro x
    have hKcard : Nat.card K = 2 ^ (2 * max f 1) := bmSTS_natCard_of_finrank_two f K hKrank
    have hτne1 : τ ≠ 1 := by intro h; exact hτne (by rw [h]; rfl)
    have hτ2mul : τ * τ = 1 := by ext a; exact hτ2 a
    obtain ⟨-, hpow⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution_prime
        Nat.prime_two (by omega) hKcard hτne1 hτ2mul
    rw [hpow x, map_pow, CFSG.LieType.BorelTits.unitaryInvolution_apply]
    congr 1
    rw [Nat.mul_div_cancel_left (max f 1) (by norm_num : 0 < 2)]
  intro c
  have h := hcompat (algebraMap (GaloisField 2 f) K c)
  rw [bmSTS_tauFixesBase n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne c,
    AlgEquiv.commutes φ c] at h
  exact h.symm

private theorem bmSTS_transvectionGL {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [CharP F 2] (v φ : ι → F) (hv : φ ⬝ᵥ v = 0) (c : F) :
    ∃ T : GL ι F, (T : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v φ := by
  set T : Matrix ι ι F := Matrix.vecMulVec v φ with hT
  have hv' : φ ⬝ᵥ v = 0 := hv
  have hφT : Matrix.vecMul φ (Matrix.vecMulVec v φ) = 0 := by
    have h1 : Matrix.vecMul φ (Matrix.vecMulVec v φ) = (v ⬝ᵥ φ) • φ := by
      have h := Matrix.vecMul_transpose (A := (Matrix.vecMulVec v φ)ᵀ) φ
      rw [Matrix.transpose_transpose, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mulVec,
        op_smul_eq_smul] at h
      exact h
    rw [h1, dotProduct_comm, hv', zero_smul]
  have hsq : T * T = 0 := by
    rw [hT, Matrix.vecMulVec_mul, hφT]
    ext i j
    simp
  have hprod : ∀ a b : F, (1 + a • T) * (1 + b • T) = 1 + (a + b) • T := by
    intro a b
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_smul, hsq, smul_zero, add_zero]
    rw [add_assoc, ← add_smul]
  have hcc : (1 + c • T) * (1 + c • T) = 1 := by
    rw [hprod c c, CharTwo.add_self_eq_zero c, zero_smul, add_zero]
  exact ⟨⟨1 + c • T, 1 + c • T, hcc, hcc⟩,
    by change 1 + c • T = 1 + c • Matrix.vecMulVec v φ; rw [hT]⟩

private theorem bmSTS_siegelCore_generator_unit
    (n f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))] (S : Set (GL (Fin n ⊕ Fin n)
        (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG)
    (hrootG' : ∀ g' ∈ rootG, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ((bmSTS_ggU_K_eq m' f) ▸ g) = g') :
    ∀ c : GaloisField 2 f, ∃ T : GL (Fin m') (GaloisField 2 (2 * max f 1)),
      (T : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) = 1 + (algebraMap (GaloisField 2
          f) (GaloisField 2 (2 * max f 1)) c) •
        Matrix.vecMulVec v₀ (Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m')) ∧
      T ∈ unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
          (max f 1)).toRingHom (Unitary.antidiag m') v₀ := by
  intro c
  let σR : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
      CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  let c' : GaloisField 2 (2 * max f 1) := algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1))
      c
  have hc' : σR c' = c' :=
    bmSTS_involution_fixes_base n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj
      hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong rootG u_SU v₀ a v ω hv₀ hiso ha0 haa
      ha_eq hv_eq hvv hω hu_SU hrootG hrootG' c
  obtain ⟨T, hTmat⟩ := bmSTS_transvectionGL v₀
    (Matrix.vecMul (fun i => σR (v₀ i)) (Unitary.antidiag m')) hiso c'
  refine ⟨T, hTmat, ?_⟩
  exact (bmSTS_mem_unitTransvGroup_iff σR.toRingHom (Unitary.antidiag m') v₀ hiso T).2
    ⟨c', hc', hTmat⟩

private theorem bmSTS_siegelCore_suAction_of_generator
    (n f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))] (S : Set (GL (Fin n ⊕ Fin n)
        (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG)
    (hrootG' : ∀ g' ∈ rootG, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ((bmSTS_ggU_K_eq m' f) ▸ g) = g') :
    ∀ c : GaloisField 2 f, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
      ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
        bmSTS_blockEmbeddingEV_PSU_suAction m' f g y =
          y + (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) •
              CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
                  (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a y • a := by
  intro c
  let c' : GaloisField 2 (2 * max f 1) := algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1))
      c
  obtain ⟨T, hTmat, hTmem⟩ :=
    bmSTS_siegelCore_generator_unit n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
      heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong rootG u_SU v₀ a v ω hv₀ hiso
      ha0 haa ha_eq hv_eq hvv hω hu_SU hrootG hrootG' c
  have hc' : CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1) c' =
      c' :=
    bmSTS_involution_fixes_base n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj
      hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong rootG u_SU v₀ a v ω hv₀ hiso ha0 haa
      ha_eq hv_eq hvv hω hu_SU hrootG hrootG' c
  have hT' : T ∈ ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
          m').subtype) := by
    rw [hu_SU]; exact hTmem
  obtain ⟨y, hy, hyT⟩ := Subgroup.mem_map.mp hT'
  obtain ⟨g', hg', hg'y⟩ := Subgroup.mem_map.mp hy
  obtain ⟨g, hgm, hg'g⟩ := hrootG' g' hg'
  have hmat : (u_SU * g' * u_SU⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) =
      1 + c' • Matrix.vecMulVec v₀ (Matrix.vecMul (fun i =>
        CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i))
            (Unitary.antidiag m')) := by
    have h1 : (u_SU * g' * u_SU⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) = y := by
      have h2 : (((MulAut.conj u_SU) g' : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m')) : GL (Fin m') (GaloisField 2 (2 * max f
              1))) = (y : GL (Fin m') (GaloisField 2 (2 * max f 1))) :=
        congrArg (fun z : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
            max f 1)) 2 (max f 1)) m') => (z : GL (Fin m') (GaloisField 2 (2 * max f 1)))) hg'y
      simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h2
    rw [h1]
    exact (congrArg (fun z : GL (Fin m') (GaloisField 2 (2 * max f 1)) => (z : Matrix (Fin m') (Fin
        m') (GaloisField 2 (2 * max f 1)))) hyT).trans hTmat
  have hact' := bmSTS_suAction_transvection_of_unitTransv u_SU v₀ g' c' hc' hmat
  rw [← ha_eq, ← hg'g] at hact'
  exact ⟨g, hgm, hact'⟩

private theorem bmSTS_suAction_stdActionMap_transvection
    (n f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))] (S : Set (GL (Fin n ⊕ Fin n)
        (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((@bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K _ _ _ hKrank
              (Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f))).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG)
    (hrootG' : ∀ g' ∈ rootG, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ((bmSTS_ggU_K_eq m' f) ▸ g) = g')
    (c : GaloisField 2 f) (g : (ggU .PSU m' (max f 1)).K) (hgm : g ∈ (ggU .PSU m' (max f
        1)).D.rootGroup β₀)
    (hact : ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      bmSTS_blockEmbeddingEV_PSU_suAction m' f g y =
        y + (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) •
            CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField
                2 (2 * max f 1)) 2 (max f 1)) a y • a) :
    ∀ y : Fin m' → K,
      bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
          m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g y =
        (@bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K _ _ _ hKrank (Classical.choice
            (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f))).symm
                ((@bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K _ _ _ hKrank (Classical.choice
                    (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f))) y + (algebraMap (GaloisField 2 f)
                        (GaloisField 2 (2 * max f 1)) c) • CFSG.ClassicalGroups.Unitary.herm
                            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1))
                                2 (max f 1)) a ((@bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K _
                                    _ _ hKrank (Classical.choice
                                        (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f))) y) • a) := by
  intro y
  set A := @bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K _ _ _ hKrank
    (Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)) with hA
  simp only [bmSTS_blockEmbeddingEV_PSU_stdActionMap, LinearMap.comp_apply]
  change ⇑A.symm ((bmSTS_blockEmbeddingEV_PSU_suAction m' f g) (⇑A y)) =
    ⇑A.symm (⇑A y + (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) •
        CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
            (2 * max f 1)) 2 (max f 1)) a (⇑A y) • a)
  exact congrArg A.symm (hact (⇑A y))

private theorem bmSTS_stdActionMap_stdAction_normal_form
    (n f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))] (S : Set (GL (Fin n ⊕ Fin n)
        (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((@bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K _ _ _ hKrank
              (Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f))).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG)
    (hrootG' : ∀ g' ∈ rootG, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ((bmSTS_ggU_K_eq m' f) ▸ g) = g')
    (c : GaloisField 2 f) (g : (ggU .PSU m' (max f 1)).K) (hgm : g ∈ (ggU .PSU m' (max f
        1)).D.rootGroup β₀)
    (hact : ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      bmSTS_blockEmbeddingEV_PSU_suAction m' f g y =
        y + (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) •
            CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField
                2 (2 * max f 1)) 2 (max f 1)) a y • a)
    (hmap : ∀ y : Fin m' → K, bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj
        hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g y =
            (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm
                ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank) y + (algebraMap
                    (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) •
                        CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
                            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a
                                ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank) y) • a))
                                    :
    ∀ y : Fin m' → K,
      bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g y =
        y + (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm (algebraMap (GaloisField 2 f)
            (GaloisField 2 (2 * max f 1)) c) • CFSG.ClassicalGroups.Unitary.herm τ
                ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a) y •
                    ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a) := by
  intro y
  let A := bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
  let φ := bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank
  have hAsmul : ∀ (d : GaloisField 2 (2 * max f 1)) (w : Fin m' → GaloisField 2 (2 * max f 1)),
      A.symm (d • w) = φ.symm d • A.symm w := by
    intro d w
    funext i
    exact map_mul φ.symm d (w i)
  have h1 : bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g y = A.symm (A y + (algebraMap
          (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) • CFSG.ClassicalGroups.Unitary.herm
              (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a
                  (A y) • a) := by
    show (bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) y = _
    exact hmap y
  rw [h1, map_add]
  rw [show (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) •
      CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2
          * max f 1)) 2 (max f 1)) a (A y) • a =
      ((algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) *
          CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
              (2 * max f 1)) 2 (max f 1)) a (A y)) • a from
    smul_smul (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c)
        (CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
            (2 * max f 1)) 2 (max f 1)) a (A y)) a]
  rw [hAsmul, map_mul]
  rw [show A.symm (A y) = y from A.symm_apply_apply y]
  have h2 := bmSTS_herm_stdModuleEquiv f m' K hKrank τ hτ2 hτne a (A y)
  rw [← h2]
  rw [show A.symm (A y) = y from A.symm_apply_apply y]
  rw [smul_smul]

private theorem bmSTS_stdAction_parameter_tau_fixed
    (n f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))] (S : Set (GL (Fin n ⊕ Fin n)
        (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((@bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K _ _ _ hKrank
              (Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f))).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG)
    (hrootG' : ∀ g' ∈ rootG, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ((bmSTS_ggU_K_eq m' f) ▸ g) = g')
    (c : GaloisField 2 f) (g : (ggU .PSU m' (max f 1)).K) (hgm : g ∈ (ggU .PSU m' (max f
        1)).D.rootGroup β₀)
    (hact : ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      bmSTS_blockEmbeddingEV_PSU_suAction m' f g y =
        y + (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) •
            CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField
                2 (2 * max f 1)) 2 (max f 1)) a y • a) :
    τ ((bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm (algebraMap (GaloisField 2 f)
        (GaloisField 2 (2 * max f 1)) c)) = (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K
            hKrank).symm (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) := by
  let φ := bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank
  have hcompat : ∀ x : K, φ (τ x) = (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
      max f 1)) 2 (max f 1)) (φ x) := by
    intro x
    have hKcard : Nat.card K = 2 ^ (2 * max f 1) := bmSTS_natCard_of_finrank_two f K hKrank
    have hτne1 : τ ≠ 1 := by intro h; exact hτne (by rw [h]; rfl)
    have hτ2mul : τ * τ = 1 := by ext a; exact hτ2 a
    obtain ⟨-, hpow⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution_prime
        Nat.prime_two (by omega) hKcard hτne1 hτ2mul
    rw [hpow x, map_pow, CFSG.LieType.BorelTits.unitaryInvolution_apply]
    congr 1
    rw [Nat.mul_div_cancel_left (max f 1) (by norm_num : 0 < 2)]
  have hσ : (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
      (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) = algebraMap (GaloisField 2 f)
          (GaloisField 2 (2 * max f 1)) c := by
    have h := hcompat (algebraMap (GaloisField 2 f) K c)
    rw [bmSTS_tauFixesBase n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne c,
      AlgEquiv.commutes φ c] at h
    exact h.symm
  apply φ.injective
  have h2 : φ (φ.symm (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c)) = algebraMap
      (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c :=
    AlgEquiv.apply_symm_apply φ _
  rw [hcompat (φ.symm (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c)), h2, hσ]

private theorem bmSTS_suAction_scalar_eq_base
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((@bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K _ _ _ hKrank
              (Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f))).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG)
    (hrootG' : ∀ g' ∈ rootG, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ((bmSTS_ggU_K_eq m' f) ▸ g) = g')
    (c : GaloisField 2 f) (g : (ggU .PSU m' (max f 1)).K) (hgm : g ∈ (ggU .PSU m' (max f
        1)).D.rootGroup β₀)
    (hact : ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      bmSTS_blockEmbeddingEV_PSU_suAction m' f g y =
        y + (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) •
            CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField
                2 (2 * max f 1)) 2 (max f 1)) a y • a)
    (hcK : τ ((bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm (algebraMap (GaloisField 2
        f) (GaloisField 2 (2 * max f 1)) c)) = (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K
            hKrank).symm (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c)) :
    ∃ cF : GaloisField 2 f, algebraMap (GaloisField 2 f) K cF =
        (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm (algebraMap (GaloisField 2 f)
            (GaloisField 2 (2 * max f 1)) c) ∧ cF = c := by
  obtain ⟨cF, hcF⟩ := bmSTS_fixed_eq_algebraMap K hKrank τ hτne
    (bmSTS_tauFixesBase n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne) hcK
  exact ⟨cF, hcF, by
    apply (algebraMap (GaloisField 2 f) K).injective
    rw [hcF, AlgEquiv.commutes (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm c]⟩
private theorem bmSTS_siegelCore_blockAction_of_suAction_transvection
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((@bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K _ _ _ hKrank
              (Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f))).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG)
    (hrootG' : ∀ g' ∈ rootG, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ((bmSTS_ggU_K_eq m' f) ▸ g) = g')
    (c : GaloisField 2 f) (g : (ggU .PSU m' (max f 1)).K) (hgm : g ∈ (ggU .PSU m' (max f
        1)).D.rootGroup β₀)
    (hact : ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      bmSTS_blockEmbeddingEV_PSU_suAction m' f g y =
        y + (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c) •
            CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField
                2 (2 * max f 1)) 2 (max f 1)) a y • a) :
    ∀ x : W, bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x = x + (c • h v x) • v :=
            by
  have hstd : ∀ y : Fin m' → K, bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁
      hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g y = y +
          ((bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm (algebraMap (GaloisField 2 f)
              (GaloisField 2 (2 * max f 1)) c)) • CFSG.ClassicalGroups.Unitary.herm τ
                  ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a) y •
                      ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a) :=
    bmSTS_stdActionMap_stdAction_normal_form n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong rootG u_SU v₀ a v ω hv₀
            hiso ha0 haa ha_eq hv_eq hvv hω hu_SU hrootG hrootG' c g hgm hact
                (bmSTS_suAction_stdActionMap_transvection n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                    K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong
                        rootG u_SU v₀ a v ω hv₀ hiso ha0 haa ha_eq hv_eq hvv hω hu_SU hrootG hrootG'
                            c g hgm hact)
  have hcK : τ ((bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm (algebraMap (GaloisField
      2 f) (GaloisField 2 (2 * max f 1)) c)) = ((bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K
          hKrank).symm (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) c)) :=
              bmSTS_stdAction_parameter_tau_fixed n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
                  eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong rootG
                      u_SU v₀ a v ω hv₀ hiso ha0 haa ha_eq hv_eq hvv hω hu_SU hrootG hrootG' c g hgm
                          hact
  obtain ⟨cF, hcF, hcFc⟩ := bmSTS_suAction_scalar_eq_base n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
      K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong rootG u_SU v₀
          a v ω hv₀ hiso ha0 haa ha_eq hv_eq hvv hω hu_SU hrootG hrootG' c g hgm hact hcK
  intro x
  rw [bmSTS_stdAction_blockAction_transvection_fixed n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
          ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a)
              ((bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm (algebraMap (GaloisField 2
                  f) (GaloisField 2 (2 * max f 1)) c)) hstd x, hv_eq, ← hcF, hcFc]
  simp only [algebraMap_smul]
  rw [smul_assoc]
private theorem bmSTS_unitTransv_isotropicPair
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (β : Fin (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rank → ℤ)
    (hβ : GGLongRoot (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2
        (max f 1) (le_max_right f 1)) m') β)
    (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ : Fin m' → GaloisField 2 (2 * max f 1)) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (hu_SU : ((((Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rootGroup β).map (MulAut.conj u_SU).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1)) m').subtype) =
      unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)).toRingHom (Unitary.antidiag m') v₀) :
    ∃ (a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K),
      a = ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
          GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2 (2
              * max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2
                  * max f 1))) *ᵥ v₀)) ∧ v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd
                      he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm'
                          htrace).symm ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K
                              hKrank).symm a) ∧ v ≠ 0 ∧ h v v = 0 ∧
        Algebra.trace (GaloisField 2 f) K ω = 1 := by
  let σR : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
      CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  let P : GL (Fin m') (GaloisField 2 (2 * max f 1)) := bmSTS_antidiagConj m' f
  have hP : Unitary.conjTr σR (P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) * (P :
      Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) = Unitary.antidiag m' :=
          bmSTS_antidiagConj_spec m' f
  let Cu : GL (Fin m') (GaloisField 2 (2 * max f 1)) := (Unitary.conjEquiv (bmSTS_antidiagConj m' f)
      (bmSTS_antidiagConj_spec m' f) u_SU).1
  have hisoCu : ∀ u v : Fin m' → GaloisField 2 (2 * max f 1), CFSG.ClassicalGroups.Unitary.herm σR
      ((Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ u) ((Cu : Matrix (Fin m')
          (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v) = CFSG.ClassicalGroups.Unitary.herm σR u v
              :=
    fun u v => CFSG.ClassicalGroups.Unitary.herm_smul_smul σR (Unitary.conjEquiv (bmSTS_antidiagConj
        m' f) (bmSTS_antidiagConj_spec m' f) u_SU) u v
  have hPv0 : (P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀ ≠ 0 :=
      (bmSTS_antidiagConj_mulVec_isotropic m' f v₀ hv₀ hiso).1
  have hPv0aa : CFSG.ClassicalGroups.Unitary.herm σR ((P : Matrix (Fin m') (Fin m') (GaloisField 2
      (2 * max f 1))) *ᵥ v₀) ((P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀) =
          0 := (bmSTS_antidiagConj_mulVec_isotropic m' f v₀ hv₀ hiso).2
  obtain ⟨ha0, haa⟩ := bmSTS_mulVec_inv_nonzero_isotropic σR Cu ((P : Matrix (Fin m') (Fin m')
      (GaloisField 2 (2 * max f 1))) *ᵥ v₀) hPv0 hPv0aa hisoCu
  have ha0' : ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1
      : GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2 (2 *
          max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max
              f 1))) *ᵥ v₀)) ≠ 0 := by
                simpa only [Cu, P, hP, Matrix.GeneralLinearGroup.coe_inv] using ha0
  have haa' : CFSG.ClassicalGroups.Unitary.herm σR ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f)
      (bmSTS_antidiagConj_spec m' f) u_SU).1 : GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix
          (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix
              (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀)) ((((Unitary.conjEquiv
                  (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 : GL (Fin m')
                      (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2 (2
                          * max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
                              (GaloisField 2 (2 * max f 1))) *ᵥ v₀)) = 0 := by
                                simpa only [Cu, P, hP, Matrix.GeneralLinearGroup.coe_inv] using haa
  obtain ⟨ω, hω⟩ := bmSTS_rootGroup_canonical_traceScalar (f := f) K hKrank
  refine ⟨((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
      GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2 (2 *
          max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max
              f 1))) *ᵥ v₀)), (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁
                  hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
                      ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm
                          ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec
                              m' f) u_SU).1 : GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix
                                  (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                                      ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
                                          (GaloisField 2 (2 * max f 1))) *ᵥ v₀))), ω, rfl, rfl, ?_,
                                              ?_, hω⟩
  · intro hzero
    apply ha0'
    have h := congrArg (fun w : W => (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank)
        ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
            m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) w)) hzero
    simpa using h
  · haveI : FiniteDimensional K W := FiniteDimensional.of_finrank_pos (by omega)
    let Φ := bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace
    have hΦ : ∀ a b : W, CFSG.ClassicalGroups.Unitary.herm τ (Φ a) (Φ b) = h a b := by
      intro a b
      have hspec := Classical.choose_spec
          (CFSG.Fischer.Classification.exists_linearEquiv_herm_of_form
        (bmSTS_blockEmbeddingEV_PSU_unitaryInvolution n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
          W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
        (bmSTS_blockEmbeddingEV_PSU_isHermForm n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
          m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
        hnd hrank)
      simpa only [Φ, bmSTS_blockEmbeddingEV_PSU_hermEquiv, LinearEquiv.restrictScalars_apply]
        using hspec a b
    have h2 := bmSTS_herm_stdModuleEquiv f m' K hKrank τ hτ2 hτne ((((Unitary.conjEquiv
        (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 : GL (Fin m') (GaloisField
            2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))
                    *ᵥ v₀)) ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec
                        m' f) u_SU).1 : GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin
                            m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ ((bmSTS_antidiagConj m' f
                                : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀))
    rw [haa', map_zero] at h2
    rw [← hΦ (Φ.symm ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm
        ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 : GL
            (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2 (2 *
                max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2
                    * max f 1))) *ᵥ v₀))))
        (Φ.symm ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm
            ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
                GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField
                    2 (2 * max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
                        (GaloisField 2 (2 * max f 1))) *ᵥ v₀)))),
      LinearEquiv.apply_symm_apply]
    exact h2

private theorem bmSTS_siegelCore_altSiegel_le_image_of_hroot
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG)
    (hrootG' : ∀ g' ∈ rootG, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ((bmSTS_ggU_K_eq m' f) ▸ g) = g')
    (hroot : ∀ c : GaloisField 2 f, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
      ∀ x : W, bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
          W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x = x + (c • h v x) • v) :
    altSiegelGroup (bmSTS_J n f) (eW v) (eW (ω • v)) ≤ (Subgroup.map ((CFSG.Open.StatedSp n
        (GaloisField 2 f)).subtype)
            (Subgroup.map (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)
              ((ggU .PSU m' (max f 1)).D.rootGroup β₀))) := by
  have hunif := bmSTS_blockExtend_transvection_uniform n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace β₀ hlong v
          ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a) hv_eq hvv ω hω hroot
  have hv0 : v ≠ 0 := by
    rw [hv_eq]
    intro hzero
    refine ha0 ?_
    have h1 : (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a = 0 := by
      have := congrArg (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂
          hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) hzero
      simpa using this
    have h2 : a = 0 := by
      have := congrArg ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank)) h1
      simpa using this
    exact h2
  rw [(bmSTS_rootGroupImage_altSiegel n f h eW heWinj htrace hKrank v hv0 hvv ω hω).2.2]
  rw [Subgroup.closure_le]
  rintro x ⟨c, hxc⟩
  have hc := hunif c
  dsimp only at hc
  obtain ⟨hgmem, hgact, hgmat⟩ := hc
  refine Subgroup.mem_map.mpr ⟨bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂
      hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
          (bmSTS_transvectionModelElem f ((ggU .PSU m' (max f 1)).D.rootGroup β₀) (fun g x =>
              bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
                  h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x) (fun x => x +
                      (c • h v x) • v) (hroot c)), Subgroup.mem_map.mpr ⟨bmSTS_transvectionModelElem
                          f ((ggU .PSU m' (max f 1)).D.rootGroup β₀) (fun g x =>
                              bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁
                                  hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm'
                                      hKrank htrace g x) (fun x => x + (c • h v x) • v) (hroot c),
                                          hgmem, rfl⟩, ?_⟩
  apply Units.ext
  change ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace (bmSTS_transvectionModelElem f
          ((ggU .PSU m' (max f 1)).D.rootGroup β₀) (fun g x =>
              bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
                  h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x) (fun x => x +
                      (c • h v x) • v) (hroot c)) : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix
                          (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = (x : Matrix (Fin n ⊕
                              Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
  rw [hgmat]
  exact hxc.symm

private theorem bmSTS_siegelCore_image_le_altSiegel
    (n f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))] (S : Set (GL (Fin n ⊕ Fin n)
        (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((@bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K _ _ _ hKrank
              (Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f))).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG) :
    (Subgroup.map ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)
            (Subgroup.map (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                K τ W h eW m'
              heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)
              ((ggU .PSU m' (max f 1)).D.rootGroup β₀))) ≤ altSiegelGroup (bmSTS_J n f) (eW v) (eW
                  (ω • v)) := by
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1)) :=
    Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra f)
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  rcases Subgroup.mem_map.mp hy with ⟨g, hgm, rfl⟩
  have hgm' : ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG := hrootG g hgm
  obtain ⟨c, hc, hact'⟩ :=
    bmSTS_suAction_transvection_fixed u_SU v₀ hv₀ hiso rootG hu_SU ((bmSTS_ggU_K_eq m' f) ▸ g) hgm'
  rw [← ha_eq] at hact'
  have hact : ∀ y : Fin m' → GaloisField 2 (2 * max f 1),
      bmSTS_blockEmbeddingEV_PSU_suAction m' f g y =
        y + c • CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a y • a := hact'
  let φ : K ≃ₐ[GaloisField 2 f] (GaloisField 2 (2 * max f 1)) :=
      bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank
  let A : (Fin m' → K) ≃ₗ[GaloisField 2 f] (Fin m' → GaloisField 2 (2 * max f 1)) :=
    bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
  let a' : Fin m' → K := A.symm a
  let cK : K := φ.symm c
  have hA_smul : ∀ (c' : GaloisField 2 (2 * max f 1)) (w : Fin m' → GaloisField 2 (2 * max f 1)),
      A.symm (c' • w) = φ.symm c' • A.symm w := by
    intro c' w
    funext i
    exact map_mul φ.symm c' (w i)
  have hstd : ∀ y : Fin m' → K,
      bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g y =
        y + cK • CFSG.ClassicalGroups.Unitary.herm τ a' y • a' := by
    intro y
    have h1 : bmSTS_blockEmbeddingEV_PSU_stdAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g y =
        A.symm (A y + c • CFSG.ClassicalGroups.Unitary.herm
            (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a (A y) • a) := by
      show (bmSTS_blockEmbeddingEV_PSU_stdActionMap n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g) y = _
      simp only [bmSTS_blockEmbeddingEV_PSU_stdActionMap, LinearMap.comp_apply]
      rw [hact ((↑(bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank) :
        (Fin m' → K) →ₗ[GaloisField 2 f] (Fin m' → GaloisField 2 (2 * max f 1))) y)]
      rfl
    rw [h1, map_add]
    rw [show c • CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a (A y) • a =
        (c * CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a (A y)) • a from
      smul_smul c (CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a (A y)) a]
    rw [hA_smul, map_mul]
    rw [show A.symm (A y) = y from A.symm_apply_apply y]
    have h2 := bmSTS_herm_stdModuleEquiv f m' K hKrank τ hτ2 hτne a (A y)
    rw [← h2]
    rw [show A.symm (A y) = y from A.symm_apply_apply y]
    rw [show cK = φ.symm c from rfl, smul_smul]
  have hcK : τ cK = cK := by
    have hcompat : ∀ x : K, φ (τ x) = CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1) (φ x) := by
      intro x
      have hKcard : Nat.card K = 2 ^ (2 * max f 1) := bmSTS_natCard_of_finrank_two f K hKrank
      have hτne1 : τ ≠ 1 := by intro h; exact hτne (by rw [h]; rfl)
      have hτ2mul : τ * τ = 1 := by ext a; exact hτ2 a
      obtain ⟨-, hpow⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.even_and_eq_pow_of_involution_prime
          Nat.prime_two (by omega) hKcard hτne1 hτ2mul
      rw [hpow x, map_pow, CFSG.LieType.BorelTits.unitaryInvolution_apply]
      congr 1
      rw [Nat.mul_div_cancel_left (max f 1) (by norm_num : 0 < 2)]
    have h1 := hcompat cK
    have h2 : φ cK = c := by
      rw [show cK = φ.symm c from rfl, AlgEquiv.apply_symm_apply]
    rw [h2, hc] at h1
    have h3 := congrArg φ.symm h1
    rw [AlgEquiv.symm_apply_apply] at h3
    simpa only [cK] using h3
  have hblock := bmSTS_stdAction_blockAction_transvection_fixed n f S hSU hS hodd he hadj hdeg₁
      hdeg₂
    hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g a' cK hstd
  have hτlin := bmSTS_tauFixesBase n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne
  obtain ⟨cF, hcF⟩ := bmSTS_fixed_eq_algebraMap K hKrank τ hτne hτlin hcK
  have hact2 : ∀ x : W,
      bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x = x + (cF • h v x) • v := by
    intro x
    rw [hblock x, hv_eq, ← hcF]
    simp only [algebraMap_smul]
    dsimp only [a', A]
    rw [smul_assoc]
  have hmat := bmSTS_blockExtend_transvection_matrix n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
    h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace v ω hω g cF hact2
  refine Subgroup.subset_closure ⟨cF, ?_⟩
  change ((bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : GL (Fin n ⊕ Fin n)
          (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
    1 + cF • (Matrix.vecMulVec (eW v) (Matrix.mulVec (bmSTS_J n f) (eW (ω • v))) +
      Matrix.vecMulVec (eW (ω • v)) (Matrix.mulVec (bmSTS_J n f) (eW v)))
  exact hmat

private theorem bmSTS_siegelCore_altSiegel_le_image
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (rootG : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1)) m')) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (ha0 : a ≠ 0) (haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0)
    (ha_eq : a = (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 :
            GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2
                (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v₀))
    (hv_eq : v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
        W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
            ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hu_SU : ((rootG.map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
            m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K, g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ →
        ((bmSTS_ggU_K_eq m' f) ▸ g) ∈ rootG)
    (hrootG' : ∀ g' ∈ rootG, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        ((bmSTS_ggU_K_eq m' f) ▸ g) = g') :
    altSiegelGroup (bmSTS_J n f) (eW v) (eW (ω • v)) ≤ (Subgroup.map ((CFSG.Open.StatedSp n
        (GaloisField 2 f)).subtype)
            (Subgroup.map (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                K τ W h eW m'
              heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)
              ((ggU .PSU m' (max f 1)).D.rootGroup β₀))) := by
  have hroot : ∀ c : GaloisField 2 f, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
      ∀ x : W, bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
          W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g x = x + (c • h v x) • v :=
            by
    intro c
    obtain ⟨g, hgm, hact⟩ := bmSTS_siegelCore_suAction_of_generator n f S hSU hS hodd he hadj hdeg₁
        hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong
            rootG u_SU v₀ a v ω hv₀ hiso ha0 haa ha_eq hv_eq hvv hω hu_SU hrootG hrootG' c
    exact ⟨g, hgm, bmSTS_siegelCore_blockAction_of_suAction_transvection n f S hSU hS hodd he hadj
        hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀
            hlong rootG u_SU v₀ a v ω hv₀ hiso ha0 haa ha_eq hv_eq hvv hω hu_SU hrootG hrootG' c g
                hgm hact⟩
  exact bmSTS_siegelCore_altSiegel_le_image_of_hroot n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong rootG u_SU v₀ a v ω
          hv₀ hiso ha0 haa ha_eq hv_eq hvv hω hu_SU hrootG hrootG' hroot

private theorem bmSTS_unitTransv_pair_nonzero
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (β : Fin (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rank → ℤ)
    (hβ : GGLongRoot (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2
        (max f 1) (le_max_right f 1)) m') β)
    (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ : Fin m' → GaloisField 2 (2 * max f 1)) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (hu_SU : ((((Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rootGroup β).map (MulAut.conj u_SU).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1)) m').subtype) =
      unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (ha_eq : a = ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 : GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m')
            (GaloisField 2 (2 * max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
                (GaloisField 2 (2 * max f 1))) *ᵥ v₀))) (hv_eq : v =
                    (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
                            ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a)) :
    a ≠ 0 := by
  rw [ha_eq]
  let σR : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
      CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  let P : GL (Fin m') (GaloisField 2 (2 * max f 1)) := bmSTS_antidiagConj m' f
  have hP : Unitary.conjTr σR (P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) * (P :
      Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) = Unitary.antidiag m' :=
          bmSTS_antidiagConj_spec m' f
  let Cu : GL (Fin m') (GaloisField 2 (2 * max f 1)) := (Unitary.conjEquiv (bmSTS_antidiagConj m' f)
      (bmSTS_antidiagConj_spec m' f) u_SU).1
  have hisoCu : ∀ u v : Fin m' → GaloisField 2 (2 * max f 1), CFSG.ClassicalGroups.Unitary.herm σR
      ((Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ u) ((Cu : Matrix (Fin m')
          (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v) = CFSG.ClassicalGroups.Unitary.herm σR u v
              :=
    fun u v => CFSG.ClassicalGroups.Unitary.herm_smul_smul σR (Unitary.conjEquiv (bmSTS_antidiagConj
        m' f) (bmSTS_antidiagConj_spec m' f) u_SU) u v
  have hPv0 : (P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀ ≠ 0 :=
      (bmSTS_antidiagConj_mulVec_isotropic m' f v₀ hv₀ hiso).1
  have hPv0aa : CFSG.ClassicalGroups.Unitary.herm σR ((P : Matrix (Fin m') (Fin m') (GaloisField 2
      (2 * max f 1))) *ᵥ v₀) ((P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀) =
          0 := (bmSTS_antidiagConj_mulVec_isotropic m' f v₀ hv₀ hiso).2
  obtain ⟨ha0c, -⟩ := bmSTS_mulVec_inv_nonzero_isotropic σR Cu ((P : Matrix (Fin m') (Fin m')
      (GaloisField 2 (2 * max f 1))) *ᵥ v₀) hPv0 hPv0aa hisoCu
  simpa only [Cu, P, hP, Matrix.GeneralLinearGroup.coe_inv] using ha0c

private theorem bmSTS_unitTransv_pair_isotropic
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (β : Fin (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rank → ℤ)
    (hβ : GGLongRoot (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2
        (max f 1) (le_max_right f 1)) m') β)
    (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ : Fin m' → GaloisField 2 (2 * max f 1)) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (hu_SU : ((((Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rootGroup β).map (MulAut.conj u_SU).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1)) m').subtype) =
      unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (ha_eq : a = ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 : GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m')
            (GaloisField 2 (2 * max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
                (GaloisField 2 (2 * max f 1))) *ᵥ v₀))) (hv_eq : v =
                    (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
                            ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a)) :
    CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        max f 1)) 2 (max f 1)) a a = 0 := by
  rw [ha_eq]
  let σR : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
      CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)
  let P : GL (Fin m') (GaloisField 2 (2 * max f 1)) := bmSTS_antidiagConj m' f
  have hP : Unitary.conjTr σR (P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) * (P :
      Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) = Unitary.antidiag m' :=
          bmSTS_antidiagConj_spec m' f
  let Cu : GL (Fin m') (GaloisField 2 (2 * max f 1)) := (Unitary.conjEquiv (bmSTS_antidiagConj m' f)
      (bmSTS_antidiagConj_spec m' f) u_SU).1
  have hisoCu : ∀ u v : Fin m' → GaloisField 2 (2 * max f 1), CFSG.ClassicalGroups.Unitary.herm σR
      ((Cu : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ u) ((Cu : Matrix (Fin m')
          (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v) = CFSG.ClassicalGroups.Unitary.herm σR u v
              :=
    fun u v => CFSG.ClassicalGroups.Unitary.herm_smul_smul σR (Unitary.conjEquiv (bmSTS_antidiagConj
        m' f) (bmSTS_antidiagConj_spec m' f) u_SU) u v
  have hPv0 : (P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀ ≠ 0 :=
      (bmSTS_antidiagConj_mulVec_isotropic m' f v₀ hv₀ hiso).1
  have hPv0aa : CFSG.ClassicalGroups.Unitary.herm σR ((P : Matrix (Fin m') (Fin m') (GaloisField 2
      (2 * max f 1))) *ᵥ v₀) ((P : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v₀) =
          0 := (bmSTS_antidiagConj_mulVec_isotropic m' f v₀ hv₀ hiso).2
  obtain ⟨-, haac⟩ := bmSTS_mulVec_inv_nonzero_isotropic σR Cu ((P : Matrix (Fin m') (Fin m')
      (GaloisField 2 (2 * max f 1))) *ᵥ v₀) hPv0 hPv0aa hisoCu
  simpa only [Cu, P, hP, Matrix.GeneralLinearGroup.coe_inv] using haac

private theorem bmSTS_unitTransv_pair_exists
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (β : Fin (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rank → ℤ)
    (hβ : GGLongRoot (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2
        (max f 1) (le_max_right f 1)) m') β)
    (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ : Fin m' → GaloisField 2 (2 * max f 1)) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (hu_SU : ((((Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rootGroup β).map (MulAut.conj u_SU).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1)) m').subtype) =
      unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)).toRingHom (Unitary.antidiag m') v₀) :
    ∃ (a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K),
      a = ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
          GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m') (GaloisField 2 (2
              * max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2
                  * max f 1))) *ᵥ v₀)) ∧ v = (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd
                      he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm'
                          htrace).symm ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K
                              hKrank).symm a) ∧ v ≠ 0 ∧ h v v = 0 ∧
        Algebra.trace (GaloisField 2 f) K ω = 1 ∧ a ≠ 0 ∧ CFSG.ClassicalGroups.Unitary.herm
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a
                = 0 := by
  obtain ⟨a, v, ω, ha_eq, hv_eq, hv, hvv, hω⟩ :=
    bmSTS_unitTransv_isotropicPair n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong β hβ u_SU v₀ hv₀ hiso hu_SU
  have ha0 : a ≠ 0 := bmSTS_unitTransv_pair_nonzero n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong β hβ u_SU v₀ hv₀
          hiso hu_SU a v ω ha_eq hv_eq
  have haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0 :=
    bmSTS_unitTransv_pair_isotropic n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong β hβ u_SU v₀ hv₀ hiso hu_SU a
            v ω ha_eq hv_eq
  exact ⟨a, v, ω, ha_eq, hv_eq, hv, hvv, hω, ha0, haa⟩

private theorem bmSTS_unitTransv_pair_image_le
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (β : Fin (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rank → ℤ)
    (hβ : GGLongRoot (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2
        (max f 1) (le_max_right f 1)) m') β)
    (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ : Fin m' → GaloisField 2 (2 * max f 1)) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (hu_SU : ((((Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rootGroup β).map (MulAut.conj u_SU).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1)) m').subtype) =
      unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (ha_eq : a = ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 : GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m')
            (GaloisField 2 (2 * max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
                (GaloisField 2 (2 * max f 1))) *ᵥ v₀))) (hv_eq : v =
                    (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
                            ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K,
        g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ → (bmSTS_ggU_K_eq m' f ▸ g) ∈ (Unitary.rootDatum
            (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f 1))
                m').rootGroup β) :
    (((ggU .PSU m' (max f 1)).D.rootGroup β₀).map (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd
        he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank
            htrace)).map ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) ≤ altSiegelGroup
                (bmSTS_J n f) (eW v) (eW (ω • v)) := by
  have ha0 : a ≠ 0 := bmSTS_unitTransv_pair_nonzero n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong β hβ u_SU v₀ hv₀
          hiso hu_SU a v ω ha_eq hv_eq
  have haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0 :=
    bmSTS_unitTransv_pair_isotropic n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong β hβ u_SU v₀ hv₀ hiso hu_SU a
            v ω ha_eq hv_eq
  exact bmSTS_siegelCore_image_le_altSiegel n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong ((Unitary.rootDatum
          (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f 1))
              m').rootGroup β) u_SU v₀ a v ω hv₀ hiso ha0 haa ha_eq hv_eq hvv hω hu_SU hrootG

private theorem bmSTS_unitTransv_pair_image_ge
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (hlong : GGLongRoot (ggU .PSU m' (max f 1)).D β₀)
    (β : Fin (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rank → ℤ)
    (hβ : GGLongRoot (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2
        (max f 1) (le_max_right f 1)) m') β)
    (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ : Fin m' → GaloisField 2 (2 * max f 1)) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (hu_SU : ((((Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rootGroup β).map (MulAut.conj u_SU).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1)) m').subtype) =
      unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (a : Fin m' → GaloisField 2 (2 * max f 1)) (v : W) (ω : K)
    (ha_eq : a = ((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f)
        u_SU).1 : GL (Fin m') (GaloisField 2 (2 * max f 1)))⁻¹ : Matrix (Fin m') (Fin m')
            (GaloisField 2 (2 * max f 1))) *ᵥ ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m')
                (GaloisField 2 (2 * max f 1))) *ᵥ v₀))) (hv_eq : v =
                    (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).symm
                            ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm a))
    (hvv : h v v = 0) (hω : Algebra.trace (GaloisField 2 f) K ω = 1)
    (hrootG : ∀ g : (ggU .PSU m' (max f 1)).K,
        g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀ → (bmSTS_ggU_K_eq m' f ▸ g) ∈ (Unitary.rootDatum
            (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f 1))
                m').rootGroup β)
    (hrootG' : ∀ g' ∈ (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f
        1) (le_max_right f 1)) m').rootGroup β, ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup β₀,
        (bmSTS_ggU_K_eq m' f ▸ g) = g') :
    altSiegelGroup (bmSTS_J n f) (eW v) (eW (ω • v)) ≤ (((ggU .PSU m' (max f 1)).D.rootGroup β₀).map
        (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
            heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map ((CFSG.Open.StatedSp n
                (GaloisField 2 f)).subtype) := by
  have ha0 : a ≠ 0 := bmSTS_unitTransv_pair_nonzero n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong β hβ u_SU v₀ hv₀
          hiso hu_SU a v ω ha_eq hv_eq
  have haa : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a = 0 :=
    bmSTS_unitTransv_pair_isotropic n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong β hβ u_SU v₀ hv₀ hiso hu_SU a
            v ω ha_eq hv_eq
  exact bmSTS_siegelCore_altSiegel_le_image n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong ((Unitary.rootDatum
          (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f 1))
              m').rootGroup β) u_SU v₀ a v ω hv₀ hiso ha0 haa ha_eq hv_eq hvv hω hu_SU hrootG
                  hrootG'

private theorem bmSTS_ggLongRoot_neg
    (m' f : ℕ)
    (β : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
    (h : GGLongRoot (ggU .PSU m' (max f 1)).D β) :
    GGLongRoot (ggU .PSU m' (max f 1)).D (-β) := by
  obtain ⟨w, γ₀, hγ₀, hmax, hw⟩ := h
  have hmem : γ₀ ∈ (ggU .PSU m' (max f 1)).D.roots := hγ₀
  have hneg : ∃ s, ((CFSG.LieType.RootSystem.weylAction
      (ggU .PSU m' (max f 1)).D.isFiniteType) s) γ₀ = -γ₀ := by
    rw [CFSG.LieType.Universal.UniversalRootDatum.roots] at hmem
    rcases hmem with h | h
    · rcases h with ⟨w₀, i, hγ₀eq⟩
      have hδ : ((CFSG.LieType.RootSystem.weylAction
          (ggU .PSU m' (max f 1)).D.isFiniteType) w₀) (Pi.single i (1 : ℤ)) ∈
          CFSG.LieType.RootSystem.roots (ggU .PSU m' (max f 1)).D.isFiniteType
            (∅ : Set (Fin (ggU .PSU m' (max f 1)).D.rank)) := Or.inl ⟨w₀, i, rfl⟩
      obtain ⟨s, hs⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_weylAction_eq_neg
        (hA := (ggU .PSU m' (max f 1)).D.isFiniteType)
        (γ := ((CFSG.LieType.RootSystem.weylAction
          (ggU .PSU m' (max f 1)).D.isFiniteType) w₀) (Pi.single i (1 : ℤ))) hδ
      exact ⟨s, by rw [hγ₀eq]; exact hs⟩
    · rcases h with ⟨w₀, i, _hiD, hγ₀eq⟩
      have hδ : ((CFSG.LieType.RootSystem.weylAction
          (ggU .PSU m' (max f 1)).D.isFiniteType) w₀) (Pi.single i (1 : ℤ)) ∈
          CFSG.LieType.RootSystem.roots (ggU .PSU m' (max f 1)).D.isFiniteType
            (∅ : Set (Fin (ggU .PSU m' (max f 1)).D.rank)) := Or.inl ⟨w₀, i, rfl⟩
      obtain ⟨s, hs⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_weylAction_eq_neg
        (hA := (ggU .PSU m' (max f 1)).D.isFiniteType)
        (γ := ((CFSG.LieType.RootSystem.weylAction
          (ggU .PSU m' (max f 1)).D.isFiniteType) w₀) (Pi.single i (1 : ℤ))) hδ
      refine ⟨s, ?_⟩
      have hlin : ((CFSG.LieType.RootSystem.weylAction
          (ggU .PSU m' (max f 1)).D.isFiniteType) s)
            (2 • (((CFSG.LieType.RootSystem.weylAction
              (ggU .PSU m' (max f 1)).D.isFiniteType) w₀) (Pi.single i (1 : ℤ)))) =
          2 • (((CFSG.LieType.RootSystem.weylAction
              (ggU .PSU m' (max f 1)).D.isFiniteType) s)
            (((CFSG.LieType.RootSystem.weylAction
              (ggU .PSU m' (max f 1)).D.isFiniteType) w₀) (Pi.single i (1 : ℤ)))) :=
        map_smul _ (2 : ℤ) _
      rw [hγ₀eq, hlin, hs, smul_neg]
  obtain ⟨s, hs⟩ := hneg
  refine ⟨w * s, γ₀, hγ₀, hmax, ?_⟩
  have hwneg : -β = ((CFSG.LieType.RootSystem.weylAction
      (ggU .PSU m' (max f 1)).D.isFiniteType) w) (-γ₀) := by
    rw [hw]
    exact (map_neg ((CFSG.LieType.RootSystem.weylAction
      (ggU .PSU m' (max f 1)).D.isFiniteType) w) γ₀).symm
  rw [hwneg, ← hs]
  exact congrArg (fun g => g γ₀) (map_mul (CFSG.LieType.RootSystem.weylAction
    (ggU .PSU m' (max f 1)).D.isFiniteType) w s).symm

private lemma bmSTS_LieUniversal_transport_neg {A B : LieUniversal} (heq : A = B)
    (β : Fin A.D.rank → ℤ) :
    (congrArg (fun X : LieUniversal => Fin X.D.rank → ℤ) heq) ▸ (-β) =
      -((congrArg (fun X : LieUniversal => Fin X.D.rank → ℤ) heq) ▸ β) := by
  cases heq
  rfl

private theorem bmSTS_altSiegel_smul_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Matrix ι ι F) (c₁ c₂ : F) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (v w : ι → F) :
    altSiegelGroup G (c₁ • v) (c₂ • w) = altSiegelGroup G v w := by
  rw [altSiegelGroup, altSiegelGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e * (c₁ * c₂), ?_⟩
    rw [he]
    congr 1
    simp only [Matrix.mulVec_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_add,
      smul_smul]
    module
  · rintro ⟨e, he⟩
    refine ⟨e * (c₁ * c₂)⁻¹, ?_⟩
    rw [he]
    congr 1
    simp only [Matrix.mulVec_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_add,
      smul_smul]
    field_simp

private theorem bmSTS_hermEquiv_isometry
    (n f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ u v : W,
      CFSG.ClassicalGroups.Unitary.herm τ
        ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) u)
        ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) v) = h u v := by
  intro u v
  haveI : FiniteDimensional K W := FiniteDimensional.of_finrank_pos (by rw [hrank]; omega)
  have hspec := Classical.choose_spec (CFSG.Fischer.Classification.exists_linearEquiv_herm_of_form
    (bmSTS_blockEmbeddingEV_PSU_unitaryInvolution n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
    (bmSTS_blockEmbeddingEV_PSU_isHermForm n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace)
    hnd hrank)
  simpa only [bmSTS_blockEmbeddingEV_PSU_hermEquiv, LinearEquiv.restrictScalars_apply]
    using hspec u v

private theorem bmSTS_antidiagConj_herm_pair
    (m' f : ℕ) (u v : Fin m' → GaloisField 2 (2 * max f 1)) :
    CFSG.ClassicalGroups.Unitary.herm
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
        ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ u)
        ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v) =
      Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1) (u i)) (Unitary.antidiag m') ⬝ᵥ v := by
  set σ : GaloisField 2 (2 * max f 1) ≃+* GaloisField 2 (2 * max f 1) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1) with hσ
  have hherm_mul : ∀ (M : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))
      (y : Fin m' → GaloisField 2 (2 * max f 1)),
      CFSG.ClassicalGroups.Unitary.herm σ (M *ᵥ u) y =
        CFSG.ClassicalGroups.Unitary.herm σ u (Unitary.conjTr σ M *ᵥ y) := by
    intro M y
    rw [CFSG.ClassicalGroups.Unitary.herm_def, CFSG.ClassicalGroups.Unitary.herm_def]
    simp only [Matrix.mulVec, dotProduct, Unitary.conjTr, Matrix.transpose_apply,
      Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finset.sum_congr rfl fun i _ => by ring
  have hP : Unitary.conjTr σ
      (bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
      (bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) =
      Unitary.antidiag m' := by
    simpa only [hσ] using bmSTS_antidiagConj_spec m' f
  have hb : CFSG.ClassicalGroups.Unitary.herm σ u (Unitary.antidiag m' *ᵥ v) =
      Matrix.vecMul (fun i => σ (u i)) (Unitary.antidiag m') ⬝ᵥ v := by
    rw [CFSG.ClassicalGroups.Unitary.herm_def]
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
    have hL : (∑ x, σ (u x) * ∑ x_1, Unitary.antidiag m' x x_1 * v x_1) =
        ∑ x, ∑ x_1, σ (u x) * (Unitary.antidiag m' x x_1 * v x_1) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
    rw [hL, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc CFSG.ClassicalGroups.Unitary.herm σ
        ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ u)
        ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v)
      = CFSG.ClassicalGroups.Unitary.herm σ u
          (Unitary.conjTr σ (bmSTS_antidiagConj m' f :
            Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
            ((bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ
                v)) :=
        hherm_mul _ _
    _ = CFSG.ClassicalGroups.Unitary.herm σ u
          ((Unitary.conjTr σ (bmSTS_antidiagConj m' f :
            Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *
            (bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ
                v) := by
        rw [Matrix.mulVec_mulVec]
    _ = CFSG.ClassicalGroups.Unitary.herm σ u (Unitary.antidiag m' *ᵥ v) := by rw [hP]
    _ = Matrix.vecMul (fun i => σ (u i)) (Unitary.antidiag m') ⬝ᵥ v := hb

private theorem bmSTS_altSiegel_basis_change {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (G : Matrix ι ι F) (x y : ι → F) (α β γ δ : F) (hΔ : α * δ + β * γ ≠ 0) :
    altSiegelGroup G (α • x + β • y) (γ • x + δ • y) = altSiegelGroup G x y := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hgen : Matrix.vecMulVec (α • x + β • y) (Matrix.mulVec G (γ • x + δ • y)) +
      Matrix.vecMulVec (γ • x + δ • y) (Matrix.mulVec G (α • x + β • y)) =
      (α * δ + β * γ) • (Matrix.vecMulVec x (Matrix.mulVec G y) +
        Matrix.vecMulVec y (Matrix.mulVec G x)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.add_apply,
      Pi.smul_apply, Matrix.mulVec_add, Matrix.mulVec_smul, smul_eq_mul]
    ring_nf
    simp only [htwo, mul_zero, add_zero, zero_add]
  rw [altSiegelGroup, altSiegelGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e * (α * δ + β * γ), ?_⟩
    rw [he, hgen, smul_smul]
  · rintro ⟨e, he⟩
    refine ⟨e * (α * δ + β * γ)⁻¹, ?_⟩
    rw [he, hgen, smul_smul, mul_assoc, inv_mul_cancel₀ hΔ, mul_one]

private theorem bmSTS_trace_base_zero (f : ℕ) (K : Type) [Field K] [Algebra (GaloisField 2 f) K]
    [Finite K] (hKrank : Module.finrank (GaloisField 2 f) K = 2) (c : GaloisField 2 f) :
    Algebra.trace (GaloisField 2 f) K (algebraMap (GaloisField 2 f) K c) = 0 := by
  rw [Algebra.trace_algebraMap (R := GaloisField 2 f) (S := K) c, hKrank]
  rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

private theorem bmSTS_conjEquiv_isometry
    (m' f : ℕ) [Algebra (GaloisField 2 f) (GaloisField 2 (2 * max f 1))]
    (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m')) :
    ∀ u v : Fin m' → GaloisField 2 (2 * max f 1),
      CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1))
        (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
          Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ u)
        (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
          Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1))) *ᵥ v) =
      CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1)) u v :=
  fun u v => CFSG.ClassicalGroups.Unitary.herm_smul_smul
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
    (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU) u v

private theorem bmSTS_herm_inv_isometry {F : Type} [Field F] {m' : ℕ}
    (σ : F ≃+* F) (M : GL (Fin m') F)
    (hiso : ∀ u v : Fin m' → F,
      CFSG.ClassicalGroups.Unitary.herm σ ((M : Matrix (Fin m') (Fin m') F) *ᵥ u)
        ((M : Matrix (Fin m') (Fin m') F) *ᵥ v) = CFSG.ClassicalGroups.Unitary.herm σ u v) :
    ∀ u v : Fin m' → F,
      CFSG.ClassicalGroups.Unitary.herm σ
        (((M⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ u)
        (((M⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ v) =
      CFSG.ClassicalGroups.Unitary.herm σ u v := by
  intro u v
  have hCa : ∀ x : Fin m' → F, (M : Matrix (Fin m') (Fin m') F) *ᵥ
      (((M⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hh := hiso (((M⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ u)
    (((M⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ v)
  rw [hCa u, hCa v] at hh
  exact hh.symm

private theorem bmSTS_herm_conj_pair_value {F : Type} [Field F] {m' : ℕ}
    (σ : F ≃+* F) (M : GL (Fin m') F) (Pm : Matrix (Fin m') (Fin m') F)
    (hiso : ∀ u v : Fin m' → F,
      CFSG.ClassicalGroups.Unitary.herm σ ((M : Matrix (Fin m') (Fin m') F) *ᵥ u)
        ((M : Matrix (Fin m') (Fin m') F) *ᵥ v) = CFSG.ClassicalGroups.Unitary.herm σ u v)
    (v₀ w₀ a a' : Fin m' → F)
    (ha : a = ((M : Matrix (Fin m') (Fin m') F)⁻¹) *ᵥ (Pm *ᵥ v₀))
    (ha' : a' = ((M : Matrix (Fin m') (Fin m') F)⁻¹) *ᵥ (Pm *ᵥ w₀))
    (hPvw : CFSG.ClassicalGroups.Unitary.herm σ (Pm *ᵥ v₀) (Pm *ᵥ w₀) = 1) :
    CFSG.ClassicalGroups.Unitary.herm σ a a' = 1 := by
  have hisoInv := bmSTS_herm_inv_isometry σ M hiso
  have hisoInv' : ∀ u v : Fin m' → F,
      CFSG.ClassicalGroups.Unitary.herm σ (((M : Matrix (Fin m') (Fin m') F)⁻¹) *ᵥ u)
        (((M : Matrix (Fin m') (Fin m') F)⁻¹) *ᵥ v) = CFSG.ClassicalGroups.Unitary.herm σ u v := by
    intro u v
    have h := hisoInv u v
    rwa [Matrix.GeneralLinearGroup.coe_inv] at h
  rw [ha, ha', hisoInv' (Pm *ᵥ v₀) (Pm *ᵥ w₀), hPvw]

private theorem bmSTS_rootPair_images
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∃ (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ) (v w : W) (ω ω' : K),
      GGLongRoot (ggU .PSU m' (max f 1)).D β₀ ∧
      v ≠ 0 ∧ h v v = 0 ∧ w ≠ 0 ∧ h w w = 0 ∧ h v w = 1 ∧
      Algebra.trace (GaloisField 2 f) K ω = 1 ∧
      Algebra.trace (GaloisField 2 f) K ω' = 1 ∧
      (((ggU .PSU m' (max f 1)).D.rootGroup β₀).map
          (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
            heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        altSiegelGroup (bmSTS_J n f) (eW v) (eW (ω • v)) ∧
      (((ggU .PSU m' (max f 1)).D.rootGroup (-β₀)).map
          (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
            heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        altSiegelGroup (bmSTS_J n f) (eW w) (eW (ω' • w)) := by
  obtain ⟨β₀, hlong⟩ :=
    bmSTS_rootPair_longRoot n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2
      hτne hsymm hnd hrank hm' hm3 hKrank htrace
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have heq : (ggU .PSU m' (max f 1)) =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
          (max f 1)) m',
        Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  let βT := (congrArg (fun X : LieUniversal => Fin X.D.rank → ℤ) heq) ▸ β₀
  have hβT : GGLongRoot (Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m') βT :=
    bmSTS_LieUniversal_transport_longRoot heq β₀ hlong
  obtain ⟨hrootG, hrootG'⟩ := bmSTS_LieUniversal_transport_iff heq β₀
  obtain ⟨hrootGneg, hrootGneg'⟩ := bmSTS_LieUniversal_transport_iff heq (-β₀)
  have hlongneg : GGLongRoot (ggU .PSU m' (max f 1)).D (-β₀) := bmSTS_ggLongRoot_neg m' f β₀ hlong
  have hβTneg : GGLongRoot (Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m') (-βT) :=
      by
    have h1 := bmSTS_LieUniversal_transport_longRoot heq (-β₀) hlongneg
    rwa [bmSTS_LieUniversal_transport_neg heq β₀] at h1
  have hrootGnegT : ∀ g : (ggU .PSU m' (max f 1)).K,
      g ∈ (ggU .PSU m' (max f 1)).D.rootGroup (-β₀) →
      (bmSTS_ggU_K_eq m' f ▸ g) ∈
        (Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m').rootGroup (-βT) := by
    intro g hg
    have h := hrootGneg g hg
    rwa [bmSTS_LieUniversal_transport_neg heq β₀] at h
  have hrootGnegT' : ∀ g' ∈
      (Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m').rootGroup (-βT),
      ∃ g ∈ (ggU .PSU m' (max f 1)).D.rootGroup (-β₀), (bmSTS_ggU_K_eq m' f ▸ g) = g' := by
    intro g' hg'
    refine hrootGneg' g' ?_
    rwa [← bmSTS_LieUniversal_transport_neg heq β₀] at hg'
  obtain ⟨v₀, w₀, hv₀iso, hw₀iso, hvw₀, u_SU, hu_SU, hw_SU⟩ :=
    bmSTS_rootGroup_fixedTransvection (F := GaloisField 2 (2 * max f 1)) (f := max f 1)
      (card_galoisField_two_mul 2 (max f 1) hf) m' hm3 βT hβT
  have hv₀ : v₀ ≠ 0 := by
    intro h0
    have hz : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') = 0 := by
      rw [h0]
      funext j
      simp [Matrix.vecMul]
    rw [hz, zero_dotProduct] at hvw₀
    exact zero_ne_one hvw₀
  have hw₀ : w₀ ≠ 0 := by
    intro h0
    rw [h0, dotProduct_zero] at hvw₀
    exact zero_ne_one hvw₀
  obtain ⟨a, v, ω, ha_eq, hv_eq, hv, hvv, hω, ha0, haa⟩ :=
    bmSTS_unitTransv_pair_exists n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
      heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong βT hβT u_SU v₀ hv₀ hv₀iso hu_SU
  obtain ⟨a', w, ω', ha'_eq, hw'_eq, hw, hww, hω', ha0', haa'⟩ :=
    bmSTS_unitTransv_pair_exists n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
      heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace (-β₀) hlongneg (-βT) hβTneg u_SU w₀ hw₀
      hw₀iso hw_SU
  have himg₁ : (((ggU .PSU m' (max f 1)).D.rootGroup β₀).map
        (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
          heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
      ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
      altSiegelGroup (bmSTS_J n f) (eW v) (eW (ω • v)) :=
    le_antisymm
      (bmSTS_unitTransv_pair_image_le n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong βT hβT u_SU v₀ hv₀ hv₀iso
        hu_SU a v ω ha_eq hv_eq hvv hω hrootG)
      (bmSTS_unitTransv_pair_image_ge n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong βT hβT u_SU v₀ hv₀ hv₀iso
        hu_SU a v ω ha_eq hv_eq hvv hω hrootG hrootG')
  have himg₂ : (((ggU .PSU m' (max f 1)).D.rootGroup (-β₀)).map
        (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
          heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
      ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
      altSiegelGroup (bmSTS_J n f) (eW w) (eW (ω' • w)) :=
    le_antisymm
      (bmSTS_unitTransv_pair_image_le n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace (-β₀) hlongneg (-βT) hβTneg u_SU w₀
            hw₀
        hw₀iso hw_SU a' w ω' ha'_eq hw'_eq hww hω' hrootGnegT)
      (bmSTS_unitTransv_pair_image_ge n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace (-β₀) hlongneg (-βT) hβTneg u_SU w₀
            hw₀
        hw₀iso hw_SU a' w ω' ha'_eq hw'_eq hww hω' hrootGnegT hrootGnegT')
  let Φ : W ≃ₗ[GaloisField 2 f] (Fin m' → K) :=
    bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace
  let A : (Fin m' → K) ≃ₗ[GaloisField 2 f] (Fin m' → GaloisField 2 (2 * max f 1)) :=
    bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
  have h1 : h v w = CFSG.ClassicalGroups.Unitary.herm τ (A.symm a) (A.symm a') := by
    rw [← bmSTS_hermEquiv_isometry n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
      heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace v w, hv_eq, hw'_eq]
    congr 1 <;> exact LinearEquiv.apply_symm_apply Φ _
  have h2 : CFSG.ClassicalGroups.Unitary.herm τ (A.symm a) (A.symm a') =
      (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm
        (CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a') :=
    bmSTS_herm_stdModuleEquiv f m' K hKrank τ hτ2 hτne a a'
  let M : GL (Fin m') (GaloisField 2 (2 * max f 1)) :=
    (Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1
  have h3 : CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) a a' = 1 :=
    bmSTS_herm_conj_pair_value
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
      M (bmSTS_antidiagConj m' f) (bmSTS_conjEquiv_isometry m' f u_SU) v₀ w₀ a a' ha_eq ha'_eq
      ((bmSTS_antidiagConj_herm_pair m' f v₀ w₀).trans hvw₀)
  have hfinal : h v w = 1 := by
    rw [h1, h2, h3, map_one]
  exact ⟨β₀, v, w, ω, ω', hlong, hv, hvv, hw, hww, hfinal, hω, hω', himg₁, himg₂⟩

private lemma bmSTS_hCa {m' : ℕ} {F : Type} [Field F] (M : GL (Fin m') F) (x : Fin m' → F) :
    (M : Matrix (Fin m') (Fin m') F) *ᵥ
      (((M⁻¹ : GL (Fin m') F) : Matrix (Fin m') (Fin m') F) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

private theorem bmSTS_rootPair_explicit
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∃ (β₀ : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ)
      (a₁ a₂ b₁ b₂ : (Fin n ⊕ Fin n) → GaloisField 2 f),
      GGLongRoot (ggU .PSU m' (max f 1)).D β₀ ∧
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) b₁ = 1 ∧
      a₂ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) b₂ = 1 ∧
      (a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 ∧
        b₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) b₂ = 0 ∧
        a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) b₂ = 0 ∧
        a₂ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) b₁ = 0) ∧
      (((ggU .PSU m' (max f 1)).D.rootGroup β₀).map
          (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
            heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        altSiegelGroup (bmSTS_J n f) a₁ a₂ ∧
      (((ggU .PSU m' (max f 1)).D.rootGroup (-β₀)).map
          (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
            heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
        altSiegelGroup (bmSTS_J n f) b₁ b₂ := by
  obtain ⟨β₀, v, w, ω, ω', hlong, hv, hvv, hw, hww, hvw, hω, hω', himg₁, himg₂⟩ :=
    bmSTS_rootPair_images n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2
      hτne hsymm hnd hrank hm' hm3 hKrank htrace
  haveI : FiniteDimensional (GaloisField 2 f) K := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (GaloisField 2 f) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsQuadraticExtension (GaloisField 2 f) K :=
    Algebra.IsQuadraticExtension.mk hKrank
  have hτlin := bmSTS_tauFixesBase n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne
  obtain ⟨σ, hσne, hτσ, -⟩ :=
    bmSTS_tau_eq_canonical n f S hSU hS hodd he hadj hdeg₁ hdeg₂ K hKrank τ hτ2 hτne hτlin
  have hτtrace : ∀ z : K,
      algebraMap (GaloisField 2 f) K (Algebra.trace (GaloisField 2 f) K z) = z + τ z := by
    intro z
    have h := Algebra.IsQuadraticExtension.algebraMap_trace_eq_add (GaloisField 2 f) K hσne z
    rw [h, hτσ z]
  have hTrτ : ∀ z : K,
      Algebra.trace (GaloisField 2 f) K (τ z) = Algebra.trace (GaloisField 2 f) K z := by
    intro z
    apply (algebraMap (GaloisField 2 f) K).injective
    rw [hτtrace (τ z), hτtrace z, hτ2 z]
    exact add_comm _ _
  have hsmul₁ : ∀ (k : K) (x y : W), h (k • x) y = τ k * h x y := by
    intro k x y
    rw [hsymm y (k • x), map_smul (h y) k x, smul_eq_mul, map_mul, hsymm x y, hτ2]
  have hBvv : eW v ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW w) =
      Algebra.trace (GaloisField 2 f) K (h v w) := by
    have h := htrace v w 1
    simpa only [one_smul, one_mul] using h
  have hBvω : eW v ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (ω • v)) =
      Algebra.trace (GaloisField 2 f) K (ω * h v v) := htrace v v ω
  have hBvω'w : eW v ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (ω' • w)) =
      Algebra.trace (GaloisField 2 f) K (ω' * h v w) := htrace v w ω'
  have hBωvw : eW (ω • v) ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW w) =
      Algebra.trace (GaloisField 2 f) K (τ ω * h v w) := by
    have h := htrace (ω • v) w 1
    simp only [one_smul, one_mul] at h
    rw [h, hsmul₁ ω v w]
  have hBωvω'w : eW (ω • v) ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (ω' • w)) =
      Algebra.trace (GaloisField 2 f) K (ω' * (τ ω * h v w)) := by
    have h := htrace (ω • v) w ω'
    rw [h, hsmul₁ ω v w]
  have hBww : eW w ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW w) =
      Algebra.trace (GaloisField 2 f) K (h w w) := by
    have h := htrace w w 1
    simpa only [one_smul, one_mul] using h
  have hBω'ww : eW (ω' • w) ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW w) =
      Algebra.trace (GaloisField 2 f) K (τ ω' * h w w) := by
    have h := htrace (ω' • w) w 1
    simp only [one_smul, one_mul] at h
    rw [h, hsmul₁ ω' w w]
  let c : GaloisField 2 f := Algebra.trace (GaloisField 2 f) K (ω' * τ ω)
  have hbc := bmSTS_altSiegel_basis_change (bmSTS_J n f) (eW w) (eW (ω' • w)) c 1 1 0
    (by norm_num)
  refine ⟨β₀, eW v, eW (ω • v),
    c • eW w + (1 : GaloisField 2 f) • eW (ω' • w),
    (1 : GaloisField 2 f) • eW w + (0 : GaloisField 2 f) • eW (ω' • w), ?_⟩
  refine ⟨hlong, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, himg₁, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, one_smul]
    rw [hBvv, hBvω'w, hvw, mul_one, ← map_one (algebraMap (GaloisField 2 f) K),
      bmSTS_trace_base_zero f K hKrank 1, smul_zero, zero_add, hω']
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, one_smul,
      zero_smul, Matrix.mulVec_zero, dotProduct_zero, add_zero, mul_zero]
    rw [hBωvw, hvw, mul_one, hTrτ ω, hω]
  · simp only [hBvω, hvv, mul_zero, map_zero]
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, smul_dotProduct,
      dotProduct_add, dotProduct_smul, one_smul, zero_smul, Matrix.mulVec_zero, dotProduct_zero,
      add_zero, mul_zero]
    simp only [hBww, hBω'ww, hww, mul_zero, map_zero, smul_zero, add_zero, zero_add]
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, one_smul,
      zero_smul, Matrix.mulVec_zero, dotProduct_zero, add_zero, mul_zero]
    rw [hBvv, hvw, ← map_one (algebraMap (GaloisField 2 f) K),
      bmSTS_trace_base_zero f K hKrank 1]
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul]
    rw [hBωvw, hBωvω'w, hvw, mul_one, hTrτ ω, hω]
    simp only [c, smul_eq_mul, mul_one, one_mul, one_smul]
    rw [← two_mul]
    rw [show (2 : GaloisField 2 f) = 0 from CharP.cast_eq_zero (GaloisField 2 f) 2, zero_mul]
  · rw [himg₂]
    exact hbc.symm

private theorem bmSTS_altSiegel_mem_range
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      a₁ ∈ LinearMap.range (Matrix.mulVecLin e) ∧
      a₂ ∈ LinearMap.range (Matrix.mulVecLin e) := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle
  have hJ'block : J' ≤ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e :=
      by
    rw [bmSTS_component_eq n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe]
    exact Subgroup.commutator_le_self _
  have hgen : ∀ c : GaloisField 2 f, ∃ t : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      t ∈ altSiegelGroup (bmSTS_J n f) a₁ a₂ ∧
      (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        1 + c • (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) ∧
      (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) = 1 - e := by
    intro c
    have hB : Matrix.mulVec (bmSTS_J n f) a₂ ⬝ᵥ a₁ = 0 := by
      rw [bmSTS_dotProduct_mulVec_comm, bmSTS_form_symm]; exact hiso
    have h₂ : Matrix.mulVec (bmSTS_J n f) a₁ ⬝ᵥ a₂ = 0 := by
      rw [bmSTS_dotProduct_mulVec_comm]; exact hiso
    obtain ⟨g₁, hg₁⟩ := bmSTS_transvectionGL a₁ (Matrix.mulVec (bmSTS_J n f) a₂) hB c
    obtain ⟨g₂, hg₂⟩ := bmSTS_transvectionGL a₂ (Matrix.mulVec (bmSTS_J n f) a₁) h₂ c
    have hcross : Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) *
        Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁) = 0 := by
      rw [Matrix.vecMulVec_mul]
      have hz : Matrix.vecMul (Matrix.mulVec (bmSTS_J n f) a₂)
          (Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) = 0 := by
        have h1 : Matrix.vecMul (Matrix.mulVec (bmSTS_J n f) a₂)
            (Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) =
            (a₂ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂) • Matrix.mulVec (bmSTS_J n f) a₁ := by
          have h := Matrix.vecMul_transpose
            (A := (Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁))ᵀ)
            (Matrix.mulVec (bmSTS_J n f) a₂)
          rw [Matrix.transpose_transpose, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mulVec,
            op_smul_eq_smul] at h
          exact h
        rw [h1, bmSTS_B_self, zero_smul]
      rw [hz, Matrix.vecMulVec_zero]
    have hmat : (g₁ * g₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        1 + c • (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) := by
      rw [hg₁, hg₂]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_smul, hcross, smul_zero, add_zero, zero_add, smul_add]
      abel
    refine ⟨g₁ * g₂, Subgroup.subset_closure ⟨c, hmat⟩, hmat, ?_⟩
    have htJ : g₁ * g₂ ∈ J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype :=
      hle (Subgroup.subset_closure ⟨c, hmat⟩)
    obtain ⟨x, hxJ, hx⟩ := Subgroup.mem_map.mp htJ
    have hxblock : x ∈ glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S e :=
      hJ'block hxJ
    have hmat' : ((x : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n)
        (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) = 1 - e :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hxblock)).2
    rw [← hx]
    exact hmat'
  have hg1 : ∃ t : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      t ∈ altSiegelGroup (bmSTS_J n f) a₁ a₂ ∧
      (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        1 + (1 : GaloisField 2 f) • (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) ∧
      (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - e) = 1 - e :=
    hgen 1
  obtain ⟨t, _htS, htmat, htfix⟩ := hg1
  have htmat' : (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) := by
    rw [htmat, one_smul]
  have hMy : ∀ y : (Fin n ⊕ Fin n) → GaloisField 2 f,
      y ∈ LinearMap.ker (Matrix.mulVecLin e) →
      Matrix.mulVec (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) y = 0 := by
    intro y hy
    have hyker : Matrix.mulVec e y = 0 := by
      simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hy
    have hy' : Matrix.mulVec (1 - e) y = y := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hyker, sub_zero]
    have hty : Matrix.mulVec (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) y = y :=
        by
      calc Matrix.mulVec (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) y
          = Matrix.mulVec (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
              (Matrix.mulVec (1 - e) y) :=
              congrArg (fun z => Matrix.mulVec (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) z) hy'.symm
        _ = Matrix.mulVec ((t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
              (1 - e)) y := by rw [Matrix.mulVec_mulVec]
        _ = Matrix.mulVec (1 - e) y := by rw [htfix]
        _ = y := hy'
    rw [htmat', Matrix.add_mulVec, Matrix.one_mulVec] at hty
    exact add_left_cancel (a := y) (by simpa using hty)
  have horth : ∀ y : (Fin n ⊕ Fin n) → GaloisField 2 f,
      y ∈ LinearMap.ker (Matrix.mulVecLin e) →
      y ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₁ = 0 ∧
        y ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 := by
    intro y hy
    have hM := hMy y hy
    have hvec : (Matrix.mulVec (bmSTS_J n f) a₂ ⬝ᵥ y) • a₁ +
        (Matrix.mulVec (bmSTS_J n f) a₁ ⬝ᵥ y) • a₂ = 0 := by
      simpa only [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul] using hM
    have hpair := (LinearIndependent.pair_iff.mp hind)
      (Matrix.mulVec (bmSTS_J n f) a₂ ⬝ᵥ y) (Matrix.mulVec (bmSTS_J n f) a₁ ⬝ᵥ y) hvec
    refine ⟨?_, ?_⟩
    · rw [show y ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₁ =
          Matrix.mulVec (bmSTS_J n f) a₁ ⬝ᵥ y from
        (bmSTS_form_symm n f y a₁).trans (bmSTS_dotProduct_mulVec_comm n f a₁ y).symm]
      exact hpair.2
    · rw [show y ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ =
          Matrix.mulVec (bmSTS_J n f) a₂ ⬝ᵥ y from
        (bmSTS_form_symm n f y a₂).trans (bmSTS_dotProduct_mulVec_comm n f a₂ y).symm]
      exact hpair.1
  have hJunit : IsUnit (bmSTS_J n f) :=
    (Matrix.isUnit_iff_isUnit_det (bmSTS_J n f)).mpr (bmSTS_J_det n f)
  have key : ∀ a : (Fin n ⊕ Fin n) → GaloisField 2 f,
      (∀ y ∈ LinearMap.ker (Matrix.mulVecLin e),
        y ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a = 0) →
      a ∈ LinearMap.range (Matrix.mulVecLin e) := by
    intro a ha
    have hM : Matrix.mulVec (1 - e) a ∈ LinearMap.ker (Matrix.mulVecLin e) := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
        IsIdempotentElem.mul_one_sub_self he.2.1, Matrix.zero_mulVec]
    have hvorth : ∀ w, Matrix.mulVec (1 - e) a ⬝ᵥ Matrix.mulVec (bmSTS_J n f) w = 0 := by
      intro w
      have h1 : Matrix.mulVec e w ∈ LinearMap.range (Matrix.mulVecLin e) := ⟨w, rfl⟩
      have h1' : Matrix.mulVec e a ∈ LinearMap.range (Matrix.mulVecLin e) := ⟨a, rfl⟩
      have h2 : Matrix.mulVec (1 - e) w ∈ LinearMap.ker (Matrix.mulVecLin e) := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
          IsIdempotentElem.mul_one_sub_self he.2.1, Matrix.zero_mulVec]
      have hdec : w = Matrix.mulVec e w + Matrix.mulVec (1 - e) w := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
      rw [hdec, Matrix.mulVec_add, dotProduct_add]
      have t1 : Matrix.mulVec (1 - e) a ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (Matrix.mulVec e w) = 0 := by
        rw [bmSTS_form_symm]
        simpa only [Matrix.toBilin'_apply'] using bmSTS_blockExtend_orthogonal n f S hSU hS hodd he
          hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
          (Matrix.mulVec e w) h1 (Matrix.mulVec (1 - e) a) hM
      have t2 : Matrix.mulVec (1 - e) a ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (Matrix.mulVec (1 - e) w) = 0
          := by
        rw [show Matrix.mulVec (1 - e) a = a - Matrix.mulVec e a by
              rw [Matrix.sub_mulVec, Matrix.one_mulVec],
            sub_dotProduct,
            show a ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (Matrix.mulVec (1 - e) w) = 0 by
              rw [bmSTS_form_symm]; exact ha (Matrix.mulVec (1 - e) w) h2,
            show Matrix.mulVec e a ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (Matrix.mulVec (1 - e) w) = 0 by
              simpa only [Matrix.toBilin'_apply'] using bmSTS_blockExtend_orthogonal n f S hSU hS
                  hodd
                he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank
                htrace (Matrix.mulVec e a) h1' (Matrix.mulVec (1 - e) w) h2,
            sub_zero]
      rw [t1, t2, add_zero]
    have hvzero := bmSTS_eq_zero_of_forall_dotProduct_mulVec_eq_zero' hJunit hvorth
    have hdecomp : a = Matrix.mulVec e a + Matrix.mulVec (1 - e) a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hdecomp, hvzero, add_zero]
    exact ⟨a, by rw [Matrix.mulVecLin_apply]⟩
  exact ⟨key a₁ (fun y hy => (horth y hy).1), key a₂ (fun y hy => (horth y hy).2)⟩

private theorem bmSTS_trace_exists_ne_zero (f : ℕ) (K : Type) [Field K]
    [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2) (τ : K ≃+* K)
    (hτne : τ ≠ RingHom.id K) : ∃ c : K, Algebra.trace (GaloisField 2 f) K c ≠ 0 := by
  obtain ⟨c, hc⟩ := Algebra.trace_surjective (GaloisField 2 f) K 1
  exact ⟨c, by rw [hc]; exact one_ne_zero⟩

private theorem bmSTS_independent_of_not_Kcolinear
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W]
    (z₁ z₂ : W) (hz₁ : z₁ ≠ 0) (hcol : ∀ c : K, z₂ ≠ c • z₁) :
    LinearIndependent F ![z₁, z₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hz₁, rfl⟩
  · exfalso
    have hz : z₂ = (-(t⁻¹ * s)) • z₁ := by
      have h : (t⁻¹ * s) • z₁ + z₂ = 0 := by
        have h1 := congrArg (fun w => t⁻¹ • w) hst
        simpa [smul_add, smul_smul, inv_mul_cancel₀ ht] using h1
      exact (eq_neg_of_add_eq_zero_right h).trans (neg_smul _ _).symm
    exact hcol (algebraMap F K (-(t⁻¹ * s)))
      (hz.trans (IsScalarTower.algebraMap_smul K (-(t⁻¹ * s)) z₁).symm)

private theorem bmSTS_smul_base_smul {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W]
    (c : K) (a : F) (z : W) : c • (a • z) = (c * algebraMap F K a) • z := by
  rw [← IsScalarTower.algebraMap_smul K a z, smul_smul]

private theorem bmSTS_herm_add_left {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    (W : Type) [AddCommGroup W] [Module K W]
    (h : W → W →ₗ[K] K) (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hsymm : ∀ x y : W, h y x = τ (h x y)) (x y z : W) :
    h (x + y) z = h x z + h y z := by
  calc h (x + y) z = τ (h z (x + y)) := hsymm z (x + y)
    _ = τ (h z x + h z y) := by rw [map_add]
    _ = τ (h z x) + τ (h z y) := by rw [map_add]
    _ = h x z + h y z := by rw [hsymm x z, hτ2, hsymm y z, hτ2]

private theorem bmSTS_herm_smul_left {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    (W : Type) [AddCommGroup W] [Module K W]
    (h : W → W →ₗ[K] K) (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hsymm : ∀ x y : W, h y x = τ (h x y)) (c : K) (w z : W) :
    h (c • w) z = τ c * h w z := by
  calc h (c • w) z = τ (h z (c • w)) := hsymm z (c • w)
    _ = τ (c * h z w) := by rw [map_smul, smul_eq_mul]
    _ = τ c * τ (h z w) := by rw [map_mul]
    _ = τ c * h w z := by rw [hsymm w z, hτ2]

private theorem bmSTS_exists_hdual {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W]
    (h : W → W →ₗ[K] K) (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (z₁ z₂ : W) (hcol : ∀ c : K, z₂ ≠ c • z₁) :
    ∃ w : W, h w z₁ = 0 ∧ h w z₂ = 1 := by
  by_cases hg : ∃ w : W, h w z₁ = 0 ∧ h w z₂ ≠ 0
  · obtain ⟨w₀, hw₀₁, hw₀₂⟩ := hg
    refine ⟨τ.symm ((h w₀ z₂)⁻¹) • w₀, ?_, ?_⟩
    · rw [bmSTS_herm_smul_left (F := F) (K := K) W h τ hτ2 hsymm, hw₀₁, mul_zero]
    · rw [bmSTS_herm_smul_left (F := F) (K := K) W h τ hτ2 hsymm,
        RingEquiv.apply_symm_apply τ ((h w₀ z₂)⁻¹), inv_mul_cancel₀ hw₀₂]
  · push_neg at hg
    exfalso
    by_cases hf : ∃ y : W, h y z₁ ≠ 0
    · obtain ⟨y₁, hy₁⟩ := hf
      have hkey : ∀ x : W, h x z₂ = (h y₁ z₂ * (h y₁ z₁)⁻¹) * h x z₁ := by
        intro x
        have hker : h (x + (-(τ.symm (h x z₁ * (h y₁ z₁)⁻¹))) • y₁) z₁ = 0 := by
          rw [bmSTS_herm_add_left (F := F) (K := K) W h τ hτ2 hsymm,
            bmSTS_herm_smul_left (F := F) (K := K) W h τ hτ2 hsymm, map_neg,
            RingEquiv.apply_symm_apply τ]
          rw [neg_mul, mul_assoc, inv_mul_cancel₀ hy₁, mul_one, add_neg_cancel]
        have h2 := hg _ hker
        rw [bmSTS_herm_add_left (F := F) (K := K) W h τ hτ2 hsymm,
          bmSTS_herm_smul_left (F := F) (K := K) W h τ hτ2 hsymm, map_neg,
          RingEquiv.apply_symm_apply τ, neg_mul] at h2
        rw [add_neg_eq_zero] at h2
        rw [h2]
        ring
      have hzero : z₂ - (h y₁ z₂ * (h y₁ z₁)⁻¹) • z₁ = 0 := by
        apply hnd
        intro y
        rw [hsymm y (z₂ - (h y₁ z₂ * (h y₁ z₁)⁻¹) • z₁), map_sub, map_smul, smul_eq_mul,
          hkey y, sub_self, map_zero]
      exact hcol _ (sub_eq_zero.mp hzero)
    · push_neg at hf
      exact hcol 0 (by simpa using hnd z₂ (fun y => by rw [hsymm y z₂, hg y (hf y), map_zero]))

private theorem bmSTS_Klinear_transvection_relation
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] [Finite K]
    (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W]
    (h : W → W →ₗ[K] K) (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (z₁ z₂ : W) (hfind : LinearIndependent F ![z₁, z₂])
    (T : W →ₗ[F] W)
    (hform : ∀ w : W, T w = w + Algebra.trace F K (h w z₂) • z₁ +
      Algebra.trace F K (h w z₁) • z₂)
    (hKlin : ∀ (c : K) (w : W), T (c • w) = c • T w) (hz₁ : z₁ ≠ 0) :
    ∀ (c : K) (w : W),
      (algebraMap F K (Algebra.trace F K (h (c • w) z₂)) -
          c * algebraMap F K (Algebra.trace F K (h w z₂))) • z₁ +
        (algebraMap F K (Algebra.trace F K (h (c • w) z₁)) -
          c * algebraMap F K (Algebra.trace F K (h w z₁))) • z₂ = 0 := by
  intro c w
  have h1 := hKlin c w
  rw [hform (c • w), hform w] at h1
  simp only [smul_add] at h1
  rw [bmSTS_smul_base_smul, bmSTS_smul_base_smul] at h1
  rw [← IsScalarTower.algebraMap_smul K (Algebra.trace F K (h (c • w) z₂)) z₁,
    ← IsScalarTower.algebraMap_smul K (Algebra.trace F K (h (c • w) z₁)) z₂] at h1
  rw [add_assoc, add_assoc] at h1
  have h2 := add_left_cancel h1
  rw [sub_smul, sub_smul]
  rw [show (algebraMap F K (Algebra.trace F K (h (c • w) z₂)) • z₁ -
        (c * algebraMap F K (Algebra.trace F K (h w z₂))) • z₁) +
        (algebraMap F K (Algebra.trace F K (h (c • w) z₁)) • z₂ -
        (c * algebraMap F K (Algebra.trace F K (h w z₁))) • z₂) =
      (algebraMap F K (Algebra.trace F K (h (c • w) z₂)) • z₁ +
        algebraMap F K (Algebra.trace F K (h (c • w) z₁)) • z₂) -
      ((c * algebraMap F K (Algebra.trace F K (h w z₂))) • z₁ +
        (c * algebraMap F K (Algebra.trace F K (h w z₁))) • z₂) from by abel]
  rw [sub_eq_zero]
  exact h2

private theorem bmSTS_colinear_of_dual_transvection_Klinear
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] [Finite K]
    (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hTr1 : Algebra.trace F K 1 = 0) (hTr : ∃ c : K, Algebra.trace F K c ≠ 0)
    (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W]
    (h : W → W →ₗ[K] K) (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (z₁ z₂ : W) (T : W →ₗ[F] W)
    (hform : ∀ w : W, T w = w + Algebra.trace F K (h w z₂) • z₁ +
      Algebra.trace F K (h w z₁) • z₂)
    (hKlin : ∀ (c : K) (w : W), T (c • w) = c • T w) :
    z₁ ≠ 0 → ∃ c : K, z₂ = c • z₁ := by
  intro hz₁
  by_contra hcon
  push_neg at hcon
  have hfind := bmSTS_independent_of_not_Kcolinear (F := F) (K := K) W z₁ z₂ hz₁ hcon
  have hrel := bmSTS_Klinear_transvection_relation (F := F) (K := K) τ hτ2 W h hsymm hnd z₁ z₂
    hfind T hform hKlin hz₁
  obtain ⟨w₁, hw₁, hw₂⟩ := bmSTS_exists_hdual (F := F) (K := K) W h τ hτ2 hsymm hnd z₁ z₂ hcon
  obtain ⟨c₀, hc₀⟩ := hTr
  have hh := hrel (τ c₀) w₁
  rw [bmSTS_herm_smul_left (F := F) (K := K) W h τ hτ2 hsymm (τ c₀) w₁ z₂,
    bmSTS_herm_smul_left (F := F) (K := K) W h τ hτ2 hsymm (τ c₀) w₁ z₁, hw₁, hw₂, hτ2 c₀] at hh
  simp only [hTr1, map_zero, mul_zero, sub_zero, zero_smul, zero_add, add_zero, mul_one] at hh
  have hz : algebraMap F K (Algebra.trace F K c₀) = 0 :=
    (smul_eq_zero.mp hh).resolve_right hz₁
  exact hc₀ (by
    have := congrArg (fun x : K => x) hz
    rwa [map_eq_zero] at this)

private theorem bmSTS_generator_altSiegel_mem
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      ∃ t : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
        t ∈ altSiegelGroup (bmSTS_J n f) a₁ a₂ ∧
        (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
          1 + (1 : GaloisField 2 f) • (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) +
              Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) := by
  intro a₁ a₂ ha₁ ha₂ hind hiso
  have hB : Matrix.mulVec (bmSTS_J n f) a₂ ⬝ᵥ a₁ = 0 := by
    rw [bmSTS_dotProduct_mulVec_comm, bmSTS_form_symm]; exact hiso
  have h₂ : Matrix.mulVec (bmSTS_J n f) a₁ ⬝ᵥ a₂ = 0 := by
    rw [bmSTS_dotProduct_mulVec_comm]; exact hiso
  obtain ⟨g₁, hg₁⟩ := bmSTS_transvectionGL a₁ (Matrix.mulVec (bmSTS_J n f) a₂) hB (1 : GaloisField 2
      f)
  obtain ⟨g₂, hg₂⟩ := bmSTS_transvectionGL a₂ (Matrix.mulVec (bmSTS_J n f) a₁) h₂ (1 : GaloisField 2
      f)
  have hcross : Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) *
      Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁) = 0 := by
    rw [Matrix.vecMulVec_mul]
    have hz : Matrix.vecMul (Matrix.mulVec (bmSTS_J n f) a₂)
        (Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) = 0 := by
      have h1 : Matrix.vecMul (Matrix.mulVec (bmSTS_J n f) a₂)
          (Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) =
          (a₂ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂) • Matrix.mulVec (bmSTS_J n f) a₁ := by
        have h := Matrix.vecMul_transpose
          (A := (Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁))ᵀ)
          (Matrix.mulVec (bmSTS_J n f) a₂)
        rw [Matrix.transpose_transpose, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mulVec,
          op_smul_eq_smul] at h
        exact h
      rw [h1, bmSTS_B_self, zero_smul]
    rw [hz, Matrix.vecMulVec_zero]
  have hmat : ((g₁ * g₂ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) (GaloisField 2 f)) = 1 + (1 : GaloisField 2 f) •
      (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) := by
    rw [Units.val_mul, hg₁, hg₂]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, hcross, smul_zero, add_zero, zero_add, smul_add]
    abel
  exact ⟨g₁ * g₂, Subgroup.subset_closure ⟨1, hmat⟩, hmat⟩

private theorem bmSTS_generator_hom_range
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∀ t : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
        t ∈ altSiegelGroup (bmSTS_J n f) a₁ a₂ →
        ∃ g : (ggU .PSU m' (max f 1)).K,
          (bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
              eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : Matrix (Fin n ⊕ Fin n)
                  (Fin n ⊕ Fin n) (GaloisField 2 f)) = (t : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                      (GaloisField 2 f)) := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle t hts
  obtain ⟨x, hxJ, hx⟩ := Subgroup.mem_map.mp (hle hts)
  obtain ⟨g, hg⟩ := hrange.symm ▸ hxJ
  refine ⟨g, ?_⟩
  exact (congrArg (fun y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) =>
      ((y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f))) hg).trans
    (congrArg (fun y : GL (Fin n ⊕ Fin n) (GaloisField 2 f) => (y : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) (GaloisField 2 f))) hx)

private theorem bmSTS_generator_blockAction
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ g : (ggU .PSU m' (max f 1)).K,
      ∃ T : W →ₗ[GaloisField 2 f] W,
        (∀ w : W, eW (T w) = (bmSTS_blockEmbeddingEV_PSU_blockExtend n f S hSU hS hodd he hadj hdeg₁
            hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : Matrix
                (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ eW w) ∧
        (∀ (c : K) (w : W), T (c • w) = c • T w) := by
  intro g
  refine ⟨((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W ≃ₗ[GaloisField 2 f] W) :
    W →ₗ[GaloisField 2 f] W), ?_, ?_⟩
  · intro w
    exact ((bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).1 w).symm
  · exact bmSTS_blockAction_smul n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj
      hτ2 hτne hsymm hnd hrank hm' hKrank htrace g

private theorem bmSTS_altSiegel_generator_KLinear
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∃ T : W →ₗ[GaloisField 2 f] W,
        (∀ w : W, eW (T w) = (1 + (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) +
            Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁))) *ᵥ eW w) ∧
        (∀ (c : K) (w : W), T (c • w) = c • T w) := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle
  obtain ⟨t, hts, htmat⟩ := bmSTS_generator_altSiegel_mem n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
      K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace a₁ a₂ ha₁ ha₂ hind hiso
  obtain ⟨g, hg⟩ := bmSTS_generator_hom_range n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange a₁ a₂ ha₁ ha₂ hind hiso hle t
          hts
  obtain ⟨T, hTact, hTK⟩ := bmSTS_generator_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K
      τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g
  refine ⟨T, ?_, hTK⟩
  intro w
  rw [hTact w, hg, htmat, one_smul]

private theorem bmSTS_altSiegel_generator_action_form
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, ∀ (z₁ z₂ : W) (T : W →ₗ[GaloisField 2 f] W),
      eW z₁ = a₁ → eW z₂ = a₂ →
      (∀ w : W, eW (T w) = (1 + (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁))) *ᵥ eW w) →
      ∀ w : W, T w = w + (Algebra.trace (GaloisField 2 f) K (h w z₂)) • z₁ +
          (Algebra.trace (GaloisField 2 f) K (h w z₁)) • z₂ := by
  intro a₁ a₂ z₁ z₂ T hz₁ hz₂ hT w
  apply heWinj
  rw [hT w]
  have h2 : Matrix.mulVec (bmSTS_J n f) a₂ ⬝ᵥ eW w =
      Algebra.trace (GaloisField 2 f) K (h w z₂) := by
    have h := htrace w z₂ 1
    rw [one_smul, hz₂, one_mul] at h
    exact (dotProduct_comm _ _).trans h
  have h1 : Matrix.mulVec (bmSTS_J n f) a₁ ⬝ᵥ eW w =
      Algebra.trace (GaloisField 2 f) K (h w z₁) := by
    have h := htrace w z₁ 1
    rw [one_smul, hz₁, one_mul] at h
    exact (dotProduct_comm _ _).trans h
  rw [Matrix.add_mulVec, Matrix.one_mulVec, map_add, map_add, map_smul, map_smul, hz₁, hz₂,
    Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    op_smul_eq_smul, h2, h1]
  abel

private theorem bmSTS_altSiegel_plane_colinear
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      a₁ ∈ LinearMap.range (Matrix.mulVecLin e) →
      a₂ ∈ LinearMap.range (Matrix.mulVecLin e) →
      ∃ (z : W) (c : K), z ≠ 0 ∧ a₁ = eW z ∧ a₂ = eW (c • z) := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle hm₁ hm₂
  obtain ⟨z₁, hz₁⟩ := LinearMap.mem_range.mp (heW.symm ▸ hm₁)
  obtain ⟨z₂, hz₂⟩ := LinearMap.mem_range.mp (heW.symm ▸ hm₂)
  obtain ⟨T, hTact, hTK⟩ := bmSTS_altSiegel_generator_KLinear n f S hSU hS hodd he hadj hdeg₁ hdeg₂
      hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange a₁ a₂ ha₁ ha₂
          hind hiso hle
  have hform := bmSTS_altSiegel_generator_action_form n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace a₁ a₂ z₁ z₂ T hz₁ hz₂ hTact
  obtain ⟨c, hc⟩ := bmSTS_colinear_of_dual_transvection_Klinear (F := GaloisField 2 f) (K := K)
    τ hτ2 (by simpa using bmSTS_trace_base_zero f K hKrank (1 : GaloisField 2 f))
    (bmSTS_trace_exists_ne_zero f K hKrank τ hτne) W h hsymm hnd z₁ z₂ T hform hTK
    (fun h0 => ha₁ (by rw [← hz₁, h0, map_zero]))
  exact ⟨z₁, c, (fun h0 => ha₁ (by rw [← hz₁, h0, map_zero])), hz₁.symm, by rw [← hz₂, hc]⟩

private theorem bmSTS_trace_eq_add
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] [Finite K]
    (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hτfix : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a)
    (hτne : τ ≠ RingHom.id K) (hKrank : Module.finrank F K = 2) (x : K) :
    algebraMap F K (Algebra.trace F K x) = x + τ x := by
  haveI : Module.Free F K := inferInstance
  haveI : Algebra.IsQuadraticExtension F K := Algebra.IsQuadraticExtension.mk hKrank
  haveI : Algebra.IsSeparable F K := inferInstance
  let τa : K ≃ₐ[F] K := { τ with commutes' := fun a => hτfix a }
  have hτa : τa ≠ 1 := by
    intro h
    exact hτne (by ext z; exact congrFun (congrArg (fun e : K ≃ₐ[F] K => (e : K → K)) h) z)
  have h := Algebra.IsQuadraticExtension.algebraMap_trace_eq_add F K hτa x
  exact h

private theorem bmSTS_trace_add_semilinear
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hτfix : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a)
    (hτne : τ ≠ RingHom.id K)
    (hKrank : Module.finrank F K = 2) (c ρ : K) :
    algebraMap F K (Algebra.trace F K (c * ρ)) + c * algebraMap F K (Algebra.trace F K ρ) =
      algebraMap F K (Algebra.trace F K c) * τ ρ := by
  have h1 := bmSTS_trace_eq_add K τ hτ2 hτfix hτne hKrank (c * ρ)
  have h2 := bmSTS_trace_eq_add K τ hτ2 hτfix hτne hKrank ρ
  have h3 := bmSTS_trace_eq_add K τ hτ2 hτfix hτne hKrank c
  rw [h1, h2, h3, map_mul]
  have h2z : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (c * ρ) * h2z

private theorem bmSTS_herm_add_smul_sq
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    {W : Type} [AddCommGroup W] [Module K W]
    (h : W → W →ₗ[K] K) (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hsymm : ∀ x y : W, h y x = τ (h x y)) (w z : W) (s : K) :
    h (w + s • z) (w + s • z) =
      h w w + s * h w z + τ s * h z w + τ s * s * h z z := by
  have h1 : h (w + s • z) (w + s • z) =
      h w (w + s • z) + h (s • z) (w + s • z) :=
    bmSTS_herm_add_left (F := F) K W h τ hτ2 hsymm w (s • z) (w + s • z)
  have h2 : h (s • z) (w + s • z) = τ s * h z (w + s • z) :=
    bmSTS_herm_smul_left (F := F) K W h τ hτ2 hsymm s z (w + s • z)
  have h3 : h w (w + s • z) = h w w + s * h w z := by
    rw [map_add (h w), map_smul (h w) s z]
    rfl
  have h4 : h z (w + s • z) = h z w + s * h z z := by
    rw [map_add (h z), map_smul (h z) s z]
    rfl
  rw [h1, h2, h3, h4]
  ring

private theorem bmSTS_trace_action_nontrivial
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] [Finite K]
    {W : Type} [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W]
    (τ : K ≃+* K) (h : W → W →ₗ[K] K) (z : W) (c : K) (T : W →ₗ[F] W)
    (hT : ∀ w : W, T w = w + Algebra.trace F K c • (τ (h w z) • z))
    (hz : z ≠ 0) (hTne : ∃ w : W, T w ≠ w) :
    Algebra.trace F K c ≠ 0 ∧ ∃ w : W, h w z ≠ 0 := by
  obtain ⟨w₀, hw₀⟩ := hTne
  have hne : Algebra.trace F K c • (τ (h w₀ z) • z) ≠ 0 := by
    intro h0
    exact hw₀ (by rw [hT w₀, h0, add_zero])
  have hne' : ¬ (Algebra.trace F K c = 0 ∨ τ (h w₀ z) • z = 0) :=
    fun hh => hne (smul_eq_zero.mpr hh)
  rw [not_or] at hne'
  exact ⟨hne'.1, w₀, fun hρ => hne'.2 (by rw [hρ, map_zero, zero_smul])⟩

private theorem bmSTS_trace_action_arith
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] [CharP K 2]
    (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c) {a ρ lam : K}
    (ha : a ≠ 0)
    (hρ : ρ ≠ 0) (hafix : τ a = a)
    (h : (a * τ ρ) * ρ + τ (a * τ ρ) * τ ρ + τ (a * τ ρ) * (a * τ ρ) * lam = 0) : lam = 0 := by
  rw [map_mul, hτ2, hafix] at h
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hτρ : τ ρ ≠ 0 := fun hh => hρ (τ.injective (by rw [hh, map_zero]))
  have hc : a * ρ * τ ρ ≠ 0 := mul_ne_zero (mul_ne_zero ha hρ) hτρ
  have hpair : (a * τ ρ) * ρ + (a * ρ) * τ ρ = 0 := by
    have hh : (a * τ ρ) * ρ + (a * ρ) * τ ρ = (2 : K) * (a * ρ * τ ρ) := by ring
    rw [hh, h2, zero_mul]
  have hfac : a * ρ * τ ρ * (a * lam) = 0 := by
    rw [hpair, zero_add] at h
    rw [← h]
    ring
  have hlam : a * lam = 0 := (mul_eq_zero.mp hfac).resolve_left hc
  exact (mul_eq_zero.mp hlam).resolve_left ha

private theorem bmSTS_isotropic_of_trace_action
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hτfix : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a)
    {W : Type} [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W]
    (h : W → W →ₗ[K] K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (z : W) (c : K) (T : W →ₗ[F] W)
    (hT : ∀ w : W, T w = w + Algebra.trace F K c • (τ (h w z) • z))
    (hiso : ∀ w w' : W, h (T w) (T w') = h w w')
    (hTne : ∃ w : W, T w ≠ w) (hz : z ≠ 0) :
    h z z = 0 := by
  obtain ⟨hA, w₀, hρ⟩ := bmSTS_trace_action_nontrivial (F := F) K τ h z c T hT hz hTne
  set A : K := algebraMap F K (Algebra.trace F K c) with hA_def
  have hAne : A ≠ 0 := by
    intro hh
    exact hA ((FaithfulSMul.algebraMap_injective F K) (by rw [hA_def] at hh; rw [hh, map_zero]))
  have hτρ : τ (h w₀ z) ≠ 0 := fun hh => hρ (τ.injective (by rw [hh, map_zero]))
  have hTw : T w₀ = w₀ + (A * τ (h w₀ z)) • z := by
    rw [hT w₀]
    show w₀ + Algebra.trace F K c • (τ (h w₀ z) • z) = w₀ + (A * τ (h w₀ z)) • z
    rw [← IsScalarTower.algebraMap_smul K (Algebra.trace F K c), ← smul_assoc]
    rfl
  have hE := hiso w₀ w₀
  rw [hTw, bmSTS_herm_add_smul_sq (F := F) K h τ hτ2 hsymm w₀ z (A * τ (h w₀ z)),
    hsymm w₀ z] at hE
  have hzero : (A * τ (h w₀ z)) * h w₀ z + τ (A * τ (h w₀ z)) * τ (h w₀ z) +
      τ (A * τ (h w₀ z)) * (A * τ (h w₀ z)) * h z z = 0 := by
    have h1 : h w₀ w₀ + ((A * τ (h w₀ z)) * h w₀ z + τ (A * τ (h w₀ z)) * τ (h w₀ z) +
        τ (A * τ (h w₀ z)) * (A * τ (h w₀ z)) * h z z) = h w₀ w₀ + 0 := by
      rw [add_zero]
      calc h w₀ w₀ + ((A * τ (h w₀ z)) * h w₀ z + τ (A * τ (h w₀ z)) * τ (h w₀ z) +
            τ (A * τ (h w₀ z)) * (A * τ (h w₀ z)) * h z z)
          = (((h w₀ w₀ + (A * τ (h w₀ z)) * h w₀ z) + τ (A * τ (h w₀ z)) * τ (h w₀ z)) +
            τ (A * τ (h w₀ z)) * (A * τ (h w₀ z)) * h z z) := by abel
        _ = h w₀ w₀ := hE
    exact add_left_cancel h1
  exact bmSTS_trace_action_arith (F := F) K τ hτ2 (ρ := h w₀ z) (lam := h z z) hAne hρ (hτfix _)
      hzero

private theorem bmSTS_altSiegel_generator_g_exists
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∃ g : (ggU .PSU m' (max f 1)).K,
        ∀ w : W, eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂
            hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W
                ≃ₗ[GaloisField 2 f] W) w) = (1 + (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f)
                    a₂) + Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁))) *ᵥ eW w := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle
  obtain ⟨t, hts, htmat⟩ := bmSTS_generator_altSiegel_mem n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
      K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace a₁ a₂ ha₁ ha₂ hind hiso
  obtain ⟨g, hg⟩ := bmSTS_generator_hom_range n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange a₁ a₂ ha₁ ha₂ hind hiso hle t
          hts
  exact ⟨g, fun w => by
    rw [← (bmSTS_blockExtend_apply n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g).1 w, hg, htmat, one_smul]⟩

private theorem bmSTS_trace_smul_cancel
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hτfix : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a)
    (hτne : τ ≠ RingHom.id K) (hKrank : Module.finrank F K = 2)
    {W : Type} [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W]
    (z : W) (c ρ : K) :
    (Algebra.trace F K (c * ρ)) • z + (Algebra.trace F K ρ) • (c • z) =
      (Algebra.trace F K c) • (τ ρ • z) := by
  have h2 : (Algebra.trace F K ρ) • (c • z) = (c * algebraMap F K (Algebra.trace F K ρ)) • z := by
    rw [show (Algebra.trace F K ρ) • (c • z) = algebraMap F K (Algebra.trace F K ρ) • (c • z)
        from (IsScalarTower.algebraMap_smul K (Algebra.trace F K ρ) (c • z)).symm, ← mul_smul]
    exact congrArg (fun t => t • z) (mul_comm _ _)
  rw [h2, ← IsScalarTower.algebraMap_smul K (Algebra.trace F K (c * ρ)), ← add_smul,
    bmSTS_trace_add_semilinear K τ hτ2 hτfix hτne hKrank c ρ,
    mul_smul, ← IsScalarTower.algebraMap_smul K (Algebra.trace F K c)]

private theorem bmSTS_altSiegel_generator_g_reduced
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K] [CharP K 2]
    (τ : K ≃+* K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →

      ∀ (z : W) (c : K), z ≠ 0 → a₁ = eW z → a₂ = eW (c • z) →
            ∀ g : (ggU .PSU m' (max f 1)).K,
        (∀ w : W, eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂
            hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W
                ≃ₗ[GaloisField 2 f] W) w) = (1 + (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f)
                    a₂) + Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁))) *ᵥ eW w) →
        ∀ w : W, ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
            K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W ≃ₗ[GaloisField
                2 f] W) : W →ₗ[GaloisField 2 f] W) w =
          w + Algebra.trace (GaloisField 2 f) K c • (τ (h w z) • z) := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle z c hz0 hza₁ hza₂ g hTact w
  have hform := bmSTS_altSiegel_generator_action_form n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace a₁ a₂ z (c • z)
    ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W ≃ₗ[GaloisField 2 f] W) : W
            →ₗ[GaloisField 2 f] W) hza₁.symm hza₂.symm hTact
  have h1 : h w (c • z) = c * h w z := by rw [map_smul, smul_eq_mul]
  rw [hform w, h1, add_assoc,
    bmSTS_trace_smul_cancel (F := GaloisField 2 f) K τ hτ2 hτfix hτne hKrank z c (h w z)]

private theorem bmSTS_herm_surjective
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    {W : Type} [AddCommGroup W] [Module K W]
    (h : W → W →ₗ[K] K) (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0) (z : W) (hz : z ≠ 0) (κ : K) :
    ∃ w : W, h w z = κ := by
  have hne : ∃ w₁, h w₁ z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hz (hnd z (fun y => by rw [hsymm y z, hcon y, map_zero]))
  obtain ⟨w₁, hw₁⟩ := hne
  refine ⟨τ.symm (κ * (h w₁ z)⁻¹) • w₁, ?_⟩
  rw [bmSTS_herm_smul_left (F := F) K W h τ hτ2 hsymm _ w₁ z, RingEquiv.apply_symm_apply,
    mul_assoc, inv_mul_cancel₀ hw₁, mul_one]

private theorem bmSTS_herm_trace_exists_ne_zero
    {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] [Finite K] [Algebra.IsSeparable F K]
    {W : Type} [AddCommGroup W] [Module K W]
    (h : W → W →ₗ[K] K) (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hKrank : Module.finrank F K = 2) (hτne : τ ≠ RingHom.id K) (z : W) (hz : z ≠ 0) :
    ∃ w : W, Algebra.trace F K (h w z) ≠ 0 := by
  obtain ⟨c₀, hc₀⟩ := Algebra.trace_surjective F K 1
  obtain ⟨w, hw⟩ := bmSTS_herm_surjective (F := F) K h τ hτ2 hsymm hnd z hz c₀
  exact ⟨w, by rw [hw, hc₀]; exact one_ne_zero⟩

private theorem bmSTS_vv_add_mulVec
    {F : Type} [Field F] {ι : Type} [Fintype ι]
    (u v φ ψ x : ι → F) :
    Matrix.mulVec (Matrix.vecMulVec u φ + Matrix.vecMulVec v ψ) x =
      (φ ⬝ᵥ x) • u + (ψ ⬝ᵥ x) • v := by
  rw [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    op_smul_eq_smul]

private theorem bmSTS_blockAction_ne_of_matrix
    {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {W : Type} [AddCommGroup W] [Module F W]
    (eW : W →ₗ[F] (ι → F)) (heWinj : Function.Injective eW)
    (M : Matrix ι ι F) (T : W → W)
    (hT : ∀ w : W, eW (T w) = (1 + M) *ᵥ eW w) (w : W)
    (hM : M *ᵥ eW w ≠ 0) : T w ≠ w := by
  intro hfix
  have h1 := hT w
  rw [hfix, Matrix.add_mulVec, Matrix.one_mulVec] at h1
  have h1' : eW w + 0 = eW w + M *ᵥ eW w := by rw [add_zero]; exact h1
  exact hM (add_left_cancel h1').symm

private theorem bmSTS_vv_mulVec_trace
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, ∀ (z₁ z₂ : W) (w : W),
      a₁ = eW z₁ → a₂ = eW z₂ →
      Matrix.mulVec (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) + Matrix.vecMulVec a₂
          (Matrix.mulVec (bmSTS_J n f) a₁)) (eW w) = Algebra.trace (GaloisField 2 f) K (h w z₂) • a₁
              + Algebra.trace (GaloisField 2 f) K (h w z₁) • a₂ := by
  intro a₁ a₂ z₁ z₂ w hza₁ hza₂
  rw [bmSTS_vv_add_mulVec a₁ a₂ (Matrix.mulVec (bmSTS_J n f) a₂)
    (Matrix.mulVec (bmSTS_J n f) a₁) (eW w)]
  have h2 : Matrix.mulVec (bmSTS_J n f) a₂ ⬝ᵥ eW w = Algebra.trace (GaloisField 2 f) K (h w z₂) :=
      by
    rw [dotProduct_comm, hza₂]
    have hh := htrace w z₂ 1
    rw [one_smul, one_mul] at hh
    rw [hh]
  have h1 : Matrix.mulVec (bmSTS_J n f) a₁ ⬝ᵥ eW w = Algebra.trace (GaloisField 2 f) K (h w z₁) :=
      by
    rw [dotProduct_comm, hza₁]
    have hh := htrace w z₁ 1
    rw [one_smul, one_mul] at hh
    rw [hh]
  rw [h2, h1]

private theorem bmSTS_vv_mulVec_ne_zero
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∀ (z : W) (c : K), z ≠ 0 → a₁ = eW z → a₂ = eW (c • z) →
      ∃ w : W, Matrix.mulVec (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁)) (eW w) ≠ 0 := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle z c hz0 hza₁ hza₂
  obtain ⟨w₀, hw₀⟩ := bmSTS_herm_trace_exists_ne_zero (F := GaloisField 2 f) K h τ hτ2 hsymm hnd
    hKrank hτne z hz0
  refine ⟨w₀, fun h0 => ?_⟩
  rw [bmSTS_vv_mulVec_trace n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ hτfix W h eW m' heW heWinj
      hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange a₁ a₂ z (c • z) w₀ hza₁ hza₂] at h0
  exact hw₀ ((LinearIndependent.pair_iff.mp hind) _ _ h0).2

private theorem bmSTS_altSiegel_generator_g_ne_one
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →

      ∀ (z : W) (c : K), z ≠ 0 → a₁ = eW z → a₂ = eW (c • z) →
      ∀ g : (ggU .PSU m' (max f 1)).K,
        (∀ w : W, eW ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂
            hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W
                ≃ₗ[GaloisField 2 f] W) w) = (1 + (Matrix.vecMulVec a₁ (Matrix.mulVec (bmSTS_J n f)
                    a₂) + Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁))) *ᵥ eW w) →
        ∃ w : W, ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
            K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W ≃ₗ[GaloisField
                2 f] W) : W →ₗ[GaloisField 2 f] W) w ≠ w := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle z c hz0 hza₁ hza₂ g hTact
  obtain ⟨w₀, hw₀⟩ := bmSTS_vv_mulVec_ne_zero n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ hτfix W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange a₁ a₂ ha₁ ha₂ hind hiso
          hle z c hz0 hza₁ hza₂
  exact ⟨w₀, bmSTS_blockAction_ne_of_matrix (F := GaloisField 2 f) eW heWinj (Matrix.vecMulVec a₁
      (Matrix.mulVec (bmSTS_J n f) a₂) + Matrix.vecMulVec a₂ (Matrix.mulVec (bmSTS_J n f) a₁))
    ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W ≃ₗ[GaloisField 2 f] W) : W
            →ₗ[GaloisField 2 f] W) hTact w₀ hw₀⟩

private theorem bmSTS_altSiegel_generator_isometry
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ (g : (ggU .PSU m' (max f 1)).K) (w w' : W),
      h ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
          eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W ≃ₗ[GaloisField 2 f] W)
              w) ((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                  K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W
                      ≃ₗ[GaloisField 2 f] W) w') = h w w' := by
  intro g w w'
  exact bmSTS_blockAction_isometry n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
      heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g w w'

private theorem bmSTS_altSiegel_generator_reduced
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K] [CharP K 2]
    (τ : K ≃+* K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∀ (z : W) (c : K), z ≠ 0 → a₁ = eW z → a₂ = eW (c • z) →
      ∃ T : W →ₗ[GaloisField 2 f] W,
        (∀ w : W, T w = w + Algebra.trace (GaloisField 2 f) K c • (τ (h w z) • z)) ∧
        (∀ w w' : W, h (T w) (T w') = h w w') ∧
        (∃ w : W, T w ≠ w) := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle z c hz0 hza₁ hza₂
  obtain ⟨g, hg⟩ := bmSTS_altSiegel_generator_g_exists n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      hτfix W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange a₁ a₂ ha₁ ha₂
          hind hiso hle
  refine ⟨((bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace g : W ≃ₗ[GaloisField 2 f] W) : W
          →ₗ[GaloisField 2 f] W), ?_, ?_, ?_⟩
  · exact bmSTS_altSiegel_generator_g_reduced n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ hτfix W
      h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange a₁ a₂ ha₁ ha₂ hind hiso
          hle z c hz0 hza₁ hza₂ g hg
  · intro w w'
    exact bmSTS_altSiegel_generator_isometry n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange g w w'
  · exact bmSTS_altSiegel_generator_g_ne_one n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ hτfix W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange a₁ a₂ ha₁ ha₂ hind hiso hle
          z c hz0 hza₁ hza₂ g hg

private theorem bmSTS_altSiegel_plane_isotropic
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K] [CharP K 2]
    (τ : K ≃+* K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, ∀ (z : W) (c : K), z ≠ 0 →
      a₁ = eW z → a₂ = eW (c • z) → a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      h z z = 0 := by
  intro a₁ a₂ z c hz0 hza₁ hza₂ ha₁ ha₂ hind hiso hle
  obtain ⟨T, hTform, hiso', hne⟩ :=
    bmSTS_altSiegel_generator_reduced n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ hτfix W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange a₁ a₂ ha₁ ha₂ hind hiso hle z c
            hz0 hza₁ hza₂
  exact bmSTS_isotropic_of_trace_action (F := GaloisField 2 f) K τ hτ2 hτfix h hsymm z c T hTform
      hiso' hne hz0

private theorem bmSTS_altSiegel_plane_isKLine
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K] [CharP K 2]
    (τ : K ≃+* K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      a₁ ∈ LinearMap.range (Matrix.mulVecLin e) →
      a₂ ∈ LinearMap.range (Matrix.mulVecLin e) →
      ∃ (z : W) (c : K), z ≠ 0 ∧ h z z = 0 ∧ a₁ = eW z ∧ a₂ = eW (c • z) := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle hm₁ hm₂
  obtain ⟨z, c, hz0, hza₁, hza₂⟩ := bmSTS_altSiegel_plane_colinear n f S hSU hS hodd he hadj hdeg₁
      hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange
    a₁ a₂ ha₁ ha₂ hind hiso hle hm₁ hm₂
  exact ⟨z, c, hz0, bmSTS_altSiegel_plane_isotropic n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
      hτfix W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace hrange
    a₁ a₂ z c hz0 hza₁ hza₂ ha₁ ha₂ hind hiso hle, hza₁, hza₂⟩

private theorem bmSTS_altSiegelGroup_smul_right {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Matrix ι ι F) (u v : ι → F) {lam : F} (hlam : lam ≠ 0) :
    altSiegelGroup G u (lam • v) = altSiegelGroup G u v := by
  simpa using bmSTS_altSiegel_smul_smul G 1 lam one_ne_zero hlam u v

private theorem bmSTS_trace_eq_zero_mem_base {f : ℕ} (K : Type) [Field K]
    [Algebra (GaloisField 2 f) K] [Finite K]
    (hKrank : Module.finrank (GaloisField 2 f) K = 2) (τ : K ≃+* K)
    (hτne : τ ≠ RingHom.id K) {c : K}
    (hc : Algebra.trace (GaloisField 2 f) K c = 0) :
    c ∈ Set.range (algebraMap (GaloisField 2 f) K) := by
  have htop : LinearMap.range (Algebra.trace (GaloisField 2 f) K) = ⊤ := by
    obtain ⟨d, hd⟩ := bmSTS_trace_exists_ne_zero f K hKrank τ hτne
    refine (Submodule.eq_top_iff').mpr fun x => ?_
    have h1 : (1 : (GaloisField 2 f)) ∈ LinearMap.range (Algebra.trace (GaloisField 2 f) K) :=
      ⟨(Algebra.trace (GaloisField 2 f) K d)⁻¹ • d, by
        rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hd]⟩
    have hx := Submodule.smul_mem (LinearMap.range (Algebra.trace (GaloisField 2 f) K)) x h1
    simpa using hx
  have hfrT : Module.finrank (GaloisField 2 f) ↥(LinearMap.range (Algebra.trace (GaloisField 2 f)
      K)) = 1 := by
    rw [htop, LinearEquiv.finrank_eq (Submodule.topEquiv (R := (GaloisField 2 f)) (M := (GaloisField
        2 f))),
      Module.finrank_self]
  have hker : Module.finrank (GaloisField 2 f) ↥(LinearMap.ker (Algebra.trace (GaloisField 2 f) K))
      = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (Algebra.trace (GaloisField 2 f) K)
    rw [hfrT, hKrank] at h
    omega
  have hfr : Module.finrank (GaloisField 2 f) ↥(LinearMap.range (Algebra.linearMap (GaloisField 2 f)
      K)) = 1 := by
    rw [← LinearEquiv.finrank_eq (LinearEquiv.ofInjective (Algebra.linearMap (GaloisField 2 f) K)
      (FaithfulSMul.algebraMap_injective (GaloisField 2 f) K)), Module.finrank_self]
  have hle : LinearMap.range (Algebra.linearMap (GaloisField 2 f) K) ≤ LinearMap.ker (Algebra.trace
      (GaloisField 2 f) K) := by
    rintro x ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    change Algebra.trace (GaloisField 2 f) K (algebraMap (GaloisField 2 f) K a) = 0
    rw [Algebra.trace_algebraMap, hKrank, nsmul_eq_mul,
      CharP.cast_eq_zero (GaloisField 2 f) 2, zero_mul]
  have heq : LinearMap.range (Algebra.linearMap (GaloisField 2 f) K) = LinearMap.ker (Algebra.trace
      (GaloisField 2 f) K) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hker])
  have hc' : c ∈ LinearMap.ker (Algebra.trace (GaloisField 2 f) K) := LinearMap.mem_ker.mpr hc
  rw [← heq, LinearMap.mem_range] at hc'
  obtain ⟨a, ha⟩ := hc'
  exact ⟨a, ha⟩

private theorem bmSTS_altSiegel_omega_exists
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ (z : W) (c : K), z ≠ 0 → h z z = 0 →
      Algebra.trace (GaloisField 2 f) K c ≠ 0 →
      ∃ ω : K, Algebra.trace (GaloisField 2 f) K ω = 1 ∧
        altSiegelGroup (bmSTS_J n f) (eW z) (eW (c • z)) =
          altSiegelGroup (bmSTS_J n f) (eW z) (eW (ω • z)) := by
  intro z c hz0 hzz hctrace
  refine ⟨(Algebra.trace (GaloisField 2 f) K c)⁻¹ • c, ?_, ?_⟩
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hctrace]
  · have hb : eW (((Algebra.trace (GaloisField 2 f) K c)⁻¹ • c) • z) = (Algebra.trace (GaloisField 2
      f) K c)⁻¹ • eW (c • z) := by
      rw [smul_assoc, map_smul]
    rw [hb]
    exact (bmSTS_altSiegelGroup_smul_right (bmSTS_J n f) (eW z) (eW (c • z))
      (inv_ne_zero hctrace)).symm

private theorem bmSTS_altSiegel_eq_canonical
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, ∀ (z : W) (c : K), z ≠ 0 → h z z = 0 →
      a₁ = eW z → a₂ = eW (c • z) → a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      ∃ ω : K, Algebra.trace (GaloisField 2 f) K ω = 1 ∧
        altSiegelGroup (bmSTS_J n f) (eW z) (eW (ω • z)) =
          altSiegelGroup (bmSTS_J n f) a₁ a₂ := by
  intro a₁ a₂ z c hz0 hzz hza₁ hza₂ ha₁ ha₂ hind
  have hctrace : Algebra.trace (GaloisField 2 f) K c ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := bmSTS_trace_eq_zero_mem_base (f := f) K hKrank τ hτne h0
    have ha2 : a₂ = a • a₁ := by
      rw [hza₂, ← ha, IsScalarTower.algebraMap_smul K a z, map_smul, ← hza₁]
    have hrel : a • a₁ + (-1 : GaloisField 2 f) • a₂ = 0 := by
      rw [ha2, neg_smul, one_smul, add_neg_cancel]
    exact one_ne_zero (neg_eq_zero.mp (LinearIndependent.pair_iff.mp hind a (-1) hrel).2)
  obtain ⟨ω, hω, hcanon⟩ := bmSTS_altSiegel_omega_exists n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K
      τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace z c hz0 hzz hctrace
  exact ⟨ω, hω, by rw [hza₁, hza₂]; exact hcanon.symm⟩

private theorem bmSTS_isotropic_companion {f : ℕ} (K : Type) [Field K]
    [Algebra (GaloisField 2 f) K] [Finite K]
    {W : Type} [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K) (τ : K ≃+* K) (hτ2 : ∀ c : K, τ (τ c) = c)
    (hτne : τ ≠ RingHom.id K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (z : W) (hz : z ≠ 0) (hzz : h z z = 0) :
    ∃ w : W, h z w = 1 ∧ h w w = 0 := by
  obtain ⟨y, hyz⟩ :=
    bmSTS_herm_surjective (F := GaloisField 2 f) K h τ hτ2 hsymm hnd z hz (1 : K)
  have hzy : h z y = 1 := by rw [hsymm y z, hyz, map_one]
  obtain ⟨s, hs⟩ := Algebra.trace_surjective (GaloisField 2 f) K (-1)
  have ha : τ (h y y) = h y y := (hsymm y y).symm
  have htr : s + τ s = -1 := by
    have h1 := bmSTS_trace_eq_add (F := GaloisField 2 f) K τ hτ2 hτfix hτne hKrank s
    rw [hs] at h1
    rw [map_neg, map_one] at h1
    exact h1.symm
  have ht : ((h y y) * s) + τ ((h y y) * s) = -(h y y) := by
    rw [map_mul, ha, ← mul_add, htr]
    ring
  refine ⟨y + ((h y y) * s) • z, ?_, ?_⟩
  · rw [map_add, map_smul, smul_eq_mul, hzz, mul_zero, add_zero]
    exact hzy
  · rw [bmSTS_herm_add_smul_sq (F := GaloisField 2 f) K h τ hτ2 hsymm y z ((h y y) * s)]
    rw [hyz, hzy, hzz]
    simp only [mul_one, mul_zero, add_zero]
    rw [add_assoc, ht]
    simp

private lemma bmSTS_K_antidiag_herm
    {m' f : ℕ} (a b : Fin m' → GaloisField 2 (2 * max f 1)) :
    Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1) ((((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) :
            Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ a) i)) (Unitary.antidiag m')
                ⬝ᵥ
        (((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) : Matrix (Fin
            m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ b) =
      CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2
          * max f 1)) 2 (max f 1)) a b := by
  rw [← bmSTS_antidiagConj_herm_pair]
  rw [bmSTS_hCa, bmSTS_hCa]

private theorem bmSTS_K_root_u_su_z
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))     (z : W) (hz : z ≠ 0) (hzz : h z z = 0) :
    ∃ (β : Fin (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rank → ℤ) (u_SU : ↥(Unitary.SU
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
                m'))
      (v₀ : Fin m' → GaloisField 2 (2 * max f 1)),
      β ∈ (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
          (le_max_right f 1)) m').roots ∧ GGLongRoot (Unitary.rootDatum
              (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f 1)) m') β
                  ∧ v₀ ≠ 0 ∧
      Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1))
          2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0 ∧
      (((((Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
          (le_max_right f 1)) m').rootGroup β).map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
              (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
                  m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀) ∧
      v₀ = ((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) : Matrix (Fin
          m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ
        (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
            (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
                eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace z)) := by
  have hstd : ∀ v w : W, CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * max f 1)) 2 (max f 1)) (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K
          hKrank (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
              W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace v))
                  (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                      (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂
                          hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace w)) =
                              (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank) (h v w) := by
    intro v w
    have h1 : (bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank).symm
        (CFSG.ClassicalGroups.Unitary.herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
            (2 * max f 1)) 2 (max f 1)) (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
                    W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace v))
                        (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                            (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁
                                hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm'
                                    htrace w))) = h v w := by
      rw [← bmSTS_herm_stdModuleEquiv f m' K hKrank τ hτ2 hτne
          (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
              (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
                  h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace v))
                      (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                          (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁
                              hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace
                                  w))]
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact bmSTS_hermEquiv_isometry n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
          heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace v w
    have h2 := congrArg (⇑(bmSTS_blockEmbeddingEV_PSU_fieldAlgEquiv f K hKrank)) h1
    simpa using h2
  obtain ⟨w, hzw, hww⟩ := bmSTS_isotropic_companion K h τ hτ2 hτne hτfix hsymm hnd hKrank z hz hzz
  let v₀ : Fin m' → GaloisField 2 (2 * max f 1) := ((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m')
      (GaloisField 2 (2 * max f 1))) : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ
          (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
              (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
                  h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace z))
  let w₀ : Fin m' → GaloisField 2 (2 * max f 1) := ((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m')
      (GaloisField 2 (2 * max f 1))) : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ
          (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
              (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
                  h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace w))
  have hisoV : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
      max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0 := by
    change Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1) ((((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f
            1))) : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ
                (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                    (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace z))) i))
                            (Unitary.antidiag m') ⬝ᵥ
      (((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) : Matrix (Fin m')
          (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f
              m' K hKrank (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁
                  hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace z))) = 0
    rw [bmSTS_K_antidiag_herm, hstd z z, hzz, map_zero]
  have hisoW : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
      max f 1)) 2 (max f 1) (w₀ i)) (Unitary.antidiag m') ⬝ᵥ w₀ = 0 := by
    change Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1) ((((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f
            1))) : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ
                (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                    (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace w))) i))
                            (Unitary.antidiag m') ⬝ᵥ
      (((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) : Matrix (Fin m')
          (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f
              m' K hKrank (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁
                  hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace w))) = 0
    rw [bmSTS_K_antidiag_herm, hstd w w, hww, map_zero]
  have hpair : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
      max f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ w₀ = 1 := by
    change Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1) ((((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f
            1))) : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ
                (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                    (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
                        K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace z))) i))
                            (Unitary.antidiag m') ⬝ᵥ
      (((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) : Matrix (Fin m')
          (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f
              m' K hKrank (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁
                  hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace w))) = 1
    rw [bmSTS_K_antidiag_herm, hstd z w, hzw, map_one]
  have hA0 : bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
      (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
          heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace z) ≠ 0 := by
    intro h0
    have h1 : bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
        eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace z = 0 := by
      have := congrArg (⇑(bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank).symm) h0
      simpa using this
    exact hz ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
        h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace).injective (by simpa using h1))
  have hv₀ : v₀ ≠ 0 := by
    intro h0
    apply hA0
    have h1 := congrArg (fun x => (bmSTS_antidiagConj m' f : Matrix (Fin m') (Fin m') (GaloisField 2
        (2 * max f 1))) *ᵥ x) h0
    rw [Matrix.mulVec_zero] at h1
    rw [← bmSTS_hCa (bmSTS_antidiagConj m' f) (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K
        hKrank (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W
            h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace z))]
    exact h1
  obtain ⟨β, hβ, hlong, u_SU, hu_SU, _⟩ :=
    exists_conj_rootGroup_eq_unitTransvGroup_PSU (CFSG.LieType.Universal.card_galoisField_two_mul 2
        (max f 1) (le_max_right f 1)) m' hm3 v₀ w₀ hisoV hisoW hpair
  exact ⟨β, u_SU, v₀, hβ, hlong, hv₀, hisoV, hu_SU, rfl⟩

private lemma bmSTS_map_conj_map {A B : Type*} [Group A] [Group B]
    (ι : A →* B) (X : Subgroup A) (u : A) :
    (X.map (MulAut.conj u).toMonoidHom).map ι =
      (X.map ι).map (MulAut.conj (ι u)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul]

private theorem bmSTS_K_omega_given
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))     (z : W) (hz : z ≠ 0) (hzz : h z z = 0)
    (v : W) (hv : v ≠ 0) (hvv : h v v = 0) (hvz : v = z)
    (ω₀ : K) (hω₀ : Algebra.trace (GaloisField 2 f) K ω₀ = 1)
    (ω : K) (hω : Algebra.trace (GaloisField 2 f) K ω = 1) :
    altSiegelGroup (bmSTS_J n f) (eW v) (eW (ω₀ • v)) =
      altSiegelGroup (bmSTS_J n f) (eW z) (eW (ω • z)) := by
  rw [hvz]
  have hc : Algebra.trace (GaloisField 2 f) K (ω - ω₀) = 0 := by
    rw [map_sub, hω, hω₀, sub_self]
  obtain ⟨t, ht⟩ := bmSTS_trace_eq_zero_mem_base K hKrank τ hτne hc
  have hωeq : ω = ω₀ + algebraMap (GaloisField 2 f) K t := by
    rw [ht]
    ring
  have hEW : eW (ω • z) = t • eW z + eW (ω₀ • z) := by
    rw [hωeq, add_smul, map_add, algebraMap_smul K t z, map_smul eW t z]
    exact add_comm _ _
  have hbc := bmSTS_altSiegel_basis_change (bmSTS_J n f) (eW z) (eW (ω₀ • z)) 1 0 t 1 (by simp)
  simp only [one_smul, zero_smul, add_zero] at hbc
  rw [← hEW] at hbc
  exact hbc.symm

private theorem bmSTS_LieUniversal_transport_back {A B : LieUniversal} (heq : A = B)
    (β : Fin B.D.rank → ℤ) (hβ : β ∈ B.D.roots) (hlong : GGLongRoot B.D β) :
    ∃ (β₀ : Fin A.D.rank → ℤ) (_ : β₀ ∈ A.D.roots) (_ : GGLongRoot A.D β₀),
      (∀ g : A.K, g ∈ A.D.rootGroup β₀ → (congrArg LieUniversal.K heq) ▸ g ∈ B.D.rootGroup β) ∧
      (∀ g' ∈ B.D.rootGroup β, ∃ g ∈ A.D.rootGroup β₀, (congrArg LieUniversal.K heq) ▸ g = g') := by
  cases heq
  exact ⟨β, hβ, hlong, fun g hg => hg, fun g' hg' => ⟨g', hg', rfl⟩⟩

private theorem bmSTS_mulVec_inv_mulVec {m : ℕ} {F : Type} [Field F] (M : GL (Fin m) F)
    (y : Fin m → F) :
    (M : Matrix (Fin m) (Fin m) F) *ᵥ (((M⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ y) =
      y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

private theorem bmSTS_apply_symm_chain {V W U : Type} [AddCommGroup V] [AddCommGroup W]
    [AddCommGroup U] {R : Type} [Semiring R] [Module R V] [Module R W] [Module R U]
    (Φ : V ≃ₗ[R] W) (A : W ≃ₗ[R] U) (a : U) (v : V) (hv : v = Φ.symm (A.symm a)) :
    A (Φ v) = a := by
  subst hv
  simp

private theorem bmSTS_hCv_chain {m : ℕ} {F : Type} [Field F] (C P : GL (Fin m) F)
    (v₀ a y z : Fin m → F) (hy : y = a)
    (ha_eq : a = (C : Matrix (Fin m) (Fin m) F)⁻¹ *ᵥ ((P : Matrix (Fin m) (Fin m) F) *ᵥ v₀))
    (hv₀ : v₀ = (((P⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) *ᵥ z) :
    (C : Matrix (Fin m) (Fin m) F) *ᵥ y = z := by
  have hCu : IsUnit (C : Matrix (Fin m) (Fin m) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 C.isUnit
  rw [hy, ha_eq, hv₀, bmSTS_mulVec_inv_mulVec P z, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hCu, Matrix.one_mulVec]

private theorem bmSTS_K_root_transport
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))     (β : Fin (Unitary.rootDatum
          (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f 1)) m').rank
              → ℤ) (hβr : β ∈ (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2
                  (max f 1) (le_max_right f 1)) m').roots) (hβ : GGLongRoot (Unitary.rootDatum
                      (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f
                          1)) m') β) :
    ∃ (β₀ : Fin ((ggU .PSU m' (max f 1)).D).rank → ℤ) (hβ₀ : β₀ ∈ ((ggU .PSU m' (max f 1)).D).roots)
        (hlong₀ : GGLongRoot ((ggU .PSU m' (max f 1)).D) β₀),
      (∀ g : (ggU .PSU m' (max f 1)).K, g ∈ ((ggU .PSU m' (max f 1)).D).rootGroup β₀ →
          (bmSTS_ggU_K_eq m' f ▸ g) ∈ (Unitary.rootDatum
              (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f 1))
                  m').rootGroup β) ∧ (∀ g', g' ∈ (Unitary.rootDatum
                      (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f
                          1)) m').rootGroup β → ∃ g, g ∈ ((ggU .PSU m' (max f 1)).D).rootGroup β₀ ∧
                              (bmSTS_ggU_K_eq m' f ▸ g) = g') := by
  have hf : 1 ≤ max f 1 := le_max_right f 1
  have heq : (ggU .PSU m' (max f 1)) =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
          (max f 1)) m',
        Unitary.rootDatum (card_galoisField_two_mul 2 (max f 1) hf) m'⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  exact bmSTS_LieUniversal_transport_back heq β hβr hβ

private theorem bmSTS_K_pair_image
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))     (z : W) (hz : z ≠ 0) (hzz : h z z = 0)
    (β : Fin (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rank → ℤ) (hβr : β ∈ (Unitary.rootDatum
            (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f 1))
                m').roots)
    (hβ : GGLongRoot (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m') β) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ : Fin m' → GaloisField 2 (2 * max f 1)) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (hu_SU : ((((Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rootGroup β).map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
                m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (ha : v₀ = ((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) : Matrix
        (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ
            (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
                    W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace z))) :
    ∃ (β₀ : Fin ((ggU .PSU m' (max f 1)).D).rank → ℤ) (v : W) (ω₀ : K),
      β₀ ∈ ((ggU .PSU m' (max f 1)).D).roots ∧ GGLongRoot ((ggU .PSU m' (max f 1)).D) β₀ ∧
      v ≠ 0 ∧ h v v = 0 ∧ Algebra.trace (GaloisField 2 f) K ω₀ = 1 ∧
      (((((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 : GL
          (Fin m') (GaloisField 2 (2 * max f 1))) : Matrix (Fin m') (Fin m') (GaloisField 2 (2 * max
              f 1)))) *ᵥ ((bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank)
                  ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K
                      τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) v)) =
        (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank)
            ((bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
                eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace) z)) ∧
      (((((ggU .PSU m' (max f 1)).D).rootGroup β₀).map (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS
          hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank
              htrace)).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          altSiegelGroup (bmSTS_J n f) (eW v) (eW (ω₀ • v))) := by
  obtain ⟨β₀, hβ₀, hlong₀, hrootG, hrootG'⟩ :=
    bmSTS_K_root_transport n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2
      hτne hτfix hsymm hnd hrank hm' hm3 hKrank htrace β hβr hβ
  obtain ⟨a, v, ω₀, ha_eq, hv_eq, hv, hvv, hω₀, ha0, haa⟩ :=
    bmSTS_unitTransv_pair_exists n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
      heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong₀ β hβ u_SU v₀ hv₀ hiso hu_SU
  have h₁ := bmSTS_unitTransv_pair_image_le n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
    m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong₀ β hβ u_SU v₀ hv₀ hiso
    hu_SU a v ω₀ ha_eq hv_eq hvv hω₀ hrootG
  have h₂ := bmSTS_unitTransv_pair_image_ge n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
    m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace β₀ hlong₀ β hβ u_SU v₀ hv₀ hiso
    hu_SU a v ω₀ ha_eq hv_eq hvv hω₀ hrootG hrootG'
  refine ⟨β₀, v, ω₀, hβ₀, hlong₀, hv, hvv, hω₀, ?_, le_antisymm h₁ h₂⟩
  have hAΦv := bmSTS_apply_symm_chain _ _ a v hv_eq
  exact bmSTS_hCv_chain _ _ v₀ a _ _ hAΦv ha_eq ha

private lemma bmSTS_cast_cast {A B : Type} (h h' : A = B) (x : B) :
    h ▸ (h'.symm ▸ x) = x := by
  cases h
  cases h'
  rfl

private lemma bmSTS_chain_close {V W U : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
    {R : Type} [Semiring R] [Module R V] [Module R W] [Module R U]
    (Φ : V ≃ₗ[R] W) (A : W ≃ₗ[R] U) (y : U) (z : V) (h : y = A (Φ z)) :
    Φ.symm (A.symm y) = z := by
  subst h
  simp

private theorem bmSTS_K_blockAction_eq
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))     (z : W) (u_SU : ↥(Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
              (v : W)
    (hCv : (((Unitary.conjEquiv (bmSTS_antidiagConj m' f) (bmSTS_antidiagConj_spec m' f) u_SU).1 :
        GL (Fin m') (GaloisField 2 (2 * max f 1))) : Matrix (Fin m') (Fin m') (GaloisField 2 (2 *
            max f 1))) *ᵥ (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
                    W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace v)) =
                        bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                            (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁
                                hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm'
                                    htrace z)) :
    bmSTS_blockEmbeddingEV_PSU_blockAction n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
      ((bmSTS_ggU_K_eq m' f).symm ▸ u_SU) v = z := by
  have hg : ((bmSTS_ggU_K_eq m' f) ▸ ((bmSTS_ggU_K_eq m' f).symm ▸ u_SU) :
      ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
        (max f 1)) m')) = u_SU :=
    bmSTS_cast_cast (bmSTS_ggU_K_eq m' f) (bmSTS_ggU_K_eq m' f) u_SU
  simp only [bmSTS_blockEmbeddingEV_PSU_blockAction, LinearEquiv.trans_apply,
    bmSTS_blockEmbeddingEV_PSU_stdAction, LinearEquiv.ofBijective_apply,
    bmSTS_blockEmbeddingEV_PSU_stdActionMap, LinearMap.comp_apply,
    bmSTS_blockEmbeddingEV_PSU_suAction]
  rw [hg]
  exact bmSTS_chain_close _ _ _ _ hCv

private theorem bmSTS_K_conj_kform
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))     (z : W) (u : (ggU .PSU m' (max f 1)).K) (v
          : W) (ω₀ : K)
    (β₀ : Fin ((ggU .PSU m' (max f 1)).D).rank → ℤ)
    (hK : (((((ggU .PSU m' (max f 1)).D).rootGroup β₀).map (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU
        hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank
            htrace)).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)) =
        altSiegelGroup (bmSTS_J n f) (eW v) (eW (ω₀ • v)))
    (hact : Matrix.mulVec (CFSG.LieType.Universal.Symplectic.SpExtras.mat n (GaloisField 2 f)
        ((bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
            heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace) u)) (eW v) = eW z)
    (hact2 : Matrix.mulVec (CFSG.LieType.Universal.Symplectic.SpExtras.mat n (GaloisField 2 f)
        ((bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
            heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace) u)) (eW (ω₀ • v)) = eW (ω₀ • z)) :
    ((((ggU .PSU m' (max f 1)).D.rootGroup β₀).map (MulAut.conj u).toMonoidHom).map
            (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
                heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          altSiegelGroup (bmSTS_J n f) (eW z) (eW (ω₀ • z)) := by
  have e1 := bmSTS_map_conj_map (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁
    hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)
    ((ggU .PSU m' (max f 1)).D.rootGroup β₀) u
  have e2 := bmSTS_map_conj_subtype
    (X := ((ggU .PSU m' (max f 1)).D.rootGroup β₀).map
      (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
        heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace))
    ((bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace) u)
  have e3 := bmSTS_conj_altSiegelGroup (n := n) (F := GaloisField 2 f)
    ((bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace) u) (eW v) (eW (ω₀ • v))
  rw [hact, hact2] at e3
  refine (congrArg (Subgroup.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) e1).trans
    (e2.trans ?_)
  rw [hK]
  exact e3

private theorem bmSTS_K_act_pair
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (u : (ggU .PSU m' (max f 1)).K) (v z : W) (ω : K) (hBA : bmSTS_blockEmbeddingEV_PSU_blockAction
        n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank
            hm' hKrank htrace u v = z) :
    Matrix.mulVec (CFSG.LieType.Universal.Symplectic.SpExtras.mat n (GaloisField 2 f)
        (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
            heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace u)) (eW v) = eW z ∧
      Matrix.mulVec (CFSG.LieType.Universal.Symplectic.SpExtras.mat n (GaloisField 2 f)
        (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
            heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace u)) (eW (ω • v)) = eW (ω • z) := by
  have hhom := (bmSTS_hom_action n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj
      hτ2 hτne hsymm hnd hrank hm' hKrank htrace).1 u
  exact ⟨(hhom v).trans (congrArg eW hBA),
    (hhom (ω • v)).trans (congrArg eW
      ((bmSTS_blockAction_smul n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj
          hτ2 hτne hsymm hnd hrank hm' hKrank htrace u ω v).trans
        (congrArg (ω • ·) hBA)))⟩

private theorem bmSTS_K_model_Kform
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))     (z : W) (hz : z ≠ 0) (hzz : h z z = 0)
    (β : Fin (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rank → ℤ) (hβr : β ∈ (Unitary.rootDatum
            (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1) (le_max_right f 1))
                m').roots)
    (hβ : GGLongRoot (Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m') β) (u_SU : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * max f 1)) 2 (max f 1)) m'))
    (v₀ : Fin m' → GaloisField 2 (2 * max f 1)) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max
        f 1)) 2 (max f 1) (v₀ i)) (Unitary.antidiag m') ⬝ᵥ v₀ = 0)
    (hu_SU : ((((Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 (max f 1)
        (le_max_right f 1)) m').rootGroup β).map (MulAut.conj u_SU).toMonoidHom).map (Unitary.SU
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2 (max f 1))
                m').subtype) =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * max f 1)) 2
            (max f 1)).toRingHom (Unitary.antidiag m') v₀)
    (ha : v₀ = ((((bmSTS_antidiagConj m' f)⁻¹ : GL (Fin m') (GaloisField 2 (2 * max f 1))) : Matrix
        (Fin m') (Fin m') (GaloisField 2 (2 * max f 1)))) *ᵥ
            (bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv f m' K hKrank
                (bmSTS_blockEmbeddingEV_PSU_hermEquiv n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ
                    W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' htrace z))) :
    ∃ (β₀ : Fin ((ggU .PSU m' (max f 1)).D).rank → ℤ) (u : (ggU .PSU m' (max f 1)).K) (ω₀ : K),
      β₀ ∈ ((ggU .PSU m' (max f 1)).D).roots ∧ GGLongRoot ((ggU .PSU m' (max f 1)).D) β₀ ∧
      Algebra.trace (GaloisField 2 f) K ω₀ = 1 ∧
      ((((ggU .PSU m' (max f 1)).D.rootGroup β₀).map (MulAut.conj u).toMonoidHom).map
            (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
                heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          altSiegelGroup (bmSTS_J n f) (eW z) (eW (ω₀ • z)) := by
  obtain ⟨β₀, v, ω₀, hβ₀, hlong₀, hv, hvv, hω₀, hCv, hK⟩ :=
    bmSTS_K_pair_image n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne
        hτfix hsymm hnd hrank hm' hm3 hKrank htrace z hz hzz β hβr hβ u_SU
      v₀ hv₀ hiso hu_SU ha
  have hBA := bmSTS_K_blockAction_eq n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
      heWinj hτ2 hτne hτfix hsymm hnd hrank hm' hm3 hKrank htrace z u_SU v
    hCv
  generalize ((bmSTS_ggU_K_eq m' f).symm ▸ u_SU : (ggU .PSU m' (max f 1)).K) = u at hBA
  obtain ⟨hact, hact2⟩ := bmSTS_K_act_pair n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace u v z ω₀ hBA
  exact ⟨β₀, u, ω₀, hβ₀, hlong₀, hω₀,
    bmSTS_K_conj_kform n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne
        hτfix hsymm hnd hrank hm' hm3 hKrank htrace z u v ω₀ β₀ hK hact
      hact2⟩

private theorem bmSTS_siegelClosure_of_canonical_K
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K]
    (τ : K ≃+* K)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y)) :
    ∀ (z : W) (ω : K), z ≠ 0 → h z z = 0 → Algebra.trace (GaloisField 2 f) K ω = 1 →
      ∃ (β : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ) (u : (ggU .PSU m' (max f 1)).K),
        β ∈ (ggU .PSU m' (max f 1)).D.roots ∧ GGLongRoot (ggU .PSU m' (max f 1)).D β ∧
        ((((ggU .PSU m' (max f 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
            (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
              m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          altSiegelGroup (bmSTS_J n f) (eW z) (eW (ω • z)) := by
  intro z ω hz0 hzz hω
  obtain ⟨w, hzw, hww⟩ :=
    bmSTS_isotropic_companion K h τ hτ2 hτne hτfix hsymm hnd hKrank z hz0 hzz
  have hK :
      ∃ (β : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ) (u : (ggU .PSU m' (max f 1)).K),
        β ∈ (ggU .PSU m' (max f 1)).D.roots ∧ GGLongRoot (ggU .PSU m' (max f 1)).D β ∧
        ((((ggU .PSU m' (max f 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
            (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
              m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          altSiegelGroup (bmSTS_J n f) (eW z) (eW (ω • z))  := by
    obtain ⟨β, u_SU, v₀, hβr, hlong, hv₀, hiso, hu_SU, ha⟩ :=
      bmSTS_K_root_u_su_z n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2
          hτne hτfix hsymm hnd hrank hm' hm3 hKrank htrace z hz0 hzz
    obtain ⟨β₀, u, ω₀, hβ₀, hlong₀, hω₀, hK⟩ :=
      bmSTS_K_model_Kform n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2
          hτne hτfix hsymm hnd hrank hm' hm3 hKrank htrace z hz0 hzz β hβr hlong u_SU v₀ hv₀ hiso
              hu_SU ha
    have hωeq := bmSTS_K_omega_given n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m' heW
        heWinj hτ2 hτne hτfix hsymm hnd hrank hm' hm3 hKrank htrace z hz0 hzz z hz0 hzz rfl ω₀ hω₀ ω
            hω
    exact ⟨β₀, u, hβ₀, hlong₀, hK.trans hωeq⟩
  exact hK

private theorem bmSTS_siegelClosure_explicit
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f)) (bmSTS_J n f) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (K : Type) [Field K] [Algebra (GaloisField 2 f) K] [Finite K] [CharP K 2]
    (τ : K ≃+* K)
    (hτfix : ∀ a : GaloisField 2 f, τ (algebraMap (GaloisField 2 f) K a) =
      algebraMap (GaloisField 2 f) K a)
    (W : Type) [AddCommGroup W] [Module K W] [Module (GaloisField 2 f) W]
    [IsScalarTower (GaloisField 2 f) K W]
    (h : W → W →ₗ[K] K)
    (eW : W →ₗ[GaloisField 2 f] ((Fin n ⊕ Fin n) → GaloisField 2 f)) (m' : ℕ)
    (heW : LinearMap.range eW = LinearMap.range (Matrix.mulVecLin e))
    (heWinj : Function.Injective eW) (hτ2 : ∀ a : K, τ (τ a) = a) (hτne : τ ≠ RingHom.id K)
    (hsymm : ∀ x y : W, h y x = τ (h x y))
    (hnd : ∀ x : W, (∀ y : W, h x y = 0) → x = 0)
    (hrank : Module.finrank K W = m') (hm' : 1 ≤ m')
    (hm3 : 2 ≤ m')
    (hKrank : Module.finrank (GaloisField 2 f) K = 2)
    (htrace : ∀ (x y : W) (c : K),
      eW x ⬝ᵥ Matrix.mulVec (bmSTS_J n f) (eW (c • y)) =
      Algebra.trace (GaloisField 2 f) K (c * h x y))
    (hrange : (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
        m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace).range = J') :
    ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (bmSTS_J n f) a₂ = 0 →
      altSiegelGroup (bmSTS_J n f) a₁ a₂ ≤
          J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∃ (β : Fin (ggU .PSU m' (max f 1)).D.rank → ℤ) (u : (ggU .PSU m' (max f 1)).K),
        β ∈ (ggU .PSU m' (max f 1)).D.roots ∧ GGLongRoot (ggU .PSU m' (max f 1)).D β ∧
        ((((ggU .PSU m' (max f 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
            (bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
              m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace)).map
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
          altSiegelGroup (bmSTS_J n f) a₁ a₂     := by
  intro a₁ a₂ ha₁ ha₂ hind hiso hle
  obtain ⟨hm₁, hm₂⟩ := bmSTS_altSiegel_mem_range n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h
      eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace a₁ a₂ ha₁ ha₂ hind hiso hle
  obtain ⟨z, c, hz0, hzz, hza₁, hza₂⟩ := bmSTS_altSiegel_plane_isKLine n f S hSU hS hodd he hadj
      hdeg₁ hdeg₂ hJe K τ hτfix W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
          hrange
    a₁ a₂ ha₁ ha₂ hind hiso hle hm₁ hm₂
  obtain ⟨ω, hω, hcanon⟩ := bmSTS_altSiegel_eq_canonical n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K
      τ W h eW m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
    a₁ a₂ z c hz0 hzz hza₁ hza₂ ha₁ ha₂ hind
  obtain ⟨β, u, hβ, hlong, heq⟩ := bmSTS_siegelClosure_of_canonical_K n f S hSU hS hodd he hadj
      hdeg₁ hdeg₂ hJe K τ W h eW m' heW heWinj hτ2 hτne hτfix hsymm hnd hrank hm' hm3 hKrank htrace
    z ω hz0 hzz hω
  exact ⟨β, u, hβ, hlong, heq.trans hcanon⟩

theorem exists_blockModel_selfDualTwo_PSp_explicit_inj
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆) :
    ∃ (r : ℕ)
      (ι : (ggU .PSU r (max f 1)).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ), 2 * r = Module.finrank (GaloisField 2 f)
          (LinearMap.range (Matrix.mulVecLin e)) ∧
      GGLongRoot (ggU .PSU r (max f 1)).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) → y ∈ Subgroup.center
        (ggU .PSU r (max f 1)).K) ∧ ι.range = J' ∧
      (Function.Injective ι ∧ 2 ≤ r ∧ (2 ^ max f 1 ≠ 2 ∨ 4 ≤ r)) ∧
      ∃ a₁ a₂ b₁ b₂ : (Fin n ⊕ Fin n) → (GaloisField 2 f),
        a₁ ⬝ᵥ Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          b₁ = 1 ∧ a₂ ⬝ᵥ Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          b₂ = 1 ∧
        (a₁ ⬝ᵥ Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          a₂ = 0 ∧ b₁ ⬝ᵥ Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          b₂ = 0 ∧
          a₁ ⬝ᵥ Matrix.mulVec
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) b₂ = 0 ∧ a₂ ⬝ᵥ Matrix.mulVec
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) b₁ = 0) ∧
        (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) = altSiegelGroup
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁
        a₂ ∧
        (((ggU .PSU r (max f 1)).D.rootGroup (-β₀)).map ι).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) = altSiegelGroup
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁
        b₂ := by
  obtain ⟨K, hKf, hKa, hKfin, hKrank, τ, W, hWadd, hWmodK, hWmodF, hWtower, h, eW, m', heW, heWinj,
    hτ2, hτne, hτfix, hsymm, hnd, hrank, hm', hm3, hnq, htrace, hKlinRepC, hKlinRep, hcommS⟩ :=
    bmSTS_explicit_data n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 f) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWadd
  letI : Module K W := hWmodK
  letI : Module (GaloisField 2 f) W := hWmodF
  letI : IsScalarTower (GaloisField 2 f) K W := hWtower
  let ι₀ := bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
    heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
  obtain ⟨hcen, hrange⟩ :=
    bmSTS_blockEmbeddingEV_PSU_props n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace hKlinRepC hKlinRep hcommS
  have hrangeJ' : ι₀.range = J' :=
    bmSTS_rangeEqJ' hrange (bmSTS_component_eq n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe)
  obtain ⟨β₀, a₁, a₂, b₁, b₂, hlong, h₁, h₂, h₃, himg₁, himg₂⟩ :=
    bmSTS_rootPair_explicit n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace
  have hdim : 2 * m' = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) := by
    have h1 : LinearMap.range (Matrix.mulVecLin e) = LinearMap.range eW := by rw [heW]
    calc 2 * m' = Module.finrank (GaloisField 2 f) K * Module.finrank K W := by
          rw [hKrank, hrank]
      _ = Module.finrank (GaloisField 2 f) W :=
          Module.finrank_mul_finrank (GaloisField 2 f) K W
      _ = Module.finrank (GaloisField 2 f) (LinearMap.range eW) :=
          LinearEquiv.finrank_eq (LinearEquiv.ofInjective eW heWinj)
      _ = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) :=
          LinearEquiv.finrank_eq (LinearEquiv.ofEq (LinearMap.range eW)
            (LinearMap.range (Matrix.mulVecLin e)) h1.symm)
  exact ⟨m', ι₀, β₀, hdim, hlong, hcen, hrangeJ',
    ⟨bmSTS_blockEmbeddingEV_PSU_hom_injective n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW
      m' heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace, hm3, hnq⟩,
    a₁, a₂, b₁, b₂, h₁, h₂, h₃, himg₁, himg₂⟩

theorem exists_blockModel_selfDualTwo_PSp_explicit
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆) :
    ∃ (r : ℕ)
      (ι : (ggU .PSU r (max f 1)).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
      (β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ), 2 * r = Module.finrank (GaloisField 2 f)
          (LinearMap.range (Matrix.mulVecLin e)) ∧
      GGLongRoot (ggU .PSU r (max f 1)).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) → y ∈ Subgroup.center
        (ggU .PSU r (max f 1)).K) ∧ ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : (Fin n ⊕ Fin n) → (GaloisField 2 f),
        a₁ ⬝ᵥ Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          b₁ = 1 ∧ a₂ ⬝ᵥ Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          b₂ = 1 ∧
        (a₁ ⬝ᵥ Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          a₂ = 0 ∧ b₁ ⬝ᵥ Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          b₂ = 0 ∧
          a₁ ⬝ᵥ Matrix.mulVec
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) b₂ = 0 ∧ a₂ ⬝ᵥ Matrix.mulVec
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) b₁ = 0) ∧
        (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) = altSiegelGroup
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁
        a₂ ∧
        (((ggU .PSU r (max f 1)).D.rootGroup (-β₀)).map ι).map
        ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) = altSiegelGroup
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁
        b₂ := by
  obtain ⟨r, ι, β₀, hdim, hlong, hcen, hrange, -, rest⟩ :=
    exists_blockModel_selfDualTwo_PSp_explicit_inj n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  exact ⟨r, ι, β₀, hdim, hlong, hcen, hrange, rest⟩

theorem exists_blockModelClosure_selfDualTwo_PSp_explicit
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆) :
    ∃ (r : ℕ) (ι : (ggU .PSU r (max f 1)).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2
        f))),
      2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) ∧
      (∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) → y ∈ Subgroup.center
          (ggU .PSU r (max f 1)).K) ∧
      ι.range = J' ∧
      (∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 → LinearIndependent
          (GaloisField 2 f) ![a₁, a₂] → a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix
          (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 → altSiegelGroup
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          a₁ a₂ ≤ J'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
        ∃ (β : Fin (ggU .PSU r (max f 1)).D.rank → ℤ) (u : (ggU .PSU r (max f 1)).K),
            β ∈ (ggU .PSU r (max f 1)).D.roots ∧
            GGLongRoot (ggU .PSU r (max f 1)).D β ∧
          ((((ggU .PSU r (max f 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
              (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype = altSiegelGroup (Matrix.fromBlocks
              0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂) := by
  obtain ⟨K, hKf, hKa, hKfin, hKrank, τ, W, hWadd, hWmodK, hWmodF, hWtower, h, eW, m', heW, heWinj,
    hτ2, hτne, hτfix, hsymm, hnd, hrank, hm', hm3, hnq, htrace, hKlinRepC, hKlinRep, hcommS⟩ :=
    bmSTS_explicit_data n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  letI : Field K := hKf
  letI : Algebra (GaloisField 2 f) K := hKa
  letI : Finite K := hKfin
  letI : AddCommGroup W := hWadd
  letI : Module K W := hWmodK
  letI : Module (GaloisField 2 f) W := hWmodF
  letI : IsScalarTower (GaloisField 2 f) K W := hWtower
  let ι₀ := bmSTS_blockEmbeddingEV_PSU_hom n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
    heW heWinj hτ2 hτne hsymm hnd hrank hm' hKrank htrace
  obtain ⟨hcen, hrange⟩ :=
    bmSTS_blockEmbeddingEV_PSU_props n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m'
      heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hnq hKrank htrace hKlinRepC hKlinRep hcommS
  have hrangeJ' : ι₀.range = J' :=
    bmSTS_rangeEqJ' hrange (bmSTS_component_eq n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe)
  haveI hchar : CharP K 2 :=
    charP_of_injective_algebraMap (RingHom.injective (algebraMap (GaloisField 2 f) K)) 2
  have hdim : 2 * m' = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) := by
    have h1 : LinearMap.range (Matrix.mulVecLin e) = LinearMap.range eW := by rw [heW]
    calc 2 * m' = Module.finrank (GaloisField 2 f) K * Module.finrank K W := by
          rw [hKrank, hrank]
      _ = Module.finrank (GaloisField 2 f) W :=
          Module.finrank_mul_finrank (GaloisField 2 f) K W
      _ = Module.finrank (GaloisField 2 f) (LinearMap.range eW) :=
          LinearEquiv.finrank_eq (LinearEquiv.ofInjective eW heWinj)
      _ = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) :=
          LinearEquiv.finrank_eq (LinearEquiv.ofEq (LinearMap.range eW)
            (LinearMap.range (Matrix.mulVecLin e)) h1.symm)
  refine ⟨m', ι₀, hdim, hcen, hrangeJ', ?_⟩
  intro a₁ a₂ ha₁ ha₂ hind hiso hle
  exact bmSTS_siegelClosure_explicit n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ hτfix W h eW m'
    heW heWinj hτ2 hτne hsymm hnd hrank hm' hm3 hKrank htrace hrangeJ' a₁ a₂ ha₁ ha₂ hind hiso hle

section LinearModelAtTwo

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

theorem exists_linearBlockModel_selfDualTwo_PSp_at_two
    (n : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 1)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 1))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 1))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 4)
    {J' : Subgroup (CFSG.Open.StatedSp n (GaloisField 2 1))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 1)).subtype S e,
      glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 1)).subtype S e⁆) :
    ∃ (m : ℕ) (_ : Algebra (GaloisField 2 1) (GaloisField 2 2))
      (ι : SU (unitaryInvolution (GaloisField 2 2) 2 1) m →*
        CFSG.Open.StatedSp n (GaloisField 2 1))
      (E : (Fin m → GaloisField 2 2) →ₗ[GaloisField 2 1]
        ((Fin n ⊕ Fin n) → GaloisField 2 1))
      (C : Submodule (GaloisField 2 1) ((Fin n ⊕ Fin n) → GaloisField 2 1)),
      4 ≤ m ∧ Function.Injective ι ∧ ι.range = J' ∧ Function.Injective E ∧
      (∀ g x, ((ι g : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ E x =
        E (natRep (SU (unitaryInvolution (GaloisField 2 2) 2 1) m) g x)) ∧
      (∀ g w, w ∈ C → ((ι g : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ w = w) ∧
      (∀ z, ∃ x, ∃ w ∈ C, z = E x + w) ∧
      (∀ g, g ^ 2 = 1 → ∀ z, z ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)).mulVec
          ((((ι g : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ z) - z) = 0) := by
  have h : ∃ (m : ℕ) (_ : Algebra (GaloisField 2 1) (GaloisField 2 (2 * max 1 1)))
      (ι : SU (unitaryInvolution (GaloisField 2 (2 * max 1 1)) 2 (max 1 1)) m →*
        CFSG.Open.StatedSp n (GaloisField 2 1))
      (E : (Fin m → GaloisField 2 (2 * max 1 1)) →ₗ[GaloisField 2 1]
        ((Fin n ⊕ Fin n) → GaloisField 2 1))
      (C : Submodule (GaloisField 2 1) ((Fin n ⊕ Fin n) → GaloisField 2 1)),
      4 ≤ m ∧ Function.Injective ι ∧ ι.range = J' ∧ Function.Injective E ∧
      (∀ g x, ((ι g : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ E x =
        E (natRep (SU (unitaryInvolution (GaloisField 2 (2 * max 1 1)) 2 (max 1 1)) m) g x)) ∧
      (∀ g w, w ∈ C → ((ι g : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ w = w) ∧
      (∀ z, ∃ x, ∃ w ∈ C, z = E x + w) ∧
      (∀ g, g ^ 2 = 1 → ∀ z, z ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)).mulVec
          ((((ι g : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ z) - z) = 0) := by
    classical
    obtain ⟨K, hKf, hKa, hKfin, hKrank, τ, W, hWadd, hWmodK, hWmodF, hWtower, h, eW, m, heW, heWinj,
      hτ2, hτne, hτfix, hsymm, hnd, hrank, hm, hm3, hnq, htrace, hKlinRepC, hKlinRep, hcommS⟩ :=
      bmSTS_explicit_data n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
    let : Field K := hKf
    let : Algebra (GaloisField 2 1) K := hKa
    have : Finite K := hKfin
    let : AddCommGroup W := hWadd
    let : Module K W := hWmodK
    let : Module (GaloisField 2 1) W := hWmodF
    have : IsScalarTower (GaloisField 2 1) K W := hWtower
    let A : Algebra (GaloisField 2 1) (GaloisField 2 (2 * max 1 1)) :=
      Classical.choice (bmSTS_blockEmbeddingEV_PSU_baseAlgebra 1)
    let := A
    have hm4 : 4 ≤ m := by simpa using hnq
    let α : (ggU .PSU m (max 1 1)).K ≃* SU (unitaryInvolution (GaloisField 2 (2 * max 1 1)) 2 (max 1 1)) m := by
      change SU (unitaryInvolution (GaloisField 2 (2 * max 1 1)) 2 (max 1 1)) m ≃*
        SU (unitaryInvolution (GaloisField 2 (2 * max 1 1)) 2 (max 1 1)) m
      exact MulEquiv.refl _
    let ι₀ := bmSTS_blockEmbeddingEV_PSU_hom n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace
    let ι := ι₀.comp α.symm.toMonoidHom
    have hi₀ : Function.Injective ι₀ := bmSTS_blockEmbeddingEV_PSU_hom_injective n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace
    obtain ⟨hcen, hRange⟩ := bmSTS_blockEmbeddingEV_PSU_props
      n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m
        heW heWinj hτ2 hτne hsymm hnd hrank hm hm3 hnq hKrank htrace hKlinRepC hKlinRep hcommS
    have hRangeJ : ι₀.range = J' :=
      bmSTS_rangeEqJ' hRange (bmSTS_component_eq n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe)
    let ξ := bmSTS_blockEmbeddingEV_PSU_hermEquiv n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm htrace
    let η := bmSTS_blockEmbeddingEV_PSU_stdModuleEquiv 1 m K hKrank
    let P := bmSTS_antidiagConj m 1
    let T : (Fin m → GaloisField 2 (2 * max 1 1)) →ₗ[GaloisField 2 1] (Fin m → GaloisField 2 (2 * max 1 1)) :=
      (Matrix.mulVecLin (P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1)))).restrictScalars (GaloisField 2 1)
    let E := eW.comp (ξ.symm.toLinearMap.comp (η.symm.toLinearMap.comp T))
    let C := LinearMap.ker (Matrix.mulVecLin e)
    have hT : Function.Injective T := by
      change Function.Injective (Matrix.mulVecLin (P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1))))
      exact bmSTS_mulVecLin_GL_injective P
    have hE : Function.Injective E := heWinj.comp (ξ.symm.injective.comp
      (η.symm.injective.comp hT))
    have hAct : ∀ g x, ((ι g : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ E x =
        E (natRep (SU (unitaryInvolution (GaloisField 2 (2 * max 1 1)) 2 (max 1 1)) m) g x) := by
      intro g x
      have h0 := (bmSTS_blockExtend_apply n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace (α.symm g)).1 (ξ.symm (η.symm (T x)))
      change ((bmSTS_blockEmbeddingEV_PSU_blockExtend
        n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace (α.symm g) : GL (Fin n ⊕ Fin n) (GaloisField 2 1)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) *ᵥ
        eW (ξ.symm (η.symm (T x))) = E _
      rw [h0]
      apply congrArg eW
      simp only [bmSTS_blockEmbeddingEV_PSU_blockAction, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply]
      change ξ.symm ((bmSTS_blockEmbeddingEV_PSU_stdAction n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace (α.symm g))
        (ξ (ξ.symm (η.symm (T x))))) = ξ.symm (η.symm (T _))
      rw [LinearEquiv.apply_symm_apply]
      apply congrArg ξ.symm
      change η.symm ((bmSTS_blockEmbeddingEV_PSU_suAction m 1 (α.symm g))
        (η (η.symm (T x)))) = η.symm (T _)
      rw [LinearEquiv.apply_symm_apply]
      apply congrArg η.symm
      change ((P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1))) *
        ((g : GL (Fin m) (GaloisField 2 (2 * max 1 1))) : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1))) *
        ((P⁻¹ : GL (Fin m) (GaloisField 2 (2 * max 1 1))) : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1)))) *ᵥ
        ((P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1))) *ᵥ x) =
        (P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1))) *ᵥ
          (((g : GL (Fin m) (GaloisField 2 (2 * max 1 1))) : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1))) *ᵥ x)
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [show ((P⁻¹ : GL (Fin m) (GaloisField 2 (2 * max 1 1))) : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1))) *
        (P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1))) = 1 from congrArg Units.val (inv_mul_cancel P)]
      rw [Matrix.mul_one, Matrix.mulVec_mulVec]

    refine ⟨m, A, ι, E, C, hm4, hi₀.comp α.symm.injective, ?_, hE, hAct, ?_, ?_, ?_⟩
    · have heq : ι.range = ι₀.range := by
        ext z
        constructor
        · rintro ⟨g, rfl⟩
          exact ⟨α.symm g, rfl⟩
        · rintro ⟨g, rfl⟩
          refine ⟨α g, ?_⟩
          change ι₀ (α.symm (α g)) = ι₀ g
          rw [MulEquiv.symm_apply_apply]
      exact heq.trans hRangeJ

    · intro g w hw
      exact (bmSTS_blockExtend_apply n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace (α.symm g)).2 w hw
    · intro z
      obtain ⟨w, hw⟩ : ∃ w : W, eW w = Matrix.mulVecLin e z := by
        apply LinearMap.mem_range.mp
        rw [heW]
        exact LinearMap.mem_range_self (Matrix.mulVecLin e) z
      let x := ((P⁻¹ : GL (Fin m) (GaloisField 2 (2 * max 1 1))) : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1))) *ᵥ
        η (ξ w)
      have hEx : E x = eW w := by
        change eW (ξ.symm (η.symm ((P : Matrix (Fin m) (Fin m) (GaloisField 2 (2 * max 1 1))) *ᵥ x))) = eW w
        dsimp only [x]
        rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec,
          LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      have hb : z - eW w ∈ C := by
        rw [LinearMap.mem_ker, map_sub, hw]
        have hid : (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e := by
          rw [← Matrix.mulVecLin_mul, he.2.1]
        have h := congrArg (fun Q : Module.End (GaloisField 2 1) _ => Q z) hid
        change Matrix.mulVecLin e (Matrix.mulVecLin e z) = Matrix.mulVecLin e z at h
        rw [h, sub_self]
      exact ⟨x, z - eW w, hb, by rw [hEx]; abel⟩

    · intro g hg z
      let L := bmSTS_blockEmbeddingEV_PSU_blockAction n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace (α.symm g)
      have hLact (w : W) : natRep (CFSG.Open.StatedSp n (GaloisField 2 1)) (ι g) (eW w) = eW (L w) :=
        (bmSTS_blockExtend_apply n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace (α.symm g)).1 w
      have hgg : ι g * ι g = 1 := by rw [← map_mul, ← pow_two, hg, map_one]
      have hL2 (w : W) : L (L w) = w := by
        apply heWinj
        have h0 := congrArg (fun t : CFSG.Open.StatedSp n (GaloisField 2 1) =>
          natRep (CFSG.Open.StatedSp n (GaloisField 2 1)) t (eW w)) hgg
        rw [map_mul, Module.End.mul_apply, hLact w, hLact (L w), map_one, Module.End.one_apply] at h0
        exact h0
      have hLiso (x y : W) : h (L x) (L y) = h x y :=
        bmSTS_blockAction_isometry n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace (α.symm g) x y
      have hCharK : CharP K 2 :=
        charP_of_injective_algebraMap (algebraMap (GaloisField 2 1) K).injective 2
      have := hCharK
      obtain ⟨w, hw⟩ : ∃ w : W, eW w = Matrix.mulVecLin e z := by
        apply LinearMap.mem_range.mp
        rw [heW]
        exact LinearMap.mem_range_self (Matrix.mulVecLin e) z
      let b := z - eW w
      have hb : b ∈ C := by
        rw [LinearMap.mem_ker, map_sub, hw]
        have hid : (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e := by
          rw [← Matrix.mulVecLin_mul, he.2.1]
        have h0 := congrArg (fun Q : Module.End (GaloisField 2 1) _ => Q z) hid
        change Matrix.mulVecLin e (Matrix.mulVecLin e z) = Matrix.mulVecLin e z at h0
        rw [h0, sub_self]
      have hzb : z = eW w + b := by dsimp only [b]; abel
      have hbfix : natRep (CFSG.Open.StatedSp n (GaloisField 2 1)) (ι g) b = b :=
        (bmSTS_blockExtend_apply n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace (α.symm g)).2 b hb
      have hd : natRep (CFSG.Open.StatedSp n (GaloisField 2 1)) (ι g) z - z = eW (L w - w) := by
        rw [hzb, map_add, hLact, hbfix, map_sub]
        abel
      have hcfix : τ (h w (L w - w)) = h w (L w - w) := by
        have h1 : τ (h w (L w)) = h w (L w) := by
          have h0 := hLiso w (L w)
          rw [hL2] at h0
          exact (hsymm w (L w)).symm.trans h0
        have h2 : τ (h w w) = h w w := (hsymm w w).symm
        rw [map_sub, map_sub, h1, h2]
      have htrace0 : Algebra.trace (GaloisField 2 1) K (h w (L w - w)) = 0 := by
        apply (algebraMap (GaloisField 2 1) K).injective
        rw [map_zero, bmSTS_trace_eq_add K τ hτ2 hτfix hτne hKrank, hcfix, CharTwo.add_self_eq_zero]
      have hcross : b ⬝ᵥ Matrix.mulVec (bmSTS_J n 1) (eW (L w - w)) = 0 := by
        have h0 := bmSTS_blockExtend_orthogonal' n 1 S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe K τ W h eW m heW heWinj hτ2 hτne hsymm hnd hrank hm hKrank htrace b hb (eW (L w - w))
          (by rw [← heW]; exact LinearMap.mem_range_self eW _)
        simpa only [Matrix.toBilin'_apply'] using h0
      have hpure : eW w ⬝ᵥ Matrix.mulVec (bmSTS_J n 1) (eW (L w - w)) = 0 := by
        have h0 := htrace w (L w - w) 1
        simpa only [one_smul, one_mul, htrace0] using h0
      change z ⬝ᵥ Matrix.mulVec (bmSTS_J n 1)
        (natRep (CFSG.Open.StatedSp n (GaloisField 2 1)) (ι g) z - z) = 0
      rw [hd, hzb, add_dotProduct, hpure, hcross, add_zero]
  have hmax : max (1 : ℕ) 1 = 1 := _root_.max_self 1
  rw [hmax] at h
  simpa only [Nat.reduceMul] using h

end LinearModelAtTwo

end CFSG.StandardType.ClassicalPosition
