module

public import CFSG.RankThree.PartOne.KE.SuzukiLangSp4Group
public import CFSG.RankThree.PartOne.KE.SuzukiLangSp4Aut
public import CFSG.LieType.AlgebraicGroups.TwistedOrbitSurjectivity
public import CFSG.LieType.AlgebraicGroups.G2ExceptionalComorphism
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix WithConv Bialgebra CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

open scoped CFSG.ConvolutionPoints

section Setup

variable (k : Type) [Field k] [IsAlgClosed k] [CharP k 2]

abbrev SpCoord : Type := GLCoord k (Fin 4) ⧸ subgroupIdeal (glPointSubgroup (antiSp k))

theorem isConnectedAlgebraicSubgroup_antiSp :
    IsConnectedAlgebraicSubgroup k (glPointSubgroup (antiSp k)) :=
  (antiSp_algebraic_group_connected_smooth k).2.1

instance smooth_spCoord : Algebra.Smooth k (SpCoord k) :=
  (antiSp_algebraic_group_connected_smooth k).2.2.1

instance isDomain_spCoord : IsDomain (SpCoord k) :=
  (isConnectedAlgebraicSubgroup_antiSp k).isDomain

instance connectedSpace_spCoord : ConnectedSpace (PrimeSpectrum (SpCoord k)) :=
  (isConnectedAlgebraicSubgroup_antiSp k).connectedSpace

abbrev spProj : GLCoord k (Fin 4) →ₐ[k] SpCoord k := Ideal.Quotient.mkₐ k _

structure SpPointData where
  e : WithConv (SpCoord k →ₐ[k] k) ≃* antiSp k
  he : ∀ φ, ((e φ : antiSp k) : GL (Fin 4) k) =
    glPointEquiv.symm (toConv (φ.ofConv.comp (spProj k)))

theorem nonempty_spPointData : Nonempty (SpPointData k) :=
  (antiSp_algebraic_group_connected_smooth k).2.2.2.2.elim fun e he => ⟨⟨e, he⟩⟩

end Setup

section Matrix

theorem exteriorSquareMinor_map {R S : Type} [CommRing R] [CommRing S] {F : Type*} [FunLike F R S]
    [RingHomClass F R S] (f : F) (M : Matrix (Fin 4) (Fin 4) R) :
    (CFSG.LinearAlgebra.exteriorSquareMinor M).map f =
      CFSG.LinearAlgebra.exteriorSquareMinor (M.map f) := by
  ext a b
  simp only [Matrix.map_apply, CFSG.LinearAlgebra.exteriorSquareMinor_apply, map_sub, map_mul]

variable {k : Type} [Field k] [IsAlgClosed k] [CharP k 2]

variable (k) in
@[expose] def spEntryMatrix : Matrix (Fin 4) (Fin 4) (SpCoord k) :=
  (glEntryMatrix k (Fin 4)).map (spProj k)

variable (k) in
@[expose] def suzukiMatrix (b : ℕ) : Matrix (Fin 4) (Fin 4) (SpCoord k) :=
  (CFSG.LinearAlgebra.exteriorSquareMinor (spEntryMatrix k)).map fun x => x ^ 2 ^ b

omit [CharP k 2] in
theorem glMat_spPointData (D : SpPointData k) (φ : WithConv (SpCoord k →ₐ[k] k)) :
    glMat ((D.e φ : antiSp k) : GL (Fin 4) k) = (spEntryMatrix k).map φ.ofConv := by
  ext i j
  rw [D.he φ, glMat_glPointEquiv_symm_apply]
  rfl

theorem suzukiMatrix_map (D : SpPointData k) (b : ℕ) (y : WithConv (SpCoord k →ₐ[k] k)) :
    (suzukiMatrix k b).map y.ofConv = glMat (suzukiMap k b (D.e y) : GL (Fin 4) k) := by
  rw [glMat_suzukiMap, glMat_spPointData D y]
  ext i j
  have h := congrFun (congrFun (exteriorSquareMinor_map y.ofConv (spEntryMatrix k)) i) j
  simp only [Matrix.map_apply] at h ⊢
  rw [suzukiMatrix, Matrix.map_apply, map_pow, h]

theorem det_suzukiMatrix (D : SpPointData k) (b : ℕ) : (suzukiMatrix k b).det = 1 := by
  refine sub_eq_zero.1 (eq_zero_of_forall_algHom k (SpCoord k) _ fun y => ?_)
  rw [map_sub, AlgHom.map_det, map_one]
  have h : (suzukiMatrix k b).map y = glMat (suzukiMap k b (D.e (toConv y)) : GL (Fin 4) k) :=
    suzukiMatrix_map D b (toConv y)
  change ((suzukiMatrix k b).map y).det - 1 = 0
  rw [h, det_glMat_eq_one k (suzukiMap k b (D.e (toConv y))).2, sub_self]

end Matrix

section Comorphism

variable {k : Type} [Field k] [IsAlgClosed k] [CharP k 2]

@[expose] def suzukiLift (D : SpPointData k) (b : ℕ) : GLCoord k (Fin 4) →ₐ[k] SpCoord k :=
  glLiftOne (suzukiMatrix k b) (det_suzukiMatrix D b)

theorem glPointEquiv_symm_comp_suzukiLift (D : SpPointData k) (b : ℕ)
    (z : SpCoord k →ₐ[k] k) :
    glPointEquiv.symm (toConv (z.comp (suzukiLift D b))) =
      (suzukiMap k b (D.e (toConv z)) : GL (Fin 4) k) :=
  Units.ext ((glMat_glPointEquiv_symm_comp_glLiftOne _ (det_suzukiMatrix D b) z).trans
    (suzukiMatrix_map D b (toConv z)))

theorem comp_suzukiLift_mem (D : SpPointData k) (b : ℕ) (z : SpCoord k →ₐ[k] k) :
    z.comp (suzukiLift D b) ∈ subgroupPoints (glPointSubgroup (antiSp k)) :=
  Subgroup.mem_map.2 ⟨_, (suzukiMap k b (D.e (toConv z))).2,
    (glPointEquiv.eq_symm_apply.1 (glPointEquiv_symm_comp_suzukiLift D b z).symm)⟩

@[expose] def sigmaAlg (D : SpPointData k) (b : ℕ) : SpCoord k →ₐ[k] SpCoord k :=
  liftOfPoints (subgroupPoints (glPointSubgroup (antiSp k))) (suzukiLift D b)
    (comp_suzukiLift_mem D b)

theorem sigmaAlg_comp_spProj (D : SpPointData k) (b : ℕ) :
    (sigmaAlg D b).comp (spProj k) = suzukiLift D b :=
  liftOfPoints_comp_mkₐ _ _ _

theorem e_comp_sigmaAlg (D : SpPointData k) (b : ℕ) (y : WithConv (SpCoord k →ₐ[k] k)) :
    D.e (toConv (y.ofConv.comp (sigmaAlg D b))) = suzukiMap k b (D.e y) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have h1 := glMat_spPointData D (toConv (y.ofConv.comp (sigmaAlg D b)))
  have h2 := suzukiMatrix_map D b y
  have h3 := congrFun (congrFun h1 i) j
  have h4 := congrFun (congrFun h2 i) j
  refine h3.trans (Eq.trans ?_ h4)
  simp only [Matrix.map_apply, AlgHom.comp_apply]
  congr 1
  exact DFunLike.congr_fun (sigmaAlg_comp_spProj D b) (glEntry k (Fin 4) i j) |>.trans
    (glLiftOne_glEntry _ _ i j)

theorem sigmaAlg_pointMul (D : SpPointData k) (b : ℕ) (y z : WithConv (SpCoord k →ₐ[k] k)) :
    toConv ((y * z).ofConv.comp (sigmaAlg D b)) =
      toConv (y.ofConv.comp (sigmaAlg D b)) * toConv (z.ofConv.comp (sigmaAlg D b)) := by
  apply D.e.injective
  simp only [e_comp_sigmaAlg, map_mul]

@[expose] def sigmaHom (D : SpPointData k) (b : ℕ) : SpCoord k →ₐc[k] SpCoord k :=
  bialgHomOfPointMul (sigmaAlg D b) (sigmaAlg_pointMul D b)

theorem e_pointMap_sigmaHom (D : SpPointData k) (b : ℕ) (φ : WithConv (SpCoord k →ₐ[k] k)) :
    D.e (pointMap (sigmaHom D b) φ) = suzukiMap k b (D.e φ) :=
  e_comp_sigmaAlg D b φ

end Comorphism

section Tangent

variable {k : Type} [Field k] [IsAlgClosed k] [CharP k 2]

theorem sigmaAlg_sq_comp_spProj (D : SpPointData k) (b : ℕ) :
    ((sigmaAlg D b) ^ 2).comp (spProj k) = (spProj k).comp (frobCo 2 (2 * b + 1)) := by
  refine (exceptional_Lang_affine_point_and_product_geometry k).2.2.2.2.1 (SpCoord k)
    (GLCoord k (Fin 4)) _ _ fun x => ?_
  apply toConv_injective
  apply glPointEquiv.symm.injective
  have hsq : (sigmaAlg D b) ^ 2 = (sigmaAlg D b).comp (sigmaAlg D b) :=
    (sq _).trans (algHom_mul_eq_comp _ _)
  have hL : glPointEquiv.symm (toConv (x.comp (((sigmaAlg D b) ^ 2).comp (spProj k)))) =
      (suzukiMap k b (suzukiMap k b (D.e (toConv x))) : GL (Fin 4) k) := by
    have h0 : D.e (toConv (x.comp (sigmaAlg D b))) = suzukiMap k b (D.e (toConv x)) :=
      e_comp_sigmaAlg D b (toConv x)
    have h1 : D.e (toConv ((x.comp (sigmaAlg D b)).comp (sigmaAlg D b))) =
        suzukiMap k b (D.e (toConv (x.comp (sigmaAlg D b)))) :=
      e_comp_sigmaAlg D b (toConv (x.comp (sigmaAlg D b)))
    rw [h0] at h1
    have h2 := D.he (toConv ((x.comp (sigmaAlg D b)).comp (sigmaAlg D b)))
    rw [h1] at h2
    rw [hsq]
    exact h2.symm
  have hR : glPointEquiv.symm (toConv (x.comp ((spProj k).comp (frobCo 2 (2 * b + 1))))) =
      (frobPow k (2 * b + 1) (D.e (toConv x)) : GL (Fin 4) k) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h := congrFun (congrFun (glMat_spPointData D (toConv x)) i) j
    change glMat (glPointEquiv.symm (toConv (x.comp ((spProj k).comp
      (frobCo 2 (2 * b + 1)))))) i j =
        (glMat ((D.e (toConv x) : antiSp k) : GL (Fin 4) k) i j) ^ 2 ^ (2 * b + 1)
    rw [h, glMat_glPointEquiv_symm_apply]
    simp only [AlgHom.comp_apply, frobCo_glEntry, map_pow]
    rfl
  rw [hL, hR, suzukiMap_comp_self]

theorem sigmaAlg_tangent (D : SpPointData k) (b : ℕ) :
    ∀ T ∈ tangentSpace k (SpCoord k) (counitAlgHom k (SpCoord k)),
      T ∘ₗ ((sigmaHom D b : SpCoord k →ₐ[k] SpCoord k) ^ 2).toLinearMap = 0 := by
  intro T hT
  have hT' : T ∘ₗ (spProj k).toLinearMap ∈ tangentSpace k (GLCoord k (Fin 4))
      ((counitAlgHom k (SpCoord k)).comp (spProj k)) :=
    (tangentMap (spProj k) rfl ⟨T, hT⟩).2
  have h1 := tangent_comp_frobCo 2 (e := 2 * b + 1) (by omega) hT'
  refine LinearMap.ext fun a => ?_
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ a
  have h2 := DFunLike.congr_fun (sigmaAlg_sq_comp_spProj D b) a'
  have h3 := LinearMap.congr_fun h1 a'
  simp only [AlgHom.comp_apply] at h2
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply] at h3 ⊢
  change T (((sigmaAlg D b) ^ 2) (spProj k a')) = 0
  rw [h2]
  exact h3

end Tangent

end CFSG.RankThree.PartOne.KE
