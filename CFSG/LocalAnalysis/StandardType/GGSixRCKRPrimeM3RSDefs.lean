module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSL

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

@[expose] noncomputable def rckBlockRSMat {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {K : Type} [Field K] [Algebra F K] {k : ℕ} {e : Matrix ι ι F}
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e))]
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (x : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    Matrix ι ι F :=
  LinearMap.toMatrix' ((LinearMap.id - Matrix.mulVecLin e) +
    (LinearMap.range (Matrix.mulVecLin e)).subtype ∘ₗ
      ((Matrix.toLin b b x).restrictScalars F) ∘ₗ
      (Matrix.mulVecLin e).rangeRestrict)

@[expose] def RCKBlockCoord {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (e : Matrix ι ι F) (K : Type) [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K) : Prop :=
  Function.Surjective π ∧
    (∀ (a : Algebra.adjoin F (Units.val '' S))
      (w : (LinearMap.range (Matrix.mulVecLin e))),
      ((π a • w : (LinearMap.range (Matrix.mulVecLin e))) : ι → F) =
        (a : Matrix ι ι F).mulVec w) ∧
    Nat.card K = Nat.card F ^ blockDegree (Algebra.adjoin F (Units.val '' S)) e

private lemma rckBlockAction {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {e : Matrix ι ι F}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin F (Units.val '' S)) :
    ∃ actA : Algebra.adjoin F (Units.val '' S) →ₐ[F]
        Module.End F (LinearMap.range (Matrix.mulVecLin e)),
      ∀ (a : Algebra.adjoin F (Units.val '' S))
        (w : LinearMap.range (Matrix.mulVecLin e)),
        (actA a w : ι → F) = (a : Matrix ι ι F).mulVec w := by
  classical
  let A := Algebra.adjoin F (Units.val '' S)
  let W : Submodule F (ι → F) := LinearMap.range (Matrix.mulVecLin e)
  have hpair : (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ _
    exact (hS s hs s' hs').map (Units.coeHom (Matrix ι ι F))
  letI : CommRing A := Algebra.adjoinCommRingOfComm F (s := Units.val '' S) hpair
  have hcomm : ∀ a : A, (a : Matrix ι ι F) * e = e * (a : Matrix ι ι F) := by
    intro a
    exact congrArg Subtype.val (mul_comm a (⟨e, heA⟩ : A))
  let actA : A →ₐ[F] Module.End F W :=
  { toFun := fun a =>
      ((Matrix.mulVecLin (a : Matrix ι ι F)).comp W.subtype).codRestrict W
        (fun v => by
          rw [LinearMap.comp_apply, Submodule.coe_subtype]
          obtain ⟨u, hu⟩ := v.2
          rw [← hu]
          refine ⟨Matrix.mulVec (a : Matrix ι ι F) u, ?_⟩
          calc Matrix.mulVecLin e (Matrix.mulVec (a : Matrix ι ι F) u)
              = Matrix.mulVec e (Matrix.mulVec (a : Matrix ι ι F) u) := rfl
            _ = Matrix.mulVec (e * (a : Matrix ι ι F)) u :=
                  Matrix.mulVec_mulVec u e (a : Matrix ι ι F)
            _ = Matrix.mulVec ((a : Matrix ι ι F) * e) u := by rw [hcomm a]
            _ = Matrix.mulVec (a : Matrix ι ι F) (Matrix.mulVec e u) :=
                  (Matrix.mulVec_mulVec u (a : Matrix ι ι F) e).symm
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
      rw [show algebraMap F (ι → F) c = fun _ => c from rfl,
        Matrix.diagonal_const_mulVec] }
  exact ⟨actA, fun _ _ => rfl⟩

private lemma rckBlockKModule {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {e : Matrix ι ι F}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin F (Units.val '' S))
    (K : Type) [Field K] [Algebra F K]
    (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ a, π a = 0 ↔ (a : Matrix ι ι F) * e = 0) :
    ∃ (_ : Module K (LinearMap.range (Matrix.mulVecLin e)))
      (_ : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e))),
      ∀ (a : Algebra.adjoin F (Units.val '' S))
        (w : LinearMap.range (Matrix.mulVecLin e)),
        ((π a • w : LinearMap.range (Matrix.mulVecLin e)) : ι → F) =
          (a : Matrix ι ι F).mulVec w := by
  classical
  let A := Algebra.adjoin F (Units.val '' S)
  let W : Submodule F (ι → F) := LinearMap.range (Matrix.mulVecLin e)
  obtain ⟨actA, hact⟩ := rckBlockAction hS heA
  have hker : RingHom.ker (π : A →+* K) ≤ RingHom.ker (actA : A →+* Module.End F W) := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have hae : (a : Matrix ι ι F) * e = 0 := (hπker a).mp ha
    refine LinearMap.ext fun w => Subtype.ext ?_
    change (actA a w : ι → F) = 0
    rw [hact a w]
    obtain ⟨v, hv⟩ := w.2
    rw [← hv, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec v (a : Matrix ι ι F) e, hae, Matrix.zero_mulVec]
  have hp : Function.Surjective (π : A →+* K) := fun k => hπsurj k
  let ψ : K →+* Module.End F W :=
    (Ideal.Quotient.lift (RingHom.ker (π : A →+* K)) (actA : A →+* Module.End F W)
      (fun a ha => RingHom.mem_ker.mp (hker ha))).comp
      (RingHom.quotientKerEquivOfSurjective (f := (π : A →+* K)) hp).symm.toRingHom
  have hψ : ∀ a : A, ψ (π a) = actA a := fun a => by
    change (Ideal.Quotient.lift (RingHom.ker (π : A →+* K)) (actA : A →+* Module.End F W)
      (fun a ha => RingHom.mem_ker.mp (hker ha)))
      ((RingHom.quotientKerEquivOfSurjective (f := (π : A →+* K)) hp).symm
        ((π : A →+* K) a)) = actA a
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    rfl
  letI : Module K W := Module.compHom W ψ
  have htower : IsScalarTower F K W :=
    ⟨fun c k w => by
      change (ψ (c • k)) w = c • ((ψ k) w)
      obtain ⟨a, rfl⟩ := hπsurj k
      rw [← map_smul π c a, hψ (c • a), hψ a, map_smul]
      rfl⟩
  exact ⟨Module.compHom W ψ, htower, fun a w => by
    change (ψ (π a) w : ι → F) = (a : Matrix ι ι F).mulVec w
    rw [hψ a]
    exact hact a w⟩

theorem rckBlockCoord_exists {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] (S : Set (GL ι F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra F K)
      (_ : Module K (LinearMap.range (Matrix.mulVecLin e)))
      (_ : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)))
      (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K),
      RCKBlockCoord S e K π := by
  obtain ⟨K, hKfield, hKalg, hKfin, π, hsurj, hker, hdeg⟩ := exists_blockField hS hodd he
  letI : Field K := hKfield
  letI : Algebra F K := hKalg
  letI : Finite K := hKfin
  obtain ⟨hKmod, hKtower, hact⟩ := rckBlockKModule hS he.1 K π hsurj hker
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) := hKmod
  letI : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)) := hKtower
  refine ⟨K, hKfield, hKfin, hKalg, hKmod, hKtower, π, hsurj, hact, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := F) (V := K), hdeg]

end CFSG.StandardType.RCKRP
