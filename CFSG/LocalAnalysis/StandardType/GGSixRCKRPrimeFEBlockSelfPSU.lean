module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.LieType.Universal
open scoped Matrix

theorem exists_blockAction_selfDual_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {S : Set (GL (Fin n) F)}
    (hSU : ∀ s ∈ S, Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 f)
      (s : Matrix (Fin n) (Fin n) F) * Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) F) =
      Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hadj : formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) e = e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e)
    (hnt : ⁅glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S e,
      glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S e⁆ ≠ ⊥) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
      (W : Type) (_ : AddCommGroup W) (_ : Module F W) (_ : Module K W)
      (_ : IsScalarTower F K W) (_ : FiniteDimensional K W)
      (σ : K ≃+* K) (β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K)
      (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
      (φ : ↥(glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S e) →*
          (W ≃ₗ[K] W)),
      Nat.card K = (2 ^ (f * blockDegree (Algebra.adjoin F (Units.val '' S)) e)) ^ 2 ∧
      σ ^ 2 = 1 ∧ σ ≠ 1 ∧ β.IsSymm ∧ β.SeparatingLeft ∧ Function.Injective φ ∧
      (∀ g w w', β (φ g w) (φ g w') = β w w') ∧
      (∀ g : W ≃ₗ[K] W, (∀ w w', β (g w) (g w') = β w w') →
        LinearMap.det (g : W →ₗ[K] W) = 1 → g ∈ φ.range) ∧
      ∀ g w, (eW (φ g w) : Fin n → F) =
        (((g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
          GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (eW w : Fin n → F) := by
  classical
  let A : Subalgebra F (Matrix (Fin n) (Fin n) F) := Algebra.adjoin F (Units.val '' S)
  let d : ℕ := blockDegree A e
  have hε : IsPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) A e :=
    ⟨he.1, he.2.1, he.2.2.1, hadj,
      fun e' he' hidem _ he'e => he.2.2.2 e' he' hidem he'e⟩
  obtain ⟨K, hKfield, hKalg, hKfin, π, hπsurj, hπker, -, hKcard⟩ :=
    fePSU_blockField_card hc S hS hodd he d rfl
  letI : Field K := hKfield
  letI : Algebra F K := hKalg
  letI : Finite K := hKfin
  haveI : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap F K) 2 (by norm_num)
  have hKcard' : Nat.card K = ((2 ^ f) ^ d) ^ 2 := by
    rw [hKcard, ← pow_mul (2 ^ f) d 2, Nat.mul_comm 2 d]
  obtain ⟨hmod, hfin, htower, act, hact, hactm, hactπ⟩ :=
    fePSU_selfDual_blockHeldSUid_action S hS he K π hπsurj hπker
  letI : Module K (LinearMap.range (Matrix.mulVecLin e)) := hmod
  letI : FiniteDimensional K (LinearMap.range (Matrix.mulVecLin e)) := hfin
  letI : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)) := htower
  have hdim := fePSU_selfDual_blockHeldSUid_dim S K act hact hnt
  have hadjmem : ∀ a : A, formAdj (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
      (Unitary.antidiag n) (a : Matrix (Fin n) (Fin n) F) ∈ A := by
    intro a
    have hG : IsUnit (Unitary.antidiag n).det :=
      isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero (F := F) n)
    have hSU' : ∀ s ∈ S, Matrix.transpose
        ((s : Matrix (Fin n) (Fin n) F).map
          (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom) * Unitary.antidiag n *
          (s : Matrix (Fin n) (Fin n) F) = Unitary.antidiag n := by
      intro s hs
      simpa [Unitary.conjTr] using hSU s hs
    exact Geo.formAdj_mem_adjoin
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom hG hSU' a.2
  have hadj' := fePSU_selfDual_blockHeldSUid_hadj hc S hS hε d K hKcard'
    π hπsurj hπker hactπ hadjmem
  have hunitF := fePSU_selfDual_blockFormDescent_actInvariant S K act hactm
  have hbar :=
    fePSU_selfDual_blockFormDescent_involution hc S hSU hS hodd hε he d rfl K
  have hBsF := fePSU_selfDual_blockFormF_isSymm (f := f) hc e
  have hBlF := fePSU_selfDual_blockFormF_separatingLeft hc hε.2.2.2.1 hε.2.1
  obtain ⟨B, hBs, hBl, hBt⟩ :=
    fePSU_selfDual_blockFormDescent_trace hc S d rfl hdeg K hKcard'
      (fePSU_selfDual_blockFormF (f := f) e) hBsF hBlF hbar hadj'
  have hunit :=
    fePSU_selfDual_blockFormDescent_unitary S d K act
      (fePSU_selfDual_blockFormF (f := f) e) B hBt hunitF
  have hsurj := fePSU_selfDual_blockHeldSUid_surj hc S hS hε he d rfl hdeg K hKcard' act B
    hBs hBl hdim hactm hBt π hactπ
  have hKcard'' : Nat.card K = (2 ^ (f * d)) ^ 2 := by
    rw [hKcard', ← pow_mul 2 f d]
  have hσ2 : (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)) ^ 2 = 1 := by
    ext x
    change CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d)
      (CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) x) = x
    exact CFSG.LieType.BorelTits.unitaryInvolution_involutive hKcard'' x
  have hσne : CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d) ≠ 1 :=
    fePSU_unitaryInvolution_ne_one hKcard'
  let eW : (LinearMap.range (Matrix.mulVecLin e)) ≃ₗ[F] LinearMap.range (Matrix.toLin' e) :=
    LinearEquiv.ofEq _ _ (by rw [Matrix.toLin'_apply'])
  let φ : ↥(glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S e) →*
        ((LinearMap.range (Matrix.mulVecLin e)) ≃ₗ[K] (LinearMap.range (Matrix.mulVecLin e))) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K
      (LinearMap.range (Matrix.mulVecLin e))).toMonoidHom.comp act
  have hinj : Function.Injective φ := by
    have h1 : Function.Injective act := fePSU_selfDual_blockKAction_faithful S K act hactm
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K
      (LinearMap.range (Matrix.mulVecLin e))).injective.comp h1
  have hisom : ∀ g w w', B (φ g w) (φ g w') = B w w' := by
    intro g w w'
    simpa [φ] using
      (CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup.mp (hunit g)) w w'
  have hdet : ∀ g : (LinearMap.range (Matrix.mulVecLin e)) ≃ₗ[K]
      (LinearMap.range (Matrix.mulVecLin e)),
      (∀ w w', B (g w) (g w') = B w w') →
      LinearMap.det (g : (LinearMap.range (Matrix.mulVecLin e)) →ₗ[K]
        (LinearMap.range (Matrix.mulVecLin e))) = 1 → g ∈ φ.range := by
    intro g hg hgdet
    have hgg : LinearMap.GeneralLinearGroup.ofLinearEquiv g ∈
        CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B := by
      rw [CFSG.LocalAnalysis.ComponentInitial.mem_sesqSpecialUnitaryGroup,
        CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
      exact ⟨fun x y => hg x y, hgdet⟩
    let G : Subgroup ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) :=
      glBlockCentralizer
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype S e
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (hsurj hgg)
    have hu' : act (Subgroup.inclusion (Subgroup.commutator_le_self G) u) =
        LinearMap.GeneralLinearGroup.ofLinearEquiv g := hu
    have hsymm : LinearMap.GeneralLinearGroup.generalLinearEquiv K
        (LinearMap.range (Matrix.mulVecLin e))
        (LinearMap.GeneralLinearGroup.ofLinearEquiv g) = g :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K
        (LinearMap.range (Matrix.mulVecLin e))).apply_symm_apply g
    refine MonoidHom.mem_range.mpr
      ⟨Subgroup.inclusion (Subgroup.commutator_le_self G) u, ?_⟩
    change LinearMap.GeneralLinearGroup.generalLinearEquiv K
      (LinearMap.range (Matrix.mulVecLin e))
      (act (Subgroup.inclusion (Subgroup.commutator_le_self G) u)) = g
    rw [hu']
    exact hsymm
  have hactfinal : ∀ g w, (eW (φ g w) : Fin n → F) =
      (((g : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (eW w : Fin n → F) := by
    intro g w
    simpa [φ, eW] using hactm g w
  exact ⟨K, hKfield, hKalg, hKfin, LinearMap.range (Matrix.mulVecLin e), inferInstance,
    inferInstance, hmod, htower, hfin, CFSG.LieType.BorelTits.unitaryInvolution K 2 (f * d), B,
    eW, φ, hKcard'', hσ2, hσne, hBs, hBl, hinj, hisom, hdet, hactfinal⟩

end CFSG.StandardType.ClassicalPosition
