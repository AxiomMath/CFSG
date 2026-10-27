module

public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcLang
import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenFrame
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore
import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ExcTwoGen

theorem isUnit_det_symmetrizedCartan_three {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) :
    IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod 3) := by
  rcases hτ with rfl | rfl
  · rw [ExcFrames.det_symmetrizedCartan_E7]
    decide
  · rw [ExcFrames.det_symmetrizedCartan_E8, Int.cast_one]
    exact isUnit_one

theorem smul_eq_neg_of_langFrame_two
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {ι₀ : Multiplicative (Fin τ.rank → ZMod 3) →* adjointGroup τ K}
    (hbase : ∀ s : Fin τ.rank → ZMod 3,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    (u : Fin τ.rank → ℤ) : w • u = -u := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hw3 := PhiTwoRootGen.torusAct_eq_neg_of_langFrame (by rw [hK])
    (isUnit_det_symmetrizedCartan_three hτ) hFr hg0 hζo hζ hbase
  have hroot : ∀ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1 := fun i =>
    PhiTwoRootGen.smul_eq_neg_of_torusAct_eq_neg hτ le_rfl hw3 (isRoot_single τ i)
  have hf : DistribSMul.toAddMonoidHom (Fin τ.rank → ℤ) w =
      -AddMonoidHom.id (Fin τ.rank → ℤ) := by
    refine AddMonoidHom.functions_ext _ _ _ fun i x => ?_
    have hx : (Pi.single i x : Fin τ.rank → ℤ) = x • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hx, map_zsmul, DistribSMul.toAddMonoidHom_apply, hroot, AddMonoidHom.neg_apply,
      AddMonoidHom.id_apply, smul_neg]
  exact DFunLike.congr_fun hf u

theorem frob_conj_baseChange_two
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (v : ModGL τ K) :
    canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
        Units.map (entrywiseHom Fr)
          (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) v * g0) *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) v * g0 := by
  rw [map_mul, map_mul, map_inv, hg0, units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr v]
  group

end ExcTwoGen

end CFSG.StandardType
