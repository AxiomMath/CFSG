module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47PGLMat

public section

open Polynomial Module

namespace CFSG.StandardType

namespace SpNS

theorem linearMap_eq_mul_one_of_commute_root
    {K : Type} [Field K] {g : K[X]}
    (T : AdjoinRoot g →ₗ[K] AdjoinRoot g)
    (hT : ∀ u, T (AdjoinRoot.root g * u) = AdjoinRoot.root g * T u) :
    ∀ u, T u = T 1 * u := by
  intro u
  refine AdjoinRoot.induction_on (f := g) (C := fun u => T u = T 1 * u) u ?_
  intro P
  rw [← AdjoinRoot.aeval_eq]
  induction P using Polynomial.induction_on with
  | C c =>
      rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, map_smul]
      simp only [Algebra.smul_def, mul_one]; ring
  | add P Q hP hQ => simp only [map_add]; rw [hP, hQ]; ring
  | monomial n c ih =>
      have e1 : aeval (AdjoinRoot.root g) (Polynomial.C c * Polynomial.X ^ (n + 1)) =
          AdjoinRoot.root g * aeval (AdjoinRoot.root g) (Polynomial.C c * Polynomial.X ^ n) := by
        simp only [map_mul, map_pow, aeval_X, aeval_C, pow_succ]; ring
      rw [e1, hT, ih, ← mul_assoc]; ring

theorem card_adjoinRoot_eq_four
    {K : Type} [Field K] [Finite K] [CharP K 2] {g : K[X]} [Fact (Irreducible g)]
    (hK : Nat.card K = 2) (hgd : g ∣ cyclotomic 3 K) : Nat.card (AdjoinRoot g) = 4 := by
  have hp : (3 : ℕ).Prime := by norm_num
  have hp2 : 3 ≠ 2 := by norm_num
  have hpK : (3 : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  have hdimL : Module.finrank K (AdjoinRoot g) = 2 := by
    rw [(CoordSL.rootPB g).finrank, rootPB_dim_eq_two hp hp2 hpK hgd hpq]
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have h := Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot g)
  rw [h, hK, hdimL]; norm_num

theorem adjoinRoot_pow_three_eq_one
    {K : Type} [Field K] [Finite K] [CharP K 2] {g : K[X]} [Fact (Irreducible g)]
    (hK : Nat.card K = 2) (hgd : g ∣ cyclotomic 3 K) {x : AdjoinRoot g} (hx : x ≠ 0) :
    x ^ 3 = 1 := by
  have h := GH74.GLS.Stage2.Signalizer.Odd87.P47PGL.cube_eq_one_of_card_four
    (card_adjoinRoot_eq_four hK hgd) (Units.mk0 x hx)
  simpa using congrArg Units.val h

end SpNS

end CFSG.StandardType
