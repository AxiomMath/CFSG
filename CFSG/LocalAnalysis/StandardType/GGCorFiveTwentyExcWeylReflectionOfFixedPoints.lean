module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylRealMatrix
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflectionFormula
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Multiplicative Polynomial Matrix

variable {τ : Tag} {p : ℕ}

theorem torusAct_eq_weylMatrix_mulVec [NeZero p] (w : WeylGroup τ) (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p w x = (weylLatticeMatrix τ w).map (Int.castRingHom (ZMod p)) *ᵥ x := by
  rw [NoOffRest.torusAct_eq_sum]
  funext i
  simp [Matrix.mulVec, dotProduct, weylLatticeMatrix_apply]

theorem natCard_fix_torusMulAut_eq [NeZero p] (w : WeylGroup τ) :
    Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) // ExcWeylOuter.torusMulAut τ p w f = f} =
      Nat.card {f : Fin τ.rank → ZMod p //
        (weylLatticeMatrix τ w).map (Int.castRingHom (ZMod p)) *ᵥ f = f} := by
  refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun f => ?_)
  rw [← ofAdd_toAdd f, ExcWeylOuter.torusMulAut_apply, torusAct_eq_weylMatrix_mulVec]
  constructor
  · intro h
    simpa using congrArg toAdd h
  · intro h
    exact (congrArg ofAdd h).trans (ofAdd_toAdd f)

theorem exists_rootReflection_of_natCard_fix_torusMulAut [Fact p.Prime] (hp2 : p ≠ 2)
    (hτ : ∀ i, τ.symmetrizer i i = 1) (hr : 0 < τ.rank) {w : WeylGroup τ} (hw : w * w = 1)
    (hw1 : w ≠ 1)
    (hfix : Nat.card {f : Multiplicative (Fin τ.rank → ZMod p) //
      ExcWeylOuter.torusMulAut τ p w f = f} = p ^ (τ.rank - 1)) :
    ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ w = rootReflection β := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcard : Fintype.card (Fin τ.rank) = (τ.rank - 1) + 1 := by
    rw [Fintype.card_fin]
    omega
  have hch := charpoly_eq_of_natCard_fixed_zmod hp2 (weylLatticeMatrix τ w)
    (weylLatticeMatrix_mul_self hw) hcard
    (by rw [← natCard_fix_torusMulAut_eq]; exact hfix)
  have hdim := finrank_ker_weylLinear_add_one hw hch
  obtain ⟨x, hx, hform⟩ := exists_reflection_formula_of_finrank_ker_add_one hw hdim
  exact exists_rootReflection_of_reflection_formula hτ hw1 hx hform

end CFSG.StandardType

end
