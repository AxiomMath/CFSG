module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619OrthFixed
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619OrthMoving

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615
open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

theorem orthDerivedModelAction_holds {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hV : 8 ≤ Module.finrank F V) :
    ClassicalModelAction ↥(orthDerived Q) := by
  intro x hx1 hx3 C hC hlab y hxy hyC
  have hx : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (orderOf x) hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h3
  have hCop : CFSG.Open.IsComponentOf C
      (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open C
      (Subgroup.centralizer ({x} : Set ↥(orthDerived Q)))).mp hC
  rcases CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.comp_cases_orthDerived_of_prime
      hQ Nat.prime_three (by norm_num) hx hCop with
    ⟨h, hh, hne, hq, hLC⟩ | ⟨G, hGq, hGle, hGn, hGdim, hLC⟩
  · exact orthMovingBlock_action hQ hV hx hh hne hq hLC hlab hxy hyC
  · exact orthFixedBlock_action hQ hV hx hGq hGle hGn hGdim hLC hlab hxy hyC

end S2MathAs3_1619Final

end
