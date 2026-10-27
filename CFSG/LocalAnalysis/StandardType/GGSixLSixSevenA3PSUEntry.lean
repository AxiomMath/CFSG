module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ExcRank
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag
public import CFSG.LocalAnalysis.StandardType.UnitaryA3Contradiction
public import CFSG.LocalAnalysis.StandardType.UnitaryTwoLocalRankLower

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits

section Holds


theorem ggSixLSixSevenConjA3At_PSU : GGSixLSixSevenConjA3At .PSU := by
  intro G _ _ p B Bs x L D J n f ψ hctx _ _ _ hA
  exfalso
  obtain ⟨-, hf, hn, hnq⟩ := hctx.2.2.2.1.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hrk : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn4 : 4 ≤ n := by omega
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  obtain ⟨hp3, hm⟩ := hctx.twoLocalRank_eq_four_of_a3 ggLNoncyclicInput_holds hA
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hp : p.Prime := hctx.prime
  subst hp3
  have hrank := UnitaryRank.n_le_of_largeEvenTwoLocalRank_eq_four hF hf hn4 ψ hker hm
  have hcen : ¬ 3 ∣ Nat.card (Subgroup.centralizer (ψ.range : Set G)) := by
    rw [hrange]
    exact not_dvd_card_centralizer_ggG0_of_stdSub hp hctx.sstar hctx.stdType hctx.stdSub
  have hJψ : J ≤ ψ.range := by
    rw [hrange]
    exact hctx.le_ggG0
  have hinner : ∀ b ∈ D, ∃ A : GL (Fin n) (GaloisField 2 (2 * (f + 1))),
      (b, A) ∈ UFusion.suInducedPairs ψ := by
    intro b hb
    obtain ⟨A, hA, hAc⟩ := InnerDiagSU.suInnerDiagConj hF hn4 G ψ hker b⁻¹
      (hctx.2.2.2.2.2.2.1.2 b⁻¹ (Bs.inv_mem (hctx.d_le_bstar hb)))
    refine ⟨A, hA, fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  exact UnitaryA3.false_of_a3_unitary hF hf hn4 hrank hker hcen hctx.d_elem hctx.card_d hJψ
    (hctx.alternating_eight_quotient hA) hctx.le_centralizer_J hinner

end Holds

end CFSG.StandardType
