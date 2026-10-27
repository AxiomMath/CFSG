module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpRank
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaSec
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType

theorem pumpUpSymplecticRankInput_holds : PumpUpSymplecticRankInput := by
  intro K _ _ W Wk ζ ξ Q A h r hr hmodel
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hmodel
  · obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := hcl
    have hK₀2 : Nat.card K₀ = 2 := by rw [hK₀, pow_one]
    letI : Fintype K₀ := Fintype.ofFinite K₀
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K₀ 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK₀2])
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    exact h.false_of_ggTorusLift e (by omega) (TwoThree.ggTorusLift_sp_two (K := K₀) (k := k) hK₀2)
  · omega

theorem pumpUpOrthogonalRankInput_holds :
    PumpUpOrthogonalRankInput := by
  intro K _ _ W Wk ζ ξ Q A h r hr hmodel
  rcases hmodel with ⟨-, hcl | ⟨h0, -⟩⟩ | ⟨-, hcl | ⟨h0, -⟩⟩
  · obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := hcl
    have hK₀2 : Nat.card K₀ = 2 := by rw [hK₀, pow_one]
    exact h.false_of_ggTorusLift e (by omega)
      (ggOrthRestTorusLiftInput_holds.2 K₀ r hK₀2 (by omega))
  · omega
  · obtain ⟨-, K₀, _, _, hK₀, b, c, hirr, ⟨e⟩⟩ := hcl
    have hK₀2 : Nat.card K₀ = 2 := by rw [hK₀, pow_one]
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have hT := ggOrthRestTorusLiftInput_holds.1 K₀ 1 m 3 b c hK₀ (by omega) Nat.prime_three
      (by norm_num) hirr
    have hS : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (H : Subgroup (GL ι K₀)),
        (StatedScalars ι K₀).subgroupOf H = ⊥ := fun {ι} _ _ H => by
      rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK₀2, Subgroup.bot_subgroupOf]
    let eR : StatedProj (StatedOmega (StatedQuadMinus (m + 1) K₀ b c)) ≃*
        OrthRest.RMinus K₀ m b c :=
      ((((QuotientGroup.quotientMulEquivOfEq (hS _)).trans QuotientGroup.quotientBot).trans
        (LayerCyc.largeEvenOmegaMinusEquiv m K₀ b c).symm).trans
        ((QuotientGroup.quotientMulEquivOfEq (hS _)).trans QuotientGroup.quotientBot).symm)
    exact h.false_of_ggTorusLift e (by omega) (TableBF4.ggTorusLift_of_mulEquiv eR hT)
  · omega

theorem pumpUpUnitaryRankInput_holds :
    PumpUpUnitaryRankInput := by
  intro K _ _ W Wk ζ ξ Q A h n hn hmodel
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hmodel
  · obtain ⟨-, K₁, _, _, hK₁, ⟨e⟩⟩ := hcl
    have hT := ggTorusLift_unitary (K := K₁) (n := 1) (d := n) (p := 3) hK₁ le_rfl (by omega)
      (by intro h; simp only [Prod.mk.injEq] at h; omega) Nat.prime_three (by norm_num)
    refine h.false_of_ggTorusLift e ?_ hT
    unfold ggUnitaryTorusRank
    split_ifs <;> omega
  · omega

end CFSG.GGQ2Prime
