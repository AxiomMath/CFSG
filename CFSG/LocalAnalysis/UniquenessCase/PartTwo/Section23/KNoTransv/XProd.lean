module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveEquiv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

theorem quotient_center_of_isOmegaPlus_four {X : Type} [Group X] {k : ℕ}
    (hX : IsOmegaPlus X 4 k) (hk : 2 ≤ k) :
    ∃ (S₀ : Type) (_ : Group S₀), IsSimpleGroup S₀ ∧ Nat.card S₀ = ordA 1 (2 ^ k) ∧
      Nonempty ((X ⧸ center X) ≃* S₀ × S₀) := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hX
  letI := hKf
  letI := hKfin
  haveI hKchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hadm : StatedLieAdmissible .PSL 2 2 k := by
    refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩
    · intro h3
      have h2 := congrArg Prod.snd h3
      omega
    · intro h3
      have h2 := congrArg Prod.snd h3
      omega
  have hSC : StatedClassicalModel ↥(StatedSL 2 K) .PSL 2 2 k :=
    ⟨hadm, K, hKf, hKfin, hKcard, ⟨(statedProjStatedSLTwoEquiv K).symm⟩⟩
  have hSimple : IsSimpleGroup ↥(StatedSL 2 K) :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hSC
  have hCard : Nat.card ↥(StatedSL 2 K) = ordA 1 (2 ^ k) := by
    have h := (CFSG.Timmesfeld.card_statedClassicalModel_two hSC).1 rfl
    simpa using h
  obtain ⟨eΩ⟩ := nonempty_statedOmegaFour_mulEquiv_prod (K := K) h4
  have eX : X ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K) :=
    (e.trans (statedProjStatedOmegaFourEquiv K)).trans eΩ
  have hCenterSL : Subgroup.center ↥(StatedSL 2 K) = ⊥ := by
    have hmap := Subgroup.map_center_eq
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
    rw [s16c13bcA_center_sl2, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hCenterProd : Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) = ⊥ := by
    rw [Subgroup.center_prod, hCenterSL, Subgroup.bot_prod_bot]
  have hCenterX : Subgroup.center X = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz' : eX z ∈ Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := eX.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hCenterProd, Subgroup.mem_bot] at hz'
    exact eX.injective (by rw [hz', map_one])
  refine ⟨↥(StatedSL 2 K), inferInstance, hSimple, hCard, ?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hCenterX).trans
    (QuotientGroup.quotientBot.trans eX)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
