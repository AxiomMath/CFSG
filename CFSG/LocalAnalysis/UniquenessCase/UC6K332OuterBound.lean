module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderFamilies
import CFSG.LocalAnalysis.UniquenessCase.UC6K332OuterArith
import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (OuterRow outerRow_of_fixed_card_dvd)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator (OuterFixedOrderBoundAt)

theorem center_eq_bot_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : Subgroup.center T = ⊥) : Subgroup.center S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx z]
  rw [h, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.2 (e.injective (by rw [hex, map_one]))

theorem outerRow_of_bound {t : StatedLieTag} {n : ℕ} (hB : OuterFixedOrderBoundAt t)
    (ht : t ≠ .Tits) (htr : t ≠ .trialityD4) (ho : t ≠ .POmegaPlus) {S : Type} [Group S]
    [Finite S] {ℓ f : ℕ} (hadm : StatedLieAdmissible t n ℓ f) (hM : LieModel S t n ℓ f)
    (hZ : Subgroup.center S = ⊥) (hD : ¬ 3 ∣ lieOrderDivisor t n (ℓ ^ f))
    (hcard : Nat.card S * lieOrderDivisor t n (ℓ ^ f) = lieOrderNumerator t n (ℓ ^ f))
    (hpos : ∀ x, 2 ≤ x → 0 < lieOrderNumerator t n x)
    (harith : ∀ x, 3 * lieOrderNumerator t n x ∣ lieOrderNumerator t n (x ^ 3)) : OuterRow S := by
  refine outerRow_of_fixed_card_dvd hZ fun σ hσ hout => ?_
  rcases hB S n ℓ f hadm hM ht 3 Nat.prime_three (by decide) hD (fun h => ho h.1) σ hσ hout with
    ⟨f₀, rfl, hdvd⟩ | ⟨h1, -⟩
  · have hf0 : 1 ≤ f₀ := by
      have := hadm.2.1
      omega
    have hq2 : 2 ≤ ℓ ^ f₀ :=
      (hadm.1.two_le).trans (Nat.le_self_pow (by omega) ℓ)
    have hpow : ℓ ^ (3 * f₀) = (ℓ ^ f₀) ^ 3 := by rw [mul_comm, pow_mul]
    rw [hpow] at hcard hD
    obtain ⟨M, hCM, h3M⟩ := exists_mul_three_dvd (hpos _ hq2) hdvd
      (Subgroup.card_subgroup_dvd_card _) (by rw [hcard]; exact harith _) hD
    exact ⟨fixedSubgroup σ, M, fun x => Iff.rfl, hCM, h3M⟩
  · exact absurd h1 htr

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
