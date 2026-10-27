module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTStable
import CFSG.LocalAnalysis.UniquenessCase.Lie.Suzuki
import CFSG.Sporadic.Schreier.TitsComponent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.LieType.Ree
open CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem borelMoves_of_surjective_sz {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {a : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (π : ↥(CFSG.Blueprint.suzukiGroup a K) ≃* ↥L)
    (hx : ∃ x : W, (∀ u v : K, ((π (suzukiSElt a K u v) : ↥L) : MulAut W) x = x) ∧
      ∃ l : Kˣ, ((π (suzukiDElt a K l) : ↥L) : MulAut W) x ≠ x) :
    ∃ S₀ : Subgroup (MulAut W), IsSylowIn 2 S₀ L ∧ BorelMoves L S₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  let U₀ : Subgroup ↥(CFSG.Blueprint.suzukiGroup a K) := suzukiU a K
  let T₀ : Subgroup ↥(CFSG.Blueprint.suzukiGroup a K) := suzukiT a K
  have hU₀ : IsSylowIn 2 U₀ ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · simpa [U₀] using (CFSG.Sporadic.Schreier.Tits.suzukiU_isSylow hK).1
    · rw [Subgroup.relIndex_top_right]
      exact (CFSG.Sporadic.Schreier.Tits.suzukiU_isSylow hK).2
  have hT₀ : Odd (Nat.card ↥T₀) := by
    have hTcard : Nat.card T₀ = 2 ^ (2 * a + 1) - 1 := by
      simpa [T₀] using (CFSG.LieType.Ree.suzuki_borel_structure hK).2.2.1
    rw [hTcard]
    have he : Even (2 ^ (2 * a + 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact Nat.Even.sub_odd Nat.one_le_two_pow he odd_one
  have hTN : T₀ ≤ Subgroup.normalizer (U₀ : Set ↥(CFSG.Blueprint.suzukiGroup a K)) := by
    simpa [T₀, U₀] using CFSG.LieType.Ree.suzukiT_le_normalizer hK
  have hN : Subgroup.normalizer (U₀ : Set ↥(CFSG.Blueprint.suzukiGroup a K)) ≤ U₀ ⊔ T₀ := by
    rw [show Subgroup.normalizer (U₀ : Set ↥(CFSG.Blueprint.suzukiGroup a K)) =
      CFSG.LieType.Ree.suzukiB a K from uc22pwr1_sz_normalizer hK]
    simp [CFSG.LieType.Ree.suzukiB, U₀, T₀]
  obtain ⟨x, hxS, l, hxD⟩ := hx
  have hx' : ∀ u ∈ U₀, ((π u : ↥L) : MulAut W) x = x := by
    intro u hu
    refine Subgroup.closure_induction (p := fun u _ => ((π u : ↥L) : MulAut W) x = x)
      ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨p, rfl⟩
      exact hxS p.1 p.2
    · rw [map_one]
      rfl
    · intro b c _ _ hb hc
      simp only [map_mul, Subgroup.coe_mul, MulAut.mul_apply]
      rw [hc, hb]
    · intro b _ hb
      rw [map_inv]
      simp only [Subgroup.coe_inv]
      exact (π b : MulAut W).injective (by rw [MulAut.apply_inv_self, hb])
  have ht : ∃ t ∈ T₀, ((π t : ↥L) : MulAut W) x ≠ x :=
    ⟨suzukiDElt a K l, suzukiDElt_mem_suzukiT a K l, hxD⟩
  exact ⟨_, borelMoves_map hW π hU₀ hT₀ hTN hN hx' ht⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
