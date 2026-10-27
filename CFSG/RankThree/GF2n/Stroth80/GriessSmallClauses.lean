module

public import CFSG.RankThree.GF2n.Stroth80.GriessLinear
public import CFSG.GroupTheory.PerfectCentralSylow
public import CFSG.Quasithin.Background.P3OrthoOm4

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.GroupTheory.PerfectCover

section SL24

variable {K : Type} [Field K] [Finite K]

theorem card_statedSL_two_four (hK : Nat.card K = 4) : Nat.card (StatedSL 2 K) = 60 := by
  rw [CFSG.Open.StatedAPI.card_statedSL_two, hK]
  norm_num

theorem statedSL_two_four_clause (hGA : GriessAllModelsStatement) (hK : Nat.card K = 4)
    {E : Type} [Group E] [Finite E] (hE : Group.IsPerfect E) (π : E →* GL (Fin 2) K)
    (hrange : π.range = StatedSL 2 K) (hker : π.ker ≤ Subgroup.center E) :
    π.ker = ⊥ ∨ ∀ A : Subgroup E, A ⊓ π.ker = ⊥ → IsElemAbelian 2 A →
      (∀ e ∈ Subgroup.normalizer ((A ⊔ π.ker : Subgroup E) : Set E),
        e ∈ Subgroup.normalizer (A : Set E)) → Nat.card A < 4 := by
  have hdvd := statedSL_ker_card_dvd hGA (m := 2) (f := 2) le_rfl le_rfl (by simpa using hK) hE π
    hrange hker
  have he : exceptionalOrders .PSL 2 2 2 = (2, 1) := rfl
  rw [he] at hdvd
  have hY2 : ∀ y ∈ π.ker, y ^ 2 = 1 := fun y hy => pow_eq_one_of_mem_of_card_dvd hdvd hy
  have hm : Nat.card E = Nat.card π.ker * (2 ^ 2 * 15) := by
    rw [← Subgroup.card_ker_mul_card_range π, hrange, card_statedSL_two_four hK]
    norm_num
  have := eq_bot_or_lt_of_exponent_two hE hker hY2 hm (by norm_num)
  simpa using this

end SL24

section Omega44

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_statedOmega_plus_two_four (hK : Nat.card K = 4) :
    Nat.card (StatedOmega (StatedQuadPlus 2 K)) = 3600 := by
  obtain ⟨e⟩ := CFSG.Quasithin.G11.P3Ortho.Om4.iso_of_card K (by omega)
  rw [Nat.card_congr e.toEquiv, Nat.card_prod,
    Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv, card_statedSL_two_four hK]

theorem statedOmega_plus_four_four_clause (hK : Nat.card K = 4) {E : Type} [Group E] [Finite E]
    (hE : Group.IsPerfect E) (π : E →* GL (Fin 2 ⊕ Fin 2) K)
    (hrange : π.range = StatedOmega (StatedQuadPlus 2 K)) (hker : π.ker ≤ Subgroup.center E)
    (hexp : ∀ y ∈ π.ker, y ^ 2 = 1) :
    π.ker = ⊥ ∨ ∀ A : Subgroup E, A ⊓ π.ker = ⊥ → IsElemAbelian 2 A →
      (∀ e ∈ Subgroup.normalizer ((A ⊔ π.ker : Subgroup E) : Set E),
        e ∈ Subgroup.normalizer (A : Set E)) → Nat.card A < 16 := by
  have hm : Nat.card E = Nat.card π.ker * (2 ^ 4 * 225) := by
    rw [← Subgroup.card_ker_mul_card_range π, hrange, card_statedOmega_plus_two_four hK]
    norm_num
  have := eq_bot_or_lt_of_exponent_two hE hker hexp hm (by norm_num)
  simpa using this

end Omega44

end CFSG.RankThree.GF2n.Stroth80
