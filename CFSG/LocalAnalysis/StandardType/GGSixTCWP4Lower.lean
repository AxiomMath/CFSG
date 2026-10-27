module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open
open CFSG.Blueprint.Chevalley (Tag)

section Transfer

variable {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

theorem GGTCHyp.pow_le_card_of_torusLift
    {ψ : (ggU t n f).K →* X}
    (h : GGTCHyp t n f ψ p G₀ B D J L x) {r : ℕ} {R : Type} [Group R]
    (θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R) (hT : GGTorusLift p r R) : p ^ r ≤ Nat.card B := by
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, -⟩ := hT G₀ (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) h.perfect
  have hU' : U.map G₀.subtype ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ G₀.subtype_injective]
    exact hU
  have hEN : E.map G₀.subtype ≤ Subgroup.normalizer ((U.map G₀.subtype : Subgroup X) : Set X) :=
    (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)
  have key := h.rank_le (E.map G₀.subtype) (U.map G₀.subtype) hU' (hU2.map _)
    (hE.map G₀.subtype) hEN
  rwa [Subgroup.card_map_of_injective G₀.subtype_injective, hEcard] at key

end Transfer

section Leaves

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

private theorem charP_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])

private theorem exists_recipe_equiv
    {G : Type} [Group G] {τ : Tag} {f : ℕ}
    (h : UntwistedChevalleyModel G τ (2 ^ f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (G ≃* TableBExc.RecipeGroup τ K) := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, hF, hfin, this, hK,
    ⟨e.trans (Classical.choice (centerQuot_chevGroup_equiv K τ)).symm⟩⟩

private theorem dvd_two_pow_sub_one {p f : ℕ} (hp : p.Prime)
    (hc : orderOf ((2 : ZMod p) ^ f) = 1) : p ∣ 2 ^ f - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (2 : ZMod p) ^ f = 1 := orderOf_eq_one_iff.mp hc
  have hle : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hle]
  simp [h1]

private theorem dvd_two_pow_add_one {p f : ℕ} (hp : p.Prime)
    (hc : orderOf ((2 : ZMod p) ^ f) = 2) : p ∣ 2 ^ f + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsq : ((2 : ZMod p) ^ f) ^ 2 = 1 := by
    rw [← hc]
    exact pow_orderOf_eq_one _
  have hne : (2 : ZMod p) ^ f ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc
    omega
  have hm : (2 : ZMod p) ^ f = -1 := by
    rcases mul_self_eq_one_iff.mp (by rwa [sq] at hsq) with h1 | h1
    · exact absurd h1 hne
    · exact h1
  rw [← ZMod.natCast_eq_zero_iff]
  simp [hm]

theorem lower_E7_one
    {ψ : (ggU .E7 n f).K →* X} (h : GGTCHyp .E7 n f ψ p G₀ B D J L x)
    (hc : orderOf ((2 : ZMod p) ^ f) = 1) : p ^ 7 ≤ Nat.card B := by
  obtain ⟨K, _, _, _, hK, ⟨θ⟩⟩ := exists_recipe_equiv
    (h.model.chevalleyExceptionalModel (by decide)).2
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact dvd_two_pow_sub_one h.prime hc
  exact h.pow_le_card_of_torusLift θ (TableBExc.ggTorusLift_E7 h.prime h.ne_two hpq)

theorem lower_E7_two
    {ψ : (ggU .E7 n f).K →* X} (h : GGTCHyp .E7 n f ψ p G₀ B D J L x)
    (hc : orderOf ((2 : ZMod p) ^ f) = 2) : p ^ 6 ≤ Nat.card B := by
  obtain ⟨K, _, _, _, hK, ⟨θ⟩⟩ := exists_recipe_equiv
    (h.model.chevalleyExceptionalModel (by decide)).2
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact dvd_two_pow_add_one h.prime hc
  exact h.pow_le_card_of_torusLift θ (ggTorusLift_E7Plus h.prime h.ne_two hpq)

theorem lower_E8_one
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hc : orderOf ((2 : ZMod p) ^ f) = 1) : p ^ 8 ≤ Nat.card B := by
  obtain ⟨K, _, _, _, hK, ⟨θ⟩⟩ := exists_recipe_equiv
    (h.model.chevalleyExceptionalModel (by decide)).2
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact dvd_two_pow_sub_one h.prime hc
  exact h.pow_le_card_of_torusLift θ (TableBExc.ggTorusLift_E8 h.prime h.ne_two hpq)

theorem lower_E8_two
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hc : orderOf ((2 : ZMod p) ^ f) = 2) : p ^ 7 ≤ Nat.card B := by
  obtain ⟨K, _, _, _, hK, ⟨θ⟩⟩ := exists_recipe_equiv
    (h.model.chevalleyExceptionalModel (by decide)).2
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact dvd_two_pow_add_one h.prime hc
  exact h.pow_le_card_of_torusLift θ (ggTorusLift_E8Plus h.prime h.ne_two hpq)

theorem lower_E6_one
    {ψ : (ggU .E6 n f).K →* X} (h : GGTCHyp .E6 n f ψ p G₀ B D J L x)
    (hc : orderOf ((2 : ZMod p) ^ f) = 1) : p ^ 5 ≤ Nat.card B := by
  obtain ⟨K, _, _, _, hK, ⟨θ⟩⟩ := exists_recipe_equiv
    (h.model.chevalleyExceptionalModel (by decide)).2
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact dvd_two_pow_sub_one h.prime hc
  by_cases hp3 : p = 3
  · subst hp3
    exact h.pow_le_card_of_torusLift θ (TableBExc.ggTorusLift_E6_three hpq)
  · have h6 := h.pow_le_card_of_torusLift θ
      (TableBExc.ggTorusLift_E6 h.prime h.ne_two hp3 hpq)
    exact le_trans (Nat.pow_le_pow_right h.prime.pos (by norm_num)) h6

end Leaves

end CFSG.StandardType.TableCRes

end
