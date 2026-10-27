module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType.KG82

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem mem_zpowers_sup_of_mem_sup_zpowers {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] {p : ℕ} [Fact p.Prime] {φ₀ a φ : G} (ha : a ∈ N ⊔ Subgroup.zpowers φ₀)
    (hφ : φ ∈ N ⊔ Subgroup.zpowers φ₀) (hap : a ^ p ∈ N) (hφp : φ ^ p ∈ N) (hna : a ∉ N) :
    φ ∈ Subgroup.zpowers a ⊔ N := by
  obtain ⟨π, hπ⟩ : ∃ π : G →* G ⧸ N, π = QuotientGroup.mk' N := ⟨_, rfl⟩
  have hker : ∀ g, π g = 1 ↔ g ∈ N := fun g => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hle : N ⊔ Subgroup.zpowers φ₀ ≤ (Subgroup.zpowers (π φ₀)).comap π := by
    refine sup_le (fun x hx => ?_) ?_
    · rw [Subgroup.mem_comap, (hker x).2 hx]
      exact one_mem _
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      exact Subgroup.mem_zpowers _
  have hpow : ∀ {g : G}, g ^ p ∈ N → π g ^ p = 1 := fun hg => by
    rw [← map_pow]
    exact (hker _).2 hg
  have hord : ∀ {g : G} (hg : g ∈ N ⊔ Subgroup.zpowers φ₀), g ^ p ∈ N → g ∉ N →
      orderOf (⟨π g, hle hg⟩ : Subgroup.zpowers (π φ₀)) = p := fun hg hgp hgN =>
    orderOf_eq_prime (Subtype.ext (hpow hgp)) fun h => hgN ((hker _).1 (congrArg Subtype.val h))
  have hmem : (⟨π φ, hle hφ⟩ : Subgroup.zpowers (π φ₀)) ∈
      Subgroup.zpowers (⟨π a, hle ha⟩ : Subgroup.zpowers (π φ₀)) := by
    by_cases hφN : φ ∈ N
    · have e : (⟨π φ, hle hφ⟩ : Subgroup.zpowers (π φ₀)) = 1 := Subtype.ext ((hker φ).2 hφN)
      rw [e]
      exact one_mem _
    · have e : Subgroup.zpowers (⟨π φ, hle hφ⟩ : Subgroup.zpowers (π φ₀)) =
          Subgroup.zpowers ⟨π a, hle ha⟩ := by
        rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
          hord ha hap hna, hord hφ hφp hφN]
      rw [← e]
      exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : π (a ^ k) = π φ := by
    rw [map_zpow]
    exact congrArg Subtype.val hk
  have hN : (a ^ k)⁻¹ * φ ∈ N := by
    rw [← hker, map_mul, map_inv, hk', inv_mul_cancel]
  rw [← mul_inv_cancel_left (a ^ k) φ]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers a k))
    (Subgroup.mem_sup_right hN)

variable {n : ℕ} {K : Type} [Field K] [Finite K]


theorem ggOutdiagCyclic_recipe
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGOutdiagCyclic (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
  ggOutdiagCyclic_of_diagCyclicInput (TableB.TwE6.ggDiagCyclicInput_of_diagCyclicOn
    ((TableB.TwE6.diagCyclicOn_isRoot hn hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm))

theorem mem_zpowers_sup_inn_of_mem_recipeI
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {a : MulAut (TwE6Delta.RecipeR K n)} (ha : a ∈ TwE6Delta.RecipeI K n)
    (hna : a ∉ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range)
    {φ : MulAut (TwE6Delta.RecipeR K n)} (hφ : φ ∈ TwE6Delta.RecipeI K n) :
    φ ∈ Subgroup.zpowers a ⊔
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range := by
  have := TwE6Delta.finite_mulAut_recipeR hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ₀, hφ₀⟩ := ggOutdiagCyclic_recipe hn hK
  exact mem_zpowers_sup_of_mem_sup_zpowers (p := 3) (hφ₀ ha) (hφ₀ hφ)
    (TwE6Delta.pow_three_mem_inn hn hK ha) (TwE6Delta.pow_three_mem_inn hn hK hφ) hna

end CFSG.StandardType.KG82
