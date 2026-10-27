module

public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.RankThree.PartTwo.Sec12.Item124Bar

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem exists_fixed_mem_coset_pCoreOf {X L : Subgroup G} (hX : IsPGroup 3 X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) {l : G}
    (hl : ∀ x ∈ X, l⁻¹ * (x * l * x⁻¹) ∈ CFSG.Open.pCoreOf 2 L) :
    ∃ n ∈ CFSG.Open.pCoreOf 2 L, ∀ x ∈ X, x * (l * n) * x⁻¹ = l * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 L) := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  refine Sec12.exists_fixed_mem_coset hX hN3 l fun x hx n hn => ?_
  have hxK : x ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hXL hx)
  refine ⟨l⁻¹ * (x * l * x⁻¹) * (x * n * x⁻¹),
    Subgroup.mul_mem _ (hl x hx) ((Subgroup.mem_normalizer_iff.mp hxK n).mp hn), by group⟩

theorem Hyp1921.le_M_of_rank_two_of (h : Hyp1921 G A M N L)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hO2M : CFSG.Open.pCoreOf 2 L ≤ M)
    {X : Subgroup G} (hXA : X ≤ A) (hX2 : 2 ≤ CFSG.Open.pRank 3 X)
    (hXc : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) : L ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA3 : IsPGroup 3 A := (isE27_of_mem_partTwoE h.mem_partTwoE).isPGroup
  have hAN : A ≤ N := h.mem_scriptM_N.2
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := hXA.trans (hAN.trans hNL)
  intro l hl
  have hlK : l ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset_pCoreOf (hA3.to_le hXA) hXN (l := l)
    fun x hx => by
      have h1 := hXc x hx l hl
      have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hlK) _).mp h1
      simpa [mul_assoc] using h2
  have hlnM : l * n ∈ M := by
    have hc : l * n ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := hfix g hg
      calc g * (l * n) = g * (l * n) * g⁻¹ * g := by group
        _ = l * n * g := by rw [this]
    exact h.mem_scriptM.2 (normalizer_le_gamma hXA hX2 (Subgroup.centralizer_le_normalizer _ hc))
  have hnM : n ∈ M := hO2M hn
  simpa using M.mul_mem hlnM (M.inv_mem hnM)

end CFSG.RankThree.PartTwo.Late
