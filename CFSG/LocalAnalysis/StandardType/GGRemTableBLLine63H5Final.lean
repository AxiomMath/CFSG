module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Assembly
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5StepTwoB

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType

theorem three_pow_five_le_card_of_marking
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) {n : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn2 : 2 ≤ n)
    (hpq : 3 ∣ 2 ^ n + 1) (hL : commutator L = ⊤)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K 6))
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    3 ^ 5 ≤ Nat.card Bs := by
  by_contra hlt
  push Not at hlt
  have hz : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 → z = 1 := by
    intro z hzL hzc hz3
    by_contra hz1
    exact stepOne_of_marking hcfg hlt hK hn2 hpq hL θ hBN hBI hzL hzc hz3 hz1
  exact stepTwoB_of_marking hcfg hlt hK hn2 hpq hL θ hBN hBI hz

@[expose] def Line63StepTwoQ2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → Nat.card Bs < 3 ^ 5 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 → commutator L = ⊤ →
    ∀ θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6),
      Bs ≤ Subgroup.normalizer (L : Set G) →
      (∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      (∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 → z = 1) → False

@[expose] def Line63Q2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 → commutator L = ⊤ →
    ∀ θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6),
      Bs ≤ Subgroup.normalizer (L : Set G) →
      (∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      3 ^ 5 ≤ Nat.card Bs

theorem line63Q2_of_steps (h1 : Line63StepOneQ2) (h2 : Line63StepTwoQ2) : Line63Q2 := by
  intro G _ _ B Bs x L D J hcfg K _ _ hK hL θ hBN hBI
  by_contra hlt
  push Not at hlt
  have hz : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 → z = 1 :=
    h1 G B Bs x L D J hcfg hlt K hK hL θ hBN hBI
  exact h2 G B Bs x L D J hcfg hlt K hK hL θ hBN hBI hz

theorem ggUnitDvd63BstarRankInput_of_q2
    (h : Line63Q2) :
    GGUnitDvd63BstarRankInput := by
  intro G _ _ p B Bs x L D J hcfg hM
  have hp3 : p = 3 := prime_eq_three_of_innerDiagOnLab hM
  subst hp3
  obtain ⟨hL, n, K, _, _, hK, hn, hpq, θ, hBN, hBI⟩ := config_marking_data hM
  by_cases hn1 : n = 1
  · subst hn1
    exact h G B Bs x L D J hcfg K hK hL θ hBN hBI
  · exact three_pow_five_le_card_of_marking hcfg hK (by omega) hpq hL θ hBN hBI

end CFSG.StandardType.Line63.H5

end
