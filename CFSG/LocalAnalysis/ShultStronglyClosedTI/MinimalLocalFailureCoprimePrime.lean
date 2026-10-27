module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCoprimePrimeFaithful
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCoprimePrimeSuzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCoprimePrimeAlgebra
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairModelAlignment

public section

namespace CFSG.ShultStronglyClosedTI.CoprimePrime

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G] [Finite G]

theorem coprime_pair_prime_action
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hembed : ∃ f : Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) →*
      minimalLocalFailureProperPairHull H z beta t, Function.Injective f)
    {e : ℕ} (hQe : Nat.card (minimalLocalFailurePairActionPointHull H z) = 2 ^ e)
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card (minimalLocalFailureProperPairHull H z beta t))
    {P : Subgroup G} (hPB : P ≤ pairPointStabilizer H beta) (hPp : IsPGroup p P) :
    let Q := minimalLocalFailurePairActionPointHull H z
    (∀ y ∈ P, Q ≤ Subgroup.centralizer ({y} : Set G) → y = 1) ∧ IsCyclic P ∧
      Nat.card P ∣ e ∧
      ∀ W : Subgroup G, W ≤ P →
        Nat.card (Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) = 2 ^ (e / Nat.card W) := by
  intro Q
  obtain ⟨hQ, hQ4, -, -, -, hXB, -, hXcyclic, -, -, hXQcard, -, -, -, hregular⟩ :=
    CyclicSemiregular.proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, hBX, hBQ, -⟩ := coprime_torus_data h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨⟨s, hs, hPs⟩, -⟩ :=
    coprime_fixed_point_and_flip h hcomm hsmallerR1 hbeta ht hproper hp hpK hPB hPp
  have hfaith := coprime_kernel_trivial h hcomm hsmallerR1 hbeta ht hproper hembed hp hpK hPB hPp
  have he : 1 ≤ e := by
    by_contra he0
    have : e = 0 := by omega
    rw [this, pow_zero] at hQe
    have hQ4' : 4 ≤ Nat.card Q := hQ4
    omega
  obtain ⟨hcyc, hdvd, hfix⟩ := frobenius_action_structure hQ hQe he
    (fun x hx => hBQ x (hXB hx)) hXcyclic hXQcard hregular
    (fun y hy => hBQ y (hPB hy)) (fun y hy => hBX y (hPB hy)) hs hPs hfaith
  exact ⟨hfaith, hcyc, hdvd, hfix⟩

theorem existsUnique_card_three {P : Subgroup G} [IsCyclic P] {a : ℕ} (ha : 1 ≤ a)
    (hP : Nat.card P = 3 ^ a) : ∃! W : Subgroup G, W ≤ P ∧ Nat.card W = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := P) 3
    (by rw [hP]; exact dvd_pow_self 3 (by omega))
  refine ⟨Subgroup.zpowers (g : G), ⟨(Subgroup.zpowers_le).mpr g.2, ?_⟩, ?_⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg]
  · rintro W ⟨hWP, hW3⟩
    have hgP : Subgroup.zpowers (g : G) ≤ P := (Subgroup.zpowers_le).mpr g.2
    have hcardg : Nat.card (Subgroup.zpowers (g : G)) = 3 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg]
    have heq : W.subgroupOf P = (Subgroup.zpowers (g : G)).subgroupOf P := by
      rw [IsCyclic.subgroup_eq_iff_card_eq,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWP).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hgP).toEquiv, hW3, hcardg]
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hWP, inf_of_le_left hgP] at heq
    exact heq

theorem minimalLocalFailure_coprime_pair_prime_semilinear_action_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hreg : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      RegularComplementConclusion H z beta t u)
    {e : ℕ} (hQe : Nat.card (minimalLocalFailurePairActionPointHull H z) = 2 ^ e) :
    let B := pairPointStabilizer H beta
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    (∀ p : ℕ, p.Prime → ¬ p ∣ Nat.card K → ∀ P : Subgroup G, P ≤ B → IsPGroup p P → P ≠ ⊥ →
      (∀ y ∈ P, Q ≤ Subgroup.centralizer ({y} : Set G) → y = 1) ∧ IsCyclic P ∧
        Nat.card P ∣ e ∧
        Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 2 ^ (e / Nat.card P) ∧
        ∀ W : Subgroup G, W ≤ P →
          Nat.card (Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) =
            2 ^ (e / Nat.card W)) ∧
    ((∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
        Nat.card k = Nat.card Q ∧ Nonempty (K ≃* CFSG.Blueprint.suzukiGroup m k)) →
      ∀ p : ℕ, p.Prime → p ∣ Nat.card Q ^ 2 - Nat.card Q + 1 →
        ¬ p ∣ Nat.card K ∧
        ∀ P : Subgroup G, P ≤ B → IsPGroup p P → P ≠ ⊥ →
          (∀ y ∈ P, Q ≤ Subgroup.centralizer ({y} : Set G) → y = 1) ∧ IsCyclic P ∧
          Nat.card P ∣ e ∧
          Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 2 ^ (e / Nat.card P) ∧
          (∀ W : Subgroup G, W ≤ P →
            Nat.card (Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) =
              2 ^ (e / Nat.card W)) ∧
          (Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 2 →
            p = 3 ∧ ∃ a : ℕ, 1 ≤ a ∧ Nat.card P = 3 ^ a ∧ e = 3 ^ a ∧ Nat.card Q = 2 ^ 3 ^ a ∧
              (∃! W : Subgroup G, W ≤ P ∧ Nat.card W = 3) ∧
              ∀ W : Subgroup G, W ≤ P → Nat.card W = 3 →
                Nat.card (Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) =
                  2 ^ 3 ^ (a - 1) ∧
                (Nat.card (Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) = 2 ↔
                  Nat.card Q = 8))) := by
  intro B K Q
  obtain ⟨u, huB, hu⟩ := hBinv
  obtain ⟨-, -, -, -, -, -, -, -, -, hembed⟩ := hreg u huB hu
  have hmain : ∀ p : ℕ, p.Prime → ¬ p ∣ Nat.card K → ∀ P : Subgroup G, P ≤ B →
      IsPGroup p P → (∀ y ∈ P, Q ≤ Subgroup.centralizer ({y} : Set G) → y = 1) ∧ IsCyclic P ∧
        Nat.card P ∣ e ∧ ∀ W : Subgroup G, W ≤ P →
          Nat.card (Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) =
            2 ^ (e / Nat.card W) :=
    fun p hp hpK P hPB hPp =>
      coprime_pair_prime_action h hcomm hsmallerR1 hbeta ht hproper hembed hQe hp hpK hPB hPp
  refine ⟨fun p hp hpK P hPB hPp _ => ?_, fun hSz p hp hpN => ?_⟩
  · obtain ⟨hfaith, hcyc, hdvd, hfix⟩ := hmain p hp hpK P hPB hPp
    exact ⟨hfaith, hcyc, hdvd, hfix P le_rfl, hfix⟩
  obtain ⟨m, k, _, _, hk, hkQ, ⟨ψ⟩⟩ := hSz
  have hKcard : Nat.card K = Nat.card Q ^ 2 * (Nat.card Q - 1) * (Nat.card Q ^ 2 + 1) := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.LieType.Ree.suzuki_order hk, ← hk, hkQ]
  have hQ1 : 1 ≤ Nat.card Q := Nat.card_pos
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hKcard]
    exact prime_not_dvd_of_dvd_suzuki_factor hQ1 hp hpN
  refine ⟨hpK, fun P hPB hPp hP1 => ?_⟩
  obtain ⟨hfaith, hcyc, hdvd, hfix⟩ := hmain p hp hpK P hPB hPp
  refine ⟨hfaith, hcyc, hdvd, hfix P le_rfl, hfix, fun hCP => ?_⟩
  have hdiv : e / Nat.card P = 1 := by
    have h2 := (hfix P le_rfl).symm.trans hCP
    exact Nat.pow_right_injective (le_refl 2) (by simpa using h2)
  have heP : e = Nat.card P := by
    obtain ⟨c, hc⟩ := hdvd
    have hPpos : 0 < Nat.card P := Nat.card_pos
    rw [hc, Nat.mul_div_cancel_left _ hPpos] at hdiv
    rw [hc, hdiv, mul_one]
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hPp.exists_card_eq
  have ha1 : 1 ≤ a := by
    by_contra ha0
    have : a = 0 := by omega
    rw [this, pow_zero] at ha
    exact hP1 (Subgroup.card_eq_one.mp ha)
  have hQpa : Nat.card Q = 2 ^ p ^ a := by rw [← ha, ← heP]; exact hQe
  have hp3 : p = 3 := prime_eq_three_of_dvd_suzuki_factor hp (hQpa ▸ hpN)
  subst hp3
  refine ⟨rfl, a, ha1, ha, heP.trans ha, hQpa, existsUnique_card_three ha1 ha,
    fun W hWP hW3 => ?_⟩
  have hdiv3 : e / 3 = 3 ^ (a - 1) := by
    rw [heP, ha]
    exact Nat.pow_div ha1 (by norm_num)
  have hW : Nat.card (Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) = 2 ^ 3 ^ (a - 1) := by
    rw [hfix W hWP, hW3, hdiv3]
  refine ⟨hW, ?_⟩
  rw [hW, hQpa]
  constructor
  · intro h2
    have h3 : 3 ^ (a - 1) = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using h2)
    have ha' : a - 1 = 0 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h3)
    have : a = 1 := by omega
    rw [this]
    norm_num
  · intro h8
    have h3 : 3 ^ a = 3 ^ 1 := Nat.pow_right_injective (le_refl 2) (by simpa using h8)
    have : a = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
    rw [this]
    norm_num

end CFSG.ShultStronglyClosedTI.CoprimePrime
