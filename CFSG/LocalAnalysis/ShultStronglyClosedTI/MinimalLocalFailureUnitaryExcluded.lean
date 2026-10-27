module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedConstruct

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G] [Finite G]

theorem degree_injective {q i j : ℕ} (hq : 2 ≤ q)
    (h : (q ^ i + 1) * (q ^ i * (q - 1) + 1) = (q ^ j + 1) * (q ^ j * (q - 1) + 1)) :
    i = j := by
  have hmono : StrictMono (fun x : ℕ => (x + 1) * (x * (q - 1) + 1)) := by
    intro a b hab
    have h2 : a * (q - 1) + 1 ≤ b * (q - 1) + 1 := by
      have := Nat.mul_le_mul_right (q - 1) hab.le
      omega
    calc (a + 1) * (a * (q - 1) + 1) < (b + 1) * (a * (q - 1) + 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ (b + 1) * (b * (q - 1) + 1) := Nat.mul_le_mul_left _ h2
  exact Nat.pow_right_injective hq (hmono.injective h)

theorem exists_sylow_central_involution {B : Subgroup G} {u₀ : G} (hu₀ : u₀ ∈ B)
    (hu₀2 : orderOf u₀ = 2) :
    ∃ P : Subgroup G, P ≤ B ∧ IsPGroup 2 P ∧ ¬ 2 ∣ P.relIndex B ∧
      ∃ u ∈ P, orderOf u = 2 ∧ P ≤ Subgroup.centralizer {u} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y : B := ⟨u₀, hu₀⟩
  have hy : orderOf y = 2 := by rw [← Subgroup.orderOf_coe]; exact hu₀2
  have hy2 : y ^ 2 ^ 1 = 1 := by rw [pow_one, ← hy, pow_orderOf_eq_one]
  obtain ⟨S, hS⟩ := (isPGroup_zpowers hy2).exists_le_sylow
  have hyS : y ∈ (S : Subgroup B) := hS (Subgroup.mem_zpowers y)
  have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hy; omega
  have : Nontrivial (S : Subgroup B) :=
    ⟨⟨⟨y, hyS⟩, 1, fun h1 => hy1 (congrArg Subtype.val h1)⟩⟩
  have hZ : Nontrivial (Subgroup.center (S : Subgroup B)) := S.isPGroup'.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := ((S.isPGroup'.to_subgroup _).nontrivial_iff_card).mp hZ
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (S : Subgroup B)) 2
    (by rw [hcard]; exact dvd_pow_self 2 (by omega))
  refine ⟨(S : Subgroup B).map B.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_,
    (((c : S) : B) : G), ⟨(c : S), (c : S).2, rfl⟩, ?_, ?_⟩
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective]
    exact S.not_dvd_index
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  · rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_center_iff.mp c.2 ⟨s, hs⟩
    exact congrArg (fun x : (S : Subgroup B) => ((x : B) : G)) h

theorem minimalLocalFailure_pair_involution_unitary_fixed_model_excluded_of_hulls
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hhull : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      Nat.card (rightFixedSet H u) =
        Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1 →
      UnitaryFixedHullsConclusion H z beta t u) :
    let q := Nat.card (minimalLocalFailurePairActionPointHull H z)
    (∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      Nat.card (rightFixedSet H u) ≠ q ^ 3 + 1) ∧
    ∃ i : ℕ, (i = 1 ∨ i = 2) ∧ ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      Nat.card (rightFixedSet H u) = q ^ i + 1 ∧
        Nat.card (rightCosetSpace H) = (q ^ i + 1) * (q ^ i * (q - 1) + 1) := by
  intro q
  have h75 := pairInvolutionCentralizesConclusion h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, hQ4, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have hq2 : 2 ≤ q := by omega
  have hno3 : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      Nat.card (rightCosetSpace H) ≠ (q ^ 3 + 1) * (q ^ 3 * (q - 1) + 1) := by
    intro u₀ hu₀ hu₀2 hn3
    obtain ⟨P, hPB, hP2, hPidx, u, huP, hu2, hPu⟩ := exists_sylow_central_involution hu₀ hu₀2
    have huB := hPB huP
    obtain ⟨-, -, i, -, hfixi, hdegi⟩ := h75 u huB hu2
    have hi3 : i = 3 := degree_injective hq2 (hdegi.symm.trans hn3)
    subst hi3
    exact false_of_hulls h hcomm hsmallerR1 hbeta ht hproper huB hu2 hfixi hPB hP2 hPidx huP hPu
      (hhull u huB hu2 hfixi)
  have hper : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 → ∃ i : ℕ, (i = 1 ∨ i = 2) ∧
      Nat.card (rightFixedSet H u) = q ^ i + 1 ∧
        Nat.card (rightCosetSpace H) = (q ^ i + 1) * (q ^ i * (q - 1) + 1) := by
    intro u hu hu2
    obtain ⟨-, -, i, hi, hfixi, hdegi⟩ := h75 u hu hu2
    rcases hi with rfl | rfl | rfl
    · exact ⟨1, Or.inl rfl, hfixi, hdegi⟩
    · exact ⟨2, Or.inr rfl, hfixi, hdegi⟩
    · exact absurd hdegi (hno3 u hu hu2)
  refine ⟨fun u hu hu2 hfix3 => ?_, ?_⟩
  · obtain ⟨i, hi, hfixi, -⟩ := hper u hu hu2
    have hi3 := Nat.pow_right_injective hq2 (Nat.add_right_cancel (hfixi.symm.trans hfix3))
    rcases hi with hi | hi <;> rw [hi] at hi3 <;> exact absurd hi3 (by decide)
  · by_cases hex : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2
    · obtain ⟨u₁, hu₁, hu₁2⟩ := hex
      obtain ⟨i, hi, -, hdeg₁⟩ := hper u₁ hu₁ hu₁2
      refine ⟨i, hi, fun u hu hu2 => ?_⟩
      obtain ⟨j, -, hfixj, hdegj⟩ := hper u hu hu2
      obtain rfl : j = i := degree_injective hq2 (hdegj.symm.trans hdeg₁)
      exact ⟨hfixj, hdegj⟩
    · push Not at hex
      exact ⟨1, Or.inl rfl, fun u hu hu2 => absurd hu2 (hex u hu)⟩

end CFSG.ShultStronglyClosedTI.UnitaryExcluded

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G] [Finite G]

theorem unitaryFixedModelExcludedConclusion_of_hulls
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hhull : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      Nat.card (rightFixedSet H u) =
        Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1 →
      UnitaryFixedHullsConclusion H z beta t u) :
    ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u := by
  obtain ⟨-, i, hi, hall⟩ :=
    UnitaryExcluded.minimalLocalFailure_pair_involution_unitary_fixed_model_excluded_of_hulls h
      hcomm hsmallerR1 hbeta ht hproper hhull
  intro u hu hu2
  exact ⟨i, hi, (hall u hu hu2).1, (hall u hu hu2).2⟩

end CFSG.ShultStronglyClosedTI.ProperPairModel
