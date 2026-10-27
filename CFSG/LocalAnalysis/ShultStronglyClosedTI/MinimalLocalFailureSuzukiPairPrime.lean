module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPairPrimeDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPairPrimeSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCoprimePrime

public section

namespace CFSG.ShultStronglyClosedTI.SuzukiPairPrime

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_unique {P W : Subgroup G} (hWP : W ≤ P) (hW3 : Nat.card W = 3)
    (huniq : ∀ W' : Subgroup G, W' ≤ P ∧ Nat.card W' = 3 → W' = W) {r : G}
    (hr : r ∈ Subgroup.normalizer (P : Set G)) : r ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply huniq
  refine ⟨?_, by rw [Subgroup.card_map_of_injective (MulAut.conj r).injective, hW3]⟩
  rintro _ ⟨w, hw, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hr w).mp (hWP hw)

theorem suzuki_pair_prime_sylow
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hreg : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      RegularComplementConclusion H z beta t u)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* CFSG.Blueprint.suzukiGroup m k))
    {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 -
      Nat.card (minimalLocalFailurePairActionPointHull H z) + 1)
    (hpB : p ∣ Nat.card (pairPointStabilizer H beta)) {P : Subgroup G}
    (hPB : P ≤ pairPointStabilizer H beta) (hPp : IsPGroup p P)
    (hPcard : Nat.card P = p ^ (Nat.card (pairPointStabilizer H beta)).factorization p) :
    Nat.card (minimalLocalFailurePairActionPointHull H z) = 8 ∧ p = 3 ∧ Nat.card P = 3 := by
  set B := pairPointStabilizer H beta
  set K := minimalLocalFailureProperPairHull H z beta t
  set Q := minimalLocalFailurePairActionPointHull H z
  let : Fact p.Prime := ⟨hp⟩
  have hSz' := hSz
  obtain ⟨m, k, _, _, hk, hkQ, -⟩ := hSz'
  have hQe : Nat.card Q = 2 ^ (2 * m + 1) := hkQ.symm.trans hk
  obtain ⟨-, hSzpart⟩ :=
    CoprimePrime.minimalLocalFailure_coprime_pair_prime_semilinear_action_of_conclusions
      h hcomm hsmallerR1 hbeta ht hproper hBinv hreg hQe
  obtain ⟨hpK, hPall⟩ := hSzpart hSz p hp hpN
  obtain ⟨hdeg, hidxHB⟩ :=
    suzuki_pair_degree h hcomm hsmallerR1 hbeta ht hproper hBinv hexcl hreg hSz
  have hp2 : p ≠ 2 := by
    rintro rfl
    apply hpK
    have hzK : z ∈ K := Subgroup.subset_closure (Or.inl (Or.inl rfl))
    have h2 := orderOf_dvd_natCard (⟨z, hzK⟩ : K)
    rwa [Subgroup.orderOf_mk, h.local_datum.distinguished_order] at h2
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hpidx : p ∣ B.relIndex H := by
    rw [hidxHB, hdeg]
    exact Dvd.dvd.mul_left hpN _
  have hlt := factorization_lt_of_dvd_relIndex hp hBH hpidx
  have hPH : P ≤ H := hPB.trans hBH
  have hv : 0 < (Nat.card B).factorization p :=
    hp.factorization_pos_of_dvd Nat.card_pos.ne' hpB
  have hP1 : P ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hPcard] at h1
    have := Nat.pow_right_injective hp.two_le (h1.trans (pow_zero p).symm)
    omega
  have hnotH : Nat.card P ≠ p ^ (Nat.card H).factorization p := by
    rw [hPcard]
    intro heq
    have := Nat.pow_right_injective hp.two_le heq
    omega
  obtain ⟨-, -, hdvd, hCP, hfix, hthree⟩ := hPall P hPB hPp hP1
  have hC2 : Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 2 := by
    by_contra hne
    have hge : 4 ≤ Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := by
      have hpos : 1 ≤ (2 * m + 1) / Nat.card P :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) Nat.card_pos
      have hne1 : (2 * m + 1) / Nat.card P ≠ 1 := by
        intro h1
        rw [hCP, h1, pow_one] at hne
        exact hne rfl
      rw [hCP]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ ((2 * m + 1) / Nat.card P) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨-, ⟨n, hn⟩, -⟩ := CoprimePrime.minimalLocalFailure_coprime_prime_local_pair_index
      h hcomm hsmallerR1 hbeta ht hproper hp hpK hPB hPp hP1 hge
    have h1 := card_eq_pow_factorization_of_le hp (le_inf hPB (Subgroup.le_normalizer))
      inf_le_left hPcard
    rw [factorization_eq_of_two_power_relIndex hp hp2 (inf_le_inf_right _ hBH) hn] at h1
    exact hnotH (card_eq_pow_factorization_of_normalizer hPH hPp h1)
  obtain ⟨hp3, a, ha1, hPa, -, hQa, ⟨W, ⟨hWP, hW3⟩, hWuniq⟩, hWfix⟩ := hthree hC2
  subst hp3
  have ha : a = 1 := by
    by_contra hne
    have ha2 : 2 ≤ a := by omega
    obtain ⟨hCW, -⟩ := hWfix W hWP hW3
    have hge : 4 ≤ Nat.card (Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) := by
      rw [hCW]
      have h3 : 3 ≤ 3 ^ (a - 1) := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ 3 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) h3
    have hWB : W ≤ B := hWP.trans hPB
    have hWp : IsPGroup 3 W := hPp.to_le hWP
    have hW1 : W ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hW3
      omega
    obtain ⟨-, -, ⟨n, hn⟩⟩ := CoprimePrime.minimalLocalFailure_coprime_prime_local_pair_index
      h hcomm hsmallerR1 hbeta ht hproper hp hpK hWB hWp hW1 hge
    have hcyc : IsCyclic P := (hPall P hPB hPp hP1).2.1
    have hPCW : P ≤ Subgroup.centralizer (W : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val (mul_comm' (⟨w, hWP hw⟩ : P) ⟨x, hx⟩)
    have h1 := card_eq_pow_factorization_of_le hp (le_inf hPB hPCW) inf_le_left hPcard
    rw [factorization_eq_of_two_power_relIndex hp hp2 (inf_le_inf_right _ hBH) hn] at h1
    set V := H ⊓ Subgroup.normalizer (P : Set G)
    have hPV : P ≤ V := le_inf hPH Subgroup.le_normalizer
    obtain ⟨R, hR⟩ := (hPp.comap_subtype (K := V)).exists_le_sylow
    set R' := (R : Subgroup V).map V.subtype
    have hPR' : P ≤ R' := by
      intro x hx
      exact ⟨⟨x, hPV hx⟩, hR hx, rfl⟩
    have hR'CW : R' ≤ H ⊓ Subgroup.centralizer (W : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨n', hn'⟩ := R.isPGroup' ⟨r, hr⟩
      have hrn : (r : G) ^ 3 ^ n' = 1 := by
        simpa using congrArg (fun x : (R : Subgroup V) => ((x : V) : G)) hn'
      exact ⟨r.2.1, mem_centralizer_of_card_three hW3
        (mem_normalizer_of_unique hWP hW3 (fun W' hW' => hWuniq W' hW') r.2.2) hrn⟩
    have hR'card : Nat.card R' = 3 ^ (Nat.card V).factorization 3 := by
      rw [Subgroup.card_map_of_injective V.subtype_injective, R.card_eq_multiplicity]
    have hle1 : Nat.card P ≤ Nat.card R' := Subgroup.card_le_of_le hPR'
    have hle2 : (Nat.card V).factorization 3 ≤
        (Nat.card (H ⊓ Subgroup.centralizer (W : Set G) : Subgroup G)).factorization 3 := by
      rw [← Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne', ← hR'card]
      exact Subgroup.card_dvd_of_le hR'CW
    have hle3 : Nat.card R' ≤ Nat.card P := by
      rw [hR'card, h1]
      exact Nat.pow_le_pow_right (by norm_num) hle2
    have h3 : Nat.card P = 3 ^ (Nat.card V).factorization 3 := by
      rw [← hR'card]
      omega
    exact hnotH (card_eq_pow_factorization_of_normalizer hPH hPp h3)
  subst ha
  exact ⟨by rw [hQa]; norm_num, rfl, by rw [hPa, pow_one]⟩

theorem minimalLocalFailure_suzuki_pair_prime_exception_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hreg : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      RegularComplementConclusion H z beta t u)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* CFSG.Blueprint.suzukiGroup m k)) :
    let B := pairPointStabilizer H beta
    let Q := minimalLocalFailurePairActionPointHull H z
    let N := Nat.card Q ^ 2 - Nat.card Q + 1
    (∀ p : ℕ, p.Prime → p ∣ N → p ∣ Nat.card B →
      Nat.card Q = 8 ∧ p = 3 ∧ ∀ S : Sylow p B, IsCyclic S ∧ Nat.card S = 3) ∧
    Nat.card (rightCosetSpace H) - 1 = Nat.card Q ^ 3 * N ∧
    (Nat.card Q ≠ 8 → Nat.Coprime (Nat.card B) N) ∧
    (Nat.card Q = 8 → ∀ p : ℕ, p.Prime → p ∣ N → p ∣ Nat.card B → p = 3) := by
  intro B Q N
  have hmain : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ Nat.card B →
      Nat.card Q = 8 ∧ p = 3 ∧ ∀ S : Sylow p B, IsCyclic S ∧ Nat.card S = 3 := by
    intro p hp hpN hpB
    let : Fact p.Prime := ⟨hp⟩
    have hsyl : ∀ S : Sylow p B, Nat.card Q = 8 ∧ p = 3 ∧ Nat.card S = 3 := fun S => by
      rw [← Subgroup.card_map_of_injective B.subtype_injective]
      exact suzuki_pair_prime_sylow h hcomm hsmallerR1 hbeta ht hproper hBinv hexcl hreg hSz hp
        hpN hpB (Subgroup.map_subtype_le _) (S.isPGroup'.map B.subtype)
        (by rw [Subgroup.card_map_of_injective B.subtype_injective, S.card_eq_multiplicity])
    obtain ⟨hq8, hp3, -⟩ := hsyl default
    refine ⟨hq8, hp3, fun S => ?_⟩
    have hS := (hsyl S).2.2
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact ⟨isCyclic_of_prime_card hS, hS⟩
  obtain ⟨hdeg, -⟩ := suzuki_pair_degree h hcomm hsmallerR1 hbeta ht hproper hBinv hexcl hreg hSz
  refine ⟨hmain, hdeg, fun hq8 => Nat.coprime_of_dvd fun p hp hpB hpN =>
    hq8 (hmain p hp hpN hpB).1, fun _ p hp hpN hpB => (hmain p hp hpN hpB).2.1⟩

end CFSG.ShultStronglyClosedTI.SuzukiPairPrime
