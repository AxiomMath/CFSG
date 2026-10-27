module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeAlgebra
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeLocal
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePrimeCentralizerSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeFlip
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePrimeCentralizerNormalizer

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

universe u

variable {G : Type u} [Group G] [Finite G]

theorem field_prime_core
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {e : ℕ} (hQcard : Nat.card (minimalLocalFailurePairActionPointHull H z) = 2 ^ e)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ e - 1)
    {y : G} (hyB : y ∈ pairPointStabilizer H beta) (hy : orderOf y = p)
    (hXy : ¬ rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤
      Subgroup.centralizer ({y} : Set G)) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let Q := minimalLocalFailurePairActionPointHull H z
    let Y := Subgroup.centralizer ({y} : Set G)
    let E := Q ⊓ Y
    let X₀ := X ⊓ Y
    let Δ := baseOrbit H Y
    p ∣ e ∧ 4 ≤ 2 ^ (e / p) ∧ p ∣ 2 ^ (e / p) - 1 ∧ Nat.card E = 2 ^ (e / p) ∧
      IsCyclic X₀ ∧ Nat.card X₀ = 2 ^ (e / p) - 1 ∧
      (∀ a ∈ (E : Set G) \ {1}, ∀ b ∈ (E : Set G) \ {1},
        ∃! x : X₀, (x : G)⁻¹ * a * x = b) ∧
      (∃ ty ∈ (fun x => t * x) '' (X : Set G), Commute ty y ∧
        ty ∈ rightPairFlipFiber H z beta ∧
        rightCosetTranslate H beta ty = rightCosetMk H 1) ∧
      Y < ⊤ ∧ ¬ Y ≤ H ∧
      rightCosetMk H 1 ∈ Δ ∧ beta ∈ Δ ∧
      Δ ⊆ {omega | rightCosetTranslate H omega y = omega} ∧
      (∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
        ∃ g ∈ Y, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d) ∧
      (∀ P : Sylow p (B ⊓ Y : Subgroup G), ∃ S : Sylow p Y,
        (S : Subgroup Y).map Y.subtype =
          (P : Subgroup (B ⊓ Y : Subgroup G)).map (B ⊓ Y).subtype) ∧
      (∀ r ∈ E, r ≠ 1 → involutionPointClass z ∩ (Y : Set G) = conjugacyWithin Y r) ∧
      (∀ S : Sylow p Y, ∃ lam ∈ Δ, ∃ mu ∈ Δ, lam ≠ mu ∧
        pointFixedSet H ((S : Subgroup Y).map Y.subtype) ∩ Δ = {lam, mu}) := by
  intro B X Q Y E X₀ Δ
  obtain ⟨hQ, hQ4, hQclass, -, hQnorm, hXB, hXnormal, hXcyclic, -, -, hXQcard, -,
    hfiber, -, hregular⟩ := proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  have hyH : y ∈ H := pairPointStabilizer_le_point H beta hyB
  have he : 1 ≤ e := by
    by_contra he0
    have he' : e = 0 := by omega
    rw [he', pow_zero] at hQcard
    omega
  have hXQ : ∀ x ∈ X, ∀ v ∈ Q, x⁻¹ * v * x ∈ Q :=
    fun x hx => hQnorm x (pairPointStabilizer_le_point H beta (hXB hx))
  have hyQ : ∀ v ∈ Q, y⁻¹ * v * y ∈ Q := hQnorm y hyH
  have hyX : ∀ x ∈ X, y⁻¹ * x * y ∈ X := by
    intro x hx
    have hmem := hXnormal.conj_mem (⟨x, hXB hx⟩ : B) hx (⟨y, hyB⟩ : B)⁻¹
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      using hmem
  obtain ⟨hpe, hEcard, hX₀cyc, hX₀card, hX₀reg, hH1⟩ :=
    field_prime_fixed_structure hQ hQcard he hXQ hXcyclic hXQcard hregular hp hy hyQ hyX hXy
  obtain ⟨-, hpq₀, hq₀⟩ := field_prime_parameter_bounds hp hpe he hpq
  have hyp : y ^ p = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  obtain ⟨ty, htyX, htycomm, htyfiber, htyβ⟩ :=
    exists_centralizing_flip h.local_datum.distinguished_order ht hfiber hyB hyp hH1
  have htyH : ty ∉ H := rightPairFlipFiber_not_mem hbeta htyfiber
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy
    exact hp.one_lt.ne hy
  obtain ⟨hYtop, hYH⟩ := centralizer_lt_top_and_escape hsimple hnonab hy1 htycomm htyH
  have hX₀H : X₀ ≤ H ⊓ Y :=
    fun x hx => ⟨pairPointStabilizer_le_point H beta (hXB hx.1), hx.2⟩
  have htrans : ∀ a ∈ (E : Set G) \ {1}, ∀ b ∈ (E : Set G) \ {1},
      ∃ x ∈ X₀, x⁻¹ * a * x = b := by
    intro a ha b hb
    obtain ⟨x, hx, -⟩ := hX₀reg a ha b hb
    exact ⟨x, x.2, hx⟩
  obtain ⟨r, hrE, hr1⟩ := exists_mem_ne_one_of_one_lt_card (E := E) (by rw [hEcard]; omega)
  obtain ⟨h2tr, hprimes⟩ := centralizer_normal_two_hull h.local_datum h.central_sylow
    (isPGroup_two_of_isElemAbelian hQ) hQclass hYH hX₀H htrans hrE hr1
  obtain ⟨hαΔ, hβΔ, hΔfix⟩ := centralizer_baseOrbit_basic hyH htyfiber htycomm
  have hpE : p ∣ Nat.card E - 1 := by
    rw [hEcard]
    exact hpq₀
  obtain ⟨hfixpair, hfact⟩ := hprimes p hp hpE
  have hBY : (Nat.card (B ⊓ Y : Subgroup G)).factorization p =
      (Nat.card Y).factorization p := by
    have hpair := hfact (rightCosetMk H 1) hαΔ beta hβΔ hbeta.symm
    have heq : (Y ⊓ (rightCosetStabilizer H (rightCosetMk H 1) ⊓
        rightCosetStabilizer H beta) : Subgroup G) = B ⊓ Y := inf_comm _ _
    rwa [heq] at hpair
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨hpe, hq₀, hpq₀, hEcard, hX₀cyc, hX₀card, hX₀reg,
    ⟨ty, htyX, htycomm, htyfiber, htyβ⟩, hYtop, hYH, hαΔ, hβΔ, hΔfix,
    fun a ha b hb c hc d hd hab hcd => h2tr (by rw [hEcard]; omega) a ha b hb c hc d hd hab hcd,
    fun P => exists_sylow_map_eq_of_factorization_eq inf_le_right hBY P,
    fun r' hr' hr'1 => (centralizer_class_data h.local_datum h.central_sylow hQclass hYH hX₀H
      htrans hr' hr'1).2.2.1, hfixpair⟩

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
