module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCoprimePrimeLocalModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCoprimePrimeFaithful
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCoprimePrimeAlgebra

public section

namespace CFSG.ShultStronglyClosedTI.CoprimePrime

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem baseOrbit_eq_cyclic (H N : Subgroup G) :
    ProperPairModel.baseOrbit H N = CyclicSemiregular.baseOrbit H N := by
  ext ω
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [rightCosetTranslate_mk, one_mul]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [rightCosetTranslate_mk, one_mul]⟩

omit [Finite G] in
theorem pair_relIndex_of_two_transitive (H Y : Subgroup G) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (hβΔ : beta ∈ CyclicSemiregular.baseOrbit H Y)
    (h2 : ∀ a ∈ CyclicSemiregular.baseOrbit H Y, ∀ b ∈ CyclicSemiregular.baseOrbit H Y,
      ∀ c ∈ CyclicSemiregular.baseOrbit H Y, ∀ d ∈ CyclicSemiregular.baseOrbit H Y,
      a ≠ b → c ≠ d → ∃ g ∈ Y, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d) :
    (pairPointStabilizer H beta ⊓ Y).relIndex (H ⊓ Y) =
      Nat.card (CyclicSemiregular.baseOrbit H Y) - 1 := by
  set Δ := CyclicSemiregular.baseOrbit H Y
  set M := H ⊓ Y
  let := pointSubgroupInverseRightAction H M
  have hαΔ : rightCosetMk H 1 ∈ Δ := ⟨1, Y.one_mem, rightCosetTranslate_one H _⟩
  have hYΔ : ∀ ω ∈ Δ, ∀ g ∈ Y, rightCosetTranslate H ω g ∈ Δ := by
    rintro ω ⟨y, hy, rfl⟩ g hg
    exact ⟨y * g, Y.mul_mem hy hg, (rightCosetTranslate_mul H _ y g).symm⟩
  have hstab : MulAction.stabilizer M beta = (pairPointStabilizer H beta ⊓ Y).subgroupOf M := by
    ext m
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change pointRightCosetMul H beta (m : G)⁻¹ = beta ↔ _
    rw [← mem_point_right_stabilizer_iff, (rightCosetStabilizer H beta).inv_mem_iff]
    constructor
    · intro hm
      refine ⟨⟨?_, hm⟩, m.2.2⟩
      rw [rightCosetStabilizer_base]
      exact m.2.1
    · exact fun hm => hm.1.2
  have horbit : MulAction.orbit M beta = Δ \ {rightCosetMk H 1} := by
    ext ω
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨m, rfl⟩
      change pointRightCosetMul H beta (m : G)⁻¹ ∈ Δ \ {rightCosetMk H 1}
      rw [pointRightCosetMul_eq_translate]
      refine ⟨hYΔ beta hβΔ _ (Y.inv_mem m.2.2), fun hbase => hbeta ?_⟩
      have h1 := congrArg (fun ω => rightCosetTranslate H ω (m : G)) hbase
      simp only [rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one] at h1
      rw [h1]
      exact (translate_base_iff H _).mpr m.2.1
    · rintro ⟨hωΔ, hω1⟩
      obtain ⟨g, hgY, hgα, hgβ⟩ := h2 _ hαΔ beta hβΔ _ hαΔ ω hωΔ (Ne.symm hbeta) (Ne.symm hω1)
      have hgH : g ∈ H := (translate_base_iff H g).mp hgα
      refine ⟨(⟨g, hgH, hgY⟩ : M)⁻¹, ?_⟩
      change pointRightCosetMul H beta (((⟨g, hgH, hgY⟩ : M)⁻¹ : M) : G)⁻¹ = ω
      rw [Subgroup.coe_inv, inv_inv, pointRightCosetMul_eq_translate, hgβ]
  have hidx := MulAction.index_stabilizer M beta
  rw [hstab, horbit, Set.ncard_sdiff_singleton_of_mem hαΔ, ← Nat.card_coe_set_eq] at hidx
  exact hidx

theorem coprime_local_pair_index_at
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card (minimalLocalFailureProperPairHull H z beta t))
    {A : Subgroup G} (hAB : A ≤ pairPointStabilizer H beta) (hAp : IsPGroup p A) (hA1 : A ≠ ⊥)
    (hqA : 4 ≤ Nat.card (minimalLocalFailurePairActionPointHull H z ⊓
      Subgroup.centralizer (A : Set G) : Subgroup G))
    {Y : Subgroup G} (hCY : Subgroup.centralizer (A : Set G) ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (A : Set G)) :
    let B := pairPointStabilizer H beta
    let Q := minimalLocalFailurePairActionPointHull H z
    let qA := Nat.card (Q ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)
    let Δ := ProperPairModel.baseOrbit H Y
    Y < ⊤ ∧ beta ∈ Δ ∧
      (∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 3) ∧ Nat.card Δ = qA ^ i + 1 ∧
        (B ⊓ Y).relIndex (H ⊓ Y) = qA ^ i) ∧
      ∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
        ∃ g ∈ Y, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d := by
  intro B Q qA Δ
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hQ, -, hQclass, -, hQnorm, hXB, -, -, -, -, -, -, hfiber, -, hregular⟩ :=
    CyclicSemiregular.proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, hBX, -, -⟩ := coprime_torus_data h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨⟨s, hs, hAs⟩, ⟨x₀, hx₀, hfix⟩⟩ :=
    coprime_fixed_point_and_flip h hcomm hsmallerR1 hbeta ht hproper hp hpK hAB hAp
  obtain ⟨hsimple, -⟩ := minimalLocalFailure_nonabelian_simple h
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  set CA := Subgroup.centralizer (A : Set G)
  have hp2 : p ≠ 2 := by
    rintro rfl
    apply hpK
    have hzK : z ∈ minimalLocalFailureProperPairHull H z beta t :=
      Subgroup.subset_closure (Or.inl (Or.inl rfl))
    have h2 := orderOf_dvd_natCard (⟨z, hzK⟩ : minimalLocalFailureProperPairHull H z beta t)
    rwa [Subgroup.orderOf_mk, h.local_datum.distinguished_order] at h2
  have hAQ : ∀ c ∈ A, c ∈ Q → c = 1 := by
    intro c hcA hcQ
    obtain ⟨n, hn⟩ := hAp ⟨c, hcA⟩
    have hcn : c ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hc2 : c ^ 2 = 1 := hQ.2 c hcQ
    have hcop : Nat.Coprime 2 (p ^ n) :=
      Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one hcn))
  have hEeq : Q ⊓ Y = Q ⊓ CA := by
    apply le_antisymm _ (inf_le_inf_left Q hCY)
    rintro r ⟨hrQ, hrY⟩
    refine ⟨hrQ, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have hraA : r * a * r⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hYN hrY) a).mp ha
    have haH : a ∈ H := pairPointStabilizer_le_point H beta (hAB ha)
    have hc1 : r * a * r⁻¹ * a⁻¹ ∈ A := A.mul_mem hraA (A.inv_mem ha)
    have hc2 : r * a * r⁻¹ * a⁻¹ ∈ Q := by
      have hmem := hQnorm a⁻¹ (H.inv_mem haH) r⁻¹ (Q.inv_mem hrQ)
      rw [inv_inv] at hmem
      have := Q.mul_mem hrQ hmem
      simpa only [mul_assoc] using this
    have hc := hAQ _ hc1 hc2
    calc a * r = (r * a * r⁻¹ * a⁻¹)⁻¹ * r * a := by group
      _ = r * a := by rw [hc, inv_one, one_mul]
  have hE4 : 4 ≤ Nat.card (Q ⊓ Y : Subgroup G) := by rw [hEeq]; exact hqA
  have hY : Y < ⊤ := by
    refine lt_of_le_of_lt hYN (lt_top_iff_ne_top.mpr fun htop => ?_)
    have hAn : A.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (self := hsimple) A with hbot | htopA
    · exact hA1 hbot
    · apply h.local_datum.proper
      rw [eq_top_iff, ← htopA]
      exact hAB.trans (pairPointStabilizer_le_point H beta)
  have htAfiber : t * x₀ ∈ rightPairFlipFiber H z beta := by
    rw [hfiber]
    exact ⟨x₀, hx₀, rfl⟩
  have htACA : t * x₀ ∈ CA := Subgroup.mem_centralizer_iff.mpr fun a ha => by
    calc a * (t * x₀) = a * (a⁻¹ * (t * x₀) * a) := by rw [hfix a ha]
      _ = t * x₀ * a := by group
  have htAY : t * x₀ ∈ Y := hCY htACA
  have hYH : ¬ Y ≤ H := fun hle =>
    CyclicSemiregular.rightPairFlipFiber_not_mem hbeta htAfiber (hle htAY)
  have hX₀ : X ⊓ CA ≤ H ⊓ Y := fun x hx =>
    ⟨pairPointStabilizer_le_point H beta (hXB hx.1), hCY hx.2⟩
  have htrans : ∀ a ∈ ((Q ⊓ Y : Subgroup G) : Set G) \ {1},
      ∀ b ∈ ((Q ⊓ Y : Subgroup G) : Set G) \ {1}, ∃ x ∈ X ⊓ CA, x⁻¹ * a * x = b := by
    rw [hEeq]
    intro a ha b hb
    obtain ⟨x, hx, -⟩ := regular_restrict_subgroup (A := A)
      (fun c hc x hx => hBX c (hAB hc) x hx) hregular a ha b hb
    exact ⟨x, x.2, hx⟩
  have hsCA : s ∈ CA := Subgroup.mem_centralizer_iff.mpr fun a ha => by
    calc a * s = a * (a⁻¹ * s * a) := by rw [hAs a ha]
      _ = s * a := by group
  have hsE : s ∈ Q ⊓ Y := ⟨hs.1, hCY hsCA⟩
  obtain ⟨i, hi, hdeg⟩ :=
    subgroup_orbit_degree h hcomm hsmallerR1 hQ hQclass hY hYH hX₀ htrans hE4 hsE hs.2
  have hQ2 : IsPGroup 2 Q := fun x => ⟨1, Subtype.ext (by simpa using hQ.2 x x.2)⟩
  have h2 := subgroup_two_transitive h.local_datum h.central_sylow hQ2 hQclass hYH hX₀ htrans
    hsE hs.2 (by omega)
  have hβΔ : beta ∈ CyclicSemiregular.baseOrbit H Y := ⟨t * x₀, htAY, htAfiber.2⟩
  have hidx := pair_relIndex_of_two_transitive H Y hbeta hβΔ h2
  have hΔ : Δ = CyclicSemiregular.baseOrbit H Y := baseOrbit_eq_cyclic H Y
  rw [hEeq] at hdeg
  refine ⟨hY, hΔ ▸ hβΔ, ⟨i, hi, hΔ ▸ hdeg, ?_⟩, hΔ ▸ h2⟩
  rw [hidx, hdeg, Nat.add_sub_cancel]

theorem minimalLocalFailure_coprime_prime_local_pair_index
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card (minimalLocalFailureProperPairHull H z beta t))
    {A : Subgroup G} (hAB : A ≤ pairPointStabilizer H beta) (hAp : IsPGroup p A) (hA1 : A ≠ ⊥)
    (hqA : 4 ≤ Nat.card (minimalLocalFailurePairActionPointHull H z ⊓
      Subgroup.centralizer (A : Set G) : Subgroup G)) :
    let B := pairPointStabilizer H beta
    let Q := minimalLocalFailurePairActionPointHull H z
    let qA := Nat.card (Q ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)
    (∀ Y ∈ ({Subgroup.normalizer (A : Set G), Subgroup.centralizer (A : Set G)} :
        Set (Subgroup G)),
      Y < ⊤ ∧ beta ∈ ProperPairModel.baseOrbit H Y ∧
        (∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 3) ∧
          Nat.card (ProperPairModel.baseOrbit H Y) = qA ^ i + 1 ∧
          (B ⊓ Y).relIndex (H ⊓ Y) = qA ^ i) ∧
        ∀ a ∈ ProperPairModel.baseOrbit H Y, ∀ b ∈ ProperPairModel.baseOrbit H Y,
          ∀ c ∈ ProperPairModel.baseOrbit H Y, ∀ d ∈ ProperPairModel.baseOrbit H Y,
          a ≠ b → c ≠ d →
            ∃ g ∈ Y, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d) ∧
      (∃ n : ℕ, (B ⊓ Subgroup.normalizer (A : Set G)).relIndex
        (H ⊓ Subgroup.normalizer (A : Set G)) = 2 ^ n) ∧
      ∃ n : ℕ, (B ⊓ Subgroup.centralizer (A : Set G)).relIndex
        (H ⊓ Subgroup.centralizer (A : Set G)) = 2 ^ n := by
  intro B Q qA
  have hat := fun (Y : Subgroup G) (hCY : Subgroup.centralizer (A : Set G) ≤ Y)
      (hYN : Y ≤ Subgroup.normalizer (A : Set G)) =>
    coprime_local_pair_index_at h hcomm hsmallerR1 hbeta ht hproper hp hpK hAB hAp hA1 hqA hCY
      hYN
  have hCN : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hN := hat _ hCN le_rfl
  have hC := hat _ le_rfl hCN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ, -⟩ := CyclicSemiregular.proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  have hQ2 : IsPGroup 2 Q := fun x => ⟨1, Subtype.ext (by simpa using hQ.2 x x.2)⟩
  obtain ⟨f, hf⟩ := (hQ2.to_le (inf_le_left (b := Subgroup.centralizer (A : Set G)))).exists_card_eq
  have hpow : ∀ i : ℕ, qA ^ i = 2 ^ (f * i) := fun i => by
    change Nat.card (Q ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ^ i = _
    rw [hf, pow_mul]
  refine ⟨fun Y hY => ?_, ?_, ?_⟩
  · rcases hY with rfl | hY
    · exact hN
    · rw [Set.mem_singleton_iff] at hY
      subst hY
      exact hC
  · obtain ⟨-, -, ⟨i, -, -, hidx⟩, -⟩ := hN
    exact ⟨f * i, hidx.trans (hpow i)⟩
  · obtain ⟨-, -, ⟨i, -, -, hidx⟩, -⟩ := hC
    exact ⟨f * i, hidx.trans (hpow i)⟩

end CFSG.ShultStronglyClosedTI.CoprimePrime
