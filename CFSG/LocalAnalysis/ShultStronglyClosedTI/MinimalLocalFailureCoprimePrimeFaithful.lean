module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeSetup

public section

namespace CFSG.ShultStronglyClosedTI.CoprimePrime

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.CyclicSemiregular
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_fixed_of_not_dvd {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) {S : Set G} (hS : ∀ y ∈ P, ∀ a ∈ S, y⁻¹ * a * y ∈ S)
    (hpS : ¬ p ∣ Nat.card S) : ∃ a ∈ S, ∀ y ∈ P, y⁻¹ * a * y = a := by
  let act : MulAction P S :=
    { smul := fun y a => ⟨(y : G) * a * (y : G)⁻¹, by
        simpa only [inv_inv] using hS (y : G)⁻¹ (P.inv_mem y.2) a a.2⟩
      one_smul := fun a => Subtype.ext (by
        change ((1 : P) : G) * a * ((1 : P) : G)⁻¹ = a
        simp)
      mul_smul := fun y₁ y₂ a => Subtype.ext (by
        change ((y₁ * y₂ : P) : G) * a * ((y₁ * y₂ : P) : G)⁻¹ =
          (y₁ : G) * ((y₂ : G) * a * (y₂ : G)⁻¹) * (y₁ : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨a, ha⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card S hpS
  refine ⟨a, a.2, fun y hy => ?_⟩
  have h := congrArg Subtype.val (ha (⟨y, hy⟩ : P)⁻¹)
  change ((⟨y, hy⟩ : P)⁻¹ : P) * (a : G) * (((⟨y, hy⟩ : P)⁻¹ : P) : G)⁻¹ = a at h
  simpa only [Subgroup.coe_inv, inv_inv] using h

omit [Finite G] in
theorem exists_centralized_flip {p : ℕ} [Fact p.Prime] {B X A : Subgroup G} {t : G}
    (hclassB : conjugacyWithin B t = (fun x => t * x) '' (X : Set G))
    (hAB : A ≤ B) (hA : IsPGroup p A) (hpX : ¬ p ∣ Nat.card X) :
    ∃ x ∈ X, ∀ a ∈ A, a⁻¹ * (t * x) * a = t * x := by
  have hS : ∀ y ∈ A, ∀ s ∈ (fun x => t * x) '' (X : Set G),
      y⁻¹ * s * y ∈ (fun x => t * x) '' (X : Set G) := by
    intro y hy s hs
    rw [← hclassB] at hs ⊢
    obtain ⟨b, rfl⟩ := hs
    exact ⟨b * ⟨y, hAB hy⟩, by simp only [Subgroup.coe_mul, mul_inv_rev]; group⟩
  have hcard : Nat.card ((fun x => t * x) '' (X : Set G)) = Nat.card X :=
    Nat.card_image_of_injective (mul_right_injective t) _
  obtain ⟨s, ⟨x, hx, rfl⟩, hfix⟩ := exists_conj_fixed_of_not_dvd hA hS (hcard ▸ hpX)
  exact ⟨x, hx, hfix⟩

theorem card_dvd_of_injective {C K : Type*} [Group C] [Group K] [Finite K] (f : C →* K)
    (hf : Function.Injective f) : Nat.card C ∣ Nat.card K := by
  rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  exact Subgroup.card_subgroup_dvd_card f.range

theorem coprime_torus_data
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    z ∈ Q ∧ X ≤ K ∧ t ∈ K ∧ (∀ b ∈ B, ∀ x ∈ X, b⁻¹ * x * b ∈ X) ∧
      (∀ b ∈ B, ∀ v ∈ Q, b⁻¹ * v * b ∈ Q) ∧ Nat.card X ∣ Nat.card K := by
  intro B X K Q
  obtain ⟨-, -, hQclass, -, hQnorm, hXB, hXnormal, -⟩ :=
    proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  have hzQ : z ∈ Q := by
    have hz : z ∈ conjugacyWithin H z := ⟨1, by simp⟩
    rw [← hQclass] at hz
    exact hz.1
  have hXK : X ≤ K := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hBX : ∀ b ∈ B, ∀ x ∈ X, b⁻¹ * x * b ∈ X := by
    intro b hb x hx
    have hmem := hXnormal.conj_mem (⟨x, hXB hx⟩ : B) hx (⟨b, hb⟩ : B)⁻¹
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      using hmem
  refine ⟨hzQ, hXK, minimalLocalFailureProperPair_flip_mem H z beta t, hBX,
    fun b hb => hQnorm b (pairPointStabilizer_le_point H beta hb), ?_⟩
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem coprime_fixed_point_and_flip
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card (minimalLocalFailureProperPairHull H z beta t))
    {A : Subgroup G} (hAB : A ≤ pairPointStabilizer H beta) (hA : IsPGroup p A) :
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let Q := minimalLocalFailurePairActionPointHull H z
    (∃ s ∈ (Q : Set G) \ {1}, ∀ a ∈ A, a⁻¹ * s * a = s) ∧
      ∃ x ∈ X, ∀ a ∈ A, a⁻¹ * (t * x) * a = t * x := by
  intro X Q
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hXQcard, -, -, hclassB, -⟩ :=
    proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, hBQ, hXK⟩ := coprime_torus_data h hcomm hsmallerR1 hbeta ht hproper
  have hpX : ¬ p ∣ Nat.card X := fun hdvd => hpK (hdvd.trans hXK)
  refine ⟨?_, exists_centralized_flip hclassB hAB hA hpX⟩
  have hS : ∀ y ∈ A, ∀ a ∈ (Q : Set G) \ {1}, y⁻¹ * a * y ∈ (Q : Set G) \ {1} :=
    fun y hy a ha => ⟨hBQ y (hAB hy) a ha.1, conj_ne_one ha.2⟩
  have hcard : Nat.card ((Q : Set G) \ {1} : Set G) = Nat.card X := by
    rw [card_diff_one, hXQcard]
  exact exists_conj_fixed_of_not_dvd hA hS (hcard ▸ hpX)

theorem coprime_kernel_trivial
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hembed : ∃ f : Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) →*
      minimalLocalFailureProperPairHull H z beta t, Function.Injective f)
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card (minimalLocalFailureProperPairHull H z beta t))
    {P : Subgroup G} (hPB : P ≤ pairPointStabilizer H beta) (hP : IsPGroup p P) :
    ∀ y ∈ P, minimalLocalFailurePairActionPointHull H z ≤ Subgroup.centralizer ({y} : Set G) →
      y = 1 := by
  set B := pairPointStabilizer H beta
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  set K := minimalLocalFailureProperPairHull H z beta t
  set Q := minimalLocalFailurePairActionPointHull H z
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hQ4, -, -, -, hXB, -, -, -, -, -, -, -, hclassB, hregular⟩ :=
    proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨hzQ, hXK, htK, hBX, hBQ, hXdvd⟩ :=
    coprime_torus_data h hcomm hsmallerR1 hbeta ht hproper
  set P₀ := P ⊓ Subgroup.centralizer (Q : Set G)
  have hP₀B : P₀ ≤ B := inf_le_left.trans hPB
  have hP₀p : IsPGroup p P₀ := hP.to_le inf_le_left
  have hP₀Q : ∀ b ∈ P₀, ∀ v ∈ Q, b * v = v * b := fun b hb v hv =>
    ((Subgroup.mem_centralizer_iff.mp hb.2) v hv).symm
  have hQ4' : 4 ≤ Nat.card Q := hQ4
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨s, hsQ⟩, hs1'⟩ := exists_ne (1 : Q)
  have hs1 : s ≠ 1 := fun h1 => hs1' (Subtype.ext h1)
  have hs : s ∈ (Q : Set G) \ {1} := ⟨hsQ, hs1⟩
  have hP₀X : ∀ b ∈ P₀, ∀ x ∈ X, x * b = b * x := by
    intro b hb x hx
    have hxs : x⁻¹ * s * x ∈ (Q : Set G) \ {1} := ⟨hBQ x (hXB hx) s hsQ, conj_ne_one hs1⟩
    obtain ⟨y, -, huniq⟩ := hregular s hs _ hxs
    have hbx : b⁻¹ * x * b ∈ X := hBX b (hP₀B hb) x hx
    have hsb : b * s * b⁻¹ = s := by rw [hP₀Q b hb s hsQ, mul_inv_cancel_right]
    have hxsb : b⁻¹ * (x⁻¹ * s * x) * b = x⁻¹ * s * x := by
      rw [mul_assoc, ← hP₀Q b hb _ hxs.1, inv_mul_cancel_left]
    have h1 := huniq ⟨b⁻¹ * x * b, hbx⟩ (by
      change (b⁻¹ * x * b)⁻¹ * s * (b⁻¹ * x * b) = x⁻¹ * s * x
      calc (b⁻¹ * x * b)⁻¹ * s * (b⁻¹ * x * b) = b⁻¹ * (x⁻¹ * (b * s * b⁻¹) * x) * b := by
            group
        _ = x⁻¹ * s * x := by rw [hsb, hxsb])
    have h2 := huniq ⟨x, hx⟩ rfl
    have h3 : b⁻¹ * x * b = x := congrArg Subtype.val (h1.trans h2.symm)
    calc x * b = b * (b⁻¹ * x * b) := by group
      _ = b * x := by rw [h3]
  have hpX : ¬ p ∣ Nat.card X := fun hdvd => hpK (hdvd.trans hXdvd)
  obtain ⟨x₀, hx₀, hfix⟩ := exists_centralized_flip hclassB hP₀B hP₀p hpX
  have hP₀K : P₀ ≤ Subgroup.centralizer (K : Set G) := by
    intro b hb
    have hKle : K ≤ Subgroup.centralizer ({b} : Set G) := by
      apply (Subgroup.closure_le _).mpr
      rintro y ((hyz | hyt) | hy)
      · rw [hyz]
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hP₀Q b hb _ hzQ).symm
      · rw [show y = t from hyt]
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have htx : b * (t * x₀) = t * x₀ * b := by
          calc b * (t * x₀) = b * (b⁻¹ * (t * x₀) * b) := by rw [hfix b hb]
            _ = t * x₀ * b := by group
        have hxb : b * x₀⁻¹ = x₀⁻¹ * b := by
          have := hP₀X b hb x₀ hx₀
          calc b * x₀⁻¹ = x₀⁻¹ * (x₀ * b) * x₀⁻¹ := by group
            _ = x₀⁻¹ * (b * x₀) * x₀⁻¹ := by rw [this]
            _ = x₀⁻¹ * b := by group
        symm
        calc b * t = b * (t * x₀) * x₀⁻¹ := by group
          _ = t * x₀ * (b * x₀⁻¹) := by rw [htx, mul_assoc]
          _ = t * x₀ * (x₀⁻¹ * b) := by rw [hxb]
          _ = t * b := by group
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hP₀X b hb y hy)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKle hk)
  obtain ⟨f, hf⟩ := hembed
  have hdvdK : Nat.card P₀ ∣ Nat.card K := by
    have h1 : Nat.card P₀ ∣ Nat.card (Subgroup.centralizer (K : Set G)) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀K).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    exact h1.trans (card_dvd_of_injective f hf)
  have hP₀one : Nat.card P₀ = 1 := by
    rcases hP₀p.card_eq_or_dvd with h1 | hdvd
    · exact h1
    · exact absurd (hdvd.trans hdvdK) hpK
  intro y hy hyQ
  have hyP₀ : y ∈ P₀ := ⟨hy, Subgroup.mem_centralizer_iff.mpr fun v hv =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hyQ hv))⟩
  have hbot := Subgroup.card_eq_one.mp hP₀one
  rw [hbot] at hyP₀
  exact hyP₀

end CFSG.ShultStronglyClosedTI.CoprimePrime
