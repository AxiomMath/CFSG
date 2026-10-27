module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsOverlap
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsTorus
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFixed
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairInvolutionsCentralize
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsSecond
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsStatement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.OvergroupHull CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

theorem minimalLocalFailure_unitary_fixed_hulls_generate
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (hfix : Nat.card (rightFixedSet H u) =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1) :
    UnitaryFixedHullsConclusion H z beta t u := by
  set K := minimalLocalFailureProperPairHull H z beta t with hKdef
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set q := Nat.card Q with hqdef
  set Yu := Subgroup.centralizer ({u} : Set G) with hYudef
  set Lu := Subgroup.closure (involutionPointClass z ∩ (Yu : Set G)) with hLudef
  obtain ⟨-, hQK, -, hQ, -, hQ4, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨hQclass, -, -⟩ := CyclicPair.proper_pair_point_root_classes h hcomm hbeta ht hproper
  have hdatum := h.local_datum
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huB
  have htK : t ∈ K := minimalLocalFailureProperPair_flip_mem H z beta t
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two
    (order_two_of_mem_pointClass hdatum.distinguished_order ht.1)
  have hbetat : beta = rightCosetMk H t := flip_coset_eq H ht
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hQu, hKu, -⟩ :=
    PairInvolutionsCentralize.minimalLocalFailure_pair_involutions_centralize_point_group h hcomm
      hsmallerR1 hbeta ht hproper u huB hu
  obtain ⟨-, hYu, -, -, -, -, hΔorbit, -⟩ :=
    FixedPointModel.involution_centralizer_fixed_point_model h hcomm hsmallerR1 hbeta ht hproper
      huB hu
  have hdegu : Nat.card {ω : rightCosetSpace H |
      ∃ y ∈ Yu, rightCosetTranslate H (rightCosetMk H 1) y = ω} = q ^ 3 + 1 := by
    rw [← hΔorbit]
    exact hfix
  obtain ⟨hlin, ⟨cu⟩⟩ :=
    exists_unitaryHullCoordinates h hcomm hsmallerR1 hbeta ht hproper hYu hKu hdegu
  obtain ⟨-, hLuU, hLucore, hLudvd, -, hKLu⟩ :=
    unitary_hull_of_degree h hcomm hsmallerR1 hbeta ht hproper hYu hKu hdegu
  have hLuYu : Lu ≤ Yu := (Subgroup.closure_le _).mpr Set.inter_subset_right
  have hLuorbit : baseOrbit H Lu = rightFixedSet H u := by
    obtain ⟨-, -, -, -, -, -, horbit, -⟩ :=
      minimalLocalFailure_proper_overgroup_full_point_hulls h hcomm hsmallerR1 hbeta ht hproper
        hYu hKu
    rw [baseOrbit_eq_orbit horbit, ← hΔorbit]
    rfl
  obtain ⟨hA₀B, hA₀cyc, hA₀odd, hA₀K, -, p, hp, hpodd, hpq, A, hAA₀, hAcyc, hAp, hA1, -,
      ⟨e, he⟩, hinvA⟩ := cu.exists_torus (hKLu htK) ht2 hbetat
  have hAB := hAA₀.trans hA₀B
  have hAK := hAA₀.trans hA₀K
  have hAu : A ≤ Subgroup.centralizer ({u} : Set G) := fun a ha => hLuYu (hAB ha).2
  set Y := Subgroup.centralizer (A : Set G) with hYdef
  have hKY : K ≤ Y := fun x hx => Subgroup.mem_centralizer_iff.mpr fun a ha =>
    (Subgroup.mem_centralizer_iff.mp (hAK ha) x hx).symm
  have hYtop : Y < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨hsimple, a, b, hab⟩ := minimalLocalFailure_nonabelian_simple h
    have hcenter : Subgroup.center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
      · exact h0
      · exact absurd (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top b) a) hab
    apply hA1
    rw [eq_bot_iff, ← hcenter]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Y := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  obtain ⟨-, hΔU, -⟩ :=
    MixedClass.minimalLocalFailure_mixed_involution_class_closure h hcomm hsmallerR1 hbeta ht
      hproper huB hu
  have hΔ : ∀ e ∈ Q, u * e ∈ involutionPointClass u := fun e he' =>
    hΔU ⟨e, ⟨he', hQu he'⟩, rfl⟩
  have hfixA := card_fixed_ge hdatum hQclass hQab hp2 hAp
    (fun a ha => pairPointStabilizer_le_point H beta (hAB ha).1)
    (fun a ha e he' => (Subgroup.mem_centralizer_iff.mp (hAK ha) e (hQK he')).symm)
    (fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hAu ha)) huH
    (fun e he' => Subgroup.mem_centralizer_singleton_iff.mp (hQu he')) hΔ cu.hq hfix
  have hq4 : 4 ≤ q := hQ4
  have hpq1 : ¬ p ∣ q - 1 := by
    intro hdvd
    have hsum : q + 1 = (q - 1) + 2 := by omega
    rw [hsum] at hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((Nat.dvd_add_right hdvd).mp hpq))
  have hDY := overgroup_class_eq h hcomm hbeta ht hproper hKY
  have hsub : {ω : rightCosetSpace H | ∀ a ∈ A, rightCosetTranslate H ω a = ω} ⊆
      {ω : rightCosetSpace H | ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = ω} :=
    fun γ hγ => fixed_mem_centralizer_orbit hdatum hQclass hAp hpq1 hDY hγ
  have hle := hfixA.trans (Nat.card_mono (Set.toFinite _) hsub)
  have hdegA := degree_eq_of_linear_of_le h hcomm hsmallerR1 hbeta ht hproper hYtop hKY hlin hle
  obtain ⟨hLAperf, hLAU, hLAcore, hLAdvd, hLAdeg, hKLA⟩ :=
    unitary_hull_of_degree h hcomm hsmallerR1 hbeta ht hproper hYtop hKY hdegA
  have hLAY : Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) ≤ Y :=
    (Subgroup.closure_le _).mpr Set.inter_subset_right
  have hint : involutionPointClass z ∩ (Lu : Set G) ∩
      (Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) : Set G) =
      involutionPointClass z ∩ (K : Set G) :=
    inter_pointClass_eq hKLu hKLA hLAY hinvA fun x hx => by
      rw [← order_two_of_mem_pointClass hdatum.distinguished_order hx]
      exact pow_orderOf_eq_one x
  have hnle : ¬ Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) ≤ Lu :=
    not_le_of_degree h hcomm hsmallerR1 hbeta ht hproper hLAdeg hint
  have hne : Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) ≠ Lu :=
    fun heq => hnle heq.le
  refine ⟨hlin, hLuU, hLuorbit, hLucore, hLudvd, p, hp, hpodd, hpq, A, _, hAB, hAcyc, hAp, hA1,
    hAK, hAu, hA₀B, hA₀cyc, hA₀odd, hAA₀, ⟨_, he⟩, hYtop, lt_of_le_of_lt hLAY hYtop, hLAperf,
    hLAU, hLAcore, hLAdvd, hLAdeg, hfixA, hKLA, hint, hnle, hne,
    sup_eq_top_of_ne h hcomm hsmallerR1 hbeta ht hproper hKLu hLuU hLAU hne⟩

end CFSG.ShultStronglyClosedTI.UnitaryHulls
