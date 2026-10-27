module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Star36a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt SigmaOne4 SigmaTwo4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem ne_bot_of_one_le_pRank {q : ℕ} (hq : q.Prime) {Y : Subgroup G} (h : 1 ≤ Open.pRank q Y) :
    Y ≠ ⊥ := by
  rintro rfl
  obtain ⟨E, hEY, -, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained q hq (⊥ : Subgroup G)
  have hE : E = ⊥ := le_bot_iff.1 hEY
  rw [hE, Subgroup.card_bot] at hcard
  have h0 : Open.pRank q (⊥ : Subgroup G) = 0 := by
    by_contra hne
    have : 1 < q ^ Open.pRank q (⊥ : Subgroup G) :=
      Nat.one_lt_pow hne hq.one_lt
    omega
  omega

theorem star_a_of_stronglyEmbedded (hU : uniqueFourUnique G) {N : Subgroup G}
    (hN : uniqueFourIsMaxTwoLocal N) {q : ℕ} (hq : q ∈ uniqueFourSigma N)
    (hNs : IsStronglyPEmbedded q N) {H : Subgroup G} (HnN : ¬ H ≤ N) (S : Subgroup ↥H)
    (hSN : S.map H.subtype ≤ N) (hSq : IsPGroup q S) :
    (rankThreeGamma 1 q S ⊔ ⨆ (Y : Subgroup ↥H) (_ : Y ≤ S) (_ : 1 < Open.pRank q Y),
        ⨆ K ∈ calMOf Y, K) ≠ ⊤ := by
  haveI : Fact q.Prime := ⟨hq.1.1⟩
  have hle : (rankThreeGamma 1 q S ⊔ ⨆ (Y : Subgroup ↥H) (_ : Y ≤ S) (_ : 1 < Open.pRank q Y),
      ⨆ K ∈ calMOf Y, K) ≤ N.subgroupOf H := by
    refine sup_le ?_ ?_
    · rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
      intro Y hYS hY1
      have hYne : Y.map H.subtype ≠ ⊥ := fun h =>
        ne_bot_of_one_le_pRank hq.1.1 hY1
          ((Subgroup.map_eq_bot_iff_of_injective Y H.subtype_injective).1 h)
      have hYp : IsPGroup q (Y.map H.subtype) := (hSq.to_le hYS).map H.subtype
      have hYN : Y.map H.subtype ≤ N := (Subgroup.map_mono hYS).trans hSN
      have hnorm := hNs.normalizer_le hYne hYp hYN
      intro x hx
      exact Subgroup.mem_subgroupOf.2
        (hnorm (map_normalizer_subtype_le_uc6 Y (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)))
    · refine iSup_le fun Y => iSup_le fun hYS => iSup_le fun hY2 => iSup₂_le fun K hK => ?_
      obtain ⟨hKmax, hYK⟩ := hK
      obtain ⟨R, hRne, hR2, rfl⟩ := hKmax.1
      have hR₀ne : R.map H.subtype ≠ ⊥ := fun h =>
        hRne ((Subgroup.map_eq_bot_iff_of_injective R H.subtype_injective).1 h)
      have hloc : IsTwoLocal (Subgroup.normalizer (R.map H.subtype : Set G)) :=
        ⟨_, hR₀ne, hR2.map H.subtype, rfl⟩
      have hYle : Y.map H.subtype ≤ Subgroup.normalizer (R.map H.subtype : Set G) := fun y hy =>
        map_normalizer_subtype_le_uc6 R (Subgroup.map_mono hYK hy)
      have h2 : 2 ≤ Open.pRank q (Y.map H.subtype) :=
        hY2.trans_le (CFSG.SectionRank.pRank_le_map hq.1.1.one_lt H.subtype H.subtype_injective Y)
      have hYN : Y.map H.subtype ≤ N := (Subgroup.map_mono hYS).trans hSN
      have hle' := sec61 hU hN hq hYN h2 hloc hYle
      intro x hx
      exact Subgroup.mem_subgroupOf.2
        (hle' (map_normalizer_subtype_le_uc6 R (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)))
  intro hsup
  rw [hsup] at hle
  exact HnN (Subgroup.subgroupOf_eq_top.1 (top_le_iff.1 hle))

theorem strongly3_of_three_mem_beta (hU : uniqueFourUnique G) (h3 : 3 ∈ uniqueFourBeta G)
    {H : Subgroup G} (hH : ∀ N : Subgroup G, uniqueFourIsMaxTwoLocal N → ¬ H ≤ N)
    (hdvd : 3 ∣ Nat.card ↥H) : ∃ Y : Subgroup ↥H, IsStronglyPEmbedded 3 Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (⊤ : Subgroup ↥H)
  obtain ⟨N₃, hN₃, h3N₃, hQN₃⟩ := exists_sigma_ge hU h3 (hQ.isPGroup.map H.subtype)
  have hNs : IsStronglyPEmbedded 3 N₃ := by
    rcases stronglyEmbedded_or_sigmaTwo hU hN₃ h3N₃ with h | ⟨h5, -⟩
    · exact h
    · omega
  have hQY : Q ≤ N₃.subgroupOf H := fun x hx => Subgroup.mem_subgroupOf.2 (hQN₃ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩))
  refine ⟨N₃.subgroupOf H, fun h => hH N₃ hN₃ (Subgroup.subgroupOf_eq_top.1 h), ?_, fun g hg hdiv => ?_⟩
  · have h3Q : 3 ∣ Nat.card Q := by
      rw [hQ.card_eq, Subgroup.card_top]
      exact dvd_pow_self 3 (Nat.one_le_iff_ne_zero.1
        ((Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').1 hdvd))
    exact h3Q.trans (Subgroup.card_dvd_of_le hQY)
  · have hgN : (g : G) ∉ N₃ := fun h => hg (Subgroup.mem_subgroupOf.2 h)
    refine hNs.2.2 (g : G) hgN (hdiv.trans ?_)
    rw [← Subgroup.card_map_of_injective H.subtype_injective (K := _)]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨Subgroup.mem_subgroupOf.1 hx1, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx2
    exact ⟨(y : G), Subgroup.mem_subgroupOf.1 hy, by simp [MulAut.conj_apply]⟩

theorem not_sigmaTwo (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hsub : (dataOfSetup4 hS hU S).sig ⊆ (dataOfSetup4 hS hU S).sig1)
    (h3 : 3 ∉ uniqueFourBeta G) {q : ℕ} (hq : SigmaTwo4 G q) : False := by
  have hSig2 : SigmaTwo4 G S.p := hMS.2 h3 ⟨q, hq⟩
  obtain ⟨hβ, N₂, hN₂, hpN₂, P₂, hP₂N₂, -, -, -, -, P₀, hP₀⟩ := hSig2
  haveI : Fact S.p.Prime := ⟨hβ.1⟩
  have hone : S.p ∈ SigmaOne4 G := (hsub S.hp).2
  have hNs : IsStronglyPEmbedded S.p N₂ := isStronglyPEmbedded_of_sigmaOne hU hN₂ hpN₂ hone
  obtain ⟨hP₀P, hP₀card, -, -, hnlayer, -⟩ := hP₀
  have hP₀ne : P₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hP₀card
    exact hβ.1.one_lt.ne hP₀card
  have hP₀p : IsPGroup S.p P₀ := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hP₀card)
  have hnorm := hNs.normalizer_le hP₀ne hP₀p (hP₀P.trans hP₂N₂)
  apply hnlayer
  refine sSup_le fun L hL x hx => hnorm ?_
  exact Subgroup.centralizer_le_normalizer (P₀ : Set G) (hL.1 hx)

theorem star36At_dataOfSetup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : TheoremCAt S.M) : PartTwo.Star36At (dataOfSetup4 hS hU S) := by
  intro hsub r hr hr2 E hEM hEel hEcard hΓ H hEH hHtop hQ HnM q hq hq2 h3 Sq hSq
  have hH : ∀ N : Subgroup G, uniqueFourIsMaxTwoLocal N → ¬ H ≤ N := fun N hN =>
    not_le_maxLocal hS hU S hC hr hr2 hEM hEel hEcard hΓ hEH HnM hN
  have hβ : q ∈ uniqueFourBeta G := mem_beta_of_twoLocalPrimeRank H hq hq2 h3
  haveI : Fact q.Prime := ⟨hq⟩
  have hSqp : IsPGroup q Sq := hSq.isPGroup
  obtain ⟨N, hN, hqN, hSN⟩ := exists_sigma_ge hU hβ (hSqp.map H.subtype)
  rcases stronglyEmbedded_or_sigmaTwo hU hN hqN with hNs | ⟨h5, hSig2⟩
  · exact Or.inl (star_a_of_stronglyEmbedded hU hN hqN hNs (hH N hN) Sq hSN hSqp)
  · refine Or.inr ⟨by omega, fun hdvd => ?_⟩
    by_cases h3β : 3 ∈ uniqueFourBeta G
    · exact strongly3_of_three_mem_beta hU h3β hH hdvd
    · exact (not_sigmaTwo hS hU S hMS hsub h3β hSig2).elim

theorem star36_holds : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G), S.InMSigma → TheoremCAt S.M →
      PartTwo.Star36At (dataOfSetup4 hS hU S) :=
  fun _ _ _ hS hU S hMS hC => star36At_dataOfSetup4 hS hU S hMS hC

end CFSG.LocalAnalysis.UniquenessCase.UC6
