module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt SigmaOne4 SigmaTwo4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem map_normalizer_subtype_le_uc6 {H : Subgroup G} (Q : Subgroup ↥H) :
    (Subgroup.normalizer (Q : Set ↥H)).map H.subtype ≤
      Subgroup.normalizer (Q.map H.subtype : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  show ∀ n, n ∈ Q.map H.subtype ↔ H.subtype x * n * (H.subtype x)⁻¹ ∈ Q.map H.subtype
  intro y
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact Subgroup.mem_map.mpr ⟨x * y' * x⁻¹, (hx y').1 hy', by simp [map_mul]⟩
  · rintro ⟨y', hy', hy'eq⟩
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * y' * x, (hx (x⁻¹ * y' * x)).2 ?_, ?_⟩
    · have : x * (x⁻¹ * y' * x) * x⁻¹ = y' := by group
      rw [this]
      exact hy'
    · rw [map_mul, map_mul, map_inv, hy'eq]
      group

theorem mem_beta_of_twoLocalPrimeRank (H : Subgroup G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h3 : 3 < twoLocalPrimeRank q ↥H) : q ∈ uniqueFourBeta G := by
  have hne : {k | ∃ N : Subgroup ↥H, IsTwoLocal N ∧ Open.pRank q N = k}.Nonempty := by
    by_contra hempty
    have hset : {k | ∃ N : Subgroup ↥H, IsTwoLocal N ∧ Open.pRank q N = k} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    have h0 : twoLocalPrimeRank q ↥H = 0 := by
      unfold twoLocalPrimeRank
      rw [hset]
      exact csSup_empty
    omega
  obtain ⟨N, hN, hNk⟩ :=
    Nat.sSup_mem hne (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove q hq)
  have hN4 : 4 ≤ Open.pRank q N := by
    have : Open.pRank q N = twoLocalPrimeRank q ↥H := hNk
    omega
  obtain ⟨P, hPne, hP2, rfl⟩ := hN
  have hP₀ne : P.map H.subtype ≠ ⊥ := fun h =>
    hPne (Subgroup.map_eq_bot_iff_of_injective P H.subtype_injective |>.1 h)
  have hP₀2 : IsPGroup 2 (P.map H.subtype) := hP2.map H.subtype
  have hloc : IsTwoLocal (Subgroup.normalizer (P.map H.subtype : Set G)) :=
    ⟨_, hP₀ne, hP₀2, rfl⟩
  have h1 : Open.pRank q (Subgroup.normalizer (P : Set ↥H)) ≤
      Open.pRank q ((Subgroup.normalizer (P : Set ↥H)).map H.subtype) :=
    CFSG.SectionRank.pRank_le_map hq.one_lt H.subtype H.subtype_injective _
  have h2 : Open.pRank q ((Subgroup.normalizer (P : Set ↥H)).map H.subtype) ≤
      Open.pRank q (Subgroup.normalizer (P.map H.subtype : Set G)) :=
    CFSG.SectionRank.pRank_mono hq.one_lt (map_normalizer_subtype_le_uc6 P)
  have h4 : 4 ≤ Open.pRank q (Subgroup.normalizer (P.map H.subtype : Set G)) :=
    hN4.trans (h1.trans h2)
  refine ⟨hq, hq2, ?_, ?_⟩
  · exact CFSG.PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank q hq
      (Subgroup.normalizer (P.map H.subtype : Set G)) (by omega)
  · exact h4.trans (le_csSup (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove q hq)
      ⟨_, hloc, rfl⟩)

theorem exists_sigma_ge (hU : uniqueFourUnique G) {q : ℕ} (hq : q ∈ uniqueFourBeta G)
    {X : Subgroup G} (hX : IsPGroup q X) :
    ∃ N : Subgroup G, uniqueFourIsMaxTwoLocal N ∧ q ∈ uniqueFourSigma N ∧ X ≤ N := by
  haveI : Fact q.Prime := ⟨hq.1⟩
  obtain ⟨N₀, hN₀, hqN₀⟩ := exists_maxLocal_mem_sigma hq
  obtain ⟨P, hPN₀, -⟩ := exists_sylow_le_of_sigma hU hN₀ hqN₀
  obtain ⟨g, hg⟩ := exists_le_uniqueFourConj_sylow hX P
  exact ⟨uniqueFourConj g N₀, isMaxTwoLocal_conj hN₀ g, mem_uniqueFourSigma_conj hqN₀ g,
    hg.trans (uniqueFourConj_mono hPN₀ g)⟩

theorem not_le_maxLocal (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hC : TheoremCAt S.M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup G} (hEM : E ≤ S.M)
    (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) (hΓ : rankThreeGamma 1 r E ≤ S.M)
    {H : Subgroup G} (hEH : E ≤ H) (HnM : ¬ H ≤ S.M) {N : Subgroup G}
    (hN : uniqueFourIsMaxTwoLocal N) : ¬ H ≤ N := by
  intro hHN
  have h63 := r6_3_dataOfSetup4 hS hU S hC
  have hmem : N ∈ calMOf E := ⟨hN, hEH.trans hHN⟩
  rw [h63 r hr hr2 E hEM hEel hEcard hΓ] at hmem
  have hNM : N = S.M := hmem
  exact HnM (hNM ▸ hHN)

theorem stronglyEmbedded_or_sigmaTwo (hU : uniqueFourUnique G) {N : Subgroup G}
    (hN : uniqueFourIsMaxTwoLocal N) {q : ℕ} (hq : q ∈ uniqueFourSigma N) :
    IsStronglyPEmbedded q N ∨ (5 ≤ q ∧ SigmaTwo4 G q) := by
  obtain ⟨hβ, hM0, -, P, hPM, hΓ, hcl⟩ := (hU N hN ⟨q, hq⟩).1 q hq
  rcases hcl with ⟨hdvd, hstrong⟩ | ⟨h5, hsolv, hab, P₀, hP₀⟩
  · exact Or.inl (isStronglyPEmbedded_of_clause_one hM0 hdvd hstrong)
  · exact Or.inr ⟨h5, hβ, N, hN, hq, P, hPM, hΓ, h5, hsolv, hab, P₀, hP₀⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6
