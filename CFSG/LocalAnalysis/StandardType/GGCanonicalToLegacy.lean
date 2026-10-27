module

public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSmall
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open RawAutSmall

theorem largeEvenRawDatum_canonical_of_legacy_mono
    {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (hmono : ∀ (R : Type) [Group R] (I I' F : Set (MulAut R)),
      I ⊆ I' → Q R I F → Q R I' F)
    (h : CFSG.Assembly.LargeEvenRawDatumLegacy lab Q) :
    CFSG.Assembly.LargeEvenRawDatum lab Q := by
  obtain ⟨tag, rank, exponent⟩ := lab
  cases tag
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy,
    CFSG.Assembly.LargeEvenRawDatum] at h ⊢
  all_goals first
    | exact h
    | (dsimp only [LargeEvenRecipeChevalley, LargeEvenRecipeG2Derived] at h ⊢
       obtain ⟨K, fieldInst, finiteInst, hK, hQ⟩ := h
       refine ⟨K, fieldInst, finiteInst, hK, ?_⟩
       apply hmono _ _ _ _ ?_ hQ
       intro φ hφ
       exact Subgroup.subset_closure (Or.inl hφ))
    | (dsimp only [LargeEvenRecipeTwF4, LargeEvenRecipeTwF4Inherited] at h ⊢
       obtain ⟨K, fieldInst, finiteInst, hK, hQ⟩ := h
       refine ⟨K, fieldInst, finiteInst, hK, ?_⟩
       split_ifs
       · apply hmono _ _ _ _ ?_ hQ
         intro φ hφ
         exact Subgroup.subset_closure (Or.inl hφ)
       · exact hQ)

private theorem induces_pow_eq_one {G : Type*} [Group G] {R : Type}
    [Group R] (L : Subgroup G) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) {m : ℕ} (hbm : b ^ m = 1) {φ : MulAut R}
    (h : LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) : φ ^ m = 1 := by
  rw [eq_ggLAut_of_induces L θ hb h, ← map_pow]
  have hpow : (⟨b⁻¹, inv_mem hb⟩ : Subgroup.normalizer (L : Set G)) ^ m = 1 := by
    ext
    simp [inv_pow, hbm]
  rw [hpow, map_one]

private theorem largeEvenRawDatum_legacy_of_canonical {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q)
    (hG2 : ∀ {K : Type} [Field K] [Finite K], Nat.card K = 2 →
      Q (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))
        (LargeEvenChevParentIDImage LargeEvenCartanG2 K (LargeEvenChevGroup LargeEvenCartanG2 K)
          (LargeEvenChevH LargeEvenCartanG2 K true))
        (LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true)) →
      Q (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))
        (LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true))
        (LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true)))
    (hTwF4 : ∀ {a : ℕ} {K : Type} [Field K] [Finite K], a = 0 →
      Nat.card K = 2 ^ (2 * a + 1) →
      Q (LargeEvenCenterQuot (LargeEvenTwF4H a K))
        (LargeEvenChevParentIDImage LargeEvenCartanF4 K (LargeEvenTwF4Parent a K)
          (LargeEvenTwF4H a K))
        (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) →
      Q (LargeEvenCenterQuot (LargeEvenTwF4H a K))
        (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
        (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))) :
    LargeEvenRawDatumLegacy lab Q := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRawDatumLegacy] at h ⊢
  all_goals first
    | exact h
    | (dsimp only [LargeEvenRecipeG2Derived, LargeEvenRecipeChevalley] at h ⊢
       obtain ⟨K, hf, hfin, hK, hQ⟩ := h
       exact ⟨K, hf, hfin, hK, hG2 hK hQ⟩)
    | (dsimp only [LargeEvenRecipeTwF4Inherited, LargeEvenRecipeTwF4] at h ⊢
       obtain ⟨K, hf, hfin, hK, hQ⟩ := h
       by_cases ha : (n - 1) / 2 = 0
       · rw [if_pos ha] at hQ
         exact ⟨K, hf, hfin, hK, hTwF4 ha hK hQ⟩
       · rw [if_neg ha] at hQ
         exact ⟨K, hf, hfin, hK, hQ⟩)

private theorem largeEvenMarkingLegacy_of_canonical_clause1
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B : Subgroup G} (hB : ∀ b ∈ B, b ^ p = 1) {L : Subgroup G}
    (h : CFSG.Assembly.LargeEvenMarking L (fun lab _ _ I _ θ => LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :
    LargeEvenMarkingLegacy L (fun lab _ _ I _ θ => LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  obtain ⟨hL, lab, hlab, hraw⟩ := h
  refine ⟨hL, lab, hlab, ?_⟩
  refine largeEvenRawDatum_legacy_of_canonical hraw ?_ ?_
  · intro K _ _ hK hQ
    obtain ⟨hs, hna, θ, hsplit, hBL, hφ⟩ := hQ
    refine ⟨hs, hna, θ, hsplit, hBL, fun b hb => ?_⟩
    obtain ⟨φ, -, hind⟩ := hφ b hb
    refine ⟨φ, ?_, hind⟩
    have hm : Odd p := hp.odd_of_ne_two hp2
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBL hb
    have hφp : φ ^ p = 1 := induces_pow_eq_one L θ hbN (hB b hb) hind
    have hinner : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) :=
      RawAutSmall.mem_inner_g2der hK hna hm hφp
    obtain ⟨r, rfl⟩ := hinner
    exact conj_mem_chevIDImage _ r
  · intro a K _ _ ha hK hQ
    obtain ⟨hs, hna, θ, hsplit, hBL, hφ⟩ := hQ
    refine ⟨hs, hna, θ, hsplit, hBL, fun b hb => ?_⟩
    obtain ⟨φ, -, hind⟩ := hφ b hb
    refine ⟨φ, ?_, hind⟩
    have hm : Odd p := hp.odd_of_ne_two hp2
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBL hb
    have hφp : φ ^ p = 1 := induces_pow_eq_one L θ hbN (hB b hb) hind
    have h2 : IsPGroup 2 (Outer (LargeEvenCenterQuot (LargeEvenTwF4H a K))) :=
      RawAutSmall.isPGroup_outer_twF4der ha hK
    have hinner : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (LargeEvenCenterQuot (LargeEvenTwF4H a K)) :=
      RawAut.mem_inner_of_isPGroup_outer h2 hm hφp
    obtain ⟨r, rfl⟩ := hinner
    exact conj_mem_chevIDImage _ r

private theorem largeEvenMarkingLegacy_of_canonical_clause3
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : G} {J : Subgroup G}
    (h : CFSG.Assembly.LargeEvenMarking J (fun lab _ _ I F θ =>
      LargeEvenHalfSplit p lab (Subgroup.center J = ⊥) ∨
        LargeEvenPrimeField p lab I F
          (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x))) :
    LargeEvenMarkingLegacy J (fun lab _ _ I F θ =>
      LargeEvenHalfSplit p lab (Subgroup.center J = ⊥) ∨
        LargeEvenPrimeField p lab I F
          (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)) := by
  obtain ⟨hL, lab, hlab, hraw⟩ := h
  refine ⟨hL, lab, hlab, ?_⟩
  refine largeEvenRawDatum_legacy_of_canonical hraw ?_ ?_
  · intro K _ _ hK hQ
    obtain ⟨hs, hna, θ, hP⟩ := hQ
    refine ⟨hs, hna, θ, ?_⟩
    rcases hP with hhalf | hprime
    · exact Or.inl hhalf
    · exfalso
      obtain ⟨-, f, hfF, -, -, hford, -⟩ := hprime
      have hf1 : f = 1 := chevFieldImage_eq_one_of_card_two (A := LargeEvenCartanG2) hK _ hfF
      rw [hf1, orderOf_one] at hford
      exact hp.ne_one hford.symm
  · intro a K _ _ ha hK hQ
    obtain ⟨hs, hna, θ, hP⟩ := hQ
    refine ⟨hs, hna, θ, ?_⟩
    rcases hP with hhalf | hprime
    · exact Or.inl hhalf
    · exfalso
      subst ha
      obtain ⟨-, f, hfF, -, -, hford, -⟩ := hprime
      have hK2 : Nat.card K = 2 := by simpa using hK
      have hf1 : f = 1 := chevFieldImage_eq_one_of_card_two (A := LargeEvenCartanF4) hK2 _ hfF
      rw [hf1, orderOf_one] at hford
      exact hp.ne_one hford.symm

theorem legacyStandardType_of_canonical
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B : Subgroup G} (hB : ∀ b ∈ B, b ^ p = 1) {x : G} {L : Subgroup G}
    (hst : CFSG.Assembly.LargeEvenStandardType p B x L) :
    Legacy.LargeEvenStandardType p B x L := by
  obtain ⟨h1, h2, h3, h4⟩ := hst
  refine ⟨?_, h2, ?_, h4⟩
  · exact largeEvenMarkingLegacy_of_canonical_clause1 hp hp2 hB h1
  · intro y J hyJ
    obtain ⟨hBJ, hJ⟩ := h3 y J hyJ
    exact ⟨hBJ, largeEvenMarkingLegacy_of_canonical_clause3 hp hp2 hJ⟩

end CFSG.StandardType

end
