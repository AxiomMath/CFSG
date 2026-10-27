module

public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial

section Cube

theorem three_dvd_of_inducesKindPSL_field {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {n : ℕ} {K : Type} [Field K] (h : KFacts.InducesKindPSL n K L x .field)
    (hx : x ^ 3 = 1) {l f : ℕ} (hl : l.Prime) (hf : 1 ≤ f) (hK : Nat.card K = l ^ f) : 3 ∣ f := by
  obtain ⟨e, he⟩ := h
  have : Finite (K ≃+* K) := finite_ringAut hl hK
  have h3 := three_dvd_card_of_inducesKind_field (P := stdPinnedPSL n K)
    (ψ := LinearFlag.fieldAut n K) rfl he hx
  rwa [card_ringAut_eq hl hf hK] at h3

theorem three_dvd_of_inducesKindSL_field {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {n : ℕ} {K : Type} [Field K] (h : KFacts.InducesKindSL n K L x .field)
    (hx : x ^ 3 = 1) {l f : ℕ} (hl : l.Prime) (hf : 1 ≤ f) (hK : Nat.card K = l ^ f) : 3 ∣ f := by
  obtain ⟨e, hxN, hk⟩ := h
  have hα3 : (inducedAutHom L e ⟨x, hxN⟩) ^ 3 = 1 := inducedAutHom_pow_eq_one L e hxN hx
  have hτ3 : (LinearFlag.descendAut n K (inducedAutHom L e ⟨x, hxN⟩)) ^ 3 = 1 := by
    rw [← map_pow, hα3, map_one]
  have : Finite (K ≃+* K) := finite_ringAut hl hK
  have h3 := three_dvd_card_of_isField (P := stdPinnedPSL n K)
    (ψ := LinearFlag.fieldAut n K) rfl ((stdPinnedPSL n K).hasKind_field.mp hk) hτ3
  rwa [card_ringAut_eq hl hf hK] at h3

theorem three_dvd_of_inducesKindPSU3_field {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K)
    (h : KFacts.InducesKindPSU3 hK L x .field) (hx : x ^ 3 = 1) : 3 ∣ f := by
  obtain ⟨e, he⟩ := h
  have : Finite (K ≃+* K) := finite_ringAut hK.prime hK.card
  have h3 := three_dvd_card_of_inducesKind_field (P := stdPinnedPSU3 hK) (ψ := psuField hK)
    rfl he hx
  rw [card_ringAut_eq hK.prime (by have := hK.one_le; omega) hK.card] at h3
  omega

theorem three_dvd_of_inducesKindSU3_field {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K) {hq : 2 < p ^ f}
    (h : KFacts.InducesKindSU3 hK L hq x .field) (hx : x ^ 3 = 1) : 3 ∣ f := by
  obtain ⟨e, hxN, hk⟩ := h
  have hα3 : (inducedAutHom L e ⟨x, hxN⟩) ^ 3 = 1 := inducedAutHom_pow_eq_one L e hxN hx
  have hτ3 : (MulAut.congr (suCenterEquiv hK hq) (centerDescend _ (inducedAutHom L e ⟨x, hxN⟩)))
      ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hα3, map_one, map_one]
  have : Finite (K ≃+* K) := finite_ringAut hK.prime hK.card
  have h3 := three_dvd_card_of_isField (P := stdPinnedPSU3 hK) (ψ := psuField hK) rfl
    ((stdPinnedPSU3 hK).hasKind_field.mp hk) hτ3
  rw [card_ringAut_eq hK.prime (by have := hK.one_le; omega) hK.card] at h3
  omega

theorem three_dvd_of_inducesKindPSp_field {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {r : ℕ} {K : Type} [Field K] (h : KFacts.InducesKindPSp r K L x .field)
    (hx : x ^ 3 = 1) {l f : ℕ} (hl : l.Prime) (hf : 1 ≤ f) (hK : Nat.card K = l ^ f) : 3 ∣ f := by
  obtain ⟨e, he⟩ := h
  have : Finite (K ≃+* K) := finite_ringAut hl hK
  have h3 := three_dvd_card_of_inducesKind_field (P := stdPinnedPSp r K)
    (ψ := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut r K) rfl he hx
  rwa [card_ringAut_eq hl hf hK] at h3

theorem three_dvd_of_inducesKindG2_field {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {K : Type} [Field K]
    (h : KFacts.InducesKindG2 K L x .field) (hx : x ^ 3 = 1)
    {l f : ℕ} (hl : l.Prime) (hf : 1 ≤ f) (hK : Nat.card K = l ^ f) : 3 ∣ f := by
  obtain ⟨e, he⟩ := h
  have : Finite (K ≃+* K) := finite_ringAut hl hK
  have h3 := three_dvd_card_of_inducesKind_field (P := stdPinnedG2 K)
    (ψ := g2FieldHom K) rfl he hx
  rwa [card_ringAut_eq hl hf hK] at h3

theorem not_inducesKindPSU3_graphField {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K) :
    ¬ KFacts.InducesKindPSU3 hK L x .graphField := by
  rintro ⟨e, he⟩
  obtain ⟨_hxN, hk⟩ := he
  obtain ⟨γ, hγ, -⟩ := (stdPinnedPSU3 hK).hasKind_graphField.mp hk
  exact absurd hγ (Set.notMem_empty γ)

theorem not_inducesKindSU3_graphField {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K) {hq : 2 < p ^ f} :
    ¬ KFacts.InducesKindSU3 hK L hq x .graphField := by
  rintro ⟨e, _hxN, hk⟩
  obtain ⟨γ, hγ, -⟩ := (stdPinnedPSU3 hK).hasKind_graphField.mp hk
  exact absurd hγ (Set.notMem_empty γ)

theorem not_inducesKindPSp_graphField {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {r : ℕ} {K : Type} [Field K] : ¬ KFacts.InducesKindPSp r K L x .graphField := by
  rintro ⟨e, he⟩
  obtain ⟨_hxN, hk⟩ := he
  obtain ⟨γ, hγ, -⟩ := (stdPinnedPSp r K).hasKind_graphField.mp hk
  exact absurd hγ (Set.notMem_empty γ)

theorem not_inducesKindG2_graphField {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {K : Type} [Field K] :
    ¬ KFacts.InducesKindG2 K L x .graphField := by
  rintro ⟨e, he⟩
  obtain ⟨_hxN, hk⟩ := he
  obtain ⟨γ, hγ, -⟩ := (stdPinnedG2 K).hasKind_graphField.mp hk
  exact absurd hγ (Set.notMem_empty γ)

theorem not_hasKind_graphField_of_pow_three {n : ℕ} (K : Type) [Field K] [Finite K] (hn : 3 ≤ n)
    {τ : MulAut (LinearFlag.projectiveSL n K)} (hτ3 : τ ^ 3 = 1) :
    ¬ (stdPinnedPSL n K).HasKind τ .graphField := by
  intro hk
  have hsep : (stdPinnedPSL n K).Separated := stdPinnedPSL_separated hn
  have hnot : τ ∉ (stdPinnedPSL n K).inndiag :=
    hsep.not_mem_inndiag_of_hasKind hk (by decide) (by decide)
  have hD : τ ∉ LinearFlag.linearAutGroup n K := by
    rw [← stdPinnedPSL_inndiag]
    exact hnot
  have hF : (stdPinnedPSL n K).IsField τ := isField_of_pow_three_eq_one hn hτ3 hD
  exact hsep.not_isGraphField_of_isField hF ((stdPinnedPSL n K).hasKind_graphField.mp hk)

theorem not_inducesKindPSL_graphField {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n) (hx : x ^ 3 = 1) :
    ¬ KFacts.InducesKindPSL n K L x .graphField := by
  rintro ⟨e, he⟩
  obtain ⟨hxN, hk⟩ := he
  exact not_hasKind_graphField_of_pow_three K hn (inducedAutHom_pow_eq_one L e hxN hx) hk

theorem not_inducesKindSL_graphField {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {x : G} {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n) (hx : x ^ 3 = 1) :
    ¬ KFacts.InducesKindSL n K L x .graphField := by
  rintro ⟨e, hxN, hk⟩
  have hτ3 : (LinearFlag.descendAut n K (inducedAutHom L e ⟨x, hxN⟩)) ^ 3 = 1 := by
    rw [← map_pow, inducedAutHom_pow_eq_one L e hxN hx, map_one]
  exact not_hasKind_graphField_of_pow_three K hn hτ3 hk

end Cube

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof
