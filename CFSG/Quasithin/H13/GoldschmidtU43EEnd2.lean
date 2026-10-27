module

public import CFSG.Quasithin.H13.GoldschmidtU43EEnd1
public import CFSG.GH74.Uniqueness.SE

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.GH74.Uniqueness

variable {G : Type} [Group G]

theorem false_of_borel_case [Finite G] {L X : Subgroup G} (hXL : X ≤ L) (hs : IsSimpleGroup ↥X)
    (hnot2 : ¬ IsPGroup 2 ↥X) {x : G} (hxX : x ∈ X) (hxo : orderOf x = 2)
    (hK : ∀ o ∈ CFSG.pPrimeCore 2 ↥L, (o : G) ∈ X)
    (hB : ∃ P : Sylow 2 (↥L ⧸ CFSG.pPrimeCore 2 ↥L),
      (X.comap L.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥L)) =
        Subgroup.normalizer ((P : Subgroup (↥L ⧸ CFSG.pPrimeCore 2 ↥L)) : Set _)) : False := by
  obtain ⟨P, hP⟩ := hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : (CFSG.pPrimeCore 2 ↥L).Normal := CFSG.pPrimeCore_normal
  have hKodd : Nat.Coprime 2 (Nat.card (CFSG.pPrimeCore 2 ↥L)) := CFSG.pPrimeCore_coprime_card
  set K : Subgroup ↥L := CFSG.pPrimeCore 2 ↥L with hKdef
  set π : ↥L →* ↥L ⧸ K := QuotientGroup.mk' K with hπ
  set X' : Subgroup ↥L := X.comap L.subtype with hX'
  have hxL : x ∈ L := hXL hxX
  have hxX' : (⟨x, hxL⟩ : ↥L) ∈ X' := hxX
  have hKX' : K ≤ X' := fun k hk => hK k hk
  have hs' : IsSimpleGroup ↥X' := MulEquiv.isSimpleGroup (Subgroup.subgroupOfEquivOfLe hXL)
  have hK1 : ∀ k : ↥L, k ∈ K → k = 1 := by
    have : (K.subgroupOf X').Normal := Subgroup.normal_subgroupOf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf X') with h | h
    · intro k hk
      have hmem : (⟨k, hKX' hk⟩ : ↥X') ∈ K.subgroupOf X' := Subgroup.mem_subgroupOf.mpr hk
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      have hle : X' ≤ K := Subgroup.subgroupOf_eq_top.mp h
      have hxK : (⟨x, hxL⟩ : ↥L) ∈ K := hle hxX'
      have h1 : orderOf (⟨x, hxL⟩ : ↥L) ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hxK
      rw [Subgroup.orderOf_mk, hxo] at h1
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hKodd h1
  set Pc : Subgroup ↥L := (P : Subgroup (↥L ⧸ K)).comap π with hPc
  have hXπ : ∀ t : ↥L, t ∈ X' →
      π t ∈ Subgroup.normalizer ((P : Subgroup (↥L ⧸ K)) : Set (↥L ⧸ K)) := by
    intro t ht
    rw [← hP]
    exact ⟨t, ht, rfl⟩
  have hPcX' : Pc ≤ X' := by
    intro l hl
    have hlP : π l ∈ (P : Subgroup (↥L ⧸ K)) := hl
    have hl' : π l ∈ Subgroup.normalizer ((P : Subgroup (↥L ⧸ K)) : Set (↥L ⧸ K)) :=
      Subgroup.le_normalizer hlP
    rw [← hP] at hl'
    obtain ⟨t, ht, htl⟩ := hl'
    have hkt : t⁻¹ * l ∈ K := QuotientGroup.eq.mp htl
    have : l = t * (t⁻¹ * l) := by group
    rw [this]
    exact X'.mul_mem ht (hKX' hkt)
  have hPcnorm : (Pc.subgroupOf X').Normal := by
    refine ⟨fun t ht g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    have hg := (Subgroup.mem_normalizer_iff.mp (hXπ (g : ↥L) g.2)) (π (t : ↥L))
    show π ((g : ↥L) * (t : ↥L) * (g : ↥L)⁻¹) ∈ (P : Subgroup (↥L ⧸ K))
    rw [map_mul, map_mul, map_inv]
    exact hg.mp ht
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Pc.subgroupOf X') with h | h
  ·
    have hPc1 : ∀ l : ↥L, l ∈ Pc → l = 1 := by
      intro l hl
      have hmem : (⟨l, hPcX' hl⟩ : ↥X') ∈ Pc.subgroupOf X' := Subgroup.mem_subgroupOf.mpr hl
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    have hP1 : (P : Subgroup (↥L ⧸ K)) = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective K q
      have hl1 : l = 1 := hPc1 l hq
      rw [hl1, map_one]
      exact Subgroup.one_mem _
    have h2L : 2 ∣ Nat.card ↥L := by
      have h1 : orderOf (⟨x, hxL⟩ : ↥L) ∣ Nat.card ↥L := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk, hxo] at h1
    have h2Q : 2 ∣ Nat.card (↥L ⧸ K) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K] at h2L
      exact Nat.Coprime.dvd_of_dvd_mul_right hKodd h2L
    have hidx := P.not_dvd_index
    rw [hP1, Subgroup.index_bot] at hidx
    exact hidx h2Q
  ·
    apply hnot2
    intro g
    have hgL : (g : G) ∈ L := hXL g.2
    have hlX' : (⟨g, hgL⟩ : ↥L) ∈ X' := g.2
    have hlPc : (⟨g, hgL⟩ : ↥L) ∈ Pc := by
      have : (⟨(⟨g, hgL⟩ : ↥L), hlX'⟩ : ↥X') ∈ Pc.subgroupOf X' := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have hlP : π ⟨g, hgL⟩ ∈ (P : Subgroup (↥L ⧸ K)) := hlPc
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨π ⟨g, hgL⟩, hlP⟩
    refine ⟨k, ?_⟩
    have h1 : (π ⟨g, hgL⟩) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : (⟨g, hgL⟩ : ↥L) ^ 2 ^ k ∈ K := by
      apply (QuotientGroup.eq_one_iff _).mp
      show π ((⟨g, hgL⟩ : ↥L) ^ 2 ^ k) = 1
      rw [map_pow]
      exact h1
    have h3 := hK1 _ h2
    apply Subtype.ext
    have h4 := congrArg Subtype.val h3
    simpa using h4

theorem false_of_stronglyEmbedded_simple [Finite G]
    {X : Subgroup G} (hSE : CFSG.IsStronglyEmbedded X) (hs : IsSimpleGroup ↥X)
    (hnot2 : ¬ IsPGroup 2 ↥X) {x : G} (hxX : x ∈ X) (hxo : orderOf x = 2)
    {y : G} (hyo : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y) : False := by
  have hXL : X ≤ involutionClosure G := le_involutionClosure_of_simple hs hxX hxo
  rcases S_SE_proof G X hSE with h | ⟨-, hK, hB⟩
  · have := two_le_pRank_involutionClosure hxo hyo hxy hne
    omega
  · exact false_of_borel_case hXL hs hnot2 hxX hxo hK hB

end CFSG.Quasithin.H13.U43
