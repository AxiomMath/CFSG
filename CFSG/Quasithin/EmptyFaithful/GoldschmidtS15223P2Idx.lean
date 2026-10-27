module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Cfg

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem index_normalizer_le_two [Finite G] {I X : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hX : IsBlock2 I X) (h3 : 3 ∣ Nat.card X) :
    ((Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I).index ≤ 2 := by
  classical
  set N' : Subgroup ↥I := (Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I with hN'
  by_contra hcon
  push Not at hcon
  have : Fintype (↥I ⧸ N') := Fintype.ofFinite _
  have hlt : 2 < Fintype.card (↥I ⧸ N') := by
    rw [← Nat.card_eq_fintype_card]
    exact hcon
  obtain ⟨q₁, q₂, q₃, h12, h13, h23⟩ := Fintype.two_lt_card_iff.mp hlt
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  obtain ⟨g₃, rfl⟩ := QuotientGroup.mk_surjective q₃
  have key : ∀ a b : ↥I, conjByElt (a : G) X = conjByElt (b : G) X →
      (QuotientGroup.mk a : ↥I ⧸ N') = QuotientGroup.mk b := by
    intro a b hab
    rw [QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, (a⁻¹ * b).2⟩
    have e1 : conjByElt ((a : G)⁻¹ * (b : G)) X = conjByElt (a : G)⁻¹ (conjByElt (b : G) X) :=
      C2Eleven.conjByElt_mul _ _ _
    rw [← hab, ← C2Eleven.conjByElt_mul, inv_mul_cancel, C2Eleven.conjByElt_one] at e1
    exact C2Eleven.mem_normalizer_iff_conjByElt.mpr e1
  have hblk : ∀ a : ↥I, IsBlock2 I (conjByElt (a : G) X) := fun a =>
    isBlock2_conjByElt_of_normalizer1515c hX (Subgroup.le_normalizer a.2)
  have hcard : ∀ a : G, 3 ∣ Nat.card (conjByElt a X) := fun a => by
    rw [card_conjByElt]
    exact h3
  exact not_three_blocks hC19 hchar hrank (hblk g₁) (hblk g₂) (hblk g₃) (hcard _) (hcard _)
    (hcard _) (fun h => h12 (key _ _ h)) (fun h => h13 (key _ _ h)) (fun h => h23 (key _ _ h))

theorem normal_normalizer_inf [Finite G] {I X : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hX : IsBlock2 I X) (h3 : 3 ∣ Nat.card X) :
    ((Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I).Normal := by
  have hle := index_normalizer_le_two hC19 hchar hrank hX h3
  have hpos : 0 < ((Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  rcases Nat.lt_or_ge ((Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I).index 2 with h | h
  · have h1 : ((Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I).index = 1 := by omega
    rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.normal_top
  · exact Subgroup.normal_of_index_eq_two (by omega)

theorem mem_of_index_le_two {K : Type*} [Group K] [Finite K] {N : Subgroup K} (h : N.index ≤ 2)
    (a b c : K) : a⁻¹ * b ∈ N ∨ a⁻¹ * c ∈ N ∨ b⁻¹ * c ∈ N := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have : Fintype (K ⧸ N) := Fintype.ofFinite _
  have hlt : Fintype.card (K ⧸ N) ≤ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact h
  have hne : ∀ x y : K, x⁻¹ * y ∉ N → (QuotientGroup.mk x : K ⧸ N) ≠ QuotientGroup.mk y :=
    fun x y hxy heq => hxy (QuotientGroup.eq.mp heq)
  have := Fintype.two_lt_card_iff.mpr ⟨QuotientGroup.mk a, QuotientGroup.mk b,
    QuotientGroup.mk c, hne _ _ h1, hne _ _ h2, hne _ _ h3⟩
  omega

theorem isSylowIn_inf_of_block [Finite G] {I S X : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hS : IsSylowTwoOf S I)
    (hX : IsBlock2 I X) (h3 : 3 ∣ Nat.card X) : IsSylowIn 2 (S ⊓ X) X := by
  set N : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ I with hN
  have hNI : N ≤ I := inf_le_right
  have hXN : X ≤ N := le_inf Subgroup.le_normalizer hX.2.1
  have hNn : (N.subgroupOf I).Normal := normal_normalizer_inf hC19 hchar hrank hX h3
  have hS' : IsSylowIn 2 S I := ⟨hS.1, hS.2.1, hS.2.2⟩
  have hSN : IsSylowIn 2 (S ⊓ N) N := hS'.inf_normal hNI hNn
  have hXn : (X.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mpr inf_le_left
  have hSX := hSN.inf_normal hXN hXn
  have : S ⊓ N ⊓ X = S ⊓ X := by
    rw [inf_assoc, inf_eq_right.mpr hXN]
  rwa [this] at hSX

end CFSG.Quasithin.S15223
