module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggKGPos_prime_rank_ge_four {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    p.Prime ∧ p ≠ 2 ∧ 4 ≤ LargeEvenTwoLocalRank p G := by
  obtain ⟨hp, hp2, -, h4⟩ := h.1.1.1.2.2.2.2.2.1
  exact ⟨hp, hp2, h4⟩

theorem ggKGPos_exists_central_elt {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) :
    ∃ y : G, y ∈ B ∧ y ≠ 1 ∧ y ^ p = 1 ∧ X ≤ Subgroup.centralizer ({y} : Set G) ∧
      B ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers y := by
  obtain ⟨hp, -, -⟩ := ggKGPos_prime_rank_ge_four h
  rcases hX with hXL | hXK
  · have hS : LargeEvenSStar p B x L := h.1.1.1.2.2.2.2.2.2.1
    rw [hXL]
    exact ⟨x, hS.2.1, hS.2.2.1, hS.1.1.2 x hS.2.1, hS.2.2.2.1.1,
      inf_centralizer_eq_zpowers_of_sstar hp hS⟩
  · obtain ⟨y, hnb⟩ := h.2.2.2.1.2 X hXK
    have hS : LargeEvenSHat p B y X := hnb.1
    exact ⟨y, hS.2.1, hS.2.2.1, hS.1.1.2 y hS.2.1, hS.2.2.2.1,
      inf_centralizer_eq_zpowers_of_sHat hS⟩

theorem ggKGPos_pow_mul_card_le {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) :
    p ^ (LargeEvenTwoLocalRank p G - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤
      Nat.card ↥Bs := by
  obtain ⟨hp, -, h4⟩ := ggKGPos_prime_rank_ge_four h
  obtain ⟨y, -, hy1, hyp, -, hBC⟩ := ggKGPos_exists_central_elt h hX
  have := Fact.mk hp
  have hBBs : B ≤ Bs := h.1.1.2.1.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := h.1.1.1.2.2.2.2.2.2.1.1.2.1
  set C : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hC
  have hBC' : B ⊓ C = Subgroup.zpowers y := by
    rw [hC, ← inf_assoc, inf_eq_left.mpr hBBs, hBC]
  have h1 : B.relIndex C * p = Nat.card C := by
    have := Subgroup.relIndex_mul_card B C
    rwa [hBC', Nat.card_zpowers, orderOf_eq_prime hyp hy1] at this
  have h2 : B.relIndex Bs * p ^ LargeEvenTwoLocalRank p G = Nat.card Bs := by
    have := Subgroup.relIndex_mul_card B Bs
    rwa [inf_eq_left.mpr hBBs, hBcard] at this
  have hne : B.relIndex Bs ≠ 0 := fun h0 =>
    (Nat.card_pos (α := Bs)).ne' (by rw [← h2, h0, zero_mul])
  have h3 : B.relIndex C ≤ B.relIndex Bs :=
    Subgroup.relIndex_le_of_le_right inf_le_left hne
  have hpm : p ^ (LargeEvenTwoLocalRank p G - 1) * p = p ^ LargeEvenTwoLocalRank p G := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  calc p ^ (LargeEvenTwoLocalRank p G - 1) * Nat.card C
      = B.relIndex C * (p ^ (LargeEvenTwoLocalRank p G - 1) * p) := by rw [← h1]; ring
    _ ≤ B.relIndex Bs * p ^ LargeEvenTwoLocalRank p G := by
        rw [hpm]; exact Nat.mul_le_mul_right _ h3
    _ = Nat.card Bs := h2

end CFSG.StandardType

end
