module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallCount
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section ThreeNat

variable {W : Type} [CommGroup W] [Finite W]

theorem ThreeNat.card_dvd_two_mul_card_mul_kBar_of_seven
    {A L T : Subgroup (MulAut W)} (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) :
    Nat.card ↥A ∣ (2 * Nat.card ↥L) * Nat.card ↥(s1t3KBar A L) := by
  classical
  let K := s1t3KBar A L
  obtain ⟨N, hNA, hLN, -, -, hNKbot, -, -⟩ := h.structure_of_seven h7
  have hcommLK : ∀ x ∈ L, ∀ y ∈ K, Commute x y := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 x hx
  have hLKbot : L ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxN : x ∈ N := hLN hx.1
    have hxNK : x ∈ N ⊓ K := ⟨hxN, hx.2⟩
    rw [hNKbot] at hxNK
    exact Subgroup.mem_bot.mp hxNK
  have hcardLK : Nat.card ↥(L ⊔ K) = Nat.card ↥L * Nat.card ↥K :=
    CFSG.card_sup_eq_mul_of_commute L K hcommLK hLKbot
  have hLKA : L ⊔ K ≤ A := sup_le h.le inf_le_left
  let S : Subgroup ↥A := (L ⊔ K).subgroupOf A
  have hthree : ∀ x y z : ↥A, x⁻¹ * y ∈ S ∨ x⁻¹ * z ∈ S ∨ y⁻¹ * z ∈ S := by
    intro x y z
    have hm := ThreeNat.index_kBar_le_two h h7 x.2 y.2 z.2
    rcases hm with hm | hm | hm
    · left
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hm)
    · right; left
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hm)
    · right; right
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hm)
  have hidx : S = ⊤ ∨ S.index = 2 := s16t3_index_eq_two_of_thirds S hthree
  have hScard : Nat.card ↥S = Nat.card ↥L * Nat.card ↥K :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLKA).toEquiv).trans hcardLK
  have hA : Nat.card ↥A = Nat.card ↥S * S.index := S.card_mul_index.symm
  have hidx12 : S.index = 1 ∨ S.index = 2 := by
    rcases hidx with htop | hidx2
    · left
      rw [htop, Subgroup.index_top]
    · exact Or.inr hidx2
  rw [hA, hScard]
  rcases hidx12 with hidx1 | hidx2
  · rw [hidx1, mul_one]
    exact ⟨2, by ring⟩
  · rw [hidx2]
    exact ⟨1, by ring⟩

end ThreeNat

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_kBar_card_and_simple_of_threeNat_alt_five
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hA5 : IsAlt ↥(lBar V₀ V hV L) 5)
    (h3 : 3 ∈ D.sig) :
    Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168 ∧
      IsSimpleGroup ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
  classical
  let A := Mbar D.M V₀ V hV
  let B := lBar V₀ V hV L
  let K := s1t3KBar A B
  have hT' : ThreeNat A B (barSub V₀ V hV D.T) := hT
  obtain ⟨N, hNA, hBN, hNfix, hNKcomm, hNKbot, hNKsup, hKcase⟩ :=
    hT'.structure_of_seven h7
  have hKcase' : Nat.card ↥K = 7 ∨ Nat.card ↥K = 21 ∨
      (Nat.card ↥K = 168 ∧ IsSimpleGroup ↥K) := hKcase
  rcases hKcase' with hK7 | hK21 | hK168
  ·
    exfalso
    have hdvdA : Nat.card ↥A ∣ (2 * Nat.card ↥B) * Nat.card ↥K :=
      ThreeNat.card_dvd_two_mul_card_mul_kBar_of_seven hT' h7
    have hB60 : Nat.card ↥B = 60 := by
      have h := s15k_six_alt_card hA5 (by norm_num : 2 ≤ 5)
      simpa [Nat.factorial] using h
    have h9A : 3 ^ 2 ∣ Nat.card ↥A := by
      have hrank : 2 ≤ CFSG.Open.pRank 3 A := c.two_le_pRank_mbar h3
      obtain ⟨E, hEA, -, hEcard⟩ :=
        CFSG.SectionRank.exists_pRank (G := MulAut (Vtil V₀ V hV))
          (by norm_num : 1 < 3) A
      have h9E : 3 ^ 2 ∣ Nat.card ↥E := by
        rw [hEcard]
        exact pow_dvd_pow 3 hrank
      exact h9E.trans (Subgroup.card_dvd_of_le hEA)
    rw [hB60, hK7] at hdvdA
    obtain ⟨k, hk⟩ := h9A.trans hdvdA
    norm_num at hk
    omega
  ·
    exfalso
    exact Setting16.false_of_kBar_order_21 c.setting c.std.h638 h3 hT' h7 hK21
  · exact hK168

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
