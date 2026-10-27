module

public import CFSG.RankThree.PartTwo.Sec17.Item1723Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec17.Item1725Proof

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Item1723N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
      {Y | Y ∈ scriptY1Star A (lB A) ∧ ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)} =
          {yI Y₁ w 1, yI Y₁ w 2, yI Y₁ w 3} ∧
        {Y | Y ∈ scriptY1Star A (lB A) ∧ ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)}.ncard = 3

namespace Proof1721

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem rank3II_17_23N_of (h : Sec17W G A c L Y₀ Y₁ S p P w Q) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L)
    (h1411 : Item1411_1 A (lB A)) (h1718 : Item1718)
    (h1720 : Sec4.autIn (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) A ≤
      Sec4.autIn (Subgroup.normalizer (S : Set G)) A)
    (h1722 : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Y₁ : Set G))
    (horb : ∀ g ∈ Subgroup.normalizer (A : Set G), ∃ i : ℕ,
      (S ⊓ L).map (MulAut.conj g).toMonoidHom = (S ⊓ L).map (MulAut.conj (w ^ i)).toMonoidHom)
    (hne : (S ⊓ L).map (MulAut.conj w).toMonoidHom ≠ S ⊓ L) :
    {Y | Y ∈ scriptY1Star A (lB A) ∧ ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)} =
        {yI Y₁ w 1, yI Y₁ w 2, yI Y₁ w 3} ∧
      {Y | Y ∈ scriptY1Star A (lB A) ∧ ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)}.ncard = 3 := by
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp h.w_mem).1
  have hy1 : yI Y₁ w 1 = Y₁ := by
    rw [yI, Nat.sub_self, pow_zero, map_conj_one]
  have hy2 : yI Y₁ w 2 = Y₁.map (MulAut.conj w).toMonoidHom := by
    rw [yI, show 2 - 1 = 1 from rfl, pow_one]
  have hy3 : yI Y₁ w 3 = Y₁.map (MulAut.conj (w ^ 2)).toMonoidHom := by
    rw [yI]
  have hset : {Y | Y ∈ scriptY1Star A (lB A) ∧ ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)} =
      {yI Y₁ w 1, yI Y₁ w 2, yI Y₁ w 3} := by
    ext Y
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hY, hYM⟩
      obtain ⟨g, hg, rfl⟩ := h.toSec17Y1.exists_conj_of_mem h166 hbot h168 h1411 hY hYM
      obtain ⟨i, hi3, hi⟩ := h.conj_eq_pow h166 hbot h168 horb h1720 h1722 hg
      rw [hi, hy1, hy2, hy3]
      interval_cases i
      · left
        rw [pow_zero, map_conj_one]
      · right; left
        rw [pow_one]
      · right; right
        rfl
    · rintro (rfl | rfl | rfl)
      · exact ⟨HeadProof.map_conj_mem_scriptY1Star (pow_mem hwA _) h.mem_y1Star, h.yI_not_le 1⟩
      · exact ⟨HeadProof.map_conj_mem_scriptY1Star (pow_mem hwA _) h.mem_y1Star, h.yI_not_le 2⟩
      · exact ⟨HeadProof.map_conj_mem_scriptY1Star (pow_mem hwA _) h.mem_y1Star, h.yI_not_le 3⟩
  refine ⟨hset, ?_⟩
  rw [hset, hy1, hy2, hy3]
  obtain ⟨h12, h13, h23⟩ := map_conj_pow_ne h.w_pow_three (h.map_conj_ne h1718 hne)
  exact Set.ncard_eq_three.mpr ⟨_, _, _, h12, h13, h23, rfl⟩

theorem item1723N_of (h166 : Item166S17) (hbot : Item145BotS17) (h168 : Item168S17)
    (h1411 : Item1411_1S17) (h1718 : Item1718) (h1720 : Claim1720) (h1722 : Item1722)
    (horb : Claim1723Orbit) : Item1723N :=
  fun G _ _ A c L Y₀ Y₁ S p P w Q h =>
    rank3II_17_23N_of h (h166 G A c L Y₀ h.toSec17Std) (hbot G A c L Y₀ h.toSec17Std)
      (h168 G A c L Y₀ h.toSec17Std) (h1411 G A c L Y₀ h.toSec17Std) h1718
      (rank3II_17_20_le_of h.toSec17Y1 h1720) (h1722 G A c L Y₀ Y₁ S p P h.toSec17Y1)
      (horb G A c L Y₀ Y₁ S p P w Q h).1 (horb G A c L Y₀ Y₁ S p P w Q h).2

end Proof1721

end CFSG.RankThree.PartTwo.Sec17
