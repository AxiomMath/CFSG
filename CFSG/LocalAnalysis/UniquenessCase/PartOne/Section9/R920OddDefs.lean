module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs14
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

@[expose] def R920odd (D : Data G) : Prop :=
  ∀ L D₃ Y H : Subgroup G, PartTwo.Hyp919c D L D₃ Y H → Y ≤ L →
    ∀ q : ℕ, q.Prime → 5 < q → IsL2Odd (Bar2 Y) q →
      ∃ A : Subgroup G, A ≤ Y ∧ (Nat.card A).Prime ∧ Odd (Nat.card A) ∧
        ¬ normalizer (A : Set G) ≤ D.M

structure Shape919 (X : Type) [Group X] [Finite X] : Prop where
  simple : IsSimpleGroup X
  three_dvd : 3 ∣ Nat.card X
  thin : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1
  card_mulAut_dvd : Nat.card (MulAut X) ∣ 2 * Nat.card X
  not_alt_five : ¬ IsAlt X 5

theorem Shape919.of_mulEquiv {X X' : Type} [Group X] [Group X'] [Finite X] [Finite X']
    (e : X ≃* X') (h : Shape919 X) : Shape919 X' where
  simple := e.isSimpleGroup_congr.mp h.simple
  three_dvd := by
    rw [← Nat.card_congr e.toEquiv]
    exact h.three_dvd
  thin p hp hp2 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact h.thin p hp hp2
  card_mulAut_dvd := by
    rw [← Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr e.toEquiv]
    exact h.card_mulAut_dvd
  not_alt_five := fun ⟨f⟩ => h.not_alt_five ⟨e.trans f⟩

structure SliceCore (D : Data G) (L D₃ Y H : Subgroup G) : Prop where
  hyp : PartTwo.Hyp919c D L D₃ Y H
  yl : Y ≤ L
  facts : Shape919 (Bar2 Y)

structure Slice (D : Data G) (L D₃ Y H : Subgroup G) (q : ℕ) : Prop
    extends SliceCore D L D₃ Y H where
  prime : q.Prime
  gt : 5 < q
  shape : IsL2Odd (Bar2 Y) q

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem L_mem (S : SliceCore D L D₃ Y H) : L ∈ calC D.M := S.hyp.1

theorem D₃_le (S : SliceCore D L D₃ Y H) : D₃ ≤ L := S.hyp.2.1

theorem D₃_card (S : SliceCore D L D₃ Y H) : Nat.card D₃ = 3 := S.hyp.2.2.1

theorem D₃_mem (S : SliceCore D L D₃ Y H) : D₃ ∈ uniqueSet D.M := S.hyp.2.2.2.1

theorem Y_le_M (S : SliceCore D L D₃ Y H) : Y ≤ D.M := S.hyp.2.2.2.2.1

theorem H_ne_top (S : SliceCore D L D₃ Y H) : H ≠ ⊤ := S.hyp.2.2.2.2.2.2.2.2.1

theorem Y_le_H (S : SliceCore D L D₃ Y H) : Y ≤ H := S.hyp.2.2.2.2.2.2.2.2.2.1

theorem not_H_le_M (S : SliceCore D L D₃ Y H) : ¬ H ≤ D.M := S.hyp.2.2.2.2.2.2.2.2.2.2

theorem L_eq (S : SliceCore D L D₃ Y H) : L = Y ⊔ pCoreOf 2 L := by
  have h := S.hyp.2.2.2.2.2.1
  rwa [inf_eq_right.mpr S.yl] at h

theorem L_le_M (S : SliceCore D L D₃ Y H) : L ≤ D.M := S.L_mem.1.le

end SliceCore

theorem not_isAlt_five_of_isL2Odd {X : Type} [Group X] {p : ℕ} (hp5 : 5 < p)
    (hLp : IsL2Odd X p) : ¬ IsAlt X 5 := by
  rintro ⟨e5⟩
  have hcard : Nat.card X = 60 := by
    rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hpprime : p.Prime := hLp.admissible.1
  have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
  have hcard2 : 2 * Nat.card X = p * (p ^ 2 - 1) := by
    have h := hLp.card_eq_lieOrd (by norm_num)
    rw [show Nat.card X = ordA 1 p from by
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h]
    exact CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hpodd
  have hp7 : 7 ≤ p := by
    by_contra h
    have hp6 : p = 6 := by omega
    rw [hp6] at hpprime
    norm_num at hpprime
  have h49 : 49 ≤ p ^ 2 := by nlinarith
  have h48 : 48 ≤ p ^ 2 - 1 := by omega
  have hge : 7 * 48 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hp7 h48
  omega

theorem r920odd_of_r920c (D : Data G) (h : PartTwo.R920c D) : R920odd D := by
  intro L D₃ Y H hyp _ q _ hq5 hLq
  rcases h L D₃ Y H hyp with ⟨-, -, -, -, A, hA⟩ | ⟨n, -, hL2, -⟩ | ⟨n, -, hL2, -⟩ | h4
  · exact ⟨A, hA⟩
  · exact (not_isL2_of_isL2Odd hq5 hLq hL2).elim
  · exact (not_isL2_of_isL2Odd hq5 hLq hL2).elim
  · exact (not_isAlt_five_of_isL2Odd hq5 hLq h4).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
