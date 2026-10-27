module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SteinbergConjugateBounds


public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem pRank_le_one_of_card_eq_sixty {X : Type} [Group X] [Finite X]
    {H : Subgroup X} (hcard : Nat.card H = 60) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q H ≤ 1 := by
  refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := H) (p := q) (k := 1) hq ?_
  have h60 : 2 ^ 2 * ([3, 5] : List ℕ).prod = 60 := by norm_num
  have hl : ∀ p ∈ ([3, 5] : List ℕ), p.Prime := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Nat.prime_three
    · exact Nat.prime_five
  have hnd : ([3, 5] : List ℕ).Nodup := by decide
  have hcop : Nat.Coprime q (2 ^ 2) :=
    CFSG.SectionRank.coprime_pow_of_ne hq Nat.prime_two hq2 2
  have hnot : ¬ q ^ 2 ∣ 2 ^ 2 * ([3, 5] : List ℕ).prod :=
    CFSG.SectionRank.not_sq_dvd_of_factorization hq hcop [3, 5] hl hnd
  rw [h60] at hnot
  rw [hcard]
  simpa using hnot

variable {G : Type} [Group G] [Finite G]

theorem s168e3_s_le_three_of_alt_five {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5) :
    s15 D.M V₀ V hV L ≤ 3 := by
  classical
  have hHcard : Nat.card ↥(lBar V₀ V hV L) = 60 :=
    Om8Excl.card_isAlt_five hA5
  have hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1 :=
    fun q hq hq2 => pRank_le_one_of_card_eq_sixty hHcard hq hq2
  have h3 : 3 ∣ Nat.card (lBar V₀ V hV L) := by
    rw [hHcard]
    norm_num
  obtain ⟨t, -, -, -, -, hW⟩ := c.conc
  obtain ⟨K, hK, hbar⟩ :=
    s16h_exists_cover D c.std.h127 c.std.h119 c.setting.hyp151.hyp125 hcomp
  have hRkK : CFSG.Open.pRank 3 K = 1 :=
    s16h_pRank_three_eq_one_of_thin_cover D c.setting hcomp hW hthin h3 hK hbar
  exact s168e3_s_le_three_of_pRank_one_cover c hK hbar hRkK

theorem s168e3_s_le_three_of_listTwo {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) :
    s15 D.M V₀ V hV L ≤ 3 := by
  unfold s15ListTwo at hL2
  rcases hL2 with hL3 | hA5
  · exact s168e3_s_le_three c hcomp hL3
  · exact s168e3_s_le_three_of_alt_five c hcomp hA5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
