module

public import CFSG.Quasithin.EmptyFaithful.R3c5Two
public import CFSG.Quasithin.EmptyFaithful.R3c6Exc
public import CFSG.Quasithin.EmptyFaithful.R3c6Spor

public section

namespace CFSG.Quasithin.R3c6

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.Quasithin.R3c5

theorem isSz_of_mulEquiv' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {f : ℕ} (h : IsSz f Y) :
    IsSz f X := by
  obtain ⟨hp, a, ha, K, _, _, hf, hK, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, inferInstance, inferInstance, hf, hK, ⟨e.trans e'⟩⟩

section Cases

theorem notOdd_lemma115LieCharTwo {X : Type} [Group X] (hnoSz : ¬ ∃ e : ℕ, IsSz e X)
    (hlie : Lemma115LieCharTwo X) : ¬ IsOddOrder (Nat.card X) := by
  rcases hlie with ((⟨f, hfam⟩ | hTits) | ⟨n, hn, hPSL⟩) | ⟨⟨e⟩⟩ | hU33
  · rcases hfam with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
      ⟨hodd, hf, hm⟩ | ⟨hodd, hf, hm⟩
    · exact notOdd_psl2_two (by omega) hm
    · exact notOdd_psl3_two hf hm
    · exact notOdd_psu3_two (by omega) hm
    · exact notOdd_psp4_two (by omega) hm
    · exact notOdd_g2_two (by omega) hm
    · exact notOdd_3d4_two hf hm
    · exact notOdd_2f4_two (by omega) hm
    · exact (hnoSz ⟨f, hm⟩).elim
  · exact notOdd_tits hTits
  · rcases hn with rfl | rfl
    · exact notOdd_l4 hPSL
    · exact notOdd_l5 hPSL
  · exact notOdd_alt6 e
  · exact notOdd_u33 hU33

variable {G : Type} [Group G] [Finite G]

theorem not_isOddOrder_of_lemma115 {L : Subgroup G} {z : G} (hcases : Lemma115Cases L z)
    (hq : CFSG.IsQuasisimple ↥L) (hcen : centerOf L = pCoreOf 2 L)
    (hnoSz : ¬ ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) :
    ¬ IsOddOrder (Nat.card (↥L ⧸ Subgroup.center ↥L)) := by
  rcases hcases with ⟨hs, hlie, -⟩ | ⟨-, hcpc, hL34, -⟩ | ⟨φ, σ, -, -, -⟩ | ⟨φ, σ, -, -, -⟩ |
    ⟨hE, -⟩ | ⟨⟨s, hs, ⟨e⟩⟩, -⟩
  ·
    have hp : Group.IsPerfect ↥L := hq.1
    let eC := R3c3.quotCenterEquivOfSimple hs hp
    rw [Nat.card_congr eC.toEquiv]
    exact notOdd_lemma115LieCharTwo (fun ⟨e, he⟩ => hnoSz ⟨e, isSz_of_mulEquiv' eC he⟩) hlie
  ·
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hcpc).toEquiv]
    rcases hL34 with hm | hm
    · exact notOdd_psl3_two (by norm_num) hm
    · exact notOdd_g2_two (by norm_num) hm
  ·
    exact notOdd_alt6 φ
  ·
    exact notOdd_alt7 φ
  ·
    have hp : Group.IsPerfect ↥L := hq.1
    rcases hE with hL33 | ⟨p, hFM, hm⟩
    · have hs : IsSimpleGroup ↥L := (psl3Data hL33).2.1
      rw [Nat.card_congr (R3c3.quotCenterEquivOfSimple hs hp).toEquiv]
      exact notOdd_l33 hL33
    · have hs : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hm).2
      rw [Nat.card_congr (R3c3.quotCenterEquivOfSimple hs hp).toEquiv]
      exact notOdd_psl2_prime hm
  ·
    have hcpc : Subgroup.center ↥L = CFSG.pCore 2 ↥L :=
      le_antisymm (by exact R3c3.center_le_pCore_of_centerOf_eq hcen)
        (CFSG.QuasithinUnique.Id2519.pCore_le_center_of_isQuasisimple hq)
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hcpc).toEquiv, Nat.card_congr e.toEquiv]
    exact notOdd_sporadic hs

theorem rankTwoListCatalogue_holds : RankTwoListCatalogue := by
  intro G _ _ L z hcases hQ hcen hnoSz _ s q hqmod hX
  obtain ⟨p, e, hp, he, hqe, hXs⟩ := hX
  by_cases hp2 : p = 2
  · subst hp2
    exact ⟨e, hqe, hXs⟩
  · exfalso
    subst hqe
    exact not_isOddOrder_of_lemma115 hcases hQ hcen hnoSz
      (isOddOrder_of_isPSLEps3 hp2 hqmod hXs)

end Cases

end CFSG.Quasithin.R3c6
