module

public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1519
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
import CFSG.RankThree.PartTwo.Sec15.Item1511Meta
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1519U38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ¬ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 3

variable {G : Type} [Group G] [Finite G]

theorem not_isoLThreePi_two_two_of_ctx1514 {A : Subgroup G} {c : G} {L Y : Subgroup G}
    (h : Sec15R G A c L) (h1510 : Item1510 A) (hbr : Sec16.Step169TwoBridge)
    (hctx : Ctx1514 A (lB A) c L Y) :
    ¬ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 2 := by
  rintro (⟨-, ⟨φ⟩⟩ | ⟨h2, -⟩)
  · obtain ⟨-, -, -, -, -, hprod, -, -, hΩ⟩ := hctx.concl1515
    have hiso := hbr G A c L h ⟨φ⟩ hprod
    obtain ⟨c', L', hL', hc', hne⟩ := h1510
    have hc'c : Subgroup.zpowers c' = Subgroup.zpowers c := by
      rw [hΩ] at hc'
      exact hc'
    have hL'c : L' ∈ lA A c := lA_eq_of_zpowers_eq hc'c ▸ hL'
    have h9 : Nat.card ↥(A ⊓ L) = 9 :=
      card_inf_eq_nine h.toSec13Data (isPerfect_lBar h.toSec13Data) hprod.some
    obtain ⟨f, hfAL, hfc⟩ : ∃ f ∈ A ⊓ L, f ∉ Subgroup.zpowers c := by
      by_contra hall
      push Not at hall
      have hle := Subgroup.card_le_of_le (show A ⊓ L ≤ Subgroup.zpowers c from hall)
      rw [h9, h.toSec13Data.card_zpowers] at hle
      omega
    have hL'L : L' = L :=
      eq_of_mem_lA_of_mem h.mem_thetaComponentsAt hL'c hfAL.1 hfAL.2 hfc
    subst hL'L
    exact hne.false hiso.some
  · norm_num at h2

theorem step1519Small_of (h1510 : Item1510R) (hbr : Sec16.Step169TwoBridge)
    (hU38 : Step1519U38) : Step1519Small := by
  intro G _ _ A c L h Y hctx m hiso
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact not_isoLThreePi_two_two_of_ctx1514 h (h1510 G A c L h) hbr hctx hiso
  · rintro rfl
    exact hU38 G A c L h Y hctx hiso

end CFSG.RankThree.PartTwo.Sec15
