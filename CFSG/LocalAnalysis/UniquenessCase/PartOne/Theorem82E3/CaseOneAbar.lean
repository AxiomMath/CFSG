module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLbar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLie

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3

theorem pRank_lbar (c : Ctx82E3 D) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup c.Lbar) = CFSG.Open.pRank p c.L := by
  haveI : (CFSG.Open.pCore 2 ↥c.L).Normal := CFSG.pCore_normal
  have h3 : ¬ p ∣ Nat.card (CFSG.Open.pCore 2 ↥c.L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := p)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Fact.out hp2
  rw [CFSG.SectionRank.pRank_quotient_eq (p := p) (N := CFSG.Open.pCore 2 ↥c.L) h3,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup c.L]

end Ctx82E3

namespace Case811Sylow

variable {c : Ctx82E3 D}

theorem A_le_L (h : Case811Sylow c) : h.A ≤ c.L := h.A_le.trans h.P_le_L

abbrev Abar (h : Case811Sylow c) : Subgroup c.Lbar :=
  (h.A.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))

theorem isElemAbelian_Abar (h : Case811Sylow c) : CFSG.Open.IsElemAbelian 3 h.Abar :=
  (h.elemAbelian.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))

theorem card_Abar (h : Case811Sylow c) : Nat.card h.Abar = 27 := by
  have h2 : ¬ 2 ∣ Nat.card h.A := by
    rw [h.card_A]
    norm_num
  change Nat.card ((h.A.subgroupOf c.L).map
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) = 27
  rw [Ctx82E3.card_map_lbar c h.A_le_L h2, h.card_A]

theorem map_le_Abar (h : Case811Sylow c) {X : Subgroup G} (hXA : X ≤ h.A) :
    (X.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) ≤ h.Abar :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono c.L hXA)

theorem card_map_of_le_A (h : Case811Sylow c) {X : Subgroup G} (hXA : X ≤ h.A) :
    Nat.card ((X.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))) =
      Nat.card X := by
  have hodd : ¬ 2 ∣ Nat.card X := by
    intro h2
    have hdvd : Nat.card X ∣ 27 := by
      rw [← h.card_A]
      exact Subgroup.card_dvd_of_le hXA
    exact absurd (h2.trans hdvd) (by norm_num)
  exact Ctx82E3.card_map_lbar c (hXA.trans h.A_le_L) hodd

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
