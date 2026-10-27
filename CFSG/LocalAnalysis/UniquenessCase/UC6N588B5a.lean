module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C621b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S28
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qe

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)

namespace Mz614

variable {G : Type} [Group G] [Finite G]

theorem exists_l2_sylow (m : Mz614 G) (h620 : m.C620) (hL : LieModel ↥m.L .PSL 2 m.r 2) :
    ∃ P : Sylow m.r ↥m.L, IsSylowOf m.r (P : Subgroup ↥m.L) ⊤ ∧
      (m.A ⊓ m.L).subgroupOf m.L = (P : Subgroup ↥m.L) := by
  classical
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hS0card : Nat.card ((m.A ⊓ m.L).subgroupOf m.L) = m.r ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact m.card_A_inf_L h620
  have hS0p : IsPGroup m.r ((m.A ⊓ m.L).subgroupOf m.L) := IsPGroup.of_card hS0card
  obtain ⟨P, hSP⟩ := hS0p.exists_le_sylow
  have hPsyl : IsSylowOf m.r (P : Subgroup ↥m.L) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hPcard := (UC22.uc22p22q_psl2_sylow_elem m.hr m.d.odd hL hPsyl).2
  exact ⟨P, hPsyl, Subgroup.eq_of_le_of_card_ge hSP (by rw [hPcard, hS0card])⟩

theorem c621_of_L2 (m : Mz614 G) (h620 : m.C620) (hL : LieModel ↥m.L .PSL 2 m.r 2) :
    m.C621 := by
  classical
  obtain ⟨P, hPsyl, hSP_eq⟩ := exists_l2_sylow m h620 hL
  set S0 : Subgroup ↥m.L := (m.A ⊓ m.L).subgroupOf m.L with hS0
  intro W' hW'B hW'N
  have hsub : W'.subgroupOf m.L ≤ S0 := fun x hx => hW'B hx
  have hinv : ∀ g ∈ normalizer ((S0 : Subgroup ↥m.L) : Set ↥m.L), ∀ w ∈ W'.subgroupOf m.L,
      g * w * g⁻¹ ∈ W'.subgroupOf m.L := by
    intro g hg w hw
    have hgN : (g : G) ∈ normalizer ((m.A ⊓ m.L : Subgroup G) : Set G) :=
      (mem_normalizer_subgroupOf_iff_uc6 inf_le_right).1 hg
    have hgW : (g : G) ∈ m.L ⊓ normalizer (m.A : Set G) :=
      ⟨g.2, mem_normalizer_A_of_mem_normalizer_E h620 g.2 hgN⟩
    have h1 := (mem_normalizer_iff.1 (hW'N hgW) (w : G)).1 hw
    show ((g * w * g⁻¹ : ↥m.L) : G) ∈ W'
    simpa using h1
  rcases UC22.uc22p22q_psl2_borel_irr m.hr m.d.odd hL (hSP_eq ▸ hPsyl) hsub hinv with h0 | h0
  · left
    rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ m.L := (hW'B hx).2
    have : (⟨x, hxL⟩ : ↥m.L) ∈ W'.subgroupOf m.L := hx
    rw [h0, mem_bot] at this
    rw [mem_bot]
    exact congrArg Subtype.val this
  · right
    refine le_antisymm hW'B fun x hx => ?_
    have : (⟨x, hx.2⟩ : ↥m.L) ∈ S0 := hx
    rw [← h0] at this
    exact this

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
