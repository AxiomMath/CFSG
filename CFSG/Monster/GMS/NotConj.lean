module

public import CFSG.Monster.GMS.Defs
public import CFSG.Monster.GMS.Basic

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

variable {G : Type*} [Group G]

theorem GMSDoubleF2Centralizer.card_pCore_le_two [Finite G] {d₀ : B} {a : G}
    (h : GMSDoubleF2Centralizer d₀ a) :
    Nat.card (pCore 2 (Subgroup.centralizer ({a} : Set G))) ≤ 2 := by
  obtain ⟨ha, hperf, H, _, φ, hφ, hker, hsimp, -⟩ := h
  have : IsSimpleGroup H := hsimp
  exact card_pCore_centralizer_le_two ha (exists_not_commute_of_perfect hperf φ hφ) φ hφ hker

theorem GMSF1Type.not_isConj [Finite G] {d₀ : B} {a z : G} (h : GMSF1Type d₀ a z) :
    ¬ IsConj a z := by
  refine not_isConj_of_card_pCore h.1.card_pCore_le_two ?_
  rw [h.2.2.2.1]
  norm_num

end CFSG.Monster.GMS
