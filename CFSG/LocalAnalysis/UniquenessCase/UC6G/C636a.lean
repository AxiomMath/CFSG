module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.O633Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6C636a

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22

namespace UC6G

open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {Dat : Data G}

namespace Mz614

variable (m : Mz614 Dat)

theorem normalizer_Z_le_normalizer_L : normalizer (m.Z : Set G) ≤ normalizer (m.L : Set G) := by
  intro n hn
  exact mem_normalizer_Opp_uc6 (mem_normalizer_inftyOf_uc6 (mem_normalizer_centralizer_uc6 hn)) m.r

theorem commutator_L_eq (hq : CFSG.Open.IsQuasisimple ↥m.L) : ⁅m.L, m.L⁆ = m.L := by
  have h := Subgroup.map_commutator (⊤ : Subgroup ↥m.L) ⊤ m.L.subtype
  have htop : (⊤ : Subgroup ↥m.L).map m.L.subtype = m.L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : ⁅(⊤ : Subgroup ↥m.L), ⊤⁆ = ⊤ := hq.1
  rw [htop] at h
  rw [← h, h1]
  exact htop

theorem OL_le_centralizer (hq : CFSG.Open.IsQuasisimple ↥m.L) (hr : m.r ∣ Nat.card ↥m.L) :
    m.OL ≤ centralizer (m.L : Set G) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  rcases normal_dichotomy_uc6 hq (CFSG.pPrimeCore m.r ↥m.L) with hc | htop
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [mem_centralizer_iff]
    intro l hl
    have := mem_center_iff.1 (hc hp) ⟨l, hl⟩
    exact congrArg Subtype.val this
  · exfalso
    have hcop : Nat.Coprime m.r (Nat.card (CFSG.pPrimeCore m.r ↥m.L)) := CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hcop
    exact m.hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hr)

theorem le_centralizer_of_comm_le_OL (hq : CFSG.Open.IsQuasisimple ↥m.L) (hr : m.r ∣ Nat.card ↥m.L)
    {Q : Subgroup G} (hQ : ⁅Q, m.L⁆ ≤ m.OL) : Q ≤ centralizer (m.L : Set G) := by
  have hQc : ⁅Q, m.L⁆ ≤ centralizer (m.L : Set G) := hQ.trans (m.OL_le_centralizer hq hr)
  have h1 : ⁅⁅Q, m.L⁆, m.L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hQc
  have h2 : ⁅⁅m.L, Q⁆, m.L⁆ = ⊥ := by rw [Subgroup.commutator_comm m.L Q]; exact h1
  have h3 : ⁅⁅m.L, m.L⁆, Q⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [m.commutator_L_eq hq] at h3
  exact Subgroup.le_centralizer_iff.2 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3)

end Mz614

end UC6G

end CFSG.LocalAnalysis.UniquenessCase
