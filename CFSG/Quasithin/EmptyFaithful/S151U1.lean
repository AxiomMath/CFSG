module

public import CFSG.Quasithin.EmptyFaithful.S151XD
public import CFSG.Quasithin.EmptyFaithful.S151U0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem pCore_odd_eq_bot_of_mem_cComp {X L : Subgroup G} (hL : L ∈ cComp X) (hO : oddCoreIn X = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.pCore p ↥L = ⊥ := by
  set P : Subgroup ↥L := CFSG.pCore p ↥L with hP
  have hPn : P.Normal := CFSG.pCore_normal
  have hPL : P.map L.subtype ≤ L := Subgroup.map_subtype_le P
  have hcomap : (P.map L.subtype).subgroupOf L = P :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective P
  have hnormL : ((P.map L.subtype).subgroupOf L).Normal := by rw [hcomap]; exact hPn
  have hsubL : IsSubnormal (P.map L.subtype) L := A3.subnormal_of_normal hPL hnormL
  have hsubX : IsSubnormal (P.map L.subtype) X := A3.subnormal_trans hsubL (subnormal_of_mem_cComp hL)
  have hodd : Odd (Nat.card (P.map L.subtype)) := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p) (G := ↥L)).exists_card_eq
    rw [← Nat.card_congr (P.equivMapOfInjective L.subtype L.subtype_injective).toEquiv, hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hle := le_oddCoreIn_of_isSubnormal1515c hsubX hodd
  rw [hO] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective P L.subtype_injective).mp (le_bot_iff.mp hle)

theorem input15122Dichotomy_holds : Input15122Dichotomy := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc
  have hcomp : L ∈ cComp (g1_1516 Z₁) := hc.hL.comp
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hcomp)
  rcases s151u_centralizer_pCore_le_or_quasisimple hperf hc.hL.quasi
      (fun p hp hp2 => pCore_odd_eq_bot_of_mem_cComp hcomp hc.h19.one hp hp2) with h | h
  · left
    have h' : Subgroup.centralizer (CFSG.Open.pCore 2 ↥L : Set ↥L) ≤ CFSG.Open.pCore 2 ↥L := by
      exact h
    exact (centralizer_pCore_le_iff_pCoreOf 2 L).1 h'
  · right
    exact ⟨le_of_mem_cComp hcomp, subnormal_of_mem_cComp hcomp,
      Group.isPerfect_def.mp h.1, h.2.1⟩

end CFSG.Quasithin
