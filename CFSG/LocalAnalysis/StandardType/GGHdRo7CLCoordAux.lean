module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Assembly CFSG.Open

theorem hdRo7CLCoordAux_rank_ge_five {labJ labX : LargeEvenLabel}
    (hJ2 : LargeEvenInLambda2 labJ) (hnJ : labJ.n = 1)
    (htagJ : labJ.tag = LargeEvenLieTag.B ∨ labJ.tag = LargeEvenLieTag.C)
    (hrank : labX.rank = labJ.rank + 2) : 5 ≤ labX.rank := by
  unfold LargeEvenInLambda2 at hJ2
  have h2 : 2 ≤ labJ.rank := by
    rcases htagJ with h | h <;> rw [h] at hJ2 <;> exact hJ2.2.1
  have hne : labJ.rank ≠ 2 := by
    intro h
    have hle : 2 ≤ labJ.n := by
      rcases htagJ with hh | hh <;> rw [hh] at hJ2 <;> exact hJ2.2.2 h
    omega
  omega

theorem hdRo7CLCoordAux_row_data {G : Type} [Group G] {p : ℕ} {J L : Subgroup G}
    (hrow : GGResRowAt ggRowCorank2C p J L) :
    ∃ labJ labX : LargeEvenLabel, p = 3 ∧ 5 ≤ labX.rank := by
  obtain ⟨labJ, labX, hJ2, -, -, -, hp3, htagJ, hnJ, -, -, hrank⟩ := hrow
  exact ⟨labJ, labX, hp3, hdRo7CLCoordAux_rank_ge_five hJ2 hnJ htagJ hrank⟩

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J K : Subgroup G} {x y : G}

theorem hdRo7CLCoordAux_x_pow_eq_one
    (hH : GGResHyp p B Bs x L D J y K) : x ^ p = 1 :=
  hH.1.tableB_facts.2.1.2 x hH.1.tableB_facts.2.2.1

theorem hdRo7CLCoordAux_x_ne_one
    (hH : GGResHyp p B Bs x L D J y K) : x ≠ 1 :=
  hH.1.1.2.2.2.2.2.2.1.2.2.1

theorem hdRo7CLCoordAux_bstar_centralizer_eq
    (hH : GGResHyp p B Bs x L D J y K) :
    Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hp : Nat.Prime p := hcfg.tableB_facts.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hle : Subgroup.zpowers x ≤ Bs ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hxBs, hxL⟩
  have hcard_le : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    GGConfig.card_bstar_centralizer_le hcfg
  have horder : orderOf x = p :=
    orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH) (hdRo7CLCoordAux_x_ne_one hH)
  have hcard_z : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, horder]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard_z]; exact hcard_le)).symm

theorem hdRo7CLCoordAux_inf_ab
    (hH : GGResHyp p B Bs x L D J y K) : IsElemAbelian p (Bs ⊓ L) :=
  hH.1.tableB_facts.2.1.mono inf_le_left

theorem hdRo7CLCoordAux_card_bstar_ge
    (hH : GGResHyp p B Bs x L D J y K) : p ^ 4 ≤ Nat.card ↥Bs :=
  hH.1.tableB_facts.2.2.2.2

end CFSG.StandardType.HdRo7C

end
