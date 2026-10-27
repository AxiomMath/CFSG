module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly

@[expose] def GGHdRo7SULCoordHyp {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧ GGInnerDiagAll p B Bs x L D J ∧
    GGNoTransvection p Bs

theorem hdRo7SULCoordAux_hyp_of_resHyp {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : GGHdRo7SULCoordHyp p B Bs x L D J :=
  ⟨hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.1⟩

@[expose] def GGHdRo7SULabL {G : Type} [Group G] (p : ℕ) (L : Subgroup G) : Prop :=
  ∃ labL : LargeEvenLabel, LargeEvenInLambda2 labL ∧
    GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) ∧ p = 3 ∧ labL.tag = .twA ∧ labL.n = 1 ∧
      6 ≤ labL.rank ∧ ¬ 3 ∣ labL.rank + 1

theorem hdRo7SULCoordAux_labL_of_row {G : Type} [Group G] {p : ℕ} {J L : Subgroup G}
    (hrow : GGResRowAt ggRowSUCorank2 p J L) : GGHdRo7SULabL p L := by
  obtain ⟨labJ, labL, -, hlabL, -, hLlab, hrowData⟩ := hrow
  obtain ⟨hp3, -, -, hLtag, hLn, -, hrank6, h3m⟩ := hrowData
  exact ⟨labL, hlabL, hLlab, hp3, hLtag, hLn, hrank6, h3m⟩

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SULCoordAux_rowDataCfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hrow : GGHdRo7SULabL p L) :
    ∃ (m : ℕ) (hx : x ∈ Bs), p = 3 ∧ 7 ≤ m ∧ ¬ 3 ∣ m := by
  obtain ⟨labL, -, -, hp3, -, -, hrank6, h3m⟩ := hrow
  refine ⟨labL.rank + 1, ?_, hp3, by omega, h3m⟩
  obtain ⟨-, -, -, -, -, -, hSStar, -⟩ := hH.1.1
  exact hH.1.2.1.1 hSStar.2.1

theorem hdRo7SULCoordAux_centralizerCfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hp3 : p = 3) :
    Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxp : x ^ p = 1 := hcfg.2.1.2.1.2 x hxBs
  have hx3 : x ^ 3 = 1 := by rw [← hp3]; exact hxp
  have hLCx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hLCx hl) x (Set.mem_singleton x)).symm
  have hle : Subgroup.zpowers x ≤ Bs ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hxBs, hxC⟩
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hcardle : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
    simpa [hp3] using GGConfig.card_bstar_centralizer_le hcfg
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardx]; exact hcardle)).symm

theorem hdRo7SULCoordAux_centralizer {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3) :
    Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
  hdRo7SULCoordAux_centralizerCfg (hdRo7SULCoordAux_hyp_of_resHyp hH) hp3

end CFSG.StandardType.HdRo7SU
