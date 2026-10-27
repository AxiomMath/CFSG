module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.D_le_inf_centralizer {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) :
    D ≤ Bs ⊓ Subgroup.centralizer (J : Set G) := by
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  rw [hD]
  exact le_inf (inf_le_left.trans hcfg.2.1.1) inf_le_right

theorem GGResHyp.D_le_inf_centralizer {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    D ≤ Bs ⊓ Subgroup.centralizer (J : Set G) :=
  GGConfig.D_le_inf_centralizer hH.1

@[expose] def GGResHigherFieldRootTwo {G : Type} [Group G] (p : ℕ) (B Bs J : Subgroup G) : Prop :=
  ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ J ∧
    B ≤ Subgroup.normalizer (T : Set G)

theorem GGConfig.iOne_of_rootTwo {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hT : GGResHigherFieldRootTwo p B Bs J) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D :=
  le_antisymm (ggStdSubBstarCentralizer_of_twoSubgroup hcfg hT)
    (GGConfig.D_le_inf_centralizer hcfg)

theorem GGResHyp.iOne_of_rootTwo {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hT : GGResHigherFieldRootTwo p B Bs J) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D :=
  GGConfig.iOne_of_rootTwo hH.1 hT

theorem GGConfig.iOne_iff_card_ne_p3 {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hp : p.Prime) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D ↔
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≠ p ^ 3 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  have hDle : D ≤ Bs ⊓ Subgroup.centralizer (J : Set G) :=
    GGConfig.D_le_inf_centralizer hcfg
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hHle : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hcfg
  have hHp : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) :=
    (CFSG.Open.IsElemAbelian.isPGroup hcfg.2.1.2.1).to_le inf_le_left
  constructor
  · intro hiOne
    rw [hiOne, hDcard]
    exact fun h => (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 3)).ne h
  · intro hcard
    by_contra hne
    have hlt : D < Bs ⊓ Subgroup.centralizer (J : Set G) :=
      lt_of_le_of_ne hDle (Ne.symm hne)
    have hcardlt : Nat.card D < Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) :=
      Subgroup.card_lt_of_lt hlt
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hHp
    have hkgt : p ^ 2 < p ^ k := by rwa [hDcard, hk] at hcardlt
    have hkle : p ^ k ≤ p ^ 3 := by rwa [hk] at hHle
    have hk2 : 2 < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hkgt
    have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hkle
    have hk3' : k = 3 := by omega
    exact hcard (by rw [hk, hk3'])

theorem GGResHyp.iOne_iff_card_ne_p3 {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D ↔
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≠ p ^ 3 :=
  GGConfig.iOne_iff_card_ne_p3 hH.1 hH.1.1.2.2.2.2.2.1.1

theorem GGResHyp.card_eq_p3_of_ne {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hne : Bs ⊓ Subgroup.centralizer (J : Set G) ≠ D) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := by
  by_contra hcard
  exact hne ((GGResHyp.iOne_iff_card_ne_p3 hH).mpr hcard)

theorem GGResHyp.B_lt_Bs_of_iOne_ne {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hne : Bs ⊓ Subgroup.centralizer (J : Set G) ≠ D) :
    B < Bs := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 :=
    GGResHyp.card_eq_p3_of_ne hH hne
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) :=
    hH.1.2.2.1.2.2.2.2.2.2
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hBne : B ≠ Bs := by
    intro hEq
    have hHD : Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
      rw [← hEq, ← hD]
    rw [hHD, hDcard] at hcard
    exact (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 2 < 3)).ne hcard
  exact lt_of_le_of_ne hH.1.2.1.1 hBne

theorem GGResHyp.exactThree_data_of_iOne_ne {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hne : Bs ⊓ Subgroup.centralizer (J : Set G) ≠ D) :
    ∃ r : ℕ, Nat.card Bs = p ^ r ∧ 5 ≤ r ∧
      Nat.card (ggGamma J hH.Bs_le_normalizer_J).range = p ^ (r - 3) ∧ B < Bs := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  letI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 :=
    GGResHyp.card_eq_p3_of_ne hH hne
  have hBsp : IsPGroup p Bs := CFSG.Open.IsElemAbelian.isPGroup hH.1.2.1.2.1
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).mp hBsp
  obtain ⟨hr5, himg⟩ := hH.card_range_gamma_J_of_exactThree_centralizer hr hcard
  exact ⟨r, hr, hr5, himg, GGResHyp.B_lt_Bs_of_iOne_ne hH hne⟩

theorem GGResHyp.iOne_of_eq_bstar {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hEq : B = Bs) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) :=
    hH.1.2.2.1.2.2.2.2.2.2
  rw [← hEq, ← hD]

end CFSG.StandardType

end
