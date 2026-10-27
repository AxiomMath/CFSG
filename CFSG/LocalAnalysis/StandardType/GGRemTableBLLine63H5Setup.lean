module

public import CFSG.LocalAnalysis.StandardType.GGUnitDvdLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLCover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType.Line63.H5

open CFSG.Assembly CFSG.StandardType

theorem config_card_rank {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hlt : Nat.card Bs < p ^ 5) :
    Nat.card Bs = p ^ 4 ∧ LargeEvenTwoLocalRank p G ≤ 4 := by
  obtain ⟨hp, hBs, -, -, h4⟩ := hcfg.tableB_facts
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hrank : LargeEvenTwoLocalRank p G ≤ 4 := by
    by_contra h
    push Not at h
    have : p ^ 5 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h
    omega
  refine ⟨?_, hrank⟩
  have hp3 : IsPGroup p Bs := fun g => ⟨1, Subtype.ext (by simpa using hBs.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp3
  rw [hk] at hlt h4 ⊢
  have h1 : 4 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).mp h4
  have h2 : k < 5 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  have : k = 4 := by omega
  rw [this]

theorem config_cyclic_sylow {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S :=
  hcfg.1.2.2.2.2.2.2.1.2.2.2.2

theorem config_selfCent {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
  hcfg.2.1.2.2.2

end CFSG.StandardType.Line63.H5

end
