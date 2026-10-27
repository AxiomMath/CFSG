module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGConfig.card_B_eq {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    Nat.card B = p ^ LargeEvenTwoLocalRank p G :=
  hcfg.1.2.2.2.2.2.2.1.1.2.1

theorem GGConfig.data_L {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) :
    x ∈ Subgroup.centralizer (L : Set G) ∧ x ≠ 1 ∧ x ^ p = 1 ∧ commutator ↥L = ⊤ := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  refine ⟨?_, hS.2.2.1, hS.1.1.2 x hS.2.1, hS.2.2.2.1.2.2.1⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)

theorem GGResHyp.data_K {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) :
    y ∈ Subgroup.centralizer (K : Set G) ∧ y ≠ 1 ∧ y ^ p = 1 ∧ commutator ↥K = ⊤ := by
  have hSH : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  obtain ⟨hB, hyB, hy1, hKy, -⟩ := hSH
  refine ⟨?_, hy1, hB.1.2 y hyB, (hH.2.2.1.2 y K hH.2.2.2.2.1).1⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)

end CFSG.StandardType

end
