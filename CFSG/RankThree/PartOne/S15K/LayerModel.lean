module

public import CFSG.RankThree.PartOne.S15K.BlockModel
public import CFSG.RankThree.PartOne.S15K.ThetaLayer

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G]

@[expose] def LayerModelData (p : ℕ) (E I : Subgroup G) : Prop :=
  ∀ b ∈ E, b ≠ 1 → ∃ (ι : Type) (Q : ι → Subgroup G),
    (∀ i, Q i ≤ I ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    (∀ i, IsComponent ((Q i).subgroupOf (I ⊓ Subgroup.centralizer ({b} : Set G)))) ∧
    ⁅I ⊓ Subgroup.centralizer ({b} : Set G), I ⊓ Subgroup.centralizer ({b} : Set G)⁆ = ⨆ i, Q i ∧
    ∀ i, BlockModel p ↥(Q i)

theorem LayerModelData.blockModel_of_mem_thetaComponentsAt {p : ℕ} (hp : p.Prime)
    {E I : Subgroup G} (hL : LayerModelData p E I) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt p b) (hYI : Y ≤ I) : BlockModel p ↥Y := by
  obtain ⟨ι, Q, hQH, hQc, hder, hQT⟩ := hL b hb hb1
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hY).1
  obtain ⟨i, rfl⟩ := eq_component_of_mem_thetaComponentsAt hp inf_le_right Q hQH hQc hder hY
    (le_inf hYI hYC)
  exact hQT i

end CFSG.RankThree.PartOne.S15K
