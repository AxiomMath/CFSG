module

public import CFSG.RankThree.PartOne.Q1327.Comp
public import CFSG.RankThree.PartOne.N143.SectionReduce

public section

namespace CFSG.RankThree.PartOne.Q1327R

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.Q1327

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mem_thetaComponents_of_simple {p : ℕ} (hp : p.Prime) {M K B : Subgroup G}
    (hKM : K ≤ M) (hBM : B ≤ M) (hK : K.subgroupOf M ∈ thetaComponents p ↥M)
    (hBn : ∀ y ∈ M, ∀ b ∈ B, y * b * y⁻¹ ∈ B) (hBq : CFSG.IsQuasisimple ↥B)
    (hBz : Subgroup.center ↥B = ⊥) {z : G} (hzK : z ∈ K) (hzB : z ∈ B) (hz1 : z ≠ 1) :
    K = B := by
  obtain ⟨-, hBsimple, -⟩ := N143.simple_of_quasisimple_center_bot hBq hBz
  have eB : ↥(B.subgroupOf M) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBM
  have hBq' : CFSG.IsQuasisimple ↥(B.subgroupOf M) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eB.symm hBq
  have hBnormal : (B.subgroupOf M).Normal := ⟨fun x hx g => by
    have hxB : (x : G) ∈ B := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr (hBn g g.2 x hxB)⟩
  have hBθ : B.subgroupOf M ∈ thetaComponents p ↥M :=
    mem_thetaComponents_of_quasisimple hp hBq' (Subgroup.Normal.isSubnormal hBnormal)
  have hBK : B ≤ K := by
    have hsn1 : ((K.subgroupOf M).subgroupOf (B.subgroupOf M)).IsSubnormal :=
      hK.2.1.subgroupOf
    have hs1 : IsSimpleGroup ↥(B.subgroupOf M) := eB.isSimpleGroup
    rcases hsn1.eq_bot_or_top_of_isSimpleGroup hs1 with hbot | htop
    · exfalso
      have hmem : (⟨⟨z, hBM hzB⟩, Subgroup.mem_subgroupOf.mpr hzB⟩ : ↥(B.subgroupOf M)) ∈
          (K.subgroupOf M).subgroupOf (B.subgroupOf M) :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hzK)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hz1 (congrArg (fun y : ↥(B.subgroupOf M) => ((y : ↥M) : G)) hmem)
    · intro b hb
      have : (⟨⟨b, hBM hb⟩, Subgroup.mem_subgroupOf.mpr hb⟩ : ↥(B.subgroupOf M)) ∈
          (K.subgroupOf M).subgroupOf (B.subgroupOf M) := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp this)
  obtain ⟨hP0, hPperf⟩ := subgroupOf_ne_bot_perfect hBM hBq
  have hPK : B.subgroupOf M ≤ K.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hBK (Subgroup.mem_subgroupOf.mp hx))
  have heq := theta_component_eq_of_perfect_le hp hK hBθ hP0 hPperf hPK le_rfl
  ext x
  constructor
  · intro hx
    have : (⟨x, hKM hx⟩ : ↥M) ∈ K.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at this
    exact Subgroup.mem_subgroupOf.mp this
  · exact fun hx => hBK hx

end CFSG.RankThree.PartOne.Q1327R
