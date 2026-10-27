module

public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofU4

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)
open scoped commutatorElement

namespace Item21Early3Proof

variable {G : Type} [Group G]

theorem le_of_mem_fourGroupsMinus {E U L : Subgroup G} (hU : U ∈ fourGroupsMinus E)
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hdec : ∀ e ∈ E, ∃ x ∈ E ⊓ Subgroup.centralizer (U : Set G), ∃ y ∈ E ⊓ L, e = x * y) :
    U ≤ L := by
  rw [hU.2, Subgroup.commutator_le]
  intro u hu e he
  obtain ⟨x, hx, y, hy, rfl⟩ := hdec e he
  have hxu' : u * x = x * u := Subgroup.mem_centralizer_iff.mp hx.2 u hu
  have hyL : y ∈ L := hy.2
  have h1 : u * y * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hUL hu) y).mp hyL
  have h2 : u * y * u⁻¹ * y⁻¹ ∈ L := L.mul_mem h1 (L.inv_mem hyL)
  have h3 : x * (u * y * u⁻¹ * y⁻¹) * x⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hEL hx.1) _).mp h2
  have e1 : ⁅u, x * y⁆ = x * (u * y * u⁻¹ * y⁻¹) * x⁻¹ := by
    rw [commutatorElement_def]
    calc u * (x * y) * u⁻¹ * (x * y)⁻¹ = (u * x) * y * u⁻¹ * y⁻¹ * x⁻¹ := by group
      _ = (x * u) * y * u⁻¹ * y⁻¹ * x⁻¹ := by rw [hxu']
      _ = x * (u * y * u⁻¹ * y⁻¹) * x⁻¹ := by group
  rw [e1]
  exact h3

end Item21Early3Proof

open Item21Early3Proof

end CFSG.RankThree.PartTwo.Sec21
