
module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.Centralization
public import CFSG.Adapters.ProjectiveSpecialLinear

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement
open CFSG.SectionRank.Ccomm

theorem mulAut_comm_of_isCyclic {G : Type*} [Group G] [IsCyclic G] (a b : MulAut G) :
    a * b = b * a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg (a g))
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg (b g))
  ext x
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  have h1 : a (b (g ^ k)) = g ^ (i * j * k) := by
    calc a (b (g ^ k)) = a ((b g) ^ k) := by rw [map_zpow]
      _ = (a (b g)) ^ k := by rw [map_zpow]
      _ = (a (g ^ j)) ^ k := by rw [← hj]
      _ = ((a g) ^ j) ^ k := by rw [map_zpow]
      _ = ((g ^ i) ^ j) ^ k := by rw [← hi]
      _ = g ^ (i * j * k) := by rw [← zpow_mul, ← zpow_mul, mul_assoc]
  have h2 : b (a (g ^ k)) = g ^ (j * i * k) := by
    calc b (a (g ^ k)) = b ((a g) ^ k) := by rw [map_zpow]
      _ = (b (a g)) ^ k := by rw [map_zpow]
      _ = (b (g ^ i)) ^ k := by rw [← hi]
      _ = ((b g) ^ i) ^ k := by rw [map_zpow]
      _ = ((g ^ j) ^ i) ^ k := by rw [← hj]
      _ = g ^ (j * i * k) := by rw [← zpow_mul, ← zpow_mul, mul_assoc]
  show a (b (g ^ k)) = b (a (g ^ k))
  rw [h1, h2, mul_comm i j]

theorem le_center_of_isCyclic_normal {X : Type*} [Group X] [Group.IsPerfect X] {N : Subgroup X}
    [N.Normal] (hN : IsCyclic ↥N) : N ≤ Subgroup.center X := by
  have h := perfect_hom_eq_one_of_range_comm (MulAut.conjNormal : X →* MulAut ↥N)
    (fun a _ b _ => mulAut_comm_of_isCyclic a b)
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  have h2 := congrArg (fun f : X →* MulAut ↥N => ((f g ⟨n, hn⟩ : ↥N) : X)) h
  simp only [MulAut.conjNormal_apply, MonoidHom.one_apply, MulAut.one_apply] at h2
  exact mul_inv_eq_iff_eq_mul.1 h2

variable {X : Type} [Group X]

end CFSG.Quasithin.A36B
