module

public import CFSG.RankThree.PartOne.KF1514B.Geom
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.RankThree.OrthogonalInvolutions Module

theorem mem_of_odd_orderOf_of_relIndex_two' {G : Type*} [Group G] {N H : Subgroup G}
    (hidx : N.relIndex H = 2) {g : G} (hg : g ∈ H) (hodd : Odd (orderOf g)) : g ∈ N := by
  have hN : (N.subgroupOf H).index = 2 := hidx
  have : (N.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hN
  set x : ↥H := ⟨g, hg⟩ with hx
  have h2 : x ^ 2 ∈ N.subgroupOf H := by
    have := Subgroup.pow_index_mem (N.subgroupOf H) x
    rwa [hN] at this
  obtain ⟨k, hk⟩ := hodd
  have hord : orderOf x = 2 * k + 1 := by
    rw [hx, Subgroup.orderOf_mk]
    exact hk
  have : x = (x ^ 2) ^ (k + 1) := by
    have e : (x ^ 2) ^ (k + 1) = x ^ (2 * k + 1) * x := by
      rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
    rw [e, ← hord, pow_orderOf_eq_one, one_mul]
  have : x ∈ N.subgroupOf H := by
    rw [this]
    exact pow_mem h2 _
  exact Subgroup.mem_subgroupOf.mp this

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

theorem odd_mem_G0 {g : Vt K ≃ₗ[K] Vt K}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail 3 (minusTailForm K b c)))
    (hodd : Odd (orderOf g)) : g ∈ G0 b c := by
  have hQ := nondegenerate_polarBilin_quadTail (r := 3)
    (nondegenerate_minusTailForm (AnisoPair.hirr (b := b) (c := c)))
  have hT : ∃ T : Submodule K (Vt K), finrank K T = 3 ∧
      ∀ x ∈ T, quadTail 3 (minusTailForm K b c) x = 0 :=
    ⟨tailFlag K (Fin 2 → K) 3 3, finrank_tailFlag le_rfl,
      fun _ hx => quadTail_eq_zero_of_mem_tailFlag hx⟩
  have hder := (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1
  have hΩ : CFSG.RankThree.Classical2.orthDerived (quadTail 3 (minusTailForm K b c)) =
      omegaGroup (quadTail 3 (minusTailForm K b c)) hQ :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ)
      (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT)
  have hidx := relIndex_omegaGroup (quadTail 3 (minusTailForm K b c)) hQ
  have := mem_of_odd_orderOf_of_relIndex_two' hidx hg hodd
  rw [← hΩ, hder] at this
  exact this

end CFSG.RankThree.PartOne.KF1514B
