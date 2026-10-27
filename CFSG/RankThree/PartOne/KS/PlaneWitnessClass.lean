module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.CentralizerOfInnerTrivial

public section

namespace CFSG.RankThree.PartOne

open Subgroup

section Generic

variable {G : Type} [Group G]

theorem exists_conj_mem_sylow [Finite G] {p : ℕ} (hp : p.Prime) {P Q : Subgroup G}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P) {y : G} (hyP : y ∈ P)
    (hord : orderOf y = p) : ∃ g : G, g ∈ P ∧ g⁻¹ * y * g ∈ Q := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S₀, hS₀⟩ := hSyl
  have hpgrp : IsPGroup p (zpowers (⟨y, hyP⟩ : P)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord, pow_one])
  obtain ⟨S, hS⟩ := hpgrp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S₀ S
  have hyS : (⟨y, hyP⟩ : P) ∈ (S : Subgroup P) := hS (Subgroup.mem_zpowers _)
  refine ⟨g, g.2, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
  rw [hS₀, Subgroup.mem_subgroupOf] at hyS
  simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using hyS

theorem exists_sylow_of_card [Finite G] {p : ℕ} (hp : p.Prime) {P Q : Subgroup G} (hQP : Q ≤ P)
    (hcard : Nat.card Q = p ^ (Nat.card P).factorization p) :
    ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨Sylow.ofCard (Q.subgroupOf P) ?_, rfl⟩
  rw [← hcard]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv

end Generic

end CFSG.RankThree.PartOne
