module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup

theorem exists_conj_mem_of_complement {G : Type*} [Group G] [Finite G] {N M : Subgroup G}
    [N.Normal] (hdisj : N ⊓ M = ⊥) (hprod : ∀ g : G, ∃ n ∈ N, ∃ m ∈ M, g = n * m) {p : ℕ}
    (hp : p.Prime) (hN : ¬ p ∣ Nat.card N) {x : G} (hx : orderOf x = p) :
    ∃ y : G, y * x * y⁻¹ ∈ M := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomp : Subgroup.IsComplement' N M := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hdisj) ?_
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨n, hn, m, hm, rfl⟩ := hprod g
    exact ⟨n, hn, m, hm, rfl⟩
  have hcard : Nat.card N * Nat.card M = Nat.card G := hcomp.card_mul_card
  have hfM : (Nat.card G).factorization p = (Nat.card M).factorization p := by
    rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    have : (Nat.card N).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hN
    simp [this]
  obtain ⟨RM⟩ : Nonempty (Sylow p M) := inferInstance
  set R' : Subgroup G := (RM : Subgroup M).map M.subtype with hR'
  have hR'card : Nat.card R' = p ^ (Nat.card G).factorization p := by
    have h1 : Nat.card R' = Nat.card (RM : Subgroup M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [h1, Sylow.card_eq_multiplicity, hfM]
  set RS : Sylow p G := Sylow.ofCard R' hR'card with hRS
  have hxp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨R, hxR⟩ := hxp.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G R RS
  refine ⟨y, ?_⟩
  have hxmem : x ∈ (R : Subgroup G) := hxR (Subgroup.mem_zpowers x)
  have hmem : y * x * y⁻¹ ∈ ((y • R : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨x, hxmem, by simp [MulAut.conj_apply]⟩
  rw [hy] at hmem
  obtain ⟨m, -, hm⟩ := hmem
  rw [← hm]
  exact m.2

end CFSG.RankThree.PartOne.TCX
