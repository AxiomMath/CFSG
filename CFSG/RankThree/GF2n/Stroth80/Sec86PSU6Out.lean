module

public import CFSG.RankThree.GF2n.Stroth80.Sec84InputStmt
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.RankThree.PartOne.CTP.OutEmbed

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank

section Certs

theorem exists_prime_pow_of_card_sq {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) : ∃ p j : ℕ, p.Prime ∧ 1 ≤ j ∧ q = p ^ j := by
  classical
  haveI := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
  rw [Nat.card_eq_fintype_card, hcard] at hK
  have hdvd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [hK]; ring⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  subst hj
  have h2 : p ^ (n : ℕ) = p ^ (2 * j) := by rw [hK, ← pow_mul, mul_comm]
  have hn : (n : ℕ) = 2 * j := Nat.pow_right_injective hp.two_le h2
  have hn1 : 1 ≤ (n : ℕ) := n.2
  exact ⟨p, j, hp, by omega, rfl⟩

theorem psu6OutSolvable_holds : PSU6OutSolvableStatement := by
  intro q Y _ _ F _ hF hC
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hF
  obtain ⟨p, j, hp, hj, rfl⟩ := exists_prime_pow_of_card_sq hK
  haveI : Fact p.Prime := ⟨hp⟩
  have hnq : ((6 : ℕ), p ^ j) ≠ (3, 2) := by simp
  haveI : IsSimpleGroup (StatedProj (StatedSU 6 (p ^ j) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p j hK 6 (by norm_num) hnq
  haveI : Group.IsPerfect (StatedSU 6 (p ^ j) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := p) (f := j) hK (n := 6) (by norm_num)
      hnq
  haveI : Group.IsPerfect (StatedProj (StatedSU 6 (p ^ j) K)) := inferInstance
  haveI hS : IsSimpleGroup ↥F := e.isSimpleGroup
  haveI : Group.IsPerfect ↥F :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hnonab : ∃ a b : ↥F, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative ↥F := ⟨⟨fun a b => hcon a b⟩⟩
    exact Group.IsPerfect.not_isMulCommutative ↥F inferInstance
  have hcl : StatedClassicalModel ↥F .PSU 6 p j :=
    ⟨⟨hp, hj, by norm_num, hnq⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  have hcat : CFSG.Assembly.InCatalog ↥F :=
    CFSG.ClassicalModels.inCatalog_of_statedClassicalModel ↥F .PSU 6 p j hcl
  haveI : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥F) :=
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds ↥F hnonab hcat
  have hcen : Subgroup.center ↥F = ⊥ := by
    rcases (Subgroup.center ↥F).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      have ha : a ∈ Subgroup.center ↥F := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hSc : Subgroup.centralizer (F : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxF : x ∈ F := hC hx
    have hz : (⟨x, hxF⟩ : ↥F) ∈ Subgroup.center ↥F := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
    rw [hcen, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  exact CFSG.RankThree.PartOne.CTP.solvable_quotient_of_outer F hSc

end Certs

end CFSG.RankThree.GF2n.Stroth80
