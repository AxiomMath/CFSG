module

import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec21.Implications

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

theorem subsingleton_of_isPerfect_of_isSolvable {X : Type*} [Group X] (hp : Group.IsPerfect X)
    (hs : Group.IsSolvable X) : Subsingleton X := by
  obtain ⟨n, hn⟩ := hs.solvable
  have htop : ∀ k : ℕ, derivedSeries X k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hp.commutator_eq_top]
  rw [htop n] at hn
  exact ⟨fun a b => by
    have ha : a ∈ (⊤ : Subgroup X) := Subgroup.mem_top a
    have hb : b ∈ (⊤ : Subgroup X) := Subgroup.mem_top b
    rw [hn, Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩

theorem inSubgroup_theta_eq_bot_of_isSimpleGroup [Finite G] {L : Subgroup G}
    (hperf : Group.IsPerfect L) [IsSimpleGroup L] :
    inSubgroup (aschbacherSolvableCore 3) L = ⊥ := by
  have hn := aschbacherSolvableCore_normal 3 L
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 L) with h | h
  · rw [inSubgroup, h, Subgroup.map_bot]
  · exfalso
    have hsolv := (solvable_prime_complement_core_characterization (H := L)
      Nat.prime_three).1
    rw [h] at hsolv
    have hsL : Group.IsSolvable L :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom) (MulEquiv.surjective _)
    have := subsingleton_of_isPerfect_of_isSolvable hperf hsL
    exact not_subsingleton L this

noncomputable def mulEquiv_lBar_of_theta_eq_bot {L : Subgroup G}
    (h : inSubgroup (aschbacherSolvableCore 3) L = ⊥) : L ≃* lBar L :=
  have h' : aschbacherSolvableCore 3 L = ⊥ := by
    rw [inSubgroup] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h
  (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq h'.symm)

theorem isSimpleGroup_projSp_two {n : ℕ} (hn : 2 ≤ n) :
    IsSimpleGroup (projSp 2 (GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 n
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_⟩, GaloisField 2 n, inferInstance, inferInstance,
    GaloisField.card 2 n (by omega),
    ⟨(CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSp 2 (GaloisField 2 n))).symm⟩⟩
  intro h
  have h2 : 2 ^ n = 2 ^ 1 := by
    have := (Prod.mk.inj h).2
    simpa using this
  have := Nat.pow_right_injective le_rfl h2
  omega

theorem isSimpleGroup_projSU {m n : ℕ} (hm : 4 ≤ m) (hn : 1 ≤ n) :
    IsSimpleGroup (projSU m 2 n) :=
  CFSG.PGLModel.isSimpleGroup_projSU_of_admissible ⟨Nat.prime_two, hn, by omega, fun h => by have := (Prod.mk.inj h).1; omega⟩

theorem inSubgroup_theta_eq_bot_of_mulEquiv [Finite G] {L : Subgroup G} {X : Type*} [Group X]
    [IsSimpleGroup X] (hperf : Group.IsPerfect L) (e : L ≃* X) :
    inSubgroup (aschbacherSolvableCore 3) L = ⊥ := by
  have : IsSimpleGroup L := e.isSimpleGroup
  exact inSubgroup_theta_eq_bot_of_isSimpleGroup hperf

end CFSG.RankThree.PartTwo.Sec21
