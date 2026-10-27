module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA8Pair
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltGen
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res423Two

open Equiv Equiv.Perm Item434AltPerm

theorem factorization_card_alt8 : (Nat.card (alternatingGroup (Fin 8))).factorization 3 = 2 :=
  factorization_card_alternatingGroup (m := 2240) (by norm_num) (by decide) (by norm_num)

@[expose] def F08 : Subgroup (alternatingGroup (Fin 8)) :=
  (F0 8).subgroupOf (alternatingGroup (Fin 8))

theorem sign_vecPerm2_eight : ∀ v : Fin 2 → ZMod 3, vecPerm2 8 v ∈ alternatingGroup (Fin 8) := by
  intro v
  rw [mem_alternatingGroup, vecPerm2, Perm.sign_mul, map_pow, map_pow, signs_eight.1,
    signs_eight.2.1, one_pow, one_pow, one_mul]

theorem F0_eight_le : F0 8 ≤ alternatingGroup (Fin 8) := by
  rw [F0_eq_range f0Facts_eight]
  rintro _ ⟨v, rfl⟩
  exact sign_vecPerm2_eight _

theorem card_F08 : Nat.card F08 = 9 := by
  rw [← card_F0 f0Facts_eight]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe F0_eight_le).toEquiv

theorem F08_comm : ∀ a ∈ F08, ∀ b ∈ F08, a * b = b * a := by
  intro a ha b hb
  have hab := (isElemAbelian_F0 f0Facts_eight).1
  apply Subtype.ext
  have h := congrArg Subtype.val (hab.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  exact h

theorem vecPerm2_eight_cases : ∀ v : Fin 2 → ZMod 3, v ≠ 0 →
    vecPerm2 8 v = c1 8 ∨ vecPerm2 8 v = c1 8 ^ 2 ∨ vecPerm2 8 v = c2 8 ∨
      vecPerm2 8 v = c2 8 ^ 2 ∨ vecPerm2 8 v = c1 8 * c2 8 ∨
      vecPerm2 8 v = (c1 8 * c2 8) ^ 2 ∨ vecPerm2 8 v = c1 8 * c2 8 ^ 2 ∨
      vecPerm2 8 v = (c1 8 * c2 8 ^ 2) ^ 2 := by
  decide +kernel

theorem gens_pow_three : c1 8 ^ 3 = 1 ∧ c2 8 ^ 3 = 1 ∧ (c1 8 * c2 8) ^ 3 = 1 ∧
    (c1 8 * c2 8 ^ 2) ^ 3 = 1 := by
  decide +kernel

theorem core_centralizer_F08_eq_bot {b : alternatingGroup (Fin 8)} (hb : b ∈ F08)
    (hb1 : b ≠ 1) :
    aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set (alternatingGroup (Fin 8)))) =
      ⊥ := by
  apply core_eq_bot_of_thetaPerm
  have hP := thetaLike_thetaPerm b
  have hbF : (b : Perm (Fin 8)) ∈ F0 8 := hb
  rw [F0_eq_range f0Facts_eight] at hbF
  obtain ⟨v, hv⟩ := hbF
  change vecPerm2 8 (Multiplicative.toAdd v) = (b : Perm (Fin 8)) at hv
  have hv0 : Multiplicative.toAdd v ≠ 0 := by
    intro h0
    apply hb1
    apply Subtype.ext
    rw [← hv, h0]
    simp [vecPerm2]
  obtain ⟨h1, h2, h3, h4⟩ := gens_pow_three
  rw [← hv] at hP
  rcases vecPerm2_eight_cases _ hv0 with h | h | h | h | h | h | h | h <;> rw [h] at hP
  · exact eq_bot_of_thetaLike_c1 hP
  · exact eq_bot_of_thetaLike_c1 (hP.congr fun g => (commute_sq_iff h1 g).symm)
  · exact eq_bot_of_thetaLike_c2 hP
  · exact eq_bot_of_thetaLike_c2 (hP.congr fun g => (commute_sq_iff h2 g).symm)
  · exact eq_bot_of_thetaLike_pair (Or.inl rfl) hP
  · exact eq_bot_of_thetaLike_pair (Or.inl rfl) (hP.congr fun g => (commute_sq_iff h3 g).symm)
  · exact eq_bot_of_thetaLike_pair (Or.inr rfl) hP
  · exact eq_bot_of_thetaLike_pair (Or.inr rfl) (hP.congr fun g => (commute_sq_iff h4 g).symm)

theorem top_le_closure_F08 : (⊤ : Subgroup (alternatingGroup (Fin 8))) ≤
    Subgroup.closure {x : alternatingGroup (Fin 8) | ∃ b ∈ F08, b ≠ 1 ∧ x * b = b * x} := by
  set S := {x : alternatingGroup (Fin 8) | ∃ b ∈ F08, b ≠ 1 ∧ x * b = b * x} with hS
  have hc1 : c1 8 ∈ alternatingGroup (Fin 8) := signs_eight.1
  have hc2 : c2 8 ∈ alternatingGroup (Fin 8) := signs_eight.2.1
  have hc1F : (⟨c1 8, hc1⟩ : alternatingGroup (Fin 8)) ∈ F08 :=
    (Subgroup.mem_subgroupOf).mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hc2F : (⟨c2 8, hc2⟩ : alternatingGroup (Fin 8)) ∈ F08 :=
    (Subgroup.mem_subgroupOf).mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hc1ne : (⟨c1 8, hc1⟩ : alternatingGroup (Fin 8)) ≠ 1 := fun h =>
    isThreeCycle_c1_eight.ne_one (congrArg Subtype.val h)
  have hc2ne : (⟨c2 8, hc2⟩ : alternatingGroup (Fin 8)) ≠ 1 := fun h =>
    isThreeCycle_c2_eight.ne_one (congrArg Subtype.val h)
  have hgens : ∀ i : Fin 6, ∃ h : gens8 i ∈ alternatingGroup (Fin 8),
      (⟨gens8 i, h⟩ : alternatingGroup (Fin 8)) ∈ S := by
    intro i
    obtain ⟨hs, -, h1, h2⟩ := gens8_spec i
    refine ⟨hs, ?_⟩
    rcases Nat.lt_or_ge (i : ℕ) 3 with hi | hi
    · exact ⟨_, hc1F, hc1ne, Subtype.ext (h1 hi)⟩
    · exact ⟨_, hc2F, hc2ne, Subtype.ext (h2 hi)⟩
  have hmap : alternatingGroup (Fin 8) ≤ (Subgroup.closure S).map
      (alternatingGroup (Fin 8)).subtype := by
    refine closure_gens8.trans ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨i, rfl⟩
    obtain ⟨h, hmem⟩ := hgens i
    exact ⟨_, Subgroup.subset_closure hmem, rfl⟩
  intro x _
  obtain ⟨y, hy, hyx⟩ := hmap x.2
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem alphaVanishes_F08 : AlphaVanishes (alternatingGroup (Fin 8)) F08 :=
  alphaVanishes_of_core (alternatingGroup.center_eq_bot (by simp)) F08_comm
    (fun _ hb hb1 => core_centralizer_F08_eq_bot hb hb1) top_le_closure_F08

theorem alphaVanishes_alt8 {X : Type} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 8))
    {D : Subgroup X} (hD9 : Nat.card D = 9) : AlphaVanishes X D := by
  have hD9' : Nat.card (D.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hD9]
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_card_nine factorization_card_alt8 hD9' card_F08
  refine alphaVanishes_of_mulEquiv e (alphaVanishes_of_mulEquiv (MulAut.conj g) ?_)
  rw [show (D.map e.toMonoidHom).map (MulAut.conj g : alternatingGroup (Fin 8) ≃*
    alternatingGroup (Fin 8)).toMonoidHom = F08 from hg]
  exact alphaVanishes_F08

theorem census423_of_alt8 {X : Type} [Group X] [Finite X] (e : X ≃* alternatingGroup (Fin 8)) :
    Census423 X :=
  census423_of_alphaVanishes fun _ _ hD9 => alphaVanishes_alt8 e hD9

end Res423Two

end CFSG.RankThree.PartTwo.Sec4
