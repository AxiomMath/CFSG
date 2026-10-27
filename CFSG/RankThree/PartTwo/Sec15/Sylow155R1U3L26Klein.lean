module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.BenderSuzuki.PFchapter1section1 (TwoRankAtLeastTwo)

theorem pow_four_eq_one_of_two_pow_of_pow_eight {U : Type*} [Group U]
    (h8 : ∀ u : U, u ^ 8 = 1 → u ^ 4 = 1) {u : U} {k : ℕ} (hk : u ^ 2 ^ k = 1) :
    u ^ 4 = 1 := by
  induction k using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    by_cases hk2 : k ≤ 2
    · obtain ⟨c, hc⟩ := pow_dvd_pow 2 hk2
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, hc, pow_mul, hk, one_pow]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have h1 : (u ^ 2 ^ j) ^ 8 = 1 := by
        rw [← pow_mul, show 2 ^ j * 8 = 2 ^ (j + 3) by ring]
        exact hk
      refine ih (j + 2) (by omega) ?_
      rw [show 2 ^ (j + 2) = 2 ^ j * 4 by ring, pow_mul]
      exact h8 _ h1

theorem natCard_le_two_mul_of_quaternion {U : Type*} [Group U] {n : ℕ} [NeZero n]
    (θ : QuaternionGroup n →* U) (hθ : Function.Surjective θ) {m : ℕ} (hm : 0 < m)
    (hα : θ (QuaternionGroup.a 1) ^ m = 1) : Nat.card U ≤ 2 * m := by
  set α := θ (QuaternionGroup.a 1) with hαdef
  set β := θ (QuaternionGroup.xa 0) with hβdef
  have : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩
  have hmod : ∀ i : ZMod (2 * n), θ (QuaternionGroup.a i) = α ^ (i.val % m) := by
    intro i
    have : (QuaternionGroup.a i : QuaternionGroup n) = QuaternionGroup.a 1 ^ i.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [this, map_pow, ← pow_eq_pow_mod _ hα]
  let f : Fin m ⊕ Fin m → U :=
    Sum.elim (fun j => α ^ (j : ℕ)) (fun j => β * α ^ (j : ℕ))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨q, rfl⟩ := hθ x
    cases q with
    | a i => exact ⟨Sum.inl ⟨i.val % m, Nat.mod_lt _ hm⟩, (hmod i).symm⟩
    | xa i =>
      refine ⟨Sum.inr ⟨i.val % m, Nat.mod_lt _ hm⟩, ?_⟩
      have : (QuaternionGroup.xa i : QuaternionGroup n) =
          QuaternionGroup.xa 0 * QuaternionGroup.a i := by
        rw [QuaternionGroup.xa_mul_a, zero_add]
      show β * α ^ (i.val % m) = θ (QuaternionGroup.xa i)
      rw [this, map_mul, hmod i]
  calc Nat.card U ≤ Nat.card (Fin m ⊕ Fin m) := Nat.card_le_card_of_surjective f hf
    _ = 2 * m := by simp; omega

theorem exists_klein_four_of_surjective_of_pow_eight {H U : Type*} [Group H] [Finite H]
    [Group U] (π : H →* U) (hπ : Function.Surjective π) (h16 : 16 ∣ Nat.card U)
    (h8 : ∀ u : U, u ^ 8 = 1 → u ^ 4 = 1) :
    ∃ a b : H, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  by_cases hH : TwoRankAtLeastTwo H
  · exact CFSG.RankThree.PartTwo.Sec11.LSSolvableProof.exists_klein_of_twoRank hH
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite U := Finite.of_surjective π hπ
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  set T : Subgroup U := (S : Subgroup H).map π with hT
  have hT16 : 2 ^ 4 ≤ Nat.card T :=
    Nat.le_of_dvd Nat.card_pos
      ((S.mapSurjective hπ).pow_dvd_card_of_pow_dvd_card (n := 4) (by simpa using h16))
  have hT8 : ∀ t : T, t ^ 8 = 1 → t ^ 4 = 1 := by
    intro t ht
    apply Subtype.ext
    have h := h8 (t : U) (by rw [← Subgroup.coe_pow, ht]; rfl)
    rw [Subgroup.coe_pow]
    exact h
  set θ : (S : Subgroup H) →* T := π.subgroupMap (S : Subgroup H) with hθdef
  have hθ : Function.Surjective θ := π.subgroupMap_surjective (S : Subgroup H)
  have h4 : ∀ s : (S : Subgroup H), θ s ^ 4 = 1 := by
    intro s
    obtain ⟨k, hk⟩ := S.isPGroup' s
    exact pow_four_eq_one_of_two_pow_of_pow_eight hT8 (k := k) (by rw [← map_pow, hk, map_one])
  have hT4 : Nat.card T ≤ 8 := by
    rcases CFSG.BenderSuzuki.sylowTwo_cyclic_or_quaternion_of_not_twoRank hH S with hcyc | hq
    ·
      have : IsCyclic T := isCyclic_of_surjective θ hθ
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
      have hcard : orderOf g = Nat.card T := orderOf_eq_card_of_forall_mem_zpowers hg
      obtain ⟨s, rfl⟩ := hθ g
      have := orderOf_le_of_pow_eq_one (by norm_num) (h4 s)
      omega
    · obtain ⟨r, -, ⟨ϕ⟩⟩ := hq
      exact natCard_le_two_mul_of_quaternion (θ.comp ϕ.symm.toMonoidHom)
        (hθ.comp ϕ.symm.surjective) (m := 4) (by norm_num) (h4 _)
  omega

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
