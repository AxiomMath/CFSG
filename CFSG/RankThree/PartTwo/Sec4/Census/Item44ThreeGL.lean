module

public import CFSG.RankThree.PartTwo.Toolkit.Bloom
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Certificates.Certificate8171

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Subgroup

theorem isSolvable_of_card_dvd_two_pow_mul_three_pow {H : Type*} [Group H] [Finite H]
    {a b : ℕ} (h : Nat.card H ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable H := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem le_statedSL_of_isPerfect {G : Subgroup (GL (Fin 3) (ZMod 3))} (hG : Group.IsPerfect G) :
    G ≤ CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) :=
  calc G = ⁅G, G⁆ := (Subgroup.commutator_eq_self (H := G)).symm
    _ ≤ _ := Subgroup.commutator_le.2 fun a _ b _ => by
      rw [CFSG.RankThree.SubgroupLists.mem_statedSL_iff, commutatorElement_def]
      exact Toolkit.det_commutator a b

theorem isSolvable_of_normal_card_13 {G F : Subgroup (GL (Fin 3) (ZMod 3))} (hFG : F ≤ G)
    (hnorm : ∀ g ∈ G, ∀ x ∈ F, g * x * g⁻¹ ∈ F) (hF : Nat.card F = 13) :
    Group.IsSolvable G := by
  have hGN : G ≤ normalizer (F : Set (GL (Fin 3) (ZMod 3))) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hnorm g hg x, fun h => ?_⟩
    have := hnorm g⁻¹ (G.inv_mem hg) _ h
    simpa [mul_assoc] using this
  have h78 : Nat.card G ∣ 2 ^ 1 * 3 ^ 1 * 13 := by
    have := card_dvd_of_le hGN
    rw [Toolkit.card_normalizer_of_card_13 hF] at this
    exact this
  have : (F.subgroupOf G).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hnorm g g.2 n hn⟩
  have hN : Nat.card (F.subgroupOf G) = 13 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hFG).toEquiv, hF]
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : IsCyclic (F.subgroupOf G) := isCyclic_of_prime_card hN
  have : Group.IsSolvable (G ⧸ F.subgroupOf G) := by
    apply isSolvable_of_card_dvd_two_pow_mul_three_pow (a := 1) (b := 1)
    rw [card_eq_card_quotient_mul_card_subgroup (F.subgroupOf G), hN] at h78
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h78
  exact Group.isSolvable_of_subgroup_quotient (F.subgroupOf G)

theorem eq_statedSL_of_isPerfect {G : Subgroup (GL (Fin 3) (ZMod 3))} (hG : Group.IsPerfect G)
    (hne : G ≠ ⊥) : G = CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) := by
  have : Nontrivial G := (nontrivial_iff_ne_bot G).2 hne
  have hns : ¬ Group.IsSolvable G := Group.IsPerfect.not_isSolvable G
  have h13 : 13 ∣ Nat.card G := by
    by_contra h13
    exact hns (Toolkit.isSolvable_of_not_dvd h13)
  obtain ⟨F, hFG, hF⟩ := Toolkit.exists_card_13 h13
  by_cases hnorm : ∀ g ∈ G, ∀ x ∈ F, g * x * g⁻¹ ∈ F
  · exact absurd (isSolvable_of_normal_card_13 hFG hnorm hF) hns
  push Not at hnorm
  obtain ⟨g, hg, x, hx, hgx⟩ := hnorm
  obtain ⟨F', hF'⟩ : ∃ F', F' = F.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hcard : Nat.card F' = 13 := by
    rw [hF', CFSG.RankThree.Asc83Table.card_map_conj, hF]
  have hmem : g * x * g⁻¹ ∈ F' := by
    rw [hF']
    exact ⟨x, hx, by simp⟩
  have hFF' : F ≠ F' := fun h => hgx (by rw [h]; exact hmem)
  have hF'G : F' ≤ G := by
    rw [hF']
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact G.mul_mem (G.mul_mem hg (hFG hy)) (G.inv_mem hg)
  exact le_antisymm (le_statedSL_of_isPerfect hG)
    ((Toolkit.statedSL_le_sup hF hcard hFF').trans (sup_le hFG hF'G))

theorem isSolvable_GL_zmod_three {d : ℕ} (hd : d ≤ 2) : Group.IsSolvable (GL (Fin d) (ZMod 3)) := by
  apply isSolvable_of_card_dvd_two_pow_mul_three_pow (a := 4) (b := 1)
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases d <;> decide

theorem eq_bot_of_isPerfect_of_le_two {d : ℕ} (hd : d ≤ 2) {G : Subgroup (GL (Fin d) (ZMod 3))}
    (hG : Group.IsPerfect G) : G = ⊥ := by
  have := isSolvable_GL_zmod_three hd
  by_contra hne
  have : Nontrivial G := (nontrivial_iff_ne_bot G).2 hne
  exact Group.IsPerfect.not_isSolvable G inferInstance

end CFSG.RankThree.PartTwo.Sec4.Census
