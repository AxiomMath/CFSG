module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofAltTools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res423Two

open Equiv Equiv.Perm Item434AltPerm

@[expose] def cyc8 (a b c : Fin 8) : Perm (Fin 8) := swap a b * swap b c

@[expose] def tri012 : List (Fin 8 × Fin 8 × Fin 8) :=
  [(3, 4, 5), (3, 5, 4), (3, 4, 6), (3, 6, 4), (3, 4, 7), (3, 7, 4), (3, 5, 6), (3, 6, 5),
    (3, 5, 7), (3, 7, 5), (3, 6, 7), (3, 7, 6), (4, 5, 6), (4, 6, 5), (4, 5, 7), (4, 7, 5),
    (4, 6, 7), (4, 7, 6), (5, 6, 7), (5, 7, 6)]

@[expose] def tri345 : List (Fin 8 × Fin 8 × Fin 8) :=
  [(0, 1, 2), (0, 2, 1), (0, 1, 6), (0, 6, 1), (0, 1, 7), (0, 7, 1), (0, 2, 6), (0, 6, 2),
    (0, 2, 7), (0, 7, 2), (0, 6, 7), (0, 7, 6), (1, 2, 6), (1, 6, 2), (1, 2, 7), (1, 7, 2),
    (1, 6, 7), (1, 7, 6), (2, 6, 7), (2, 7, 6)]

@[expose] def cycT (t : Fin 8 × Fin 8 × Fin 8) : Perm (Fin 8) := cyc8 t.1 t.2.1 t.2.2

theorem sign_cyc8 {a b c : Fin 8} (h1 : a ≠ b) (h2 : b ≠ c) : sign (cyc8 a b c) = 1 := by
  rw [cyc8, Perm.sign_mul, sign_swap h1, sign_swap h2]
  decide

theorem tri012_spec : ∀ t ∈ tri012, t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧
    cycT t * c1 8 = c1 8 * cycT t := by
  decide +kernel

theorem tri345_spec : ∀ t ∈ tri345, t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧
    cycT t * c2 8 = c2 8 * cycT t := by
  decide +kernel

theorem check_off012 : ∀ τ : Perm {x : Fin 8 // 3 ≤ x.val}, τ ≠ 1 →
    (ofSubtype τ ^ 3 = 1 ∧ ofSubtype τ ≠ 1) ∨
      ((ofSubtype τ ^ 2) ^ 3 = 1 ∧ ofSubtype τ ^ 2 ≠ 1) ∨
      ∃ t ∈ tri012, (ofSubtype τ * cycT t * (ofSubtype τ)⁻¹ * (cycT t)⁻¹) ^ 3 = 1 ∧
        ofSubtype τ * cycT t * (ofSubtype τ)⁻¹ * (cycT t)⁻¹ ≠ 1 := by
  decide +kernel

theorem check_off345 : ∀ τ : Perm {x : Fin 8 // x.val < 3 ∨ 6 ≤ x.val}, τ ≠ 1 →
    (ofSubtype τ ^ 3 = 1 ∧ ofSubtype τ ≠ 1) ∨
      ((ofSubtype τ ^ 2) ^ 3 = 1 ∧ ofSubtype τ ^ 2 ≠ 1) ∨
      ∃ t ∈ tri345, (ofSubtype τ * cycT t * (ofSubtype τ)⁻¹ * (cycT t)⁻¹) ^ 3 = 1 ∧
        ofSubtype τ * cycT t * (ofSubtype τ)⁻¹ * (cycT t)⁻¹ ≠ 1 := by
  decide +kernel

theorem c1_eight_ne : ∀ x : Fin 8, ¬ 3 ≤ x.val → c1 8 x ≠ x := by decide

theorem c2_eight_ne : ∀ x : Fin 8, ¬ (x.val < 3 ∨ 6 ≤ x.val) → c2 8 x ≠ x := by decide

theorem isThreeCycle_c1_eight : (c1 8).IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide +kernel)

theorem isThreeCycle_c2_eight : (c2 8).IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide +kernel)

theorem eq_bot_of_thetaLike_c1 {P : Subgroup (Perm (Fin 8))} (hP : ThetaLike (c1 8) P) :
    P = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hfix : ∀ x, c1 8 x ≠ x → y x = x := fun x hx =>
    apply_eq_self_of_commute_isThreeCycle isThreeCycle_c1_eight (hP.comm y hy)
      (hP.coprime y hy) hx
  have hsupp : (y.support : Set (Fin 8)) ⊆ Set.ofPred (fun x : Fin 8 => 3 ≤ x.val) := by
    intro x hx
    rw [Finset.mem_coe, mem_support] at hx
    by_contra h
    exact hx (hfix x (c1_eight_ne x h))
  obtain ⟨τ, rfl⟩ := mem_range_ofSubtype_iff.mpr hsupp
  by_contra hne
  have hτ : τ ≠ 1 := fun h => hne (by rw [h, map_one])
  rcases check_off012 τ hτ with ⟨h3, h1⟩ | ⟨h3, h1⟩ | ⟨t, ht, h3, h1⟩
  · exact hP.false_of_mem hy h3 h1
  · exact hP.false_of_mem (pow_mem hy 2) h3 h1
  · obtain ⟨ht1, ht2, htc⟩ := tri012_spec t ht
    exact hP.false_of_mem (hP.commutator_mem hy (sign_cyc8 ht1 ht2) htc) h3 h1

theorem eq_bot_of_thetaLike_c2 {P : Subgroup (Perm (Fin 8))} (hP : ThetaLike (c2 8) P) :
    P = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hfix : ∀ x, c2 8 x ≠ x → y x = x := fun x hx =>
    apply_eq_self_of_commute_isThreeCycle isThreeCycle_c2_eight (hP.comm y hy)
      (hP.coprime y hy) hx
  have hsupp : (y.support : Set (Fin 8)) ⊆
      Set.ofPred (fun x : Fin 8 => x.val < 3 ∨ 6 ≤ x.val) := by
    intro x hx
    rw [Finset.mem_coe, mem_support] at hx
    by_contra h
    exact hx (hfix x (c2_eight_ne x h))
  obtain ⟨τ, rfl⟩ := mem_range_ofSubtype_iff.mpr hsupp
  by_contra hne
  have hτ : τ ≠ 1 := fun h => hne (by rw [h, map_one])
  rcases check_off345 τ hτ with ⟨h3, h1⟩ | ⟨h3, h1⟩ | ⟨t, ht, h3, h1⟩
  · exact hP.false_of_mem hy h3 h1
  · exact hP.false_of_mem (pow_mem hy 2) h3 h1
  · obtain ⟨ht1, ht2, htc⟩ := tri345_spec t ht
    exact hP.false_of_mem (hP.commutator_mem hy (sign_cyc8 ht1 ht2) htc) h3 h1

end Res423Two

end CFSG.RankThree.PartTwo.Sec4
