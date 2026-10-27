module

public import CFSG.RankThree.PartOne.S11c.LyPerm

public section

namespace CFSG.RankThree.PartOne.K133Spor

open Equiv Equiv.Perm CFSG.RankThree.PartOne.LyPerm

theorem card_fix_five_eq_six {u σ : Perm (Fin 11)} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hs : sign u = 1) (hσ : orderOf σ = 5) (hc : u * σ = σ * u) : (fixF σ).card = 6 := by
  have h37 := card_fixed_eq_three_or_seven hu2 hu1 hs
  have hf := card_fix_five hσ
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h3 := card_fix_modEq (g := u) (h := σ) hc (p := 5) (n := 1)
    (by rw [pow_one, ← hσ]; exact pow_orderOf_eq_one σ)
  have h4 := card_fix_modEq (g := σ) (h := u) hc.symm (p := 2) (n := 1) (by rw [pow_one]; exact hu2)
  have hinter : fixF σ ∩ fixF u = fixF u ∩ fixF σ := Finset.inter_comm _ _
  rw [hinter] at h4
  have hle1 : (fixF u ∩ fixF σ).card ≤ (fixF u).card := Finset.card_le_card Finset.inter_subset_left
  have hle2 : (fixF u ∩ fixF σ).card ≤ (fixF σ).card :=
    Finset.card_le_card Finset.inter_subset_right
  unfold Nat.ModEq at h3 h4
  omega

theorem not_commute_plane {D : Subgroup (Perm (Fin 11))} (hD5 : ∀ g ∈ D, g ^ 5 = 1)
    (hDc : Nat.card D = 25) {u : Perm (Fin 11)} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hs : sign u = 1) (hc : ∀ g ∈ D, u * g = g * u) : False := by
  classical
  have : Fintype D := Fintype.ofFinite D
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group D (Fin 11)
  have hfix : ∀ g : D, Fintype.card (MulAction.fixedBy (Fin 11) g) =
      if g = 1 then 11 else 6 := by
    intro g
    split_ifs with hg
    · rw [hg]
      simp
    · have hg1 : (g : Perm (Fin 11)) ≠ 1 := fun h => hg (Subtype.ext h)
      have hord : orderOf (g : Perm (Fin 11)) = 5 :=
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        orderOf_eq_prime (hD5 g g.2) hg1
      have h6 := card_fix_five_eq_six hu2 hu1 hs hord (hc g g.2)
      rw [← h6, ← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun x => ⟨x.1, mem_fixF.mpr x.2⟩
          invFun := fun y => ⟨y.1, mem_fixF.mp y.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
  simp_rw [hfix] at hburn
  have hsum : ∑ g : D, (if g = 1 then 11 else 6) = 6 * Fintype.card D + 5 := by
    have : ∀ g : D, (if g = 1 then 11 else 6) = 6 + (if g = 1 then 5 else 0) := by
      intro g
      split_ifs <;> rfl
    simp_rw [this]
    rw [Finset.sum_add_distrib]
    simp
    ring
  rw [hsum] at hburn
  have hcard : Fintype.card D = 25 := by rw [← Nat.card_eq_fintype_card]; exact hDc
  rw [hcard] at hburn
  omega

end CFSG.RankThree.PartOne.K133Spor
