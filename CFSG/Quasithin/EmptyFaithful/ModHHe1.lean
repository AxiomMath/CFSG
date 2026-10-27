module

public import CFSG.Quasithin.EmptyFaithful.ModHHe0
public import CFSG.Quasithin.EmptyFaithful.ModHM24a

public section

namespace CFSG.Quasithin.ModH.He1

open CFSG.QuasithinUnique.Ch1.SporLat.He (heIncl)
open CFSG.Open

variable {J : Type} [Group J] [Finite J] (hl : HeLat J)

include hl

omit [Finite J] in
theorem member_of_complete {Z : Subgroup J} (hS : hl.S ≤ Z) : (∃ j < 11, Z = hl.Y j) ∨ Z = ⊤ :=
  hl.complete Z hS

omit [Finite J] in
theorem card_top : Nat.card (⊤ : Subgroup J) = 2 ^ 10 * 3935925 := by
  rw [Subgroup.card_top]
  exact hl.card_J

omit [Finite J] in
theorem eq_Y3_or_Y4 {W : Subgroup J} (hS : hl.S ≤ W) (hc : Nat.card ↥W = 138240) :
    W = hl.Y 3 ∨ W = hl.Y 4 := by
  rcases member_of_complete hl hS with ⟨j, hj, rfl⟩ | rfl
  · rw [hl.card_Y j hj] at hc
    interval_cases j <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hc; decide)
  · exfalso
    rw [card_top hl] at hc
    omega

omit [Finite J] in
theorem eq_Y2_Y5_Y9 {W : Subgroup J} (hS : hl.S ≤ W) (hc : Nat.card ↥W = 9216) :
    W = hl.Y 2 ∨ W = hl.Y 5 ∨ W = hl.Y 9 := by
  rcases member_of_complete hl hS with ⟨j, hj, rfl⟩ | rfl
  · rw [hl.card_Y j hj] at hc
    interval_cases j <;>
      first | (left; rfl) | (right; left; rfl) | (right; right; rfl) | (exfalso; revert hc; decide)
  · exfalso
    rw [card_top hl] at hc
    omega

theorem not_solvable_of_card_138240 {Z : Subgroup J} (hS : hl.S ≤ Z) (hZs : Group.IsSolvable ↥Z)
    (hc : Nat.card ↥Z = 138240) : False := by
  have hU : IsPGroup 2 ↥(hl.S.subgroupOf Z) :=
    hl.S_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS).symm
  obtain ⟨H, hUH, hHq, hk2, hk5⟩ := M24a.exists_hall_two_p hZs (hl.S.subgroupOf Z) hU 5
    (by norm_num)
  have hSH : hl.S ≤ H.map Z.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hS]
    exact Subgroup.map_mono hUH
  have hcardH : Nat.card ↥(H.map Z.subtype) = Nat.card ↥H :=
    (Nat.card_congr (H.equivMapOfInjective Z.subtype Subtype.val_injective).toEquiv).symm
  have h5120 : Nat.card ↥H = 5120 :=
    M24a.hall_5120_of_138240 (h := Nat.card ↥H) (k := H.index)
      (by rw [Subgroup.card_mul_index H]; exact hc) hHq hk2 hk5
  rcases member_of_complete hl hSH with ⟨j, hj, hjeq⟩ | htop
  · have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) hjeq
    rw [hcardH, h5120, hl.card_Y j hj] at h1
    interval_cases j <;> revert h1 <;> decide
  · have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) htop
    rw [hcardH, h5120, card_top hl] at h1
    omega

theorem Z_cases (hns : ¬ Group.IsSolvable J) {Z : Subgroup J} (hS : hl.S ≤ Z)
    (hZs : Group.IsSolvable ↥Z) (h9 : 9 ∣ Nat.card ↥Z) :
    Z = hl.Y 2 ∨ Z = hl.Y 5 ∨ Z = hl.Y 9 := by
  rcases member_of_complete hl hS with ⟨j, hj, rfl⟩ | rfl
  · have hc := hl.card_Y j hj
    rw [hc] at h9
    interval_cases j
    · exfalso; revert h9; decide
    · exfalso; revert h9; decide
    · left; rfl
    · exact (not_solvable_of_card_138240 hl hS hZs (by rw [hc]; rfl)).elim
    · exact (not_solvable_of_card_138240 hl hS hZs (by rw [hc]; rfl)).elim
    · right; left; rfl
    · exfalso; revert h9; decide
    · exfalso; revert h9; decide
    · exfalso; revert h9; decide
    · right; right; rfl
    · exfalso; revert h9; decide
  · exfalso
    apply hns
    exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup J).subtype)
      (by intro x; exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)

theorem normalizer_pCore_ne_top {j : ℕ} (hj : j = 3 ∨ j = 4) :
    Subgroup.normalizer ((pCoreOf 2 (hl.Y j) : Subgroup J) : Set J) ≠ ⊤ := by
  intro htop
  have hnormal : (pCoreOf 2 (hl.Y j)).Normal := Subgroup.normalizer_eq_top_iff.1 htop
  have := hl.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCoreOf 2 (hl.Y j)) with h | h
  · exact hl.o2_ne_bot j hj h
  · have hp : IsPGroup 2 ↥(pCoreOf 2 (hl.Y j)) :=
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    rw [h] at hp
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    rw [card_top hl] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

end CFSG.Quasithin.ModH.He1
