module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd subgroups and normal index-two subgroups

An odd-order subgroup maps trivially to a quotient of order two and is
therefore contained in every normal index-two subgroup.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Every odd-order subgroup lies in a normal subgroup of index two. -/
public theorem odd_card_subgroup_le_normal_index_two
    {G : Type u} [Group G] [Finite G]
    (R P : Subgroup G) (hRnormal : R.Normal) (hRindex : R.index = 2)
    (hPodd : Odd (Nat.card P)) :
    P ≤ R := by
  classical
  let : R.Normal := hRnormal
  let q : G →* G ⧸ R := QuotientGroup.mk' R
  let Pbar : Subgroup (G ⧸ R) := P.map q
  have hPbar_dvd_P : Nat.card Pbar ∣ Nat.card P :=
    Subgroup.card_map_dvd (f := q) (H := P)
  have hPbar_dvd_two : Nat.card Pbar ∣ 2 := by
    have hquot_card : Nat.card (G ⧸ R) = 2 := by
      rw [← R.index_eq_card, hRindex]
    have hdvd := Subgroup.card_subgroup_dvd_card Pbar
    rwa [hquot_card] at hdvd
  have hPbar_card : Nat.card Pbar = 1 := by
    have hcoprime : Nat.Coprime 2 (Nat.card P) := hPodd.coprime_two_right.symm
    exact Nat.eq_one_of_dvd_coprimes hcoprime hPbar_dvd_two hPbar_dvd_P
  have hPbar_bot : Pbar = ⊥ :=
    Subgroup.eq_bot_of_card_eq (H := Pbar) hPbar_card
  have hPleKer : P ≤ q.ker :=
    (Subgroup.map_eq_bot_iff (H := P) (f := q)).mp hPbar_bot
  simpa [q, QuotientGroup.ker_mk'] using hPleKer

end CFSG.GorensteinWalter
