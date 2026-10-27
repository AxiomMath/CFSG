module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
noncomputable section
namespace CFSG.GorensteinWalter
universe u
public theorem odd_pgroup_le_normal_index_two
    {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (J P : Subgroup H)
    (hJnormal : J.Normal) (hJindex : J.index = 2)
    (hPp : IsPGroup p P) : P ≤ J := by
  let q : H →* (H ⧸ J) := QuotientGroup.mk' J
  let Q : Subgroup (H ⧸ J) := P.map q
  have hQp : IsPGroup p Q := hPp.map q
  have hQdiv : Nat.card Q ∣ 2 := by
    have hquot : Nat.card (H ⧸ J) = 2 := by
      rw [← J.index_eq_card, hJindex]
    have hdiv := Subgroup.card_dvd_of_le (show Q ≤ ⊤ from le_top)
    simpa [hquot] using hdiv
  have hQodd : Odd (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    rw [hn]
    exact hpodd.pow
  have hQcard : Nat.card Q = 1 :=
    Nat.eq_one_of_dvd_coprimes hQodd.coprime_two_left
      hQdiv (dvd_refl _)
  have hQbot : Q = ⊥ := Subgroup.eq_bot_of_card_eq Q hQcard
  have hPleker : P ≤ q.ker := by
    exact (Subgroup.map_eq_bot_iff (H := P) (f := q)).mp hQbot
  simpa [q, QuotientGroup.ker_mk'] using hPleker
end CFSG.GorensteinWalter
