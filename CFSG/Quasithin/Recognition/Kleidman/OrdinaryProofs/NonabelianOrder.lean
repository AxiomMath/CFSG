module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs

theorem commute_of_natCard_le_three {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 3)
    (a b : G) : a * b = b * a := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  rcases (by omega : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3) with h1 | h23
  · obtain ⟨hs, _⟩ := Nat.card_eq_one_iff_unique.mp h1
    rw [Subsingleton.elim a b]
  · have hp : (Nat.card G).Prime := by
      rcases h23 with h | h
      · rw [h]; exact Nat.prime_two
      · rw [h]; exact Nat.prime_three
    have : Fact (Nat.card G).Prime := ⟨hp⟩
    have hnt : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hp.one_lt
    obtain ⟨g, hg⟩ : ∃ g : G, g ≠ 1 := exists_ne 1
    have htop : Subgroup.zpowers g = ⊤ := by
      have hdvd : Nat.card ↥(Subgroup.zpowers g) ∣ Nat.card G :=
        Subgroup.card_subgroup_dvd_card _
      rcases (Nat.dvd_prime hp).mp hdvd with hcard | hcard
      · exact absurd (Subgroup.zpowers_eq_bot.mp
          ((Subgroup.eq_bot_iff_card (Subgroup.zpowers g)).mpr hcard)) hg
      · exact (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers g)).mp hcard
    have hcyc : IsCyclic G := ⟨g, fun x => by
      have hx : x ∈ Subgroup.zpowers g := htop ▸ Subgroup.mem_top x
      simpa using (Subgroup.mem_zpowers_iff.mp hx)⟩
    have hc : IsMulCommutative G := IsCyclic.isMulCommutative
    exact hc.is_comm.comm a b

theorem three_lt_natCard_of_noncomm {G : Type*} [Group G] [Finite G]
    (h : ∃ a b : G, a * b ≠ b * a) : 3 < Nat.card G := by
  by_contra hle
  obtain ⟨a, b, hab⟩ := h
  exact hab (commute_of_natCard_le_three (by omega) a b)

end CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs

end
