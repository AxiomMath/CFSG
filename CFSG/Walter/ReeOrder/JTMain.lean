module

public import CFSG.Walter.ReeOrder.JT.Section7ZB
public import CFSG.Walter.ReeOrder.JT.Section6H
public import CFSG.Walter.ReeOrder.JT.Section5B
public import CFSG.Walter.Cited.Huppert

public section

namespace CFSG.Walter.JT

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace JTHyp

variable (h : JTHyp G)

theorem odd_f_of_three
    (hp3 : h.p = 3) : Odd h.f ∧ 1 < h.f := by
  obtain ⟨n, hn1, hn⟩ := lemma_4_1 h (h.p_ne_two_of_eq_three hp3)
    ⟨h.f, by rw [JTHyp.q_eq, hp3]⟩
  rw [JTHyp.q_eq, hp3] at hn
  have hf : h.f = 2 * n + 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hn
  exact ⟨⟨n, hf⟩, by omega⟩

theorem centralizer_le_of_three
    (hp3 : h.p = 3) {x : G}
    (hx : x ∈ Subgroup.centralizer ({h.t} : Set G)) (hx1 : x ≠ 1)
    (hcop : Nat.Coprime (orderOf x) 6) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({h.t} : Set G) :=
  h.centralizer_le_of_lemma712a_of_lemma716 hp3 CFSG.Walter.suzukiFourGroupTheorem
    (h.lemma_7_12_a hp3) (h.lemma_7_16 hp3) hx hx1 hcop

theorem nonempty_reeTypeHyp_of_three
    (hp3 : h.p = 3) : Nonempty (Ward.ReeTypeHyp G) :=
  h.nonempty_reeTypeHyp hp3 (h.lemma_7_12_a hp3) (h.lemma_7_16 hp3)

theorem jt_theoremA_of_three
    (hp3 : h.p = 3) :
    Odd h.f ∧ 1 < h.f ∧
      (∀ x ∈ Subgroup.centralizer ({h.t} : Set G), x ≠ 1 → Nat.Coprime (orderOf x) 6 →
        Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({h.t} : Set G)) ∧
      Nonempty (Ward.ReeTypeHyp G) :=
  ⟨(h.odd_f_of_three hp3).1, (h.odd_f_of_three hp3).2,
    fun _ hx hx1 hcop => h.centralizer_le_of_three hp3 hx hx1 hcop,
    h.nonempty_reeTypeHyp_of_three hp3⟩

theorem p_eq_three
    (hp : h.p ≠ 2) (h51 : h.Lemma51) : h.p = 3 :=
  h.p_eq_three_of_cube_dvd hp CFSG.Walter.suzukiFourGroupTheorem
    CFSG.Walter.huppertMetacyclicTheorem fun hp3 => h51.cube_dvd hp3

theorem jt_theoremA
    (hp : h.p ≠ 2) (h51 : h.Lemma51) :
    h.p = 3 ∧ Odd h.f ∧ 1 < h.f ∧
      (∀ x ∈ Subgroup.centralizer ({h.t} : Set G), x ≠ 1 → Nat.Coprime (orderOf x) 6 →
        Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({h.t} : Set G)) ∧
      Nonempty (Ward.ReeTypeHyp G) :=
  ⟨h.p_eq_three hp h51, h.jt_theoremA_of_three (h.p_eq_three hp h51)⟩

theorem p_eq_three_of_ne_two
    (hp : h.p ≠ 2) : h.p = 3 :=
  h.p_eq_three hp fun hp3 => h.lemma51 hp hp3 CFSG.Walter.suzukiFourGroupTheorem
    CFSG.Walter.huppertMetacyclicTheorem hp3

theorem jt_theoremA_of_ne_two
    (hp : h.p ≠ 2) :
    h.p = 3 ∧ Odd h.f ∧ 1 < h.f ∧
      (∀ x ∈ Subgroup.centralizer ({h.t} : Set G), x ≠ 1 → Nat.Coprime (orderOf x) 6 →
        Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({h.t} : Set G)) ∧
      Nonempty (Ward.ReeTypeHyp G) :=
  ⟨h.p_eq_three_of_ne_two hp, h.jt_theoremA_of_three (h.p_eq_three_of_ne_two hp)⟩

end JTHyp

end CFSG.Walter.JT
