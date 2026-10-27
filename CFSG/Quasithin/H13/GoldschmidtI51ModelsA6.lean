module

public import CFSG.Quasithin.H13.Sp62D3

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Quasithin.H13.A6 Equiv

abbrev A6g : Subgroup (Perm (Fin 6)) := alternatingGroup (Fin 6)

@[expose] def P0a : Subgroup ↥A6g := QA6sub.subgroupOf A6g

@[expose] def X1a : Subgroup ↥A6g := (P1sub ⊓ A6g).subgroupOf A6g

@[expose] def X2a : Subgroup ↥A6g := (P2sub ⊓ A6g).subgroupOf A6g

theorem QA6sub_le_A6 : QA6sub ≤ A6g := inf_le_right

theorem card_P0a : Nat.card P0a = 8 := by
  rw [P0a, ← card_QA6sub]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe QA6sub_le_A6).toEquiv

theorem card_A6g : Nat.card ↥A6g = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem P0a_sylow : IsPGroup 2 P0a ∧ ¬ 2 ∣ P0a.index := by
  refine ⟨IsPGroup.of_card (n := 3) (by rw [card_P0a]; norm_num), ?_⟩
  have := Subgroup.card_mul_index P0a
  rw [card_P0a, card_A6g] at this
  have h : P0a.index = 45 := by omega
  rw [h]
  norm_num

theorem P0a_le_X1a : P0a ≤ X1a := by
  intro x hx
  have hx' : (x : Perm (Fin 6)) ∈ QA6sub := hx
  have : (x : Perm (Fin 6)) ∈ P1sub ⊓ A6g :=
    ⟨(D6sub_le hx'.1).1, x.2⟩
  exact this

theorem P0a_le_X2a : P0a ≤ X2a := by
  intro x hx
  have hx' : (x : Perm (Fin 6)) ∈ QA6sub := hx
  have : (x : Perm (Fin 6)) ∈ P2sub ⊓ A6g :=
    ⟨(D6sub_le hx'.1).2, x.2⟩
  exact this

theorem X1a_not_le_X2a : ¬ X1a ≤ X2a := by
  intro h
  have hA : swap (0 : Fin 6) 2 * swap 4 5 ∈ A6g := Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have hP1 : InP1 (swap (0 : Fin 6) 2 * swap 4 5) := by decide
  have hP2 : ¬ InP2 (swap (0 : Fin 6) 2 * swap 4 5) := by decide
  have h1 : (⟨swap 0 2 * swap 4 5, hA⟩ : ↥A6g) ∈ X1a := ⟨mem_P1sub.2 hP1, hA⟩
  exact hP2 (mem_P2sub.1 (h h1).1)

theorem X2a_not_le_X1a : ¬ X2a ≤ X1a := by
  intro h
  have hA : swap (0 : Fin 6) 4 * swap 1 5 ∈ A6g := Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have hP2 : InP2 (swap (0 : Fin 6) 4 * swap 1 5) := by decide
  have hP1 : ¬ InP1 (swap (0 : Fin 6) 4 * swap 1 5) := by decide
  have h1 : (⟨swap 0 4 * swap 1 5, hA⟩ : ↥A6g) ∈ X2a := ⟨mem_P2sub.2 hP2, hA⟩
  exact hP1 (mem_P1sub.1 (h h1).1)

theorem overgroups_A6sub (Y : Subgroup ↥A6g) (hY : P0a ≤ Y) :
    Y = P0a ∨ Y = X1a ∨ Y = X2a ∨ Y = ⊤ := by
  have hle : QA6sub ≤ Y.map A6g.subtype := by
    intro x hx
    exact ⟨⟨x, QA6sub_le_A6 hx⟩, hY (show (⟨x, QA6sub_le_A6 hx⟩ : ↥A6g) ∈ P0a from hx), rfl⟩
  have hcomap : Y.map A6g.subtype ≤ A6g := Subgroup.map_subtype_le _
  have hY' : Y = (Y.map A6g.subtype).subgroupOf A6g :=
    (Subgroup.comap_map_eq_self_of_injective A6g.subtype_injective Y).symm
  rcases overgroups_QA6 _ hle hcomap with h | h | h | h
  · left; rw [hY', h]; rfl
  · right; left; rw [hY', h]; rfl
  · right; right; left; rw [hY', h]; rfl
  · right; right; right; rw [hY', h]; exact Subgroup.subgroupOf_self _

end CFSG.Quasithin.H13.I51
