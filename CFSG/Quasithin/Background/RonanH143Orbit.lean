module

public import CFSG.Quasithin.Background.RonanH143Data

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def ostdRep (x : Fin 24) : Fin 24 :=
  if (x : ℕ) < 2 then x else if (x : ℕ) < 6 then 2 else if (x : ℕ) < 8 then 6 else 8

theorem ostdRep_cases : ∀ x : Fin 24,
    ostdRep x = 0 ∨ ostdRep x = 1 ∨ ostdRep x = 2 ∨ ostdRep x = 6 ∨ ostdRep x = 8 := by
  decide +kernel

theorem ostdRep_witness : ∀ x : Fin 24,
    ∃ t : Fin 16, ∃ j : Fin 8, (koPerm t * dPerm j) (ostdRep x) = x := by
  decide +kernel

@[expose] def ostdBit (b2 b6 b8 : Bool) (r : Fin 24) : Bool :=
  if r = 2 then b2 else if r = 6 then b6 else if r = 8 then b8 else true

@[expose] def ostdPatt (b2 b6 b8 : Bool) : Finset (Fin 24) :=
  Finset.univ.filter fun x => ostdBit b2 b6 b8 (ostdRep x) = true

theorem mem_ostdPatt (b2 b6 b8 : Bool) (x : Fin 24) :
    x ∈ ostdPatt b2 b6 b8 ↔ ostdBit b2 b6 b8 (ostdRep x) = true := by
  simp [ostdPatt]

theorem ostdPatt_card_eight : ∀ a b c : Bool,
    (ostdPatt a b c).card = 8 → a = true ∧ b = true ∧ c = false := by
  decide +kernel

theorem ostdPatt_card_four : ∀ a b c : Bool,
    (ostdPatt a b c).card = 4 → a = false ∧ b = true ∧ c = false := by
  decide +kernel

theorem ostdPatt_eq_Ostd : ostdPatt true true false = Ostd := by
  decide +kernel

theorem ostdPatt_eq_Bstd : ostdPatt false true false = Bstd := by
  decide +kernel

theorem mem_iff_of_smul_fix {g : Equiv.Perm (Fin 24)} {S : Finset (Fin 24)} (hg : g • S = S)
    (x : Fin 24) : g x ∈ S ↔ x ∈ S := by
  have h : g • x ∈ g • S ↔ x ∈ S := Finset.smul_mem_smul_finset_iff g
  rw [hg, Equiv.Perm.smul_def] at h
  exact h

theorem eq_ostdPatt_of_PO_inv {S : Finset (Fin 24)} (h0 : (0 : Fin 24) ∈ S)
    (h1 : (1 : Fin 24) ∈ S) (hinv : ∀ g ∈ PO, g • S = S) :
    S = ostdPatt (decide ((2 : Fin 24) ∈ S)) (decide ((6 : Fin 24) ∈ S))
      (decide ((8 : Fin 24) ∈ S)) := by
  have key : ∀ x : Fin 24, x ∈ S ↔ ostdRep x ∈ S := by
    intro x
    obtain ⟨t, j, hx⟩ := ostdRep_witness x
    have hmem : koPerm t * dPerm j ∈ PO := PO.mul_mem (koPerm_mem_PO t) (dPerm_mem_PO j)
    have h := mem_iff_of_smul_fix (hinv (koPerm t * dPerm j) hmem) (ostdRep x)
    rw [hx] at h
    exact h
  ext x
  rw [key x, mem_ostdPatt]
  rcases ostdRep_cases x with h | h | h | h | h <;> simp [h, ostdBit, h0, h1]

theorem eq_Ostd_of_PO_inv {O : Finset (Fin 24)} (hcard : O.card = 8) (h0 : (0 : Fin 24) ∈ O)
    (h1 : (1 : Fin 24) ∈ O) (hinv : ∀ g ∈ PO, g • O = O) : O = Ostd := by
  have hO := eq_ostdPatt_of_PO_inv h0 h1 hinv
  have hc : (ostdPatt (decide ((2 : Fin 24) ∈ O)) (decide ((6 : Fin 24) ∈ O))
      (decide ((8 : Fin 24) ∈ O))).card = 8 := by
    rw [← hO]
    exact hcard
  obtain ⟨h2, h6, h8⟩ := ostdPatt_card_eight _ _ _ hc
  rw [hO, h2, h6, h8]
  exact ostdPatt_eq_Ostd

theorem eq_Bstd_of_PO_inv {B : Finset (Fin 24)} (hcard : B.card = 4) (h0 : (0 : Fin 24) ∈ B)
    (h1 : (1 : Fin 24) ∈ B) (hinv : ∀ g ∈ PO, g • B = B) : B = Bstd := by
  have hB := eq_ostdPatt_of_PO_inv h0 h1 hinv
  have hc : (ostdPatt (decide ((2 : Fin 24) ∈ B)) (decide ((6 : Fin 24) ∈ B))
      (decide ((8 : Fin 24) ∈ B))).card = 4 := by
    rw [← hB]
    exact hcard
  obtain ⟨h2, h6, h8⟩ := ostdPatt_card_four _ _ _ hc
  rw [hB, h2, h6, h8]
  exact ostdPatt_eq_Bstd

end CFSG.Quasithin.RonanH143
