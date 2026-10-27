module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7G
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NSpan

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def A1h : Subgroup Ah := listSub Al1 A1_check.1 A1_check.2.1

@[expose] def A2h : Subgroup Ah := listSub Al2 A2_check.1 A2_check.2.1

theorem A1h_le_That : A1h ≤ That :=
  listSub_le_That A1_check.2.2.2.1

theorem A2h_le_That : A2h ≤ That :=
  listSub_le_That A2_check.2.2.2.1

theorem card_A1h :
    Nat.card ↥A1h = 16 := card_A1

theorem card_A2h :
    Nat.card ↥A2h = 16 := card_A2

theorem A1h_comm {a b : Ah} (ha : a ∈ A1h) (hb : b ∈ A1h) : a * b = b * a :=
  listSub_comm A_comm_check.1 ha hb

theorem A2h_comm {a b : Ah} (ha : a ∈ A2h) (hb : b ∈ A2h) : a * b = b * a :=
  listSub_comm A_comm_check.2 ha hb

theorem A_sq_check : (∀ l ∈ Al1, comp l l = idL) ∧ (∀ l ∈ Al2, comp l l = idL) := by
  decide +kernel

theorem A1h_sq {a : Ah} (ha : a ∈ A1h) : a * a = 1 := by
  obtain ⟨l, hl, hrep⟩ := ha
  apply Subtype.ext
  apply eq_of_repL (l := comp l l) (repL_mul hrep hrep)
  rw [A_sq_check.1 l hl]
  exact repL_one 45

theorem A2h_sq {a : Ah} (ha : a ∈ A2h) : a * a = 1 := by
  obtain ⟨l, hl, hrep⟩ := ha
  apply Subtype.ext
  apply eq_of_repL (l := comp l l) (repL_mul hrep hrep)
  rw [A_sq_check.2 l hl]
  exact repL_one 45

@[expose] def gi1 : List ℕ := [1, 2, 3, 6]

@[expose] def gi2 : List ℕ := [1, 2, 4, 6]

theorem gens_check : (∀ i ∈ gi1, i < Al1.length) ∧
    (∀ l ∈ Al1, l ∈ spanL (gi1.map fun i => Al1.getD i [])) ∧
    (∀ i ∈ gi2, i < Al2.length) ∧
    (∀ l ∈ Al2, l ∈ spanL (gi2.map fun i => Al2.getD i [])) := by
  decide +kernel

end CFSG.Quasithin.H13.F431.U42Aut
