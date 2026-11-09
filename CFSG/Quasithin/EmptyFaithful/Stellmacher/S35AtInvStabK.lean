module

public import CFSG.Permutation.FinPackDec

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.At

open Equiv

namespace InvStabK

open CFSG.Permutation.FinPack

@[expose] def e5 : ℕ := 274960

@[expose] def sLt : List (List ℕ) := [
    [],
    [274960, 213520, 271120, 144400, 274945, 213505, 271105, 144385],
    [274960, 213520, 266800, 78400, 274450, 213010, 266290, 77890],
    [274960, 144400, 274720, 78400, 262675, 132115, 262435, 66115],
    [274960, 271120, 274720, 266800, 12820, 8980, 12580, 4660],
    [274960, 213520, 271120, 144400, 274945, 213505, 271105, 144385],
    [],
    [274960, 213520, 274720, 213280, 262675, 262435, 12820, 12580],
    [274960, 144400, 266800, 136240, 274450, 266290, 12820, 4660],
    [274960, 271120, 78400, 74560, 274450, 77890, 262675, 66115],
    [274960, 213520, 266800, 78400, 274450, 213010, 266290, 77890],
    [274960, 213520, 274720, 213280, 262675, 262435, 12820, 12580],
    [],
    [274960, 271120, 78400, 74560, 274945, 271105, 12820, 8980],
    [274960, 144400, 266800, 136240, 274945, 144385, 262675, 132115],
    [274960, 144400, 274720, 78400, 262675, 132115, 262435, 66115],
    [274960, 144400, 266800, 136240, 274450, 266290, 12820, 4660],
    [274960, 271120, 78400, 74560, 274945, 271105, 12820, 8980],
    [],
    [274960, 213520, 274720, 213280, 274945, 213505, 274450, 213010],
    [274960, 271120, 274720, 266800, 12820, 8980, 12580, 4660],
    [274960, 271120, 78400, 74560, 274450, 77890, 262675, 66115],
    [274960, 144400, 266800, 136240, 274945, 144385, 262675, 132115],
    [274960, 213520, 274720, 213280, 274945, 213505, 274450, 213010],
    []]

@[expose] def swT : List ℕ :=
  [274960, 274945, 274450, 262675, 12820, 274945, 274960, 274720, 266800, 78400, 274450, 274720,
    274960, 271120, 144400, 262675, 266800, 271120, 274960, 213520, 12820, 78400, 144400, 213520,
    274960]

@[expose] def sL (x y : ℕ) : List ℕ := sLt.getD (5 * x + y) []

@[expose] def swK (x y : ℕ) : ℕ := swT.getD (5 * x + y) 0

@[expose] noncomputable def inS (x y c : ℕ) : Bool :=
  ((Nat.beq (rd c x) x && Nat.beq (rd c y) y) || (Nat.beq (rd c x) y && Nat.beq (rd c y) x)) &&
    Nat.beq (mulK 5 c c) e5

@[expose] noncomputable def k2 (S : List ℕ) (s : ℕ) : Bool :=
  allK (fun a => allK (fun b => Nat.beq a e5 || Nat.beq b e5 || Nat.beq a b ||
    !memK (mulK 5 a b) S || Nat.beq a s || Nat.beq b s || Nat.beq (mulK 5 a b) s) S) S

@[expose] noncomputable def k3 (S : List ℕ) : Bool :=
  allK (fun a => allK (fun b => Nat.beq a e5 || Nat.beq b e5 || Nat.beq a b ||
    !memK (mulK 5 a b) S || allK (fun c => Nat.beq c e5 || Nat.beq c a || Nat.beq c b ||
      Nat.beq c (mulK 5 a b) || !memK (mulK 5 a c) S || !memK (mulK 5 b c) S) S) S) S

theorem sL_walk : walkK 5 (fun c => allLtK (fun x => allLtK (fun y =>
    Nat.beq x y || !inS x y c || memK c (sL x y)) 5) 5) 5 0 0 0 = true := by
  decide +kernel

theorem k_chk : allLtK (fun x => allLtK (fun y =>
    Nat.beq x y || (k2 (sL x y) (swK x y) && k3 (sL x y))) 5) 5 = true := by
  decide +kernel

theorem swK_enc : ∀ x y : Fin 5, enc (swap x y) = swK x y := by
  decide +kernel

theorem e5_enc : enc (1 : Perm (Fin 5)) = e5 := by
  unfold e5
  decide +kernel

theorem inS_of (x y : Fin 5) (g : Perm (Fin 5))
    (h : ((g x = x ∧ g y = y) ∨ (g x = y ∧ g y = x)) ∧ g ^ 2 = 1) : inS x y (enc g) = true := by
  have hn : 5 ≤ 16 := by norm_num
  unfold inS
  rw [rd_enc hn, rd_enc hn, ← enc_mul hn, ← pow_two, h.2, e5_enc, Nat.beq_refl, Bool.and_true]
  rcases h.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, Nat.beq_refl]

end InvStabK

open CFSG.Permutation.FinPack InvStabK in
theorem invStab_card_of_fix (x y : Fin 5) (hxy : x ≠ y) (F : Finset (Perm (Fin 5)))
    (hF : ∀ g ∈ F, ((g x = x ∧ g y = y) ∨ (g x = y ∧ g y = x)) ∧ g ^ 2 = 1)
    (h1 : (1 : Perm (Fin 5)) ∈ F) (hmul : ∀ a ∈ F, ∀ b ∈ F, a * b ∈ F) :
    F.card ≤ 4 ∧ (3 ≤ F.card → swap x y ∈ F) := by
  have hn : 5 ≤ 16 := by norm_num
  have hxy' : Nat.beq x y = false :=
    Bool.eq_false_iff.2 fun h => hxy (Fin.ext (Nat.eq_of_beq_eq_true h))
  have hS : ∀ g ∈ F, memK (enc g) (sL x y) = true := by
    intro g hg
    have h := allLtK_iff.1 (allLtK_iff.1 (walkK_sound sL_walk g) x x.2) y y.2
    rw [hxy', inS_of x y g (hF g hg), Bool.not_true, Bool.false_or, Bool.false_or] at h
    exact h
  have hk := allLtK_iff.1 (allLtK_iff.1 k_chk x x.2) y y.2
  rw [hxy', Bool.false_or, Bool.and_eq_true] at hk
  obtain ⟨hk2, hk3⟩ := hk
  have K2 : ∀ a ∈ F, ∀ b ∈ F, a ≠ 1 → b ≠ 1 → a ≠ b →
      a = swap x y ∨ b = swap x y ∨ a * b = swap x y := by
    intro a ha b hb ha1 hb1 hab
    have h := allK_iff.1 (allK_iff.1 hk2 _ (memK_iff.1 (hS a ha))) _ (memK_iff.1 (hS b hb))
    simp only [← e5_enc, ← swK_enc, mulK_enc hn, hS _ (hmul a ha b hb), beq_enc_eq_decide hn,
      ha1, hb1, hab, decide_false, Bool.false_or, Bool.not_true, Bool.or_eq_true,
      decide_eq_true_eq, or_assoc] at h
    exact h
  have K3 : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, a ≠ 1 → b ≠ 1 → a ≠ b → c ≠ 1 → c ≠ a → c ≠ b →
      c ≠ a * b → False := by
    intro a ha b hb c hc ha1 hb1 hab hc1 hca hcb hcab
    have h := allK_iff.1 (allK_iff.1 hk3 _ (memK_iff.1 (hS a ha))) _ (memK_iff.1 (hS b hb))
    simp only [← e5_enc, mulK_enc hn, hS _ (hmul a ha b hb), beq_enc_eq_decide hn,
      ha1, hb1, hab, decide_false, Bool.false_or, Bool.not_true] at h
    have h' := allK_iff.1 h _ (memK_iff.1 (hS c hc))
    simp only [beq_enc_eq_decide hn, mulK_enc hn, hS _ (hmul a ha c hc), hS _ (hmul b hb c hc),
      hc1, hca, hcb, hcab, decide_false, Bool.false_or, Bool.not_true, Bool.false_eq_true] at h'
  constructor
  · by_contra hc
    replace hc := not_le.1 hc
    obtain ⟨a, ha, ha1⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({1} : Finset (Perm (Fin 5)))) (t := F)
      (by rw [Finset.card_singleton]; omega)
    obtain ⟨b, hb, hb1⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({1, a} : Finset (Perm (Fin 5)))) (t := F)
      (lt_of_le_of_lt Finset.card_le_two (by omega))
    obtain ⟨c, hc', hc1⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({1, a, b, a * b} : Finset (Perm (Fin 5)))) (t := F)
      (lt_of_le_of_lt Finset.card_le_four hc)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha1 hb1 hc1
    exact K3 a ha b hb c hc' ha1 hb1.1 (Ne.symm hb1.2) hc1.1 hc1.2.1 hc1.2.2.1 hc1.2.2.2
  · intro h3
    obtain ⟨a, ha, ha1⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({1} : Finset (Perm (Fin 5)))) (t := F)
      (by rw [Finset.card_singleton]; omega)
    obtain ⟨b, hb, hb1⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({1, a} : Finset (Perm (Fin 5)))) (t := F)
      (lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha1 hb1
    rcases K2 a ha b hb ha1 hb1.1 (Ne.symm hb1.2) with h | h | h
    · rw [← h]
      exact ha
    · rw [← h]
      exact hb
    · rw [← h]
      exact hmul a ha b hb

end CFSG.Quasithin.F53.Stellmacher.S35.At
