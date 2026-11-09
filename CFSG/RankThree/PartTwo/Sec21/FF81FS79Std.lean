module

public import CFSG.Quasithin.H13.U3S1347P
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.Permutation.FinPackDec

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

namespace J6

abbrev S6 := Perm (Fin 6)

def c₁ : S6 := swap 0 1 * swap 1 2

def c₂ : S6 := swap 3 4 * swap 4 5

def d : S6 := c₁ * c₂

def d' : S6 := c₁ * c₂⁻¹

def Efin : Finset S6 :=
  (Finset.univ : Finset (Fin 3 × Fin 3)).image fun p => c₁ ^ p.1.val * c₂ ^ p.2.val

def N6 : Finset S6 := Finset.univ.filter fun n => ∀ e ∈ Efin, n * e * n⁻¹ ∈ Efin

theorem Efin_card : Efin.card = 9 := by decide +kernel

theorem Efin_mul : ∀ a ∈ Efin, ∀ b ∈ Efin, a * b ∈ Efin := by decide +kernel

theorem Efin_inv : ∀ a ∈ Efin, a⁻¹ ∈ Efin := by decide +kernel

theorem one_mem_Efin : (1 : S6) ∈ Efin := by decide +kernel

def E6 : Subgroup S6 where
  carrier := {σ | σ ∈ Efin}
  mul_mem' := fun {a b} ha hb => Efin_mul a ha b hb
  one_mem' := one_mem_Efin
  inv_mem' := fun {a} ha => Efin_inv a ha

theorem card_E6 : Nat.card E6 = 9 := by
  have h : (E6 : Set S6) = (Efin : Set S6) := by
    ext σ
    simp [E6]
  show Nat.card (E6 : Set S6) = 9
  rw [Nat.card_coe_set_eq, h, Set.ncard_coe_finset, Efin_card]

section NormPairs

open CFSG.Permutation.FinPack

def normPairsConj : List ℕ :=
  [2164035, 2163795, 1180995, 1180755, 5517840, 4534800, 5517600, 4534560]

theorem swap45_mem_N6 : swap (4 : Fin 6) 5 ∈ N6 := by
  simp only [N6, Finset.mem_filter, Finset.mem_univ, true_and]
  decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem norm_pairs : ∀ x ∈ Efin, ∀ y ∈ Efin, x ≠ 1 → (∀ k : Fin 3, x ^ k.val ≠ y) →
    (∀ n ∈ N6, (n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x⁻¹ ∨ n * x * n⁻¹ = y ∨ n * x * n⁻¹ = y⁻¹) ∧
      (n * y * n⁻¹ = x ∨ n * y * n⁻¹ = x⁻¹ ∨ n * y * n⁻¹ = y ∨ n * y * n⁻¹ = y⁻¹)) →
    (∃ g : S6, g * x * g⁻¹ = c₁ ∧ g * y * g⁻¹ = c₂) ∨
      (∃ g : S6, g * x * g⁻¹ = d ∧ g * y * g⁻¹ = d') := by
  have hw : allLtK (fun a => allLtK (fun b => allLtK (fun a' => allLtK (fun b' =>
      Nat.beq (enc (c₁ ^ a * c₂ ^ b)) (enc (1 : S6)) ||
      Nat.beq (powK 6 (enc (1 : S6)) (enc (c₁ ^ a * c₂ ^ b)) 0) (enc (c₁ ^ a' * c₂ ^ b')) ||
      Nat.beq (powK 6 (enc (1 : S6)) (enc (c₁ ^ a * c₂ ^ b)) 1) (enc (c₁ ^ a' * c₂ ^ b')) ||
      Nat.beq (powK 6 (enc (1 : S6)) (enc (c₁ ^ a * c₂ ^ b)) 2) (enc (c₁ ^ a' * c₂ ^ b')) ||
      !((Nat.beq (mulK 6 (mulK 6 (enc (swap (4 : Fin 6) 5)) (enc (c₁ ^ a * c₂ ^ b)))
            (invCK 6 (enc (swap (4 : Fin 6) 5)))) (enc (c₁ ^ a * c₂ ^ b)) ||
          Nat.beq (mulK 6 (mulK 6 (enc (swap (4 : Fin 6) 5)) (enc (c₁ ^ a * c₂ ^ b)))
            (invCK 6 (enc (swap (4 : Fin 6) 5)))) (invCK 6 (enc (c₁ ^ a * c₂ ^ b))) ||
          Nat.beq (mulK 6 (mulK 6 (enc (swap (4 : Fin 6) 5)) (enc (c₁ ^ a * c₂ ^ b)))
            (invCK 6 (enc (swap (4 : Fin 6) 5)))) (enc (c₁ ^ a' * c₂ ^ b')) ||
          Nat.beq (mulK 6 (mulK 6 (enc (swap (4 : Fin 6) 5)) (enc (c₁ ^ a * c₂ ^ b)))
            (invCK 6 (enc (swap (4 : Fin 6) 5)))) (invCK 6 (enc (c₁ ^ a' * c₂ ^ b')))) &&
        (Nat.beq (mulK 6 (mulK 6 (enc (swap (4 : Fin 6) 5)) (enc (c₁ ^ a' * c₂ ^ b')))
            (invCK 6 (enc (swap (4 : Fin 6) 5)))) (enc (c₁ ^ a * c₂ ^ b)) ||
          Nat.beq (mulK 6 (mulK 6 (enc (swap (4 : Fin 6) 5)) (enc (c₁ ^ a' * c₂ ^ b')))
            (invCK 6 (enc (swap (4 : Fin 6) 5)))) (invCK 6 (enc (c₁ ^ a * c₂ ^ b))) ||
          Nat.beq (mulK 6 (mulK 6 (enc (swap (4 : Fin 6) 5)) (enc (c₁ ^ a' * c₂ ^ b')))
            (invCK 6 (enc (swap (4 : Fin 6) 5)))) (enc (c₁ ^ a' * c₂ ^ b')) ||
          Nat.beq (mulK 6 (mulK 6 (enc (swap (4 : Fin 6) 5)) (enc (c₁ ^ a' * c₂ ^ b')))
            (invCK 6 (enc (swap (4 : Fin 6) 5)))) (invCK 6 (enc (c₁ ^ a' * c₂ ^ b'))))) ||
      anyK (fun g => permValidK 6 g &&
        (Nat.beq (mulK 6 (mulK 6 g (enc (c₁ ^ a * c₂ ^ b))) (invCK 6 g)) (enc c₁) &&
          Nat.beq (mulK 6 (mulK 6 g (enc (c₁ ^ a' * c₂ ^ b'))) (invCK 6 g)) (enc c₂))) normPairsConj ||
      anyK (fun g => permValidK 6 g &&
        (Nat.beq (mulK 6 (mulK 6 g (enc (c₁ ^ a * c₂ ^ b))) (invCK 6 g)) (enc d) &&
          Nat.beq (mulK 6 (mulK 6 g (enc (c₁ ^ a' * c₂ ^ b'))) (invCK 6 g)) (enc d'))) normPairsConj)
      3) 3) 3) 3 = true := by
    decide +kernel
  have hn : 6 ≤ 16 := by norm_num
  intro x hx y hy hx1 hk H
  obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨⟨a', b'⟩, -, rfl⟩ := Finset.mem_image.1 hy
  have h := allLtK_iff.1 (allLtK_iff.1 (allLtK_iff.1 (allLtK_iff.1 hw _ a.2) _ b.2) _ a'.2) _ b'.2
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have hH := H _ swap45_mem_N6
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  simp only [beq_enc_eq_decide hn, powK_enc hn, mulK_enc hn, invCK_enc hn, hx1, h0, h1, h2,
    decide_false, Bool.false_or, Bool.or_eq_true] at h
  rcases h with (hV | h) | h
  · exfalso
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, Bool.or_eq_false_iff,
      decide_eq_false_iff_not] at hV
    tauto
  · obtain ⟨g, hg⟩ := exists_of_anyK_valid h
    simp only [mulK_enc hn, invCK_enc hn, beq_enc_eq_decide hn, Bool.and_eq_true,
      decide_eq_true_eq] at hg
    exact Or.inl ⟨g, hg⟩
  · obtain ⟨g, hg⟩ := exists_of_anyK_valid h
    simp only [mulK_enc hn, invCK_enc hn, beq_enc_eq_decide hn, Bool.and_eq_true,
      decide_eq_true_eq] at hg
    exact Or.inr ⟨g, hg⟩

end NormPairs

theorem diag_std : ∃ g : S6, CFSG.Quasithin.H13.U3.S6Out.phi (g * d * g⁻¹) = c₁ ∧
    CFSG.Quasithin.H13.U3.S6Out.phi (g * d' * g⁻¹) = c₂ := by decide +kernel

end J6

end CFSG.RankThree.PartTwo.Sec21.FF81
