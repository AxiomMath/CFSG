module

public import CFSG.Quasithin.H13.U3S1347P
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

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

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem norm_pairs : ∀ x ∈ Efin, ∀ y ∈ Efin, x ≠ 1 → (∀ k : Fin 3, x ^ k.val ≠ y) →
    (∀ n ∈ N6, (n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x⁻¹ ∨ n * x * n⁻¹ = y ∨ n * x * n⁻¹ = y⁻¹) ∧
      (n * y * n⁻¹ = x ∨ n * y * n⁻¹ = x⁻¹ ∨ n * y * n⁻¹ = y ∨ n * y * n⁻¹ = y⁻¹)) →
    (∃ g : S6, g * x * g⁻¹ = c₁ ∧ g * y * g⁻¹ = c₂) ∨
      (∃ g : S6, g * x * g⁻¹ = d ∧ g * y * g⁻¹ = d') := by decide +kernel

theorem diag_std : ∃ g : S6, CFSG.Quasithin.H13.U3.S6Out.phi (g * d * g⁻¹) = c₁ ∧
    CFSG.Quasithin.H13.U3.S6Out.phi (g * d' * g⁻¹) = c₂ := by decide +kernel

end J6

end CFSG.RankThree.PartTwo.Sec21.FF81
