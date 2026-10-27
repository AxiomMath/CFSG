module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Std
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Fr6Pack

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open Equiv

namespace J6

def e1 : S6 := swap 0 1

def pp : S6 := swap 2 3

def qq : S6 := swap 4 5

def v1 : S6 := pp * qq

def v2 : S6 := swap 2 4 * swap 3 5

def v3 : S6 := swap 2 5 * swap 3 4

def a2 : S6 := swap 3 4

def sg3 : S6 := swap 0 3 * swap 1 4 * swap 2 5

def c0 : S6 := (swap 0 2 * swap 2 4) * (swap 1 3 * swap 3 5)

def T1fin : Finset S6 := {1, e1, v1, v2, v3, e1 * v1, e1 * v2, e1 * v3}

def V1fin : Finset S6 := {1, e1, pp, qq, e1 * pp, e1 * qq, pp * qq, e1 * pp * qq}

def Rfin : Finset S6 := Finset.univ.filter fun σ =>
  ({σ 0, σ 1} : Finset (Fin 6)) = {0, 1} ∧
    (({σ 2, σ 3} : Finset (Fin 6)) = {2, 3} ∨ ({σ 2, σ 3} : Finset (Fin 6)) = {4, 5})

theorem T1fin_card : T1fin.card = 8 := by decide +kernel

theorem V1fin_card : V1fin.card = 8 := by decide +kernel

theorem Rfin_card : Rfin.card = 16 := Fr6K.Rfin_card

theorem T1fin_mul : ∀ a ∈ T1fin, ∀ b ∈ T1fin, a * b ∈ T1fin := Fr6K.T1fin_mul

theorem V1fin_mul : ∀ a ∈ V1fin, ∀ b ∈ V1fin, a * b ∈ V1fin := Fr6K.V1fin_mul

theorem Rfin_mul : ∀ a ∈ Rfin, ∀ b ∈ Rfin, a * b ∈ Rfin := Fr6K.Rfin_mul

theorem T1fin_inv : ∀ a ∈ T1fin, a⁻¹ ∈ T1fin := Fr6K.T1fin_inv

theorem V1fin_inv : ∀ a ∈ V1fin, a⁻¹ ∈ V1fin := Fr6K.V1fin_inv

theorem Rfin_inv : ∀ a ∈ Rfin, a⁻¹ ∈ Rfin := Fr6K.Rfin_inv

theorem one_mem_T1fin : (1 : S6) ∈ T1fin := by decide +kernel

theorem one_mem_V1fin : (1 : S6) ∈ V1fin := by decide +kernel

theorem one_mem_Rfin : (1 : S6) ∈ Rfin := by decide +kernel

def T1 : Subgroup S6 where
  carrier := {σ | σ ∈ T1fin}
  mul_mem' := fun {a b} ha hb => T1fin_mul a ha b hb
  one_mem' := one_mem_T1fin
  inv_mem' := fun {a} ha => T1fin_inv a ha

def V1 : Subgroup S6 where
  carrier := {σ | σ ∈ V1fin}
  mul_mem' := fun {a b} ha hb => V1fin_mul a ha b hb
  one_mem' := one_mem_V1fin
  inv_mem' := fun {a} ha => V1fin_inv a ha

def R : Subgroup S6 where
  carrier := {σ | σ ∈ Rfin}
  mul_mem' := fun {a b} ha hb => Rfin_mul a ha b hb
  one_mem' := one_mem_Rfin
  inv_mem' := fun {a} ha => Rfin_inv a ha

theorem card_of_finset (F : Finset S6) (K : Subgroup S6) (hK : ∀ σ, σ ∈ K ↔ σ ∈ F) :
    Nat.card K = F.card := by
  have h : (K : Set S6) = (F : Set S6) := by
    ext σ
    simp [hK]
  show Nat.card (K : Set S6) = F.card
  rw [Nat.card_coe_set_eq, h, Set.ncard_coe_finset]

theorem card_T1 : Nat.card T1 = 8 := by
  rw [card_of_finset T1fin T1 (fun _ => Iff.rfl), T1fin_card]

theorem card_V1 : Nat.card V1 = 8 := by
  rw [card_of_finset V1fin V1 (fun _ => Iff.rfl), V1fin_card]

theorem card_R : Nat.card R = 16 := by
  rw [card_of_finset Rfin R (fun _ => Iff.rfl), Rfin_card]

theorem T1fin_subset_R : T1fin ⊆ Rfin := Fr6K.T1fin_subset_R

theorem V1fin_subset_R : V1fin ⊆ Rfin := Fr6K.V1fin_subset_R

theorem T1_le_R : T1 ≤ R := fun _ hσ => T1fin_subset_R hσ

theorem V1_le_R : V1 ≤ R := fun _ hσ => V1fin_subset_R hσ

theorem T1fin_sq : ∀ s ∈ T1fin, s * s = 1 := Fr6K.T1fin_sq

theorem V1fin_sq : ∀ s ∈ V1fin, s * s = 1 := Fr6K.V1fin_sq

theorem T1fin_comm : ∀ a ∈ T1fin, ∀ b ∈ T1fin, a * b = b * a := Fr6K.T1fin_comm

theorem V1fin_comm : ∀ a ∈ V1fin, ∀ b ∈ V1fin, a * b = b * a := Fr6K.V1fin_comm

theorem c2_norm_T1 : ∀ s ∈ T1fin, c₂ * s * c₂⁻¹ ∈ T1fin := Fr6K.c2_norm_T1

theorem c0_norm_V1 : ∀ s ∈ V1fin, c0 * s * c0⁻¹ ∈ V1fin := Fr6K.c0_norm_V1

theorem T1_cen_c2 : ∀ s ∈ T1fin, s * c₂ = c₂ * s → s = 1 ∨ s = e1 := Fr6K.T1_cen_c2

theorem V1_cen_c0 : ∀ s ∈ V1fin, s * c0 = c0 * s → s = 1 ∨ s = e1 * pp * qq :=
  Fr6K.V1_cen_c0

theorem T1_gen : ∀ s ∈ T1fin, ∃ x ∈ ({1, e1 * v1, e1 * v2, e1 * v3} : Finset S6),
    ∃ y ∈ ({1, e1 * v1, e1 * v2, e1 * v3} : Finset S6),
      ∃ z ∈ ({1, e1 * v1, e1 * v2, e1 * v3} : Finset S6), s = x * y * z := Fr6K.T1_gen

theorem V1_gen : ∀ s ∈ V1fin, ∃ x ∈ ({1, e1} : Finset S6), ∃ y ∈ ({1, pp} : Finset S6),
    ∃ z ∈ ({1, qq} : Finset S6), s = x * y * z := Fr6K.V1_gen

theorem a2_cen_c1 : a2 * c₁ = c₁ * a2 := by decide +kernel

theorem sg3_cen_d : sg3 * (c₁ * c₂) = (c₁ * c₂) * sg3 := by decide +kernel

theorem a2_sq : a2 * a2 = 1 := by decide +kernel

theorem sg3_sq : sg3 * sg3 = 1 := by decide +kernel

theorem a2_ne_one : a2 ≠ 1 := by decide +kernel

theorem sg3_ne_one : sg3 ≠ 1 := by decide +kernel

theorem conj_e1_a2 : ∃ γ : S6, γ * e1 * γ⁻¹ = a2 := ⟨swap 0 3 * swap 1 4, by decide +kernel⟩

theorem conj_pp_a2 : ∃ γ : S6, γ * pp * γ⁻¹ = a2 := by decide +kernel

theorem conj_qq_a2 : ∃ γ : S6, γ * qq * γ⁻¹ = a2 := by decide +kernel

theorem conj_x1_sg3 : ∃ γ : S6, γ * (e1 * v1) * γ⁻¹ = sg3 := by decide +kernel

theorem conj_x2_sg3 : ∃ γ : S6, γ * (e1 * v2) * γ⁻¹ = sg3 := by decide +kernel

theorem conj_x3_sg3 : ∃ γ : S6, γ * (e1 * v3) * γ⁻¹ = sg3 := by decide +kernel

theorem conj_y_sg3 : ∃ γ : S6, γ * (e1 * pp * qq) * γ⁻¹ = sg3 := by decide +kernel

theorem conj_c0_d : ∃ γ : S6, γ * c0 * γ⁻¹ = c₁ * c₂ :=
  ⟨swap 1 2 * swap 1 4 * swap 1 3, by decide +kernel⟩

def convVT : Finset S6 := {1, c0, c0⁻¹, swap 0 2 * swap 1 3, swap 0 4 * swap 1 5}

def convTV : Finset S6 := {1, swap 3 4, swap 3 5}

theorem V1_conj_T1 : ∀ r ∈ V1fin, ∃ γ ∈ convVT, γ * r * γ⁻¹ ∈ T1fin := Fr6K.V1_conj_T1

theorem T1_conj_V1 : ∀ r ∈ T1fin, ∃ γ ∈ convTV, γ * r * γ⁻¹ ∈ V1fin := Fr6K.T1_conj_V1

theorem R_inv_mem : ∀ r ∈ Rfin, r * r = 1 → r ∈ T1fin ∨ r ∈ V1fin := Fr6K.R_inv_mem

theorem noncomm_TV : ∀ x ∈ V1fin, x ∉ T1fin → ∀ y ∈ T1fin, y ∉ V1fin → x * y ≠ y * x :=
  Fr6K.noncomm_TV

def NT1 : Finset S6 := Finset.univ.filter fun σ => ∀ s ∈ T1fin, σ * s * σ⁻¹ ∈ T1fin

def NV1 : Finset S6 := Finset.univ.filter fun σ => ∀ s ∈ V1fin, σ * s * σ⁻¹ ∈ V1fin

theorem NT1_card : NT1.card = 48 := Fr6K.NT1_card

theorem NV1_card : NV1.card = 48 := Fr6K.NV1_card

theorem R_sub_NT1 : Rfin ⊆ NT1 := Fr6K.R_sub_NT1

theorem R_sub_NV1 : Rfin ⊆ NV1 := Fr6K.R_sub_NV1

def orbitB : Finset S6 := {c₁, c₁⁻¹, c₂, c₂⁻¹}

def orbitC : Finset S6 := {c₁ * c₂, (c₁ * c₂)⁻¹, c₁ * c₂⁻¹, c₁⁻¹ * c₂}

theorem norm_orbits : ∀ σ ∈ N6, σ * c₁ * σ⁻¹ ∈ orbitB ∧ σ * c₂ * σ⁻¹ ∈ orbitB ∧
    σ * (c₁ * c₂) * σ⁻¹ ∈ orbitC := Fr6K.norm_orbits

theorem orbitB_cyc_c1 : ∀ x ∈ orbitB, x ∈ ({1, c₁, c₁⁻¹} : Finset S6) → x = c₁ ∨ x = c₁⁻¹ :=
  Fr6K.orbitB_cyc_c1

theorem orbitB_not_cyc_d : ∀ x ∈ orbitB, x ∉ ({1, c₁ * c₂, (c₁ * c₂)⁻¹} : Finset S6) :=
  Fr6K.orbitB_not_cyc_d

theorem orbitC_not_cyc_c1 : ∀ x ∈ orbitC, x ∉ ({1, c₁, c₁⁻¹} : Finset S6) :=
  Fr6K.orbitC_not_cyc_c1

theorem orbitC_cyc_d : ∀ x ∈ orbitC, x ∈ ({1, c₁ * c₂, (c₁ * c₂)⁻¹} : Finset S6) →
    x = c₁ * c₂ ∨ x = (c₁ * c₂)⁻¹ := Fr6K.orbitC_cyc_d

end J6

end CFSG.RankThree.PartTwo.Sec21.FF81
