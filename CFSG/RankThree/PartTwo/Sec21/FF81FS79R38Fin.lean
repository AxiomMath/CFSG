module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79D1

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open Equiv

namespace R38K

structure Frame (A₁ : Subgroup J6.S6) (c₀ : J6.S6) (J₁ : Subgroup J6.S6) : Prop where
  sq : ∀ s ∈ A₁, s * s = 1
  comm : ∀ a ∈ A₁, ∀ s ∈ A₁, a * s = s * a
  cen : ∀ σ : J6.S6, (∀ s ∈ A₁, σ * s = s * σ) → σ ∈ A₁
  iso : Nonempty (↥J₁ ≃* Equiv.Perm (Fin 3))
  norm : ∀ j ∈ J₁, ∀ s ∈ A₁, j * s * j⁻¹ ∈ A₁
  inf : ∀ x ∈ J₁, x ∈ A₁ → x = 1
  nor : ∀ n : J6.S6, (∀ s ∈ A₁, n * s * n⁻¹ ∈ A₁) → ∃ a ∈ A₁, ∃ s ∈ J₁, n = a * s
  c_mem : c₀ ∈ J₁
  c_pow : c₀ ^ 3 = 1
  c_ne : c₀ ≠ 1
  f3 : ∀ x : J6.S6, x * c₀ = c₀ * x → x ≠ 1 → ∃ j : J6.S6,
    (j * c₀ * j⁻¹ = c₀ ∨ j * c₀ * j⁻¹ = c₀⁻¹) ∧ x * (j * x * j⁻¹) ≠ 1 ∧
      (x * (j * x * j⁻¹)) ^ 3 = 1
  f4 : ∀ j : J6.S6, (j * c₀ * j⁻¹ = c₀ ∨ j * c₀ * j⁻¹ = c₀⁻¹) →
    (∀ x ∈ A₁, x * c₀ = c₀ * x → j * x * j⁻¹ ∈ A₁) → ∀ s ∈ A₁, j * s * j⁻¹ ∈ A₁

theorem T_cen : ∀ σ : J6.S6, (∀ s ∈ J6.T1fin, σ * s = s * σ) → σ ∈ J6.T1fin := by
  decide +kernel

theorem T_norm : ∀ j ∈ J6.S345fin, ∀ s ∈ J6.T1fin, j * s * j⁻¹ ∈ J6.T1fin := by decide +kernel

theorem T_inf : ∀ x ∈ J6.S345fin, x ∈ J6.T1fin → x = 1 := by decide +kernel

theorem T_nor : ∀ n : J6.S6, (∀ s ∈ J6.T1fin, n * s * n⁻¹ ∈ J6.T1fin) →
    ∃ a ∈ J6.T1fin, ∃ s ∈ J6.S345fin, n = a * s := by decide +kernel

theorem T_f3 : ∀ x : J6.S6, x * J6.c₂ = J6.c₂ * x → x ≠ 1 → ∃ j : J6.S6,
    (j * J6.c₂ * j⁻¹ = J6.c₂ ∨ j * J6.c₂ * j⁻¹ = J6.c₂⁻¹) ∧ x * (j * x * j⁻¹) ≠ 1 ∧
      (x * (j * x * j⁻¹)) ^ 3 = 1 := by decide +kernel

theorem T_f4 : ∀ j : J6.S6, (j * J6.c₂ * j⁻¹ = J6.c₂ ∨ j * J6.c₂ * j⁻¹ = J6.c₂⁻¹) →
    (∀ x ∈ J6.T1fin, x * J6.c₂ = J6.c₂ * x → j * x * j⁻¹ ∈ J6.T1fin) →
      ∀ s ∈ J6.T1fin, j * s * j⁻¹ ∈ J6.T1fin := by decide +kernel

theorem frameT : Frame J6.T1 J6.c₂ J6.S345 where
  sq := fun s hs => J6.T1fin_sq s hs
  comm := fun a ha c hc => J6.T1fin_comm a ha c hc
  cen := fun σ hσ => T_cen σ hσ
  iso := J6.S345_iso
  norm := fun j hj s hs => T_norm j hj s hs
  inf := fun x hx hx' => T_inf x hx hx'
  nor := fun n hn => T_nor n hn
  c_mem := J6.c₂_mem_S345
  c_pow := J6.c₂_pow_three
  c_ne := J6.c₂_ne_one
  f3 := T_f3
  f4 := T_f4

def iV : J6.S6 := swap 0 2 * swap 1 3

def DVfin : Finset J6.S6 :=
  {1, J6.c0, J6.c0 * J6.c0, iV, J6.c0 * iV, J6.c0 * J6.c0 * iV}

theorem DVfin_mul : ∀ a ∈ DVfin, ∀ b ∈ DVfin, a * b ∈ DVfin := by decide +kernel

theorem DVfin_inv : ∀ a ∈ DVfin, a⁻¹ ∈ DVfin := by decide +kernel

theorem one_mem_DVfin : (1 : J6.S6) ∈ DVfin := by decide +kernel

theorem DVfin_card : DVfin.card = 6 := by decide +kernel

def DV : Subgroup J6.S6 where
  carrier := {σ | σ ∈ DVfin}
  mul_mem' := fun {a b} ha hb => DVfin_mul a ha b hb
  one_mem' := one_mem_DVfin
  inv_mem' := fun {a} ha => DVfin_inv a ha

theorem card_DV : Nat.card DV = 6 := by
  rw [J6.card_of_finset DVfin DV (fun _ => Iff.rfl), DVfin_card]

theorem DV_iso : Nonempty (↥DV ≃* Perm (Fin 3)) := by
  refine CFSG.RankThree.PartOne.Q1327T.nonempty_mulEquiv_perm_three
    (⟨J6.c0, (by decide +kernel : J6.c0 ∈ DVfin)⟩ : ↥DV)
    (⟨iV, (by decide +kernel : iV ∈ DVfin)⟩ : ↥DV) ?_ ?_ ?_ ?_ ?_ card_DV
  · exact Subtype.ext J6.c0_pow_three
  · intro h
    exact J6.c0_ne_one (congrArg Subtype.val h)
  · exact Subtype.ext (by decide +kernel)
  · intro h
    exact (by decide +kernel : iV ≠ 1) (congrArg Subtype.val h)
  · exact Subtype.ext (by decide +kernel)

theorem V_cen : ∀ σ : J6.S6, (∀ s ∈ J6.V1fin, σ * s = s * σ) → σ ∈ J6.V1fin := by
  decide +kernel

theorem V_norm : ∀ j ∈ DVfin, ∀ s ∈ J6.V1fin, j * s * j⁻¹ ∈ J6.V1fin := by decide +kernel

theorem V_inf : ∀ x ∈ DVfin, x ∈ J6.V1fin → x = 1 := by decide +kernel

theorem V_nor : ∀ n : J6.S6, (∀ s ∈ J6.V1fin, n * s * n⁻¹ ∈ J6.V1fin) →
    ∃ a ∈ J6.V1fin, ∃ s ∈ DVfin, n = a * s := by decide +kernel

theorem V_f3 : ∀ x : J6.S6, x * J6.c0 = J6.c0 * x → x ≠ 1 → ∃ j : J6.S6,
    (j * J6.c0 * j⁻¹ = J6.c0 ∨ j * J6.c0 * j⁻¹ = J6.c0⁻¹) ∧ x * (j * x * j⁻¹) ≠ 1 ∧
      (x * (j * x * j⁻¹)) ^ 3 = 1 := by decide +kernel

theorem V_f4 : ∀ j : J6.S6, (j * J6.c0 * j⁻¹ = J6.c0 ∨ j * J6.c0 * j⁻¹ = J6.c0⁻¹) →
    (∀ x ∈ J6.V1fin, x * J6.c0 = J6.c0 * x → j * x * j⁻¹ ∈ J6.V1fin) →
      ∀ s ∈ J6.V1fin, j * s * j⁻¹ ∈ J6.V1fin := by decide +kernel

theorem frameV : Frame J6.V1 J6.c0 DV where
  sq := fun s hs => J6.V1fin_sq s hs
  comm := fun a ha c hc => J6.V1fin_comm a ha c hc
  cen := fun σ hσ => V_cen σ hσ
  iso := DV_iso
  norm := fun j hj s hs => V_norm j hj s hs
  inf := fun x hx hx' => V_inf x hx hx'
  nor := fun n hn => V_nor n hn
  c_mem := (by decide +kernel : J6.c0 ∈ DVfin)
  c_pow := J6.c0_pow_three
  c_ne := J6.c0_ne_one
  f3 := V_f3
  f4 := V_f4

end R38K

end CFSG.RankThree.PartTwo.Sec21.FF81
