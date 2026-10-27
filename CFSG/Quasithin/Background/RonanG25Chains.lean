module

public import CFSG.Quasithin.Background.RonanG25Pi
public import CFSG.Quasithin.Background.RonanG25BaseV
public import CFSG.Quasithin.Background.RonanG25BaseVd
public import CFSG.Quasithin.Background.RonanG25BaseU

public section

namespace CFSG.Quasithin.RonanG25

open scoped MatrixGroups

theorem piPow_bot {M : Type} [AddCommGroup M] (k : ℕ) :
    piPow k (⊥ : AddSubgroup M) = ⊥ := by
  ext e
  simp only [mem_piPow, AddSubgroup.mem_bot]
  constructor
  · intro h
    funext l
    exact h l
  · rintro rfl l
    rfl

theorem piPow_top {M : Type} [AddCommGroup M] (k : ℕ) :
    piPow k (⊤ : AddSubgroup M) = ⊤ := by
  ext e
  simp [mem_piPow]

theorem aInv_top {Γ : Type} [Group Γ] {E : Type} [AddCommGroup E] (act : Γ → E →+ E) :
    AInv act ⊤ := by
  intro x e _
  exact AddSubgroup.mem_top _

theorem card_eq_two_of_not_two_lt {F : Type} [Field F] [Finite F] (h : ¬ 2 < Nat.card F) :
    Nat.card F = 2 := by
  have : 1 < Nat.card F := Finite.one_lt_card
  omega

section Chains

variable {F : Type} [Field F] [Finite F] [CharP F 2] {Γ : Type} [Group Γ]
  {ρ : Γ →* SL(3, F)}

theorem chain_V (hρ : L1Rep ρ) :
    ModChain F (actV ρ) ⊥ ⊤ 1 (if 2 < Nat.card F then 1 else 0) := by
  have hV := V_line hρ
  have hQ := V_quot hρ
  have hrest : ModChain F (actV ρ) (lineSub F) ⊤ 1 0 :=
    ModChain.natural hQ.1 hQ.2 (ModChain.refl ⊤ (aInv_top _))
  by_cases h : 2 < Nat.card F
  · rw [if_pos h]
    exact ModChain.additional hV.1 (hV.2.2 h) hrest
  · rw [if_neg h]
    exact ModChain.central hV.1 (hV.2.1 (card_eq_two_of_not_two_lt h)) hrest

theorem chain_piV_lines (hρ : L1Rep ρ) (r : ℕ) :
    ModChain F (piAct r (actV ρ)) ⊥ (piPow r (lineSub F)) 0 (if 2 < Nat.card F then r else 0) := by
  have hV := V_line hρ
  by_cases h : 2 < Nat.card F
  · rw [if_pos h]
    have h1 := ModChain.pi_additional hV.1 (hV.2.2 h) r
    rw [piPow_bot] at h1
    exact h1
  · rw [if_neg h]
    have h1 := ModChain.pi_central (F := F) hV.1 (hV.2.1 (card_eq_two_of_not_two_lt h)) r
    rw [piPow_bot] at h1
    exact h1

theorem chain_piV_up (hρ : L1Rep ρ) (r : ℕ) :
    ModChain F (piAct r (actV ρ)) (piPow r (lineSub F)) ⊤ r 0 := by
  have h1 := ModChain.pi_natural (V_quot hρ).1 (V_quot hρ).2 r
  rw [piPow_top] at h1
  exact h1

theorem chain_piVd_ann (hρ : L1Rep ρ) (s : ℕ) :
    ModChain F (piAct s (actVd ρ)) ⊥ (piPow s (annSub F)) s 0 := by
  have h1 := ModChain.pi_natural (Vd_ann hρ).1 (Vd_ann hρ).2 s
  rw [piPow_bot] at h1
  exact h1

theorem chain_piVd_up (hρ : L1Rep ρ) (s : ℕ) :
    ModChain F (piAct s (actVd ρ)) (piPow s (annSub F)) ⊤ 0
      (if 2 < Nat.card F then s else 0) := by
  have hQ := Vd_quot hρ
  by_cases h : 2 < Nat.card F
  · rw [if_pos h]
    have h1 := ModChain.pi_additional hQ.1 (hQ.2.2 h) s
    rw [piPow_top] at h1
    exact h1
  · rw [if_neg h]
    have h1 := ModChain.pi_central (F := F) hQ.1 (hQ.2.1 (card_eq_two_of_not_two_lt h)) s
    rw [piPow_top] at h1
    exact h1

theorem chain_U (hρ : L1Rep ρ) : ModChain F (actU ρ) ⊥ ⊤ 1 0 :=
  ModChain.natural (U_nat hρ).1 (U_nat hρ).2 (ModChain.refl ⊤ (aInv_top _))

end Chains

end CFSG.Quasithin.RonanG25
