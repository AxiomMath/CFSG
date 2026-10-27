module

public import CFSG.Quasithin.Background.C116Two.NatLin2Fix
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.C116Two.NatLin2LinPart
public import CFSG.Quasithin.Background.C116Two.NatLin2LinSub

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

theorem card_multiplicative_pi {F : Type} [Field F] [Fintype F] :
    Nat.card (Multiplicative (Fin 2 → F)) = Fintype.card F ^ 2 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → F) ≃ (Fin 2 → F)),
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

theorem card_fix_eq {N : Type} [AddCommGroup N] (B : Subgroup (MulAut (Multiplicative N))) :
    Nat.card {x : Multiplicative N // ∀ b ∈ B, b x = x} =
      Nat.card {x : N // ∀ b ∈ B, addMap b x = x} := by
  refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun x => ?_)
  constructor
  · intro h b hb
    have := congrArg Multiplicative.toAdd (h b hb)
    simpa [addMap] using this
  · intro h b hb
    apply Multiplicative.toAdd.injective
    have := h b hb
    simpa [addMap] using this

theorem isElemAbelian_of_le' {M : Type} [Group M] {A B : Subgroup M} (hAB : A ≤ B)
    (hB : IsElemAbelian 2 B) : IsElemAbelian 2 A := by
  exact CFSG.Open.IsElemAbelian.mono hB hAB

theorem natCountMod_lin2 {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) :
    NatCountMod (Multiplicative (Fin 2 → F)) (slAct F).range := by
  haveI : CharP F 2 := charP_two_of_card (by omega) hcard
  have hq4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  intro B hB hN
  rw [card_multiplicative_pi (F := F)]
  set q := Fintype.card F with hq
  rw [card_fix_eq B]
  have hfixle : ∀ (S : Set (Fin 2 → F)) (hS : ∀ x : Fin 2 → F, (∀ b ∈ B, addMap b x = x) → x ∈ S),
      Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x} ≤ Nat.card S := fun S hS =>
    Nat.card_le_card_of_injective (fun x => ⟨x.1, hS x.1 x.2⟩) (by
      intro x y h; apply Subtype.ext; have h' := congrArg Subtype.val h; simpa using h')
  have hfixV : Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x} ≤ q ^ 2 := by
    have := hfixle Set.univ (fun _ _ => trivial)
    have h2 : Nat.card (Set.univ : Set (Fin 2 → F)) = q ^ 2 := by
      rw [Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    rw [h2] at this
    exact this
  obtain ⟨B₁, hB₁B, hlin, hcardB, hcase⟩ := exists_linear_subgroup B hB hN
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => by
    have := hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hq2 : 2 ≤ q := by omega
  by_cases hB₁bot : B₁ = ⊥
  · rcases hcase with hEq | ⟨φ, hφB, σ, hσ1, hσ2, hφ, hφ2⟩
    ·
      have hBbot : B = ⊥ := by rw [← hEq, hB₁bot]
      have hBcard : Nat.card B = 1 := by rw [hBbot]; exact Subgroup.card_bot
      rw [hBcard, one_mul]
      exact hfixV
    ·
      have hBle : Nat.card B ≤ 2 := by
        have := hcardB
        rw [hB₁bot, Subgroup.card_bot] at this
        omega
      have hφfix := card_fixed_semilinear_involution σ hσ1 hσ2 φ hφ hφ2 ⊤ (fun _ _ => trivial)
      have hc2 : Nat.card ↥(⊤ : Submodule F (Fin 2 → F)) = q ^ 2 := by
        rw [Nat.card_congr (Submodule.topEquiv (R := F) (M := Fin 2 → F)).toEquiv,
          Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
      have hcφ : Nat.card {x : Fin 2 → F // x ∈ (⊤ : Submodule F (Fin 2 → F)) ∧
          addMap φ x = x} = q := by
        have h2 : Nat.card {x : Fin 2 → F // x ∈ (⊤ : Submodule F (Fin 2 → F)) ∧
            addMap φ x = x} ^ 2 = q ^ 2 := by rw [hφfix, hc2]
        exact Nat.pow_left_injective (by norm_num) h2
      have hFixle : Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x} ≤ q := by
        rw [← hcφ]
        refine Nat.card_le_card_of_injective (fun x => ⟨x.1, trivial, x.2 φ hφB⟩) ?_
        intro x y h; apply Subtype.ext; have h' := congrArg Subtype.val h; simpa using h'
      calc Nat.card B * Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x}
          ≤ 2 * q := Nat.mul_le_mul hBle hFixle
        _ ≤ q ^ 2 := by nlinarith
  · obtain ⟨hB₁card, ℓ, hℓcard, hℓ⟩ :=
      linear_part_card B₁ (isElemAbelian_of_le' hB₁B hB) hlin hB₁bot
    rw [← hq] at hB₁card hℓcard
    rcases hcase with hEq | ⟨φ, hφB, σ, hσ1, hσ2, hφ, hφ2⟩
    ·
      have hBle : Nat.card B ≤ q := by rw [← hEq]; exact hB₁card
      have hFixle : Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x} ≤ q := by
        rw [← hℓcard]
        refine Nat.card_le_card_of_injective (fun x =>
          (⟨x.1, (hℓ x.1).mp (fun b hb => x.2 b (hEq ▸ hb))⟩ : ℓ)) ?_
        intro x y h; apply Subtype.ext; have h' := congrArg Subtype.val h; simpa using h'
      calc Nat.card B * Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x}
          ≤ q * q := Nat.mul_le_mul hBle hFixle
        _ = q ^ 2 := by ring
    ·
      have hφinv : ∀ x ∈ ℓ, addMap φ x ∈ ℓ := by
        intro x hx
        rw [← hℓ] at hx ⊢
        intro b hb
        have hcomm : b * φ = φ * b := hBcomm b (hB₁B hb) φ hφB
        have h1 : addMap b (addMap φ x) = addMap φ (addMap b x) := by
          have := congrArg (fun g => addMap g x) hcomm
          simpa [addMap_mul] using this
        rw [h1, hx b hb]
      have hsq := card_fixed_semilinear_involution σ hσ1 hσ2 φ hφ hφ2 ℓ hφinv
      set c := Nat.card {x : Fin 2 → F // x ∈ ℓ ∧ addMap φ x = x} with hc
      have hcq : c ^ 2 = q := by rw [hsq, hℓcard]
      have hFixc : Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x} ≤ c := by
        refine Nat.card_le_card_of_injective (fun x =>
          (⟨x.1, (hℓ x.1).mp (fun b hb => x.2 b (hB₁B hb)), x.2 φ hφB⟩ :
            {x : Fin 2 → F // x ∈ ℓ ∧ addMap φ x = x})) ?_
        intro x y h; apply Subtype.ext; have h' := congrArg Subtype.val h; simpa using h'
      have hBle : Nat.card B ≤ 2 * q := hcardB.trans (Nat.mul_le_mul_left 2 hB₁card)
      have h1 : (Nat.card B * Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x}) ^ 2 ≤
          (q ^ 2) ^ 2 := by
        calc (Nat.card B * Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x}) ^ 2
            = Nat.card B ^ 2 * Nat.card {x : Fin 2 → F // ∀ b ∈ B, addMap b x = x} ^ 2 := by ring
          _ ≤ (2 * q) ^ 2 * c ^ 2 :=
              Nat.mul_le_mul (Nat.pow_le_pow_left hBle 2) (Nat.pow_le_pow_left hFixc 2)
          _ = 4 * q ^ 2 * q := by rw [hcq]; ring
          _ ≤ q ^ 2 * q ^ 2 := by nlinarith
          _ = (q ^ 2) ^ 2 := by ring
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1

end CFSG.Quasithin.C116Two
