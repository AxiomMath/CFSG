module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs2
public import CFSG.Quasithin.EmptyFaithful.S153E55B

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement Pointwise

namespace S153E56a

section Counting

variable {G : Type} [Group G]

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hBN
  have h2 := Subgroup.relIndex_mul_card A (B ⊔ A)
  have h3 := Subgroup.relIndex_mul_card A B
  have h4 : A ⊓ (B ⊔ A) = A := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [sup_comm] at h2
  rw [← h2, ← h3, inf_comm]
  ring

theorem card_multiplicative_fun (s : ℕ) :
    Nat.card (Multiplicative (Fin s → Fin 2 → ZMod 2)) = 2 ^ (2 * s) := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin s → Fin 2 → ZMod 2) ≃ _)]
  simp [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]
  rw [pow_mul]
  norm_num

theorem card_eq_of_sumNat {M Si S S₂ : Subgroup G} {s : ℕ}
    (h : IsSumOfNatSL2ModulesN153 s M Si S S₂) (hle : S₂ ≤ Si) :
    Nat.card Si = Nat.card S₂ * 2 ^ (2 * s) := by
  obtain ⟨β, φ, -, -, hφs, hφk, -⟩ := h
  have hker : MonoidHom.ker φ = S₂.subgroupOf Si := by
    ext x
    rw [MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker φ)
  have h2 : Nat.card (↥Si ⧸ MonoidHom.ker φ) =
      Nat.card (Multiplicative (Fin s → Fin 2 → ZMod 2)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv
  have h4 : Nat.card ↥(MonoidHom.ker φ) = Nat.card S₂ := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h1, h2, card_multiplicative_fun, h4, mul_comm]

theorem card_P_of_pdecomp [Finite G] {I P V N₁ N₂ P₁ P₂ : Subgroup G}
    (h : S153E55.PDecomp I P V N₁ N₂ P₁ P₂) {s : ℕ}
    (h₁ : Nat.card P₁ = Nat.card V * 2 ^ (2 * s)) (h₂ : Nat.card P₂ = Nat.card V * 2 ^ (2 * s)) :
    Nat.card P = Nat.card V * 2 ^ (4 * s) := by
  have hN : P₁ ≤ Subgroup.normalizer (P₂ : Set G) :=
    (h.P₁_le_P.trans h.P_le_I).trans h.I_le_normalizer_P₂
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  rw [sup_comm, h.sup, inf_comm, h.inf, h₁, h₂] at h1
  have hV : 0 < Nat.card V := Nat.card_pos
  have h3 : (2 : ℕ) ^ (4 * s) = 2 ^ (2 * s) * 2 ^ (2 * s) := by
    rw [← pow_add]
    ring_nf
  apply Nat.eq_of_mul_eq_mul_right hV
  rw [h1, h3]
  ring

theorem le_of_prod {P W W' : Subgroup G} (hprod : (P : Set G) = (W : Set G) * (W' : Set G)) :
    W' ≤ P := by
  intro x hx
  have : x ∈ (W : Set G) * (W' : Set G) := ⟨1, W.one_mem, x, hx, one_mul x⟩
  rw [← hprod] at this
  exact this

theorem card_W_sq {U P : Subgroup G} {g : G}
    (hprod : (P : Set G) = ((U ⊓ P : Subgroup G) : Set G) * (conjSubgroup (U ⊓ P) g : Set G))
    (hWg : conjSubgroup (U ⊓ P) g ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥P * Nat.card ↥(U ⊓ P ⊓ conjSubgroup (U ⊓ P) g) =
      Nat.card ↥(U ⊓ P) * Nat.card ↥(U ⊓ P) := by
  have hWP : conjSubgroup (U ⊓ P) g ≤ P := le_of_prod hprod
  have hN : conjSubgroup (U ⊓ P) g ≤ Subgroup.normalizer ((U ⊓ P : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf hWg (hWP.trans Subgroup.le_normalizer)
  have hsup : U ⊓ P ⊔ conjSubgroup (U ⊓ P) g = P := by
    apply SetLike.coe_injective
    rw [hprod, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN]
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  have hc : Nat.card ↥(conjSubgroup (U ⊓ P) g) = Nat.card ↥(U ⊓ P) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [hsup, hc] at h1
  exact h1

end Counting

end S153E56a

end CFSG.Quasithin
