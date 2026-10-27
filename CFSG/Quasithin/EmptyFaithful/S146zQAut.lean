module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.Quasithin

section QAut

theorem q_conjNormal_injective {X : Type} [Group X] (N : Subgroup X) [N.Normal]
    (hcen : ∀ x : X, (∀ n ∈ N, x * n = n * x) → x ∈ N)
    (hZ : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1) :
    Function.Injective (MulAut.conjNormal : X →* MulAut N) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : ∀ n ∈ N, x * n = n * x := by
    intro n hn
    have := congrArg (fun f : MulAut N => (f ⟨n, hn⟩ : N).1) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc x * n = x * n * x⁻¹ * x := by group
      _ = n * x := by rw [this]
  have hxN : x ∈ N := hcen x hc
  exact hZ x hxN fun m hm => hc m hm

theorem q_mulEquiv_mulAut {X A : Type} [Group X] [Group A] [Finite X] [Finite A]
    (N : Subgroup X) [N.Normal] (hcen : ∀ x : X, (∀ n ∈ N, x * n = n * x) → x ∈ N)
    (hZ : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1) (e : N ≃* A)
    (hcard : Nat.card (MulAut A) ≤ Nat.card X) : Nonempty (X ≃* MulAut A) := by
  let f : X →* MulAut A := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut N)
  have hinj : Function.Injective f :=
    (MulAut.congr e).injective.comp (q_conjNormal_injective N hcen hZ)
  have : Finite (MulAut A) :=
    Finite.of_injective (fun g : MulAut A => (g : A → A)) DFunLike.coe_injective
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hcard
  exact ⟨MulEquiv.ofBijective f hbij⟩

theorem q_card_le_of_ker {Y X B : Type} [Group Y] [Group X] [Group B] [Finite Y] [Finite X]
    (Φ : Y →* X) (Ψ : Y →* B) (hΨ : Function.Surjective Ψ) (hker : Φ.ker ≤ Ψ.ker) :
    Nat.card B ≤ Nat.card X := by
  have hsurj : Function.Surjective (QuotientGroup.lift Φ.ker Ψ hker) := by
    intro b
    obtain ⟨y, rfl⟩ := hΨ b
    exact ⟨QuotientGroup.mk y, rfl⟩
  have : Finite (Y ⧸ Φ.ker) := Quotient.finite _
  have h1 : Nat.card B ≤ Nat.card (Y ⧸ Φ.ker) := Nat.card_le_card_of_surjective _ hsurj
  have h2 : Nat.card (Y ⧸ Φ.ker) = Nat.card Φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv
  have h3 : Nat.card Φ.range ≤ Nat.card X := Nat.card_le_card_of_injective _ Subtype.val_injective
  omega

theorem q_mulEquiv_mulAut_of_ker {X A Y : Type} [Group X] [Group A] [Group Y] [Finite X] [Finite A]
    [Finite Y] (N : Subgroup X) [N.Normal] (hcen : ∀ x : X, (∀ n ∈ N, x * n = n * x) → x ∈ N)
    (hZ : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1) (e : N ≃* A)
    (Φ : Y →* X) (Ψ : Y →* MulAut A) (hΨ : Function.Surjective Ψ) (hker : Φ.ker ≤ Ψ.ker) :
    Nonempty (X ≃* MulAut A) :=
  q_mulEquiv_mulAut N hcen hZ e (q_card_le_of_ker Φ Ψ hΨ hker)

end QAut

end CFSG.Quasithin
