module

public import CFSG.RankThree.GF2n.Tim78S48Core

public section

namespace CFSG.RankThree.GF2n.Tim78

open Matrix

theorem no_invariant_form_mul (n : ℕ) (hn : 2 ≤ n)
    {E : Type*} [Group E] (hEc : ∀ a b : E, a * b = b * a) (hE : ∀ a : E, a * a = 1)
    {X : Type*} [Group X] (φ : X →* SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ)
    {Λ : Type*} [Group Λ] (hΛ : ∀ a b : Λ, a * b = b * a) [MulDistribMulAction X Λ]
    (ν : Multiplicative (Fin 2 → GaloisField 2 n) →* Λ) (hν : Function.Injective ν)
    (hνx : ∀ (x : X) (v : Fin 2 → GaloisField 2 n),
      ν (Multiplicative.ofAdd ((φ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ v)) =
        x • ν (Multiplicative.ofAdd v))
    (hsplit : ∀ l : Λ, ∃ (v : Fin 2 → GaloisField 2 n) (l₁ : Λ), (∀ x : X, x • l₁ = l₁) ∧
      l = ν (Multiplicative.ofAdd v) * l₁)
    (D : Λ → Λ → E) (hD₁ : ∀ a a' b, D (a * a') b = D a b * D a' b)
    (hD₂ : ∀ a b b', D a (b * b') = D a b * D a b') (hDalt : ∀ a, D a a = 1)
    (hDinv : ∀ (x : X) a b, D (x • a) (x • b) = D a b)
    (hDnd : ∀ b : Λ, b ≠ 1 → ∃ a, D a b ≠ 1)
    (κ : Λ → E) (hκ : ∀ a b, κ (a * b) = κ a * κ b * D a b)
    (hκinv : ∀ (x : X) a, κ (x • a) = κ a) : False := by
  letI : CommGroup E := { ‹Group E› with mul_comm := hEc }
  letI : CommGroup Λ := { ‹Group Λ› with mul_comm := hΛ }
  letI : DistribMulAction X (Additive Λ) :=
    { smul := fun x a => Additive.ofMul (x • Additive.toMul a)
      one_smul := fun a => by
        show Additive.ofMul ((1 : X) • Additive.toMul a) = a
        rw [one_smul]; rfl
      mul_smul := fun x y a => by
        show Additive.ofMul ((x * y) • Additive.toMul a) =
          Additive.ofMul (x • Additive.toMul (Additive.ofMul (y • Additive.toMul a)))
        rw [mul_smul]; rfl
      smul_zero := fun x => by
        show Additive.ofMul (x • (1 : Λ)) = 0
        rw [smul_one]; rfl
      smul_add := fun x a b => by
        show Additive.ofMul (x • (Additive.toMul a * Additive.toMul b)) =
          Additive.ofMul (x • Additive.toMul a) + Additive.ofMul (x • Additive.toMul b)
        rw [smul_mul']; rfl }
  let θ : (Fin 2 → GaloisField 2 n) →+ Additive Λ :=
    AddMonoidHom.mk' (fun v => Additive.ofMul (ν (Multiplicative.ofAdd v))) (fun v w => by
      show Additive.ofMul (ν (Multiplicative.ofAdd (v + w))) =
        Additive.ofMul (ν (Multiplicative.ofAdd v)) + Additive.ofMul (ν (Multiplicative.ofAdd w))
      rw [ofAdd_add, map_mul]; rfl)
  let D' : Additive Λ →+ Additive Λ →+ Additive E :=
    AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => Additive.ofMul (D a.toMul b.toMul))
      (fun b b' => hD₂ _ _ _)) (fun a a' => by
        ext b
        exact hD₁ _ _ _)
  refine no_invariant_form_gf2n n hn (A := Additive E) (fun a => ?_) φ hφ θ ?_ ?_ ?_ D' ?_ ?_ ?_
    (fun a => Additive.ofMul (κ a.toMul)) ?_ ?_
  · exact hE a.toMul
  · intro v w h
    exact Multiplicative.ofAdd.injective (hν (Additive.ofMul.injective h))
  · intro x v
    exact hνx x v
  · intro l
    obtain ⟨v, l₁, h1, h2⟩ := hsplit l.toMul
    exact ⟨v, Additive.ofMul l₁, h1, h2⟩
  · intro a
    exact hDalt a.toMul
  · intro x a b
    exact hDinv x a.toMul b.toMul
  · intro b hb
    obtain ⟨a, ha⟩ := hDnd b.toMul (fun h => hb h)
    exact ⟨Additive.ofMul a, ha⟩
  · intro a b
    exact hκ a.toMul b.toMul
  · intro x a
    exact hκinv x a.toMul

end CFSG.RankThree.GF2n.Tim78
