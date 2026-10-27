module

public import CFSG.LocalAnalysis.StandardType.GGFFModelDefs

public section

namespace CFSG.StandardType.GGFF

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {H : Type} [Group H]

@[expose] def zetaOf (z : Fin 3 → H) : H := z 0 * z 1 * z 2

@[expose] def cjp (w : H) (a : Fin 3) (u : H) : H := w ^ (a : ℕ) * u * (w ^ (a : ℕ))⁻¹

@[expose] def RootRel (w u : H) : Prop := u * (w * u * w⁻¹) = w ^ 2 * u * (w ^ 2)⁻¹

@[expose] def rootW (z : Fin 3 → H) : Fin 2 → H := ![z 0, z 1]

@[expose] def rootK₁ (z : Fin 3 → H) : Fin 2 → H := ![z 0 * z 1, z 1 * z 2]

@[expose] def rootK₂ (z : Fin 3 → H) : Fin 2 → H := ![z 2, z 0]

@[expose] def gOf (r r' : Fin 2 → H) : H := r 0 * r 1 * r' 0 * r 0 * r' 1 * r' 0

@[expose] def rOne (z : Fin 3 → H) (π : H) : Subgroup H := Subgroup.closure {z 0 * (z 1)⁻¹, zetaOf z, π}

structure ModelNB (H : Type) [Group H] (z : Fin 3 → H) (π x₀ : H) (r r' : Fin 2 → H) : Prop where
  pi_cube : π ^ 3 = 1
  pi_z : ∀ i, π * z i * π⁻¹ = z (finRotate 3 i)
  x0_z0 : x₀ * z 0 * x₀⁻¹ = z 0
  x0_z1 : x₀ * z 1 * x₀⁻¹ = z 2
  x0_z2 : x₀ * z 2 * x₀⁻¹ = z 1
  sqrt : ∀ v : Fin 3 → ZMod 3, x₀ * vecElt z v * (x₀ * vecElt z v) = 1 →
    (∃ w, x₀ * vecElt z v * π * (x₀ * vecElt z v)⁻¹ * π = vecElt z w) →
    (∃ w : Fin 3 → ZMod 3, w 0 + w 1 + w 2 = 0 ∧
      x₀ * vecElt z v * π * (x₀ * vecElt z v)⁻¹ * π = vecElt z w) ∧
    ∃ q : H, q * q = x₀ * vecElt z v ∧
      ∀ y ∈ ({z 0 * (z 1)⁻¹, zetaOf z, π} : Set H), q * y * q⁻¹ ∈ rOne z π
  root_sq : ∀ j, r j * r j = 1 ∧ r' j * r' j = 1
  root_comm : ∀ j, r j * rootK₁ z j = rootK₁ z j * r j ∧ r j * rootK₂ z j = rootK₂ z j * r j ∧
    r' j * rootK₁ z j = rootK₁ z j * r' j ∧ r' j * rootK₂ z j = rootK₂ z j * r' j
  root_rel : ∀ j, RootRel (rootW z j) (r j) ∧ RootRel (rootW z j) (r' j)
  root_char : ∀ j, ∀ u : H, u * u = 1 → u * rootK₁ z j = rootK₁ z j * u →
    u * rootK₂ z j = rootK₂ z j * u → RootRel (rootW z j) u →
    u = 1 ∨ ∃ a : Fin 3, u = cjp (rootW z j) a (r j) ∨ u = cjp (rootW z j) a (r' j)
  root_dist : ∀ j, ∀ a a' : Fin 3,
    (cjp (rootW z j) a (r j) = cjp (rootW z j) a' (r j) → a = a') ∧
    (cjp (rootW z j) a (r' j) = cjp (rootW z j) a' (r' j) → a = a') ∧
    cjp (rootW z j) a (r j) ≠ cjp (rootW z j) a' (r' j)
  braid : ∀ j, r j * r' j * r j = r' j * r j * r' j
  braid_eq : ∀ j, ∀ a a' : Fin 3,
    cjp (rootW z j) a (r j) * cjp (rootW z j) a' (r' j) * cjp (rootW z j) a (r j) =
      cjp (rootW z j) a' (r' j) * cjp (rootW z j) a (r j) * cjp (rootW z j) a' (r' j) → a = a'
  g_pow : gOf r r' ^ 7 = 1
  g_ne : gOf r r' ≠ 1
  g_out : ∀ α : MulAut H, (∀ k : H, α ≠ MulAut.conj k) → ∀ (k : H) (j : ℕ),
    (j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 4) → α (gOf r r') ≠ k * gOf r r' ^ j * k⁻¹

structure ModelN (H : Type) [Group H] (z : Fin 3 → H) : Prop where
  cen : ∀ k : H, (∀ i, k * z i = z i * k) → ∃ v, k = vecElt z v
  out : ∀ α β : MulAut H,
    (∃ k, α = MulAut.conj k) ∨ (∃ k, β = MulAut.conj k) ∨ ∃ k, α * β = MulAut.conj k
  o2 : ∀ σ : MulAut H, σ * σ = 1 → (∀ i, σ (z i) = z i) → ∀ N : Subgroup H, IsPGroup 2 N →
    (∀ n ∈ N, σ n = n) → (∀ c : H, σ c = c → ∀ n ∈ N, c * n * c⁻¹ ∈ N) → N = ⊥
  caseA : ∃ t₁ t₂ : H, t₁ * t₁ = 1 ∧ t₂ * t₂ = 1 ∧ t₁ * (z 1 * z 2) = z 1 * z 2 * t₁ ∧
    t₂ * (z 1 * z 2) = z 1 * z 2 * t₂ ∧
    ∀ y : H, y * t₁ = t₁ * y → y * t₂ = t₂ * y → y * (z 1 * z 2) = z 1 * z 2 * y
  syl7 : ∀ P : Subgroup H, IsPGroup 7 P → (∀ p ∈ P, p * zetaOf z = zetaOf z * p) →
    Nat.card P ≤ 7
  caseB : ∃ (π x₀ : H) (r r' : Fin 2 → H), ModelNB H z π x₀ r r'

end CFSG.StandardType.GGFF

end
