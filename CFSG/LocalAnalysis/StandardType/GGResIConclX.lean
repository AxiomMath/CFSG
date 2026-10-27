module

public import CFSG.LocalAnalysis.StandardType.GGResIStd
public import CFSG.LocalAnalysis.StandardType.GGResILineDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggGlueI {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (_ib ic : Fin n) (e₁ e₂ : ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun k l => if hk : k.val < n then
    (if hl : l.val < n then C ⟨k.val, hk⟩ ⟨l.val, hl⟩ else if k.val = ic.val then e₂ else 0)
    else if l.val < n then (if l.val = ic.val then e₁ else 0) else 2

@[expose] def GGResIStdShapeI {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (e₁ e₂ : ℤ) : Prop :=
  ∃ M₀ : CoxeterMatrix (Fin (n + 1)), GGIsWeylMatrix M₀ ∧ GGIntCartan M₀ (ggGlueI C ib ic e₁ e₂)

section Cert

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

@[expose] def GGResILineCertI {n : ℕ} (ib : Fin n) (C : Matrix (Fin n) (Fin n) ℤ)
    (g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)) (α : Fin (n + 1) → Module.Dual (ZMod p) V)
    (allA : Prop) : Prop :=
  ∃ (T : GGResLineJType) (e : Fin T.rank ≃ {i : Fin n // i ≠ ib}),
    (∀ k l, C (e k).1 (e l).1 = T.cartan k l) ∧
    LinearIndependent (ZMod p) (fun j : {i : Fin n // i ≠ ib} => α j.1.castSucc) ∧
    ∃ (z w : V) (F : List ((V ≃ₗ[ZMod p] V) × Fin (n + 1))) (S : Subgroup (V ≃ₗ[ZMod p] V)),
      (∀ j : Fin n, j ≠ ib → α j.castSucc z = 0) ∧ (∀ j : Fin n, j ≠ ib → α j.castSucc w = 0) ∧
      (∃ i : Fin n, α i.castSucc z ≠ 0) ∧ F ≠ [] ∧
      (∀ ψo ∈ F, (allA ∨ ψo.2 ≠ Fin.last n) ∧ ψo.1 ∈ Subgroup.closure (Set.range g) ∧
        α ψo.2 (ψo.1⁻¹ z) = 0 ∧ α ψo.2 (ψo.1⁻¹ w) ≠ 0 ∧
        ∃ j : Fin n, j ≠ ib ∧ ψo.1 * g ψo.2 * ψo.1⁻¹ * g j.castSucc ≠
          g j.castSucc * (ψo.1 * g ψo.2 * ψo.1⁻¹)) ∧
      S ≤ Subgroup.closure ({t | ∃ ψo ∈ F, t = ψo.1 * g ψo.2 * ψo.1⁻¹} ∪
        {t | ∃ j : Fin n, j ≠ ib ∧ t = g j.castSucc}) ∧
      T.bad ∣ Nat.card S

end Cert

@[expose] def GGResIO2aI (p : ℕ) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (e₁ e₂ : ℤ) (u v : ZMod p) : Prop :=
  p = 3 ∧ ∃ j₀ j₁ : Fin n, j₀ ≠ ib ∧ j₁ ≠ ib ∧ j₀ ≠ j₁ ∧ (∀ i : Fin n, i = j₀ ∨ i = j₁ ∨ i = ib) ∧
    C j₀ j₁ = -1 ∧ C j₁ j₀ = -1 ∧ C j₀ ib = -1 ∧ C ib j₀ = -1 ∧ C j₁ ib = 0 ∧ C ib j₁ = 0 ∧
    (ic = j₀ ∨ ic = j₁) ∧
    ((e₂ = -1 ∧ e₁ = -2 ∧ u = 1 ∧ v = 2) ∨ (e₂ = -2 ∧ e₁ = -1 ∧ u = 2 ∧ v = 1))

@[expose] def GGResIO2bI (p : ℕ) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (e₁ e₂ : ℤ) (u v : ZMod p) : Prop :=
  p = 3 ∧ ∃ j₁ j₂ : Fin n, ic ≠ ib ∧ j₁ ≠ ib ∧ j₂ ≠ ib ∧ ic ≠ j₁ ∧ j₁ ≠ j₂ ∧ ic ≠ j₂ ∧
    (∀ i : Fin n, i = ic ∨ i = j₁ ∨ i = j₂ ∨ i = ib) ∧
    C ic j₁ = -1 ∧ C j₁ ic = -1 ∧ C j₁ j₂ = -1 ∧ C j₂ j₁ = -1 ∧ C ic j₂ = 0 ∧ C j₂ ic = 0 ∧
    C j₁ ib = -1 ∧ C ib j₁ = -1 ∧ C ic ib = 0 ∧ C ib ic = 0 ∧ C j₂ ib = 0 ∧ C ib j₂ = 0 ∧
    ((e₂ = -1 ∧ e₁ = -2 ∧ u = 1 ∧ v = 2) ∨ (e₂ = -2 ∧ e₁ = -1 ∧ u = 2 ∧ v = 1))

section ConclX

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

@[expose] def GGResIConclX {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ)
    (u v : ZMod p) (g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)) (h : Fin (n + 1) → V)
    (α : Fin (n + 1) → Module.Dual (ZMod p) V) (x : V) : Prop :=
  GGResIConcl g h α ib x ∨ (u = 0 ∧ GGResIStdShapeI C ib ic e₁ e₂) ∨
    (p = 3 ∧ GGResILineCertI ib C g α False) ∨
    (GGResIO2aI p C ib ic e₁ e₂ u v ∧ GGResILineCertI ib C g α True) ∨
    GGResIO2bI p C ib ic e₁ e₂ u v

@[expose] def GGResIShapeOK {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) :
    Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] [Finite V] (g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)) (h : Fin (n + 1) → V)
    (α : Fin (n + 1) → Module.Dual (ZMod p) V) (x : V) (u v : ZMod p),
    p ≠ 2 → (∀ k w, g k w = w - α k w • h k) → (∀ k, α k (h k) = 2) →
    GGFTable (RingHom.id (ZMod p)) (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α →
    Submodule.span (ZMod p) (Set.range h) = ⊤ → LinearIndependent (ZMod p) h →
    (∀ i : Fin n, α i.castSucc x = 0) →
    (∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) → w ∈ Submodule.span (ZMod p) {x}) → x ≠ 0 →
    GGResIConclX C ib ic e₁ e₂ u v g h α x

end ConclX

end CFSG.StandardType
