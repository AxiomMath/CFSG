module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGTBFix
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LocalAnalysis.StandardType.GGTBWInputDefs

@[expose] public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

def ggZetaP (p m : ℕ) : Multiplicative (ZMod m) := Multiplicative.ofAdd ((m / p : ℕ) : ZMod m)

structure GGTorusTorWit (m N : ℕ) (L' : Type) [Group L'] (A : Subgroup (MulAut L')) where
  T : Subgroup (MulAut L')
  α : Fin N → MulAut L' → Multiplicative (ZMod m)
  cor : Fin N → (Multiplicative (ZMod m) →* L')
  n : Fin N → L'
  hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer (A : Set (MulAut L'))
  Tsc : Subgroup L'

def GGTorusTorWit.Holds {m N : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (w : GGTorusTorWit m N L' A) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)) :
    Prop :=
  (∀ x ∈ w.T, ∀ y ∈ w.T, x * y = y * x) ∧
  A ≤ w.T ∧
  (∀ k ζ, MulAut.conj (w.cor k ζ) ∈ w.T) ∧
  (∀ j, ∀ x ∈ w.T, ∀ y ∈ w.T, w.α j (x * y) = w.α j x * w.α j y) ∧
  (∀ k, Function.Injective (w.cor k)) ∧
  (∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) ∧
  (∀ τ ∈ w.T, ∀ k ζ, τ (w.cor k ζ) = w.cor k ζ) ∧
  (∀ i j ζ, w.α i (MulAut.conj (w.cor j ζ)) = ζ ^ C i j) ∧
  (∀ k, ∀ τ ∈ w.T, MulAut.conj (w.n k) * τ * (MulAut.conj (w.n k))⁻¹ =
    τ * (MulAut.conj (w.cor k (w.α k τ)))⁻¹) ∧
  (∀ k, ∀ τ ∈ w.T, w.n k * (τ (w.n k))⁻¹ = (w.cor k (w.α k τ))⁻¹) ∧
  (∀ τ ∈ w.T, (∀ k, w.α k τ = 1) → τ = 1) ∧
  (∀ k, ∃ a ∈ A, w.α k a ≠ 1) ∧
  (∀ a ∈ A, a ∈ (MulAut.conj : L' →* MulAut L').range →
    ∃ t ∈ ⨆ k, (w.cor k).range, a = MulAut.conj t) ∧
  (∀ z ∈ Subgroup.center L', Odd (orderOf z) → z ∈ w.Tsc) ∧
  ((∀ g : L', (∀ a ∈ A, MulAut.conj g * a = a * MulAut.conj g) →
    g ∈ w.Tsc ⊔ Subgroup.center L') ∧
    (∀ τ ∈ w.T, ∀ t ∈ w.Tsc, τ t = t) ∧
    (∀ t ∈ w.Tsc, t ^ m = 1 → t ∈ ⨆ k, (w.cor k).range)) ∧
  ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
    Subgroup.closure (Set.range fun k => ggConjAut A (w.hn k)) ∧
  ∃ e : M.Group ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A),
    ∀ k, (e (M.simple k) : MulAut ↥A) = ggConjAut A (w.hn k)

def GGTorusTorData (m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N))
    (L' : Type) [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∃ w : GGTorusTorWit m N L' A, w.Holds C M

def GGTorusTorW (p r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N))
    (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A → GGTorusTorData m N C M L' A

def ggTorM (lab : LargeEvenLabel) : ℕ :=
  if lab.tag = .twA ∨ lab.tag = .twE6 then 2 ^ lab.n + 1 else 2 ^ lab.n - 1

def ggTorME8 (lab : LargeEvenLabel) : ℕ :=
  if 3 ∣ 2 ^ lab.n - 1 then 2 ^ lab.n - 1 else 2 ^ lab.n + 1

def ggTorEnn (p : ℕ) (lab : LargeEvenLabel) : ℕ :=
  if p ∣ 2 ^ lab.n + 1 then 1 else 0

def GGTBTorA : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .A ∨ lab.tag = .twA) → 4 ≤ lab.rank → p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      ¬ (p = 3 ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n + 1) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
          (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I

def GGTBTorE6 : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .E6 → 3 ∣ ggTorM lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusTorW 3 5 (ggTorM lab) 6 CartanMatrix.E₆ CoxeterMatrix.E₆ R I

def GGTBTorE8 : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .E8 →
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusTorW 3 (8 - ggTorEnn 3 lab) (ggTorME8 lab) 8 CartanMatrix.E₈ CoxeterMatrix.E₈ R I


end CFSG.StandardType
