module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGForkClassify
public import CFSG.LocalAnalysis.StandardType.GGForkCells

public section

namespace CFSG.StandardType

open Module

@[expose] def GGQ2Lin.ScaledAut {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : D.ι)
    (π : {k // k ≠ e} ≃ {k // k ≠ e}) (μ : {k // k ≠ e} → ZMod p) : Prop :=
  (∀ i, μ i ≠ 0) ∧ ∀ i j : {k // k ≠ e},
    μ i * (D.cartan i j : ZMod p) = μ j * (D.cartan (π i) (π j) : ZMod p)

@[expose] def GGQ2Lin.ScalarModW {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : D.ι)
    (π : {k // k ≠ e} ≃ {k // k ≠ e}) (μ : {k // k ≠ e} → ZMod p) : Prop :=
  ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧ ∃ w ∈ D.parab {k | k ≠ e},
    ∀ i : {k // k ≠ e}, μ i • D.coroot (π i) = ε • w (D.coroot i)

@[expose] def GGQ2Lin.GraphList {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : D.ι) : Prop :=
  (∃ k : ℕ, 2 ≤ k ∧ ∃ f : Fin (2 * k) ≃ {i // i ≠ e},
      ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D (2 * k) i j) ∨
    ∃ f : Fin 4 ≃ {i // i ≠ e}, (∀ i j, D.cartan (f i) (f j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, D.cartan (f i) (f j) = CartanMatrix.F₄ j i)

@[expose] def GGQ2Lin.LeafModels {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : D.ι) : Prop :=
  (∃ (n : ℕ) (f : Fin n ≃ {k // k ≠ e}), 1 ≤ n ∧
      ((∀ i j, D.cartan (f i) (f j) = CartanMatrix.A n i j) ∨
        (2 ≤ n ∧ ((∀ i j, D.cartan (f i) (f j) = CartanMatrix.B n i j) ∨
          (∀ i j, D.cartan (f i) (f j) = CartanMatrix.C n i j))) ∨
        (4 ≤ n ∧ ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D n i j))) ∨
    (∃ f : Fin 6 ≃ {k // k ≠ e}, ∀ i j, D.cartan (f i) (f j) = CartanMatrix.E 6 i j) ∨
    (∃ f : Fin 7 ≃ {k // k ≠ e}, ∀ i j, D.cartan (f i) (f j) = CartanMatrix.E 7 i j) ∨
    (∃ f : Fin 8 ≃ {k // k ≠ e}, ∀ i j, D.cartan (f i) (f j) = CartanMatrix.E 8 i j) ∨
    (∃ f : Fin 4 ≃ {k // k ≠ e}, (∀ i j, D.cartan (f i) (f j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, D.cartan (f i) (f j) = CartanMatrix.F₄ j i)) ∨
    (∃ f : Fin 2 ≃ {k // k ≠ e}, (∀ i j, D.cartan (f i) (f j) = CartanMatrix.G₂ i j) ∨
      (∀ i j, D.cartan (f i) (f j) = CartanMatrix.G₂ j i))

end CFSG.StandardType

end
