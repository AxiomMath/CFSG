module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelDefs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLiftDefs

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

structure FrameData (R : Type) [Group R] where
  H : Subgroup (MulAut R)
  diag : Multiplicative (Fin Tag.E6.rank → ZMod 3) →* MulAut R
  Tor : Subgroup R
  nb : Fin 6 → R

namespace FrameData

variable {R : Type} [Group R] (D : FrameData R)

@[expose] def ad (x : Fin Tag.E6.rank → ZMod 3) : MulAut R := D.diag (Multiplicative.ofAdd x)

theorem ad_add (x y : Fin Tag.E6.rank → ZMod 3) : D.ad (x + y) = D.ad x * D.ad y :=
  D.diag.map_mul _ _

theorem ad_zero : D.ad 0 = 1 := D.diag.map_one

theorem ad_neg (x : Fin Tag.E6.rank → ZMod 3) : D.ad (-x) = (D.ad x)⁻¹ :=
  D.diag.map_inv (Multiplicative.ofAdd x)

@[expose] def V0 : Subgroup R where
  carrier := {r | r ∈ D.Tor ∧ ∃ v ∈ NoOffRest.hypE6, MulAut.conj r = D.ad v}
  one_mem' := ⟨D.Tor.one_mem, 0, NoOffRest.hypE6.zero_mem, by rw [map_one, D.ad_zero]⟩
  mul_mem' := by
    rintro a b ⟨ha, v, hv, hav⟩ ⟨hb, w, hw, hbw⟩
    exact ⟨D.Tor.mul_mem ha hb, v + w, NoOffRest.hypE6.add_mem hv hw,
      by rw [map_mul, hav, hbw, D.ad_add]⟩
  inv_mem' := by
    rintro a ⟨ha, v, hv, hav⟩
    exact ⟨D.Tor.inv_mem ha, -v, NoOffRest.hypE6.neg_mem hv, by rw [map_inv, hav, D.ad_neg]⟩

@[expose] def Faithful : Prop := Function.Injective D.diag

@[expose] def Shape : Prop :=
  ∀ X : Subgroup (MulAut R), X ≤ D.H → CFSG.Open.IsElemAbelian 3 X → 3 ^ 5 ≤ Nat.card X →
    ∃ γ ∈ D.H, ∀ x ∈ X, γ * x * γ⁻¹ ∈ D.diag.range

@[expose] def TorusOK : Prop :=
  (∀ s ∈ D.Tor, ∀ t ∈ D.Tor, s * t = t * s) ∧ (∀ t ∈ D.Tor, Odd (orderOf t)) ∧
    ∀ (x : Fin Tag.E6.rank → ZMod 3), ∀ t ∈ D.Tor, D.ad x t = t

@[expose] def Cent : Prop :=
  ∀ r : R, (∀ v ∈ NoOffRest.hypE6, D.ad v r = r) ↔ r ∈ D.Tor

@[expose] def InnerPts : Prop :=
  ∀ v ∈ NoOffRest.hypE6, ∃ r ∈ D.Tor, r ^ 3 = 1 ∧ MulAut.conj r = D.ad v

@[expose] def WeylOK : Prop :=
  (∀ i, D.nb i * D.nb i = 1) ∧
  (∀ i, ∀ t ∈ D.Tor, D.nb i * t * (D.nb i)⁻¹ ∈ D.Tor) ∧
  (∀ i (x : Fin Tag.E6.rank → ZMod 3), MulAut.conj (D.nb i) * D.ad x * (MulAut.conj (D.nb i))⁻¹ =
      D.ad (adRefl .E6 3 i x)) ∧
  (∀ i (x : Fin Tag.E6.rank → ZMod 3), D.nb i * (D.ad x (D.nb i))⁻¹ ∈ D.V0)

@[expose] def ModuleOK : Prop :=
  ∀ {L : Type} [Group L] (ψ : L →* R) (N : Set L), (∀ i, ∃ n ∈ N, ψ n = D.nb i) →
    GGNoInvFunc ψ N D.Tor ∧ GGNoInvAlt ψ N D.Tor ∧ GGNoInvFunc ψ N D.V0

@[expose] def NormOK : Prop :=
  ∀ (r : R) (S : Set (Fin Tag.E6.rank → ZMod 3)),
    (S = Set.univ ∨ S = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3))) →
    (∀ x ∈ S, ∃ y ∈ S, MulAut.conj r * D.ad x * (MulAut.conj r)⁻¹ = D.ad y) →
    ∃ u : WeylGroup .E6, ∀ x ∈ S,
      MulAut.conj r * D.ad x * (MulAut.conj r)⁻¹ = D.ad (adAct .E6 3 u x)

@[expose] def AutOK : Prop :=
  ∀ (α : MulAut R) (S : Set (Fin Tag.E6.rank → ZMod 3)),
    (S = Set.univ ∨ S = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3))) →
    (∀ x ∈ S, ∃ y ∈ S, α * D.ad x * α⁻¹ = D.ad y) →
    ∃ (c : ZMod 3) (u : WeylGroup .E6), c ≠ 0 ∧ ∀ x ∈ S,
      α * D.ad x * α⁻¹ = D.ad (c • adAct .E6 3 u x)

structure Good : Prop where
  center : Subgroup.center R = ⊥
  faithful : D.Faithful
  shape : D.Shape
  torus : D.TorusOK
  cent : D.Cent
  inner : D.InnerPts
  weyl : D.WeylOK
  modules : D.ModuleOK
  norm : D.NormOK
  aut : D.AutOK

end FrameData

@[expose] def CoverOdd (R : Type) [Group R] : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ∃ k : ℕ, Nat.card ψ.ker ∣ 2 ^ k * 3

end CFSG.StandardType.E6ThreeModel
