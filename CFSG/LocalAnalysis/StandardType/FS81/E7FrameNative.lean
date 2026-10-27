module

public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.Timmesfeld.RankTwo.LevisExceptional
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LieType.TitsSimplicity

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.Timmesfeld


abbrev L7 : Subgroup (ModGL .E7 (ZMod 2)) := adjointGroup .E7 (ZMod 2)

abbrev J (β : Fin (Tag.rank .E7) → ℤ) : Subgroup (ModGL .E7 (ZMod 2)) :=
  rootRankOneGroup .E7 (ZMod 2) β

abbrev Jn (i : Fin 7) : Subgroup (ModGL .E7 (ZMod 2)) := J (Pi.single i 1)

abbrev theta : Fin (Tag.rank .E7) → ℤ := CFSG.SeitzReduction.highRoot .E7

@[expose] def mu : Fin (Tag.rank .E7) → ℤ := ![1, 2, 2, 4, 3, 2, 1]

@[expose] def lam : Fin (Tag.rank .E7) → ℤ := ![1, 1, 2, 2, 1, 0, 0]

abbrev M0 : Subgroup (ModGL .E7 (ZMod 2)) :=
  L7 ⊓ Subgroup.centralizer (Jn 0 : Set (ModGL .E7 (ZMod 2)))

abbrev M6 : Subgroup (ModGL .E7 (ZMod 2)) :=
  L7 ⊓ Subgroup.centralizer (Jn 6 : Set (ModGL .E7 (ZMod 2)))

@[expose] def IsInnerAut {X : Type} [Group X] (φ : MulAut X) : Prop :=
  ∃ x : X, φ = MulAut.conj x

@[expose] def E7NatFrame : Prop :=
  (∀ i, Jn i ≤ L7) ∧
  (∀ i j : Fin 7, i ≠ j → ¬ edgeE 8 i.castSucc j.castSucc → ¬ edgeE 8 j.castSucc i.castSucc →
    ∀ a ∈ Jn i, ∀ c ∈ Jn j, a * c = c * a) ∧
  (∀ i j : Fin 7, edgeE 8 i.castSucc j.castSucc →
    ∃ W, LinearBlockStandardPair (ZMod 2) W (Jn i) (Jn j)) ∧
  ∀ H : Subgroup (ModGL .E7 (ZMod 2)), (∀ i, Jn i ≤ H) → L7 ≤ H

@[expose] def E7NatHigh : Prop :=
  (∀ i : Fin 7, i ≠ 0 → ∀ a ∈ J theta, ∀ c ∈ Jn i, a * c = c * a) ∧
  (∃ W, LinearBlockStandardPair (ZMod 2) W (J mu) (J theta)) ∧
  (∀ H : Subgroup (ModGL .E7 (ZMod 2)), (∀ m ∈ M0, ∀ x ∈ J theta, m * x * m⁻¹ ∈ H) →
    Jn 0 ≤ H) ∧
  J theta ≤ L7 ∧ (∀ i : Fin 7, i ≠ 0 → i ≠ 2 → Jn i ≤ M0) ∧ J mu ≤ M0 ∧ J lam ≤ M0

@[expose] def E7NatCent : Prop :=
  L7 ⊓ Subgroup.centralizer (M0 : Set (ModGL .E7 (ZMod 2))) = Jn 0 ∧
  (∀ z ∈ Jn 0, orderOf z = 3 →
    L7 ⊓ Subgroup.centralizer ({z} : Set (ModGL .E7 (ZMod 2))) = Subgroup.zpowers z ⊔ M0) ∧
  IsSimpleGroup M0 ∧ 3 ∣ Nat.card M0 ∧ (∃ z ∈ Jn 0, orderOf z = 3) ∧
  ∀ φ₁ φ₂ : MulAut M0, ¬ IsInnerAut φ₁ → ¬ IsInnerAut φ₂ → IsInnerAut (φ₁⁻¹ * φ₂)

@[expose] def E7NatPsi : Prop :=
  ∃ ψ : MulAut M0, ¬ IsInnerAut ψ ∧
    ((Jn 1).subgroupOf M0).map ψ.toMonoidHom = (Jn 6).subgroupOf M0 ∧
    ((Jn 3).subgroupOf M0).map ψ.toMonoidHom = (Jn 5).subgroupOf M0 ∧
    ((Jn 4).subgroupOf M0).map ψ.toMonoidHom = (Jn 4).subgroupOf M0 ∧
    ((Jn 5).subgroupOf M0).map ψ.toMonoidHom = (Jn 3).subgroupOf M0 ∧
    ((Jn 6).subgroupOf M0).map ψ.toMonoidHom = (J mu).subgroupOf M0 ∧
    ((J mu).subgroupOf M0).map ψ.toMonoidHom = (J lam).subgroupOf M0 ∧
    ((J lam).subgroupOf M0).map ψ.toMonoidHom = (Jn 1).subgroupOf M0

@[expose] def E7NatTau : Prop :=
  ∃ τ : MulAut M6, ¬ IsInnerAut τ ∧ ∀ x : M6,
    ((x : ModGL .E7 (ZMod 2)) ∈ Jn 0 ∨ (x : ModGL .E7 (ZMod 2)) ∈ Jn 1 ∨
      (x : ModGL .E7 (ZMod 2)) ∈ Jn 2 ∨ (x : ModGL .E7 (ZMod 2)) ∈ Jn 3 ∨
      (x : ModGL .E7 (ZMod 2)) ∈ J lam) → τ x = x

@[expose] def E7NatA5 : Prop :=
  ∀ a ∈ L7, (∀ x ∈ Jn 5, a * x = x * a) → (∀ x ∈ Jn 6, a * x = x * a) →
    (∀ x ∈ Jn 1, a * x = x * a) → (J mu).map (MulAut.conj a).toMonoidHom = Jn 0 →
    ∀ H : Subgroup (ModGL .E7 (ZMod 2)), Jn 0 ≤ H → J mu ≤ H → Jn 3 ≤ H → a ∈ H → J theta ≤ H

@[expose] def E7NatWeyl : Prop :=
  (∃ w ∈ L7, (J theta).map (MulAut.conj w).toMonoidHom = Jn 0) ∧
    ∃ k ∈ L7, (Jn 0).map (MulAut.conj k).toMonoidHom = Jn 6

end CFSG.StandardType.FrameRoute.FS81.E7Frame
