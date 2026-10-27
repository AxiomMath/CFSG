module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.Sporadic.Th.Max3.Core

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

inductive QTwoDivKind where
  | suInner | suFull | psuInner | psuFull
  deriving DecidableEq

@[expose] def QTwoDivKind.facts {G : Type} [Group G] (k : QTwoDivKind) (m : ℕ) (Bs L : Subgroup G) : Prop :=
  match k with
  | .suInner => 3 ∣ Nat.card (Subgroup.center ↥L) ∧ Nat.card Bs = 3 ^ (m - 1)
  | .suFull => 3 ∣ Nat.card (Subgroup.center ↥L) ∧ Nat.card Bs = 3 ^ m
  | .psuInner => ¬ 3 ∣ Nat.card (Subgroup.center ↥L) ∧ Nat.card Bs = 3 ^ (m - 1)
  | .psuFull => ¬ 3 ∣ Nat.card (Subgroup.center ↥L) ∧ Nat.card Bs = 3 ^ m

structure QTwoDivCoords {G : Type} [Group G] (m : ℕ) (V VT : Type) [Group V] [Group VT]
    (Bs L : Subgroup G) (x : G) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) where
  permV : Equiv.Perm (Fin m) →* MulAut V
  permVT : Equiv.Perm (Fin m) →* MulAut VT
  theta : V ≃* ↥(ggGamma L hN).range
  norm_perm : ∀ (n : ↥L) (hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
    ∃ π : Equiv.Perm (Fin m), ggConjAut (ggGamma L hN).range hn = MulAut.congr theta (permV π)
  perm_ind : ∀ σ : Equiv.Perm (Fin m), ∃ (n : ↥L) (hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
    ggConjAut (ggGamma L hN).range hn = MulAut.congr theta (permV σ)
  thetaT : VT ≃* ↥(Bs ⊓ L)
  normT : ∀ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) →
    ∃ π : Equiv.Perm (Fin m), ∀ v : VT,
      (n : G) * ((thetaT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
        ((thetaT (permVT π v) : ↥(Bs ⊓ L)) : G)
  indT : ∀ σ : Equiv.Perm (Fin m), ∃ n : ↥L,
    (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ v : VT,
      (n : G) * ((thetaT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
        ((thetaT (permVT σ v) : ↥(Bs ⊓ L)) : G)

@[expose] def qTwoLMSkel_divFrameOfCoords {G : Type} [Group G] {m : ℕ} {V VT : Type} [Group V] [Group VT]
    {Bs L : Subgroup G} {x : G} {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (C : QTwoDivCoords m V VT Bs L x hN) (hx : x ∈ Bs) (hord : orderOf x = 3)
    (helem : IsElemAbelian 3 Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hN b = 1 ↔ (b : G) ∈ Subgroup.zpowers x)
    (hlink : ∀ n : ↥L, MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) →
      ∃ n' : ↥L, (n' : G) ∈ Subgroup.normalizer (Bs : Set G) ∧
        MulAut.conj n' = MulAut.conj n) : QTwoFrame m V VT Bs L x where
  hN := hN
  hx := hx
  hord := hord
  elemAb := helem
  permV := C.permV
  permVT := C.permVT
  ker := hker
  link := hlink
  theta := C.theta
  norm_perm := C.norm_perm
  perm_ind := C.perm_ind
  thetaT := C.thetaT
  normT := C.normT
  indT := C.indT

end CFSG.StandardType.QTwo

end
