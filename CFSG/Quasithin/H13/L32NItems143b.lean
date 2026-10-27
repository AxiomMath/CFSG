module

public import CFSG.Quasithin.H13.L32NItems143
public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.G2Relaxed

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

abbrev l32nW (T V V₂ : Subgroup G) : Subgroup G :=
  fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G)

abbrev l32nE (T V V₂ : Subgroup G) (g : G) : Subgroup G :=
  l32nW T V V₂ ⊓ CFSG.conjugate (l32nW T V V₂) g

@[expose] def Lemma14312One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V),
      Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤
          2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1) →
        Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) =
            2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1) ∧
          2 * Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) = Module.finrank (ZMod 2) D.V ∧
          (centerOf (fsuU T V) = fsuV1 T V ∧ CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) ∧
            l32nCHat T V = pCoreOf 2 (l32nH T V)) ∧
          ∃ q : D.V → ZMod 2, (∀ u ∈ fsuU T V, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧
            (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
            (∀ γ ∈ D.img (l32nH T V), ∀ v, q (γ v) = q v) ∧
            ∀ e ∈ D.hat (l32nE T V V₂ g), q e = 0

structure Case14323i (T L V : Subgroup G) (g : G) (D : HatModelU (fsuU T V)) : Prop where
  iso : Nonempty (↥(D.img (l32nH T V)) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  l1_normal : D.img (l32nH T V) ≤
    Subgroup.normalizer (D.img (lOne L (fsuV1 T V)) : Set (D.V ≃ₗ[ZMod 2] D.V))
  zU : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥ →
    D.img (CFSG.conjugate (centerOf (fsuU T V)) g) = D.img (l32nH T V) ⊓
        fixingSubgroup (D.V ≃ₗ[ZMod 2] D.V) (D.hat V : Set D.V) ∧
      Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) = 2 ∧
      Nonempty (↥(D.img (conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V))) ≃*
        Equiv.Perm (Fin 3)) ∧
      D.img (conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V)) ⊔
          D.img (lOne L (fsuV1 T V)) ⊔ D.img T = D.img (l32nH T V) ∧
      ¬ conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V) ≤
        Subgroup.normalizer (L : Set G)

structure Case14323ii (T V : Subgroup G) (g : G) (D : HatModelU (fsuU T V)) : Prop where
  iso : Nonempty (↥(D.img (l32nH T V)) ≃* Equiv.Perm (Fin 5))
  natural : ∃ (φ : ↥(D.img (l32nH T V)) ≃* RuType.SigmaL2F4) (ψ : D.V ≃+ (Fin 2 → RuType.F4)),
    ∀ (h : ↥(D.img (l32nH T V))) (v : D.V),
      ψ ((h : D.V ≃ₗ[ZMod 2] D.V) v) = RuType.sigmaAct (φ h) (ψ v)
  card_zU : Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) = 2
  zU_le : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≤
    (genFittingLayer ↥(D.img (l32nH T V))).map (D.img (l32nH T V)).subtype

structure Case14323iii (T V : Subgroup G) (g : G) (D : HatModelU (fsuU T V)) : Prop where
  iso : Nonempty (↥(D.img (l32nH T V)) ≃* ↥(alternatingGroup (Fin 6))) ∨
    Nonempty (↥(D.img (l32nH T V)) ≃* Equiv.Perm (Fin 6))
  card_zU : Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) = 2 ∨
    Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) = 4

structure Case14323iv (T L V : Subgroup G) (D : HatModelU (fsuU T V)) : Prop where
  e9 : ∃ N : Subgroup ↥(D.img (l32nH T V)), N.Normal ∧ IsElemAbelian 3 N ∧ Nat.card N = 9 ∧
    N.index = 2
  l1_normal : D.img (l32nH T V) ≤
    Subgroup.normalizer (D.img (lOne L (fsuV1 T V)) : Set (D.V ≃ₗ[ZMod 2] D.V))
  q8 : IsQ8Sq ↥(fsuU T V)

@[expose] def Lemma14323Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V), Module.finrank (ZMod 2) D.V = 4 →
      (D.hat V = D.hat (l32nE T V V₂ g) ∧ Nat.card ↥(D.hat V) = 4) ∧
      (Case14323i T L V g D ∨ Case14323ii T V g D ∨ Case14323iii T V g D ∨
        Case14323iv T L V D) ∧
      ((D.img (CFSG.conjugate (centerOf (fsuU T V)) g)).relIndex
          (D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ∧
        ∀ x ∈ D.img (CFSG.conjugate (centerOf (fsuU T V)) g), ∀ v ∈ D.hat V, x v = v) ∧
      (l32nH T V ⊓ Subgroup.normalizer (L : Set G)) ⊔ l32nCHat T V < l32nH T V

@[expose] def Lemma14324One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V),
      G112Concl6 (D.img (l32nH T V)) ∨
        (Module.finrank (ZMod 2) D.V = 4 ∧
          (Case14323i T L V g D ∨ Case14323ii T V g D ∨ Case14323iii T V g D))

@[expose] def Lemma14325One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    centerOf (L ⊔ T) ⊓ fsuU T V = ⊥

@[expose] def Lemma14331One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) → centerOf (i128 T L V (fsuV1 T V)) = ⊥

end CFSG.Quasithin.H13
