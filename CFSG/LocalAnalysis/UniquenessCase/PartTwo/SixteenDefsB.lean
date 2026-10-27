module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Standing

variable {G : Type} [Group G] [Finite G]

structure Sect16 (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  setting : Setting16 D V₀ V L
  ne_bot : barSub V₀ V hV L ≠ ⊥
  conc : Conc4_136 D V₀ V hV L

end Standing

section Points

variable {W : Type*} [CommGroup W]

@[expose] def ptCent (H : Subgroup (MulAut W)) (w : W) : Subgroup (MulAut W) :=
  H ⊓ MulAction.stabilizer (MulAut W) w

end Points

section Quadratic

variable {W : Type*} [CommGroup W]

@[expose] def polarQ (Q : W → ZMod 2) (x y : W) : ZMod 2 :=
  Q (x * y) - Q x - Q y

@[expose] def IsQuadF2 (Q : W → ZMod 2) : Prop :=
  (∀ x y z, polarQ Q (x * y) z = polarQ Q x z + polarQ Q y z) ∧
    ∀ x y z, polarQ Q x (y * z) = polarQ Q x y + polarQ Q x z

@[expose] def IsNondegQuadF2 (Q : W → ZMod 2) : Prop :=
  IsQuadF2 Q ∧ ∀ x : W, x ≠ 1 → ∃ y : W, polarQ Q x y ≠ 0

@[expose] def IsPlusQuadF2 (Q : W → ZMod 2) : Prop :=
  IsNondegQuadF2 Q ∧ ∃ U : Subgroup W, (∀ u ∈ U, Q u = 0) ∧ 2 * rk ↥U = rk ↥(⊤ : Subgroup W)

@[expose] def IsMinusQuadF2 (Q : W → ZMod 2) : Prop :=
  IsNondegQuadF2 Q ∧ ¬ ∃ U : Subgroup W, (∀ u ∈ U, Q u = 0) ∧ 2 * rk ↥U = rk ↥(⊤ : Subgroup W)

@[expose] def QuadInvariant (Q : W → ZMod 2) (H : Subgroup (MulAut W)) : Prop :=
  ∀ h ∈ H, ∀ x : W, Q (h x) = Q x

end Quadratic

section Shapes

@[expose] def IsE64L3 (X : Type) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), IsElemAbelianOfRank 2 6 ↥N ∧ UC22.IsL3 (X ⧸ N) 1

@[expose] def IsSL2Prime (X : Type) [Group X] (p : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ∧ Nonempty (X ≃* ↥(StatedSL 2 K))

@[expose] def IsSp6Transvection {X : Type} [Group X] (x : X) : Prop :=
  ∃ φ : X ≃* ↥(StatedSp 3 (ZMod 2)),
    ((((φ x : ↥(StatedSp 3 (ZMod 2))) : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) - 1).rank = 1

end Shapes

section SetUps

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Case1633 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) (m : ℕ) : Prop :=
  (Case167_5 D V₀ V hV L ∧ m = 2) ∨ (Case167_6 D V₀ V hV L ∧ m = 3)

@[expose] def Sp6InL (D : Data G) (L : Subgroup G) (v₀ : G) (T₀ K : Subgroup G) : Prop :=
  T₀ ≤ K ∧ L ⊓ centralizer ({v₀} : Set G) ≤ K ∧ ¬ K ≤ D.M ∧ CFSG.QuasithinUnique.CharTwo K

end SetUps

section MoreShapes

@[expose] def IsL3Five (X : Type) [Group X] : Prop :=
  CFSG.Blueprint.LieModel X .PSL 3 5 1

@[expose] def IsExtraspecialPlus2 (X : Type) [Group X] (n : ℕ) : Prop :=
  CFSG.IsExtraspecial 2 X ∧ Nat.card X = 2 ^ (2 * n + 1) ∧
    ∃ E : Subgroup X, IsElemAbelianOfRank 2 (n + 1) ↥E

@[expose] def IsE16A5 (X : Type) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), IsElemAbelianOfRank 2 4 ↥N ∧ UC22.IsAlt (X ⧸ N) 5

@[expose] def IsQ8FourDih (X : Type) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), IsExtraspecialPlus2 ↥N 4 ∧
    ∃ m : ℕ, Odd m ∧ Nonempty ((X ⧸ N) ≃* DihedralGroup m)

@[expose] def IsQ8Q8S3 (X : Type) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), IsExtraspecialPlus2 ↥N 2 ∧ IsSym (X ⧸ N) 3

@[expose] def IsSL25By5p12 (X : Type) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), IsPOnePlusTwo 5 ↥N ∧ IsSL2Prime (X ⧸ N) 5

@[expose] def EqTimesOdd {A : Type*} [Group A] (X Y : Subgroup A) : Prop :=
  ∃ N : Subgroup A, N ≤ Y ∧ (N.subgroupOf Y).Normal ∧ Odd (Nat.card N) ∧ Y = X ⊔ N

end MoreShapes

section Omega6

variable {G : Type} [Group G] [Finite G]

@[expose] def xInf (L : Subgroup G) (z : G) : Subgroup G :=
  perfectCore (centralizer ({z} : Set G) ⊓ L)

@[expose] def hConjClosure (z : G) (U : Subgroup G) : Subgroup G :=
  ⨆ h : ↥(centralizer ({z} : Set G)), conjSubgroup U (h : G)

@[expose] def yGen (L : Subgroup G) (z : G) : Subgroup G :=
  hConjClosure z (xInf L z)

@[expose] def starImg (K X : Subgroup G) : Subgroup (Bar2 K) :=
  (X.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))

structure Setup1645 (D : Data G) (V : Subgroup G) (hV : IsElemAbelian 2 V) (x : IntMod V hV) :
    Prop where
  ne_one : x.val ≠ 1
  not_le : ¬ centralizer ({x.val} : Set G) ≤ D.M
  sylow : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G))
    (D.M ⊓ centralizer ({x.val} : Set G))

@[expose] noncomputable def Concl1646 (L : Subgroup G) (z : G) : Prop :=
  CFSG.Open.pRank 3 (centralizer ({z} : Set G)) = 1 ∧
    (∀ q : ℕ, q.Prime → 3 < q → CFSG.Open.pRank q (centralizer ({z} : Set G)) ≤ 2) ∧
    IsSL2Prime ↥(starImg (centralizer ({z} : Set G)) (xInf L z)) 5 ∧
    (IsL3Five ↥(starImg (centralizer ({z} : Set G)) (yGen L z)) ∨
      EqTimesOdd (starImg (centralizer ({z} : Set G)) (xInf L z))
        (starImg (centralizer ({z} : Set G)) (yGen L z)))

@[expose] def Concl1647 (V : Subgroup G) (z : G) : Prop :=
  Nat.card ↥(starImg (centralizer ({z} : Set G)) V) = 2 ∧
    ∀ v ∈ starImg (centralizer ({z} : Set G)) V, v ≠ 1 →
      ∀ a b : Bar2 (centralizer ({z} : Set G)),
        orderOf (a * v * a⁻¹ * (b * v * b⁻¹)) ∈ ({1, 2, 3, 5, 17} : Set ℕ)

@[expose] def uOne (V : Subgroup G) (z : G) : Subgroup G :=
  V ⊓ pCoreOf 2 (centralizer ({z} : Set G))

@[expose] def eOne (V : Subgroup G) (z : G) : Subgroup G :=
  hConjClosure z (uOne V z)

@[expose] def eTwo (D : Data G) (V₀ : Subgroup G) (z : G) : Subgroup G :=
  hConjClosure z (V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G))

@[expose] def uTwo (D : Data G) (V₀ : Subgroup G) (z : G) : Subgroup G :=
  V₀ ⊓ eTwo D V₀ z

@[expose] def Concl1647a (D : Data G) (V₀ V : Subgroup G) (z : G) : Prop :=
  (V₀ = ⊥ →
      ((uOne V z).subgroupOf (eOne V z)).Normal ∧
        (∀ h ∈ centralizer ({z} : Set G),
          ¬ uOne V z ⊓ conjSubgroup (uOne V z) h ≤ Subgroup.zpowers z → h ∈ D.M) ∧
        (∀ h ∈ centralizer ({z} : Set G),
          conjSubgroup (uOne V z) h = uOne V z ∨
            uOne V z ⊓ conjSubgroup (uOne V z) h ≤ Subgroup.zpowers z) ∧
        (⁅eOne V z, eOne V z⁆ ≤ Subgroup.zpowers z ∧
          ∀ e ∈ eOne V z, e ^ 2 ∈ Subgroup.zpowers z) ∧
        ⁅V, eOne V z⁆ ⊔ Subgroup.zpowers z = uOne V z) ∧
    (V₀ ≠ ⊥ →
      (⁅eTwo D V₀ z, eTwo D V₀ z⁆ = ⊥ ∧ ∀ e ∈ eTwo D V₀ z, e ^ 2 = 1) ∧
        (∀ h ∈ centralizer ({z} : Set G),
          conjSubgroup (uTwo D V₀ z) h = uTwo D V₀ z ∨
            uTwo D V₀ z ⊓ conjSubgroup (uTwo D V₀ z) h = ⊥) ∧
        ⁅V, eTwo D V₀ z⁆ ≤ uTwo D V₀ z)

@[expose] noncomputable def Concl1647c (L : Subgroup G) (z : G) : Prop :=
  IsSL25By5p12 ↥(starImg (centralizer ({z} : Set G)) (yGen L z)) ∧
    2 < CFSG.Open.pRank 5 (centralizer ({z} : Set G))

@[expose] def Hyp1643 (D : Data G) (V₀ V : Subgroup G) (i : ℕ) (A : Subgroup G) (g : G) : Prop :=
  (i = 0 ∨ (V₀ = ⊥ ∧ i = 1)) ∧ A ∈ E3.gammaSet V i D.M ∧ A ≤ conjSubgroup V g

end Omega6

section Final

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Sit1663 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Prop :=
  (Case167_2 D V₀ V hV L ∨ Case167_3 D V₀ V hV L) ∧ Hyp154 D V₀ V L

@[expose] noncomputable def Sit1665 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Prop :=
  Case167_3 D V₀ V hV L ∧ Hyp154 D V₀ V L

@[expose] noncomputable def Concl1667pre (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) (g : G) : Prop :=
  ¬ conjSubgroup V g ⊓ D.M ≤ normalizer (wSub V₀ V hV L : Set G) ∧
    rk ↥(barSub V₀ V hV (conjSubgroup V g ⊓ D.M)) = 2 ∧
    (∃ z : G, orderOf z = 2 ∧
      V ⊓ conjSubgroup D.M g ⊓ (conjSubgroup V g ⊓ D.M) = Subgroup.zpowers z) ∧
    ∃ _ : ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal,
      IsQ8Q8S3
        (↥(V ⊔ conjSubgroup V g) ⧸ (V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g))

@[expose] def gammaOneBar (V A : Subgroup G) : Subgroup G :=
  ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : E3.mQuot A B ≤ 1), V ⊓ centralizer (B : Set G)

end Final

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
