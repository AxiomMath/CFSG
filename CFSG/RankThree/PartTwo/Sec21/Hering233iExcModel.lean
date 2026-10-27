module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iOrbit
public import CFSG.RankThree.PartTwo.Sec21.Item233Pieces

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open Hering233i

variable {G : Type} [Group G]

@[expose] def ExcFree (I B' : Subgroup G) : Prop :=
  ∀ X : Subgroup (I ⊓ Subgroup.centralizer (B' : Set G) : Subgroup G), CFSG.IsComponent X →
    ¬ ((∀ X' : Subgroup (I ⊓ Subgroup.centralizer (B' : Set G) : Subgroup G),
      CFSG.IsComponent X' → X' = X) ∧ Nat.card X = 60)

structure L44ExcProps (I A B Xg : Subgroup G) (b a b' c₃ c₄ w : G) (X' : Subgroup G) : Prop where
  hBb : B = Subgroup.zpowers b
  hb1 : b ≠ 1
  hbA : b ∈ A
  haA : a ∈ A
  haX : a ∈ Xg
  ha1 : a ≠ 1
  eX : Nonempty (Xg ≃* projSL 2 (GaloisField 2 2))
  hb'A : b' ∈ A
  hc₃A : c₃ ∈ A
  hc₄A : c₄ ∈ A
  hb'1 : b' ≠ 1
  hc₃1 : c₃ ≠ 1
  hc₄1 : c₄ ≠ 1
  hcover : ∀ h ∈ A, h ∉ B → ∃ i : Fin 4, ![a, b', c₃, c₄] i ∈ B ⊔ Subgroup.zpowers h
  hXw : ∀ x ∈ Xg, x * w = w * x
  hw2 : orderOf w = 2
  hwX' : w ∈ X'
  hwb : w * b * w⁻¹ = b⁻¹
  hX'simple : IsSimpleGroup X'
  hbX' : b ∈ X'
  hX'Y₁ : X' ≤ layerCent I (Subgroup.zpowers b')
  hX'N : (X'.subgroupOf (layerCent I (Subgroup.zpowers b'))).Normal
  hfree₁ : ExcFree I (Subgroup.zpowers b')
  hcount' : (invSet X' b).ncard ≤ 4
  hX'Y₃ : X' ≤ layerCent I (Subgroup.zpowers c₃)
  hfree₃ : ExcFree I (Subgroup.zpowers c₃)
  hcount₃ : (invSet (layerCent I (Subgroup.zpowers c₃)) b).ncard ≤ 4
  hX'Y₄ : X' ≤ layerCent I (Subgroup.zpowers c₄)
  hfree₄ : ExcFree I (Subgroup.zpowers c₄)
  hcount₄ : (invSet (layerCent I (Subgroup.zpowers c₄)) b).ncard ≤ 4

@[expose] def L44ExceptionModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    Nonempty (I ≃* projSL 4 (GaloisField 2 2)) → Nat.card A = 3 ^ 3 →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      ∀ X : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
        CFSG.IsComponent X →
        (∀ X' : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
          CFSG.IsComponent X' → X' = X) → Nat.card X = 60 →
        ∃ (b a b' c₃ c₄ w : G) (X' : Subgroup G),
          L44ExcProps I A B (X.map (I ⊓ Subgroup.centralizer (B : Set G)).subtype) b a b' c₃ c₄ w X'

theorem mem_centralizer_zpowers_of_mul_eq {h d : G} (hd : d * h = h * d) :
    d ∈ Subgroup.centralizer ((Subgroup.zpowers h : Subgroup G) : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hd

end CFSG.RankThree.PartTwo.Sec21
