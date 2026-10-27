module

public import CFSG.Quasithin.Recognition.SzVBEvenCtx
public import CFSG.Quasithin.Recognition.SzVBOddL24Facts

public section

namespace CFSG.Quasithin.Kleidman.VBOdd

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G]

structure Ctx (G₀ G₁ G₂ T V : Subgroup G) (z : G) : Prop extends SzVB.GeoCtx G₀ G₁ G₂ T V z where
  two_fixed : ∀ e ∈ G₂, e * e = 1 → e ∈ Subgroup.normalizer (V : Set G) →
    ∀ k ∈ G₂, conjSub k V ≠ V → e ∈ Subgroup.normalizer (conjSub k V : Set G) →
    e ∈ pCoreOf 2 G₂
  comm_big : ∀ w ∈ G₂, w * w = 1 → w ∉ pCoreOf 2 G₂ → ∀ c : G,
    ∃ a ∈ conjClosure V G₂, w * a * w⁻¹ * a⁻¹ ≠ 1 ∧ w * a * w⁻¹ * a⁻¹ ≠ c
  quad_pair : ∀ e ∈ G₂, ∀ e' ∈ G₂, e * e = 1 → e' * e' = 1 → e * e' = e' * e →
    (∀ a ∈ conjClosure V G₂, e' * (e * a * e⁻¹ * a⁻¹) * e'⁻¹ = e * a * e⁻¹ * a⁻¹) →
    e ∈ pCoreOf 2 G₂ ∨ e' ∈ pCoreOf 2 G₂ ∨ e * e' ∈ pCoreOf 2 G₂
  simple : ∀ C : Subgroup G, C ≤ G₂ → G₂ ≤ Subgroup.normalizer (C : Set G) →
    ¬ C ≤ pCoreOf 2 G₂ → C ⊔ pCoreOf 2 G₂ = G₂
  twin : ∀ t ∈ G₂, t ∈ Subgroup.normalizer (V : Set G) →
    ∀ l ∈ G₁, ∃ l' ∈ G₁, l'⁻¹ * (t * l) ∈ G₂

structure Prim (P T V : Subgroup G) (z : G) : Prop where
  klein : SzVB.KleinData P V z
  l24 : SzVB.L24Facts P T V
  abel : IsElemAbelian 2 (conjClosure V P)
  ker_le : ∀ x : ↥P, x ∈ SzVB.kerAct P V → (x : G) ∈ pCoreOf 2 P
  inv_one_fixed : ∀ x : ↥P, x * x = 1 → x ∉ SzVB.kerAct P V →
    ∃ ω : SzVB.ConjSet P V, x • ω = ω ∧ ∀ U : SzVB.ConjSet P V, x • U = U → U = ω

end CFSG.Quasithin.Kleidman.VBOdd
