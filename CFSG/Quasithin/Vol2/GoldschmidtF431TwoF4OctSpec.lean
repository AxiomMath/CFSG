module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctDefs
public import CFSG.GH74.GLS.SP.GlueDefs

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open scoped Pointwise
open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag


variable (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)

@[expose] def OctComm : Prop :=
  ∀ x ∈ octH K a, ∀ y ∈ octH K a, x * y = y * x

@[expose] def OctNilp : Prop :=
  Group.IsNilpotent (Ug K a)

@[expose] def OctConj₁ : Prop :=
  ∀ h ∈ octH K a, octR1 K a * h * (octR1 K a)⁻¹ ∈ octH K a

@[expose] def OctConj₂ : Prop :=
  ∀ h ∈ octH K a, octR2 K a * h * (octR2 K a)⁻¹ ∈ octH K a

@[expose] def OctSq₁ : Prop :=
  octR1 K a * octR1 K a ∈ octH K a

@[expose] def OctSq₂ : Prop :=
  octR2 K a * octR2 K a ∈ octH K a

@[expose] def OctPow : Prop :=
  (octR1 K a * octR2 K a) ^ 8 ∈ octH K a

@[expose] def OctUH : Prop :=
  Ug K a ⊓ octH K a = ⊥

@[expose] def OctNeBot : Prop :=
  ∀ i : ℤ, IsRoot 8 i → octRoot K a i ≠ ⊥

@[expose] def OctInv : Prop :=
  ∀ i : ℤ, IsRoot 8 i → ∀ h ∈ octH K a, ∀ x ∈ octRoot K a i, h * x * h⁻¹ ∈ octRoot K a i

@[expose] def OctCarrier : Prop :=
  ((Ug K a : Subgroup (Gm K a)) : Set (Gm K a)) = chainProd (octRoot K a) (intList 1 8)

@[expose] def OctUnique : Prop :=
  ∀ f g : ℤ → Gm K a, (∀ k ∈ intList 1 8, f k ∈ octRoot K a k) →
    (∀ k ∈ intList 1 8, g k ∈ octRoot K a k) →
    ((intList 1 8).map f).prod = ((intList 1 8).map g).prod → ∀ k ∈ intList 1 8, f k = g k

@[expose] def OctRev : Prop :=
  ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ 8 →
    chainProd (octRoot K a) (intList i j) = chainProd (octRoot K a) (intList i j).reverse

@[expose] def OctSub : Prop :=
  ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ 8 →
    ∃ V : Subgroup (Gm K a), (V : Set (Gm K a)) = chainProd (octRoot K a) (intList i j) ∧
      V ≤ Ug K a ∧ (1 < i → ∀ x ∈ octRoot K a (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
      (j < 8 → ∀ x ∈ octRoot K a (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V)

@[expose] def OctAct₁ : Prop :=
  CFSG.GH74.BNPair.conjBy (octR1 K a)⁻¹ (octRoot K a 1) = octRoot K a (-1) ∧
    CFSG.GH74.BNPair.conjBy (octR1 K a)⁻¹ (octRoot K a (-1)) = octRoot K a 1 ∧
    ∀ i : ℤ, 2 ≤ i → i ≤ 8 →
      CFSG.GH74.BNPair.conjBy (octR1 K a)⁻¹ (octRoot K a i) = octRoot K a ((8 : ℕ) + 2 - i) ∧
        CFSG.GH74.BNPair.conjBy (octR1 K a)⁻¹ (octRoot K a (-i)) = octRoot K a (-((8 : ℕ) + 2 - i))

@[expose] def OctAct₂ : Prop :=
  CFSG.GH74.BNPair.conjBy (octR2 K a)⁻¹ (octRoot K a 8) = octRoot K a (-8) ∧
    CFSG.GH74.BNPair.conjBy (octR2 K a)⁻¹ (octRoot K a (-8)) = octRoot K a 8 ∧
    ∀ i : ℤ, 1 ≤ i → i ≤ (8 : ℕ) - 1 →
      CFSG.GH74.BNPair.conjBy (octR2 K a)⁻¹ (octRoot K a i) = octRoot K a ((8 : ℕ) - i) ∧
        CFSG.GH74.BNPair.conjBy (octR2 K a)⁻¹ (octRoot K a (-i)) = octRoot K a (-((8 : ℕ) - i))

@[expose] def OctMeet : Prop :=
  ∀ x ∈ octH K a ⊔ Ug K a, x ∈ negGen 8 (octRoot K a) → x = 1

@[expose] def OctRank₁ : Prop :=
  ∀ y ∈ octRoot K a (-1), y ≠ 1 →
    y ∈ (octRoot K a 1 : Set (Gm K a)) * (octH K a : Set (Gm K a)) * {octR1 K a} *
      (octRoot K a 1 : Set (Gm K a))

@[expose] def OctRank₂ : Prop :=
  ∀ y ∈ octRoot K a (-(8 : ℕ)), y ≠ 1 →
    y ∈ (octRoot K a (8 : ℕ) : Set (Gm K a)) * (octH K a : Set (Gm K a)) * {octR2 K a} *
      (octRoot K a (8 : ℕ) : Set (Gm K a))

variable {K a}

theorem octRGD2_of_fields (h₂ : OctComm K a) (h₃ : OctNilp K a) (h₄ : OctConj₁ K a)
    (h₅ : OctConj₂ K a) (h₆ : OctSq₁ K a) (h₇ : OctSq₂ K a) (h₈ : OctPow K a)
    (h₉ : OctUH K a) (h₁₀ : OctNeBot K a) (h₁₁ : OctInv K a) (h₁₂ : OctCarrier K a)
    (h₁₃ : OctUnique K a) (h₁₄ : OctRev K a) (h₁₅ : OctSub K a) (h₁₆ : OctAct₁ K a)
    (h₁₇ : OctAct₂ K a) (h₁₈ : OctMeet K a) (h₁₉ : OctRank₁ K a) (h₂₀ : OctRank₂ K a) :
    RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a) where
  three_le := by norm_num
  comm_H := h₂
  nilpotent := h₃
  conj_H₁ := h₄
  conj_H₂ := h₅
  sq₁ := h₆
  sq₂ := h₇
  pow := h₈
  U_inf_H := h₉
  ne_bot := h₁₀
  invariant := h₁₁
  carrier_eq := h₁₂
  unique := h₁₃
  reverse_eq := h₁₄
  subgroup := h₁₅
  act₁ := h₁₆
  act₂ := h₁₇
  meet_one := h₁₈
  rank₁ := h₁₉
  rank₂ := h₂₀

end CFSG.Quasithin.H13.F431.TwoF4
