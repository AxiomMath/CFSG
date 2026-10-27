module

public import CFSG.Quasithin.Background.F918P5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Shapes

variable {W : Type} [CommGroup W]

@[expose] def TypesFourShapeNat (L : Subgroup (MulAut W)) : Prop :=
  (∃ n', 2 ≤ n' ∧ BinaryNaturalSL L ⊤ (⊤ ⊓ fixV L) 2 n') ∨
    (∃ f, BinaryNaturalSz L ⊤ (⊤ ⊓ fixV L) f) ∨ (∃ a, BinaryNaturalSU3 L ⊤ (⊤ ⊓ fixV L) a)

@[expose] def TypesFourShapeTwist (L Tt : Subgroup (MulAut W)) : Prop :=
  ∃ V : Subgroup W, ∃ t ∈ Tt,
    ((∃ n', BinaryNaturalSL L V (V ⊓ fixV L) 3 n') ∨ (∃ n', BinaryNaturalSp4 L V (V ⊓ fixV L) n')) ∧
      IsSumMod (fixV L) V (V.map t.toMonoidHom) ⊤

end Shapes

section Concl

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

@[expose] def TypesFourEltConcl (hF : HypF918 T V L V₁ Vp H K) (M I : Subgroup G)
    (hIU : I ≤ conjClosure Vp H) : Prop :=
  haveI := factElem hF hIU
  ∃ t₀ : ↥H, (t₀ : G) ∈ M ∧ ∃ m : ℕ, Odd m ∧
    (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) t₀) ^ m = 1 ∧
    ∀ w : ↥(tildeOf V₁ (conjClosure I H)),
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) t₀ w * w⁻¹ ∈
        fixV (autIH V₁ I H (conjClosure K T)) → w ∈ fixV (autIH V₁ I H (conjClosure K T))

@[expose] def TypesFourTwistHyp (hF : HypF918 T V L V₁ Vp H K) (I : Subgroup G)
    (hIU : I ≤ conjClosure Vp H) : Prop :=
  haveI := factElem hF hIU
  TypesFourShapeTwist (autIH V₁ I H K) (autIH V₁ I H T)

end Concl

section Inputs

attribute [local instance] commGroupOfFact

end Inputs

end CFSG.Quasithin
