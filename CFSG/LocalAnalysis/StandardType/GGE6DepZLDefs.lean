module

public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggE6WeylCobdry {L' : Type} [Group L'] (A : Subgroup (MulAut L')) (w : Fin 6 → L') :
    Subgroup L' :=
  Subgroup.closure {c | ∃ i : Fin 6, ∃ a ∈ A, c = w i * (a (w i))⁻¹}

@[expose] def GGE6DepZLProp (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup 3 5 R I L' ψ A → Nat.card A = 3 ^ 5 →
      ∃ (Φ : A →* Multiplicative (Fin 6 → ZMod 3)) (T : Subgroup L') (w : Fin 6 → L'),
        GGE6ThreeWeylModelWith ψ.ker A Φ T w ∧
          ∀ z ∈ ψ.ker, orderOf z = 3 → z ∈ ggE6WeylCobdry A w

@[expose] def GGE6DepZLKnown : Prop :=
  ∀ lab : LargeEvenLabel, GGE6DepLabel lab → LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGE6DepZLProp R I

end CFSG.StandardType

end
