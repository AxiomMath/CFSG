module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.EmptyFaithful.S151bW3Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

namespace SixData151b

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

@[expose] def Stab₁ (g : MulAut W) : Prop := ∀ w : W, w ∈ S.W₁ ↔ g w ∈ S.W₁

@[expose] def Stab₂ (g : MulAut W) : Prop := ∀ w : W, w ∈ S.W₂ ↔ g w ∈ S.W₂

@[expose] def Swap₁₂ (g : MulAut W) : Prop :=
  (∀ w ∈ S.W₁, g w ∈ S.W₂) ∧ ∀ w ∈ S.W₂, g w ∈ S.W₁

end SixData151b

end CFSG.Quasithin
