module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushNatMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Mod

variable {G : Type} [Group G] [Finite G]

@[expose] def conjJoinOf (H₀ Z : Subgroup G) : Subgroup G :=
  ⨆ h ∈ H₀, Z.map (MulAut.conj h).toMonoidHom

@[expose] def BaumannC (X Z : Subgroup G) : Prop :=
  ⁅pCoreOf 2 X, pResidualOf 2 X⁆ ≤ Z

@[expose] def Cor42Concl (X Z H₀ : Subgroup G) : Prop :=
  conjJoinOf H₀ Z ≤ pCoreOf 2 X ∧ X ≤ Subgroup.normalizer (conjJoinOf H₀ Z : Set G)

@[expose] def BaumannS3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ X P Z : Subgroup G, PushHyp X P Z → Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3)) →
    NoCharNormal P X → BaumannC X Z

@[expose] def BaumannA5 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ X P Z : Subgroup G, PushHyp X P Z →
    Nonempty (OTwoQuot X ≃* ↥(alternatingGroup (Fin 5))) → IsNatSecA5 X (zZero X Z) Z →
    NoCharNormal P X → BaumannC X Z

end CFSG.Quasithin.F53Push
