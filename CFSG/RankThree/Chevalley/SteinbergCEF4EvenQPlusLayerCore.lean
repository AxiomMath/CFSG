module

public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusRootPair
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint F4Weyl
  EvenG2 EvenF4QPlus CFSG.RankThree.LocalRank
open scoped Pointwise commutatorElement

namespace EvenF4QPlus

section QPlus

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

@[expose] def qplusConjTransport
    (K₂ : Type) [Field K₂] [Algebra K K₂] (g : ModGL .F4 K₂)
    (c : adjointGroup .F4 K) : adjointGroup .F4 K →* ModGL .F4 K₂ :=
  ((MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂))).comp
    ((adjointGroup .F4 K).subtype.comp (MulAut.conj c).toMonoidHom)

omit [Finite K] in
theorem qplusConjTransport_apply
    (g : ModGL .F4 K₂) (c y : adjointGroup .F4 K) :
    qplusConjTransport K₂ g c y =
      g * baseChangeGL (algebraMap K K₂) ((c * y * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) *
        g⁻¹ :=
  rfl

omit [Finite K] in
theorem qplusConjTransport_injective
    (g : ModGL .F4 K₂) (c : adjointGroup .F4 K) :
    Function.Injective (qplusConjTransport K₂ g c) :=
  ((MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .F4) (algebraMap K K₂))).comp
    (Subtype.val_injective.comp (MulAut.conj c).injective)

omit [Finite K] in
theorem map_top_qplusConjTransport
    (g : ModGL .F4 K₂) (c : adjointGroup .F4 K) :
    (⊤ : Subgroup (adjointGroup .F4 K)).map (qplusConjTransport K₂ g c) =
      conjEntrywiseImage K g := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    exact ⟨_, (c * y * c⁻¹).2, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨c⁻¹ * ⟨y, hy⟩ * c, Subgroup.mem_top _, ?_⟩
    change g * baseChangeGL (algebraMap K K₂)
      ((c * (c⁻¹ * ⟨y, hy⟩ * c) * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) * g⁻¹ =
        g * baseChangeGL (algebraMap K K₂) y * g⁻¹
    rw [show c * (c⁻¹ * ⟨y, hy⟩ * c) * c⁻¹ = (⟨y, hy⟩ : adjointGroup .F4 K) by group]

omit [Finite K] in
theorem map_centralizer_qplusConjTransport
    (g : ModGL .F4 K₂) (c x : adjointGroup .F4 K) :
    (Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))).map (qplusConjTransport K₂ g c) =
      conjEntrywiseImage K g ⊓ Subgroup.centralizer {qplusConjTransport K₂ g c x} := by
  have h := map_inf_centralizer_of_injective (qplusConjTransport_injective g c) ⊤
    ({x} : Set (adjointGroup .F4 K))
  rwa [top_inf_eq, map_top_qplusConjTransport, Set.image_singleton] at h

end QPlus

end EvenF4QPlus

open EvenF4QPlus

end CFSG.RankThree.Chevalley
