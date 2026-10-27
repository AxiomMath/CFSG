module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem ncard_isRoot_E7 : {α : Fin Tag.E7.rank → ℤ | IsRoot .E7 α}.ncard = 126 := by
  have h : {α : Fin Tag.E7.rank → ℤ | IsRoot .E7 α} = ↑(rootFinset .E7) := by
    ext α
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    exact mem_rootFinset.symm
  rw [h, Set.ncard_coe_finset, card_rootFinset]
  rfl

structure RCKE7Frame {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) where
  ε : ↥(adjointGroup Tag.E7 GGL) ≃* ↥(rootSpan τ GGL Ψ)
  j : (Fin Tag.E7.rank → ℤ) →+ (Fin τ.rank → ℤ)
  ι : (Fin τ.rank → ℤ) →+ (Fin Tag.E7.rank → ℤ)
  ι_j : ∀ δ, ι (j δ) = δ
  j_ι : ∀ γ ∈ Ψ, j (ι γ) = γ
  bijOn : Set.BijOn j {δ | IsRoot Tag.E7 δ} Ψ
  isRoot : ∀ γ ∈ Ψ, IsRoot τ γ
  iform_j : ∀ δ δ', CFSG.LieType.Steinberg.Adjoint.iform (j δ) (j δ') =
    CFSG.LieType.Steinberg.Adjoint.iform δ δ'
  pinned : ∀ δ, IsRoot Tag.E7 δ → ∀ c : GGL,
    (ε ⟨pinnedX Tag.E7 GGL δ c, pinnedX_mem_adjointGroup δ c⟩ : ModGL τ GGL) =
      pinnedX τ GGL (j δ) c

@[expose] noncomputable def rckE7Kappa {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ)
    {R : Subgroup (ModGL τ GGL)} (hR : R ≤ rootSpan τ GGL Ψ) : ↥R →* ModGL Tag.E7 GGL :=
  (adjointGroup Tag.E7 GGL).subtype.comp (F.ε.symm.toMonoidHom.comp (Subgroup.inclusion hR))

theorem rckE7Kappa_apply {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ)
    {R : Subgroup (ModGL τ GGL)} (hR : R ≤ rootSpan τ GGL Ψ) (x : R) :
    rckE7Kappa F hR x = (F.ε.symm (Subgroup.inclusion hR x) : ModGL Tag.E7 GGL) :=
  rfl

theorem rckE7Kappa_injective {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ)
    {R : Subgroup (ModGL τ GGL)} (hR : R ≤ rootSpan τ GGL Ψ) :
    Function.Injective (rckE7Kappa F hR) :=
  (Subgroup.subtype_injective _).comp (F.ε.symm.injective.comp (Subgroup.inclusion_injective hR))

end CFSG.StandardType.RCKRP

end
