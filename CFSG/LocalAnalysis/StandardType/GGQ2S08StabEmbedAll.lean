module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabEmbedInduced
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabEmbedAction
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabEmbedInj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_stab_embed_all
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S) (hx : x ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x)
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (ι : Additive ↥(ggGamma L hBsN).range ≃+ (M.V ⧸ Submodule.span (ZMod 3) {M.xV}))
    (φ : M.Λ → MulAut ↥(ggGamma L hBsN).range)
    (h : M.Λ → M.V ⧸ Submodule.span (ZMod 3) {M.xV})
    (α : M.Λ → Module.Dual (ZMod 3) (M.V ⧸ Submodule.span (ZMod 3) {M.xV}))
    (hcompat : ∀ b : ↥Bs, ι (Additive.ofMul (⟨ggGamma L hBsN b, b, rfl⟩ : ↥(ggGamma L hBsN).range)) =
      Submodule.Quotient.mk (M.model (Additive.ofMul b)))
    (hpair : ∀ i j, α i (h j) = ((M.cartan i j : ℤ) : ZMod 3))
    (hsimple : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i)
    (hAut : ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range =
      Subgroup.closure (Set.range φ)) :
    Nat.card ↥(ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) ≤
      Nat.card ↥(ggHL ι φ h α) := by
  classical
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : Finite (M.V ⧸ Submodule.span (ZMod 3) {M.xV}) :=
    Finite.of_surjective (Submodule.Quotient.mk (p := Submodule.span (ZMod 3) {M.xV}))
      (Submodule.Quotient.mk_surjective _)
  haveI : Finite ((M.V ⧸ Submodule.span (ZMod 3) {M.xV}) ≃ₗ[ZMod 3]
      (M.V ⧸ Submodule.span (ZMod 3) {M.xV})) :=
    Finite.of_injective (fun e => (e : (M.V ⧸ Submodule.span (ZMod 3) {M.xV}) →
      (M.V ⧸ Submodule.span (ZMod 3) {M.xV})))
      (fun e f h => LinearEquiv.ext (fun v => congrFun h v))
  have hT : ∀ ψ : ↥(ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)),
      ∃ T ∈ ggHL ι φ h α, ∀ v : M.V,
        T (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ggLin (p := 3) M.model ψ.1 v) := by
    intro ψ
    obtain ⟨g, hg, hgL, hgψ⟩ := ggQ2s08x2_induced_exists hS hnc hx ψ.1 ψ.2
    exact ggQ2s08x2_action_mem_ggHL hTBW hS hBsN M hInn ι φ h α hcompat hpair hsimple hAut
      hg hgL ψ.1 hgψ
  choose T hTmem hTact using hT
  refine Nat.card_le_card_of_injective
    (fun ψ => (⟨T ψ, hTmem ψ⟩ : ↥(ggHL ι φ h α))) (fun ψ₁ ψ₂ hF => Subtype.ext ?_)
  have hTeq : T ψ₁ = T ψ₂ := congrArg Subtype.val hF
  exact ggQ2s08x2_inj hS hx M ψ₁.1 ψ₂.1 ψ₁.2 ψ₂.2
    (fun v => by rw [← hTact ψ₁ v, ← hTact ψ₂ v, hTeq])

end CFSG.StandardType

end
