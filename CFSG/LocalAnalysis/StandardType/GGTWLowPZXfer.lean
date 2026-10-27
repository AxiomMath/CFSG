module

public import CFSG.LocalAnalysis.StandardType.GGTWLowPZ

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTWPZ_xfer (hPZ : GGPZInput) {G : Type} [Group G] [Finite G] {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {labJ labX : LargeEvenLabel} {X : Subgroup G}
    (hX : X = L ∨ X = K) (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X)) (hrow : ggRowTwoNodeSmall p labJ labX)
    (hAtag : labX.tag = .A ∨ labX.tag = .twA) (hXrank : labX.rank = N - 1)
    (hJrank : labJ.rank = N - 3) (hcard : Nat.card ↥Bs = p ^ (N - 1))
    (hJcard : Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank) (hJrefl : GGReflGenerated p (ggAutomizer J Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod p] GGTWE p N) (pos : GGTWPos) (gensV gensJV : Set (V ≃ₗ[ZMod p] V))
    (hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) = Subgroup.closure gensV)
    (hAJ : (ggAutomizer J Bs).map (ggLin (p := p) ι) = Subgroup.closure gensJV)
    (gens : Set (Module.End (ZMod p) (GGTWE p N)))
    (hg₁ : ∀ g ∈ gensV, ∃ y ∈ gens,
      (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hg₂ : ∀ y ∈ gens, ∃ g ∈ gensV,
      (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hJ₁ : ∀ g ∈ gensJV, ∃ i : {i : Fin (N - 1) // ggTWInJ N pos i.val},
      (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1) ∘ₗ
        θ.toLinearMap)
    (hJ₂ : ∀ i : {i : Fin (N - 1) // ggTWInJ N pos i.val}, ∃ g ∈ gensJV,
      (g : V →ₗ[ZMod p] V) = θ.symm.toLinearMap ∘ₗ ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1) ∘ₗ
        θ.toLinearMap)
    (z : ↥Bs) (hzD : (z : G) ∈ D) (hzx : (z : G) ∉ Subgroup.zpowers x)
    (hzy : (z : G) ∉ Subgroup.zpowers y) :
    ¬ GGTWPZBad p N pos gens (θ (ι (Additive.ofMul z))) := by
  intro hbad
  obtain ⟨r, n, c, hW, hlo, hhi, hdiv, hcen⟩ := hPZ G p B Bs x L D J y K hH labJ labX X (N - 1)
    hX hJΛ hXΛ hJl hXl hrow ⟨hAtag, hXrank.symm⟩ hcard hJcard hJrefl z hzD hzx hzy
  obtain ⟨hc1, hc2⟩ := ggTWPZ_card_centre hp2 ι θ pos gensV gensJV hA hAJ gens hg₁ hg₂ hJ₁ hJ₂ z
  refine hbad r n c hW (hJrank ▸ hlo) hhi ⟨hc1 ▸ hdiv, fun heq => ?_⟩
  exact hc2.symm.trans (hcen (hc1.trans heq))

end CFSG.StandardType

end
