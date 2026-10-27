module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGPZE6Input
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowPZCard

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nPX_row_rank_four {p : ℕ} {labJ labX : LargeEvenLabel}
    (hrow : ggRowTwoNode p labJ labX) (htag : labX.tag = .E6 ∨ labX.tag = .twE6) :
    labJ.rank = 4 := by
  rcases hrow with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨hJ, -, -, -⟩ | ⟨hJ, -, -, -⟩
  · have hA : labX.tag = .A := congrArg LargeEvenLabel.tag hX
    rw [hA] at htag
    exact absurd htag (by decide)
  · have hA : labX.tag = .twA := congrArg LargeEvenLabel.tag hX
    rw [hA] at htag
    exact absurd htag (by decide)
  · exact congrArg LargeEvenLabel.rank hJ
  · exact congrArg LargeEvenLabel.rank hJ

theorem ggDepELPZ_xfer (hPZ : GGPZE6Input) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {labJ labX : LargeEvenLabel} {X : Subgroup G}
    (hX : X = L ∨ X = K) (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hXl : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X)) (hrow : ggRowTwoNodeSmall 3 labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) (hcard : Nat.card ↥Bs = 3 ^ 6)
    (hJcard : Nat.card ↥(Bs ⊓ J) = 3 ^ labJ.rank) (hJrefl : GGReflGenerated 3 (ggAutomizer J Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (gensV gensJV : Set (V ≃ₗ[ZMod 3] V))
    (hA : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) = Subgroup.closure gensV)
    (hAJ : (ggAutomizer J Bs).map (ggLin (p := 3) ι) = Subgroup.closure gensJV)
    (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (hg₁ : ∀ g ∈ gensV, ∃ y ∈ gens,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hg₂ : ∀ y ∈ gens, ∃ g ∈ gensV,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hJ₁ : ∀ g ∈ gensJV, ∃ i : {i : Fin 6 // GGDepED4In i},
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ
        θ.toLinearMap)
    (hJ₂ : ∀ i : {i : Fin 6 // GGDepED4In i}, ∃ g ∈ gensJV,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ ggDepARefl (ggDepELh i.1) (ggDepELα i.1) ∘ₗ
        θ.toLinearMap)
    (z : ↥Bs) (hzD : (z : G) ∈ D) (hzx : (z : G) ∉ Subgroup.zpowers x)
    (hzy : (z : G) ∉ Subgroup.zpowers y) :
    ¬ GGDepELPZBad gens (θ (ι (Additive.ofMul z))) := by
  intro hbad
  have hrankJ : labJ.rank = 4 := l05nPX_row_rank_four hrow.1 htag
  obtain ⟨r, n, c, hW, hlo, hhi, hdiv, hcen⟩ :=
    hPZ G 3 B Bs x L D J y K hH labJ labX X 6 hX hJΛ hXΛ hJl hXl hrow ⟨htag, rfl⟩ hcard hJcard
      hJrefl z hzD hzx hzy
  obtain ⟨hc1, hc2⟩ :=
    ggDepELPZ_card_centre ι θ gensV gensJV hA hAJ gens hg₁ hg₂ hJ₁ hJ₂ z
  refine hbad r n c hW (hrankJ ▸ hlo) hhi ⟨hc1 ▸ hdiv, fun heq => ?_⟩
  exact hc2.symm.trans (hcen (hc1.trans heq))

end CFSG.StandardType

end
