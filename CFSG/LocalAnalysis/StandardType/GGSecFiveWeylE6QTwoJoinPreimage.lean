module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

theorem ggAutomizer_ggConjPreimage {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (hA : A ≤ ggAutomizer ⊤ Bs) : ggAutomizer (ggConjPreimage Bs A) Bs = A := by
  have key : ∀ (g : G) (hgN : g ∈ Subgroup.normalizer (Bs : Set G)) (ψ : MulAut ↥Bs),
      (∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = g * b * g⁻¹) → Bs.normalizerMonoidHom ⟨g, hgN⟩ = ψ := by
    intro g hgN ψ hg
    ext b
    exact (hg b).symm
  refine le_antisymm (fun ψ hψ => ?_) (fun ψ hψ => ?_)
  · obtain ⟨g, hgW, hgN, hg⟩ := mem_ggAutomizer_iff.mp hψ
    have hmem := (mem_ggConjPreimage_iff ⟨g, hgN⟩).mp hgW
    rwa [key g hgN ψ hg] at hmem
  · obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp (hA hψ)
    refine mem_ggAutomizer_iff.mpr ⟨g, ?_, hgN, hg⟩
    rw [mem_ggConjPreimage_iff ⟨g, hgN⟩, key g hgN ψ hg]
    exact hψ

theorem sup_ggAutomizer_ggConjPreimage (L Bs : Subgroup G) (𝒦 : Finset (Subgroup G)) :
    ggAutomizer L Bs ⊔ ggAutomizer (ggConjPreimage Bs (ggAutomizerJoin L Bs 𝒦)) Bs =
      ggAutomizerJoin L Bs 𝒦 := by
  have hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top)
  have hL : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
  rw [ggAutomizer_ggConjPreimage hle]
  exact sup_eq_right.mpr hL

theorem GGSecFiveE6QTwoCfg.exists_weylOfType_E6_sup
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg p B Bs x L D J) :
    ∃ K' : Subgroup G, GGWeylOfType p CoxeterMatrix.E₆ (ggAutomizer L Bs ⊔ ggAutomizer K' Bs) := by
  obtain ⟨𝒦, -, -, ι, M, e, hP, ⟨e', rfl⟩, -⟩ := hC
  refine ⟨ggConjPreimage Bs (ggAutomizerJoin L Bs 𝒦), ?_⟩
  rw [sup_ggAutomizer_ggConjPreimage]
  exact GGWeylOfType.of_reindex ⟨e, hP.2⟩

end CFSG.StandardType

end
