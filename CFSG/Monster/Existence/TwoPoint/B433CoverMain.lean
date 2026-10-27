module

public import CFSG.Monster.Existence.TwoPoint.B433CoverPush
public import Certificates.Certificate6041

public section

namespace CFSG.Monster.Existence.B433Cover

open CFSG.YGroups CFSG.YGroups.DCE.B433

theorem b433_cover (g : B433) :
    ∃ l < 23, ∃ a ∈ psi.range, ∃ b ∈ psi.range, g = a * xB l * b :=
  Certificates.certificate6041 g

theorem u433_cover (g : U433) :
    ∃ l < 23, ∃ a ∈ psiU.range, ∃ b ∈ psiU.range,
      ∃ f ∈ Subgroup.normalClosure ({F433 2 1 3, F433 3 1 2} : Set U433),
        g = a * xU l * b * f :=
  u433_cover_of_cover b433_cover g

theorem exists_cover_image
    {G : Type*} [Group G] (φ : U433 →* G) (c : G)
    (hF1 : φ (F433 2 1 3) = 1) (hF2 : φ (F433 3 1 2) = c)
    (hc : ∀ g ∈ φ.range, g * c = c * g) {g : G} (hg : g ∈ φ.range) :
    ∃ l < 23, ∃ k₁ ∈ psiU.range.map φ, ∃ k₂ ∈ psiU.range.map φ, ∃ n : ℤ,
      g = k₁ * nodeProd (fun i => φ (yGen 4 3 3 i)) (φ (yGen 4 3 3 10)) l * k₂ * c ^ n :=
  exists_cover_image_of_cover b433_cover φ c hF1 hF2 hc hg

end CFSG.Monster.Existence.B433Cover
