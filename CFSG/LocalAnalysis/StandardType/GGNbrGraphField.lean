module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldB2der

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGNbrGraphD4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → p = 3 → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun lab _ _ I F θ => lab.tag = .D → lab.rank = 4 →
          ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
            ggLAut K θ ⟨b, hN hb⟩ = u * f

theorem ggLAut_pow_eq_one {G : Type} [Group G] (K : Subgroup G) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {p : ℕ} {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hbp : b ^ p = 1) :
    ggLAut K θ ⟨b, hb⟩ ^ p = 1 := by
  have h1 : (⟨b, hb⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hbp)
  rw [← map_pow, h1, map_one]

theorem ggNbrGraphInput_of_oddAut (hA : GGOddAutOn fun _ => True) (hD4 : GGNbrGraphD4Input) :
    GGNbrGraphInput := by
  intro G _ _ p B Bs x L D J hC y K hK hN P hP
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hC.2.1.2.1.2
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
  ·
    have hP' : LargeEvenMarking K fun lab' R _ I F θ => P lab' R I F θ ∧ lab' = lab := by
      refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
      rintro R _ I F ⟨hs, hna, θ, hθ⟩
      exact ⟨hs, hna, θ, hθ, rfl⟩
    refine largeEvenMarking_mono ?_ (hD4 G p B Bs x L D J hC hD.2.2 y K hK hN _ hP')
    rintro lab' R _ I F θ ⟨⟨hθ, rfl⟩, hQ⟩
    exact ⟨hθ, hQ hD.1 hD.2.1⟩
  ·
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ (hA p lab hp hp2 hlab trivial hD _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hodd⟩
    exact ⟨hs, hna, θ, hθ, fun b hb => hodd hs hna _ (ggLAut_pow_eq_one K θ (hN hb) (hexp b hb))⟩

@[expose] def GGNbrGraphDoneLabel (lab : LargeEvenLabel) : Prop :=
  GGLinearRecipeLabel lab ∨ GGSymplecticRecipeLabel lab ∨ lab.tag = .B2der

theorem ggOddAutOn_done : GGOddAutOn GGNbrGraphDoneLabel :=
  ggOddAutOn_linear.or (ggOddAutOn_symplectic.or ggOddAutOn_b2der)

theorem ggNbrGraphInput_of_rest (hrest : GGOddAutOn fun lab => ¬ GGNbrGraphDoneLabel lab)
    (hD4 : GGNbrGraphD4Input) : GGNbrGraphInput :=
  ggNbrGraphInput_of_oddAut (ggOddAutOn_true_of ggOddAutOn_done hrest) hD4

end CFSG.StandardType
