module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ShortRecognitionFinish
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NeighbourLift

@[expose] public section

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal

open CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem Matrix

open CFSG.SeitzReduction.F4Pilot

open CFSG.Timmesfeld.ARS.CaseM

open CFSG.StandardType.S2MathFi1035Pos

open CFSG.StandardType.F4ExplicitPos.ShortRecognitionFinish

open CFSG.StandardType.F4ExplicitPos.NeighbourLift

namespace CFSG.StandardType.F4ExplicitPos.Sp6NeighbourRoot

theorem ggRootVia_of_Sp6_neighbour
    (f : ℕ) (hf : 1 ≤ f)
    {Ω : Type} [Field Ω] [CharP Ω 2] [Algebra (GaloisField 2 f) Ω]
    {X Y : Type} [Group X] [Group Y]
    (G0 K R : Subgroup X) (hKG : K ≤ G0) (hRG : R ≤ G0)
    (η : G0 →* Y) (hη : Function.Injective η)
    (Λ : StatedSp 3 Ω →* Y) (hΛ : Function.Injective Λ)
    (κ : StatedSp 3 (GaloisField 2 f) →* Y)
    (hκ : κ = Λ.comp (statedSpMap (algebraMap (GaloisField 2 f) Ω) 3))
    (hκrange : κ.range = (K.subgroupOf G0).map η)
    (hcard : Nat.card ((R.subgroupOf G0).map η) = Nat.card (GaloisField 2 f))
    (hRbar : (R.subgroupOf G0).map η ≤ κ.range)
    {β : Fin (Symplectic.rootDatum 3 Ω).rank → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum 3 Ω).roots)
    (vΩ : StatedSp 3 Ω)
    (hplus : (R.subgroupOf G0).map η ≤
      (((Symplectic.rootDatum 3 Ω).rootGroup β).map (MulAut.conj vΩ).toMonoidHom).map Λ) :
    ∃ β' ∈ (ggU .PSp 3 f).D.roots, GGRootVia (ggU .PSp 3 f) K R β' := by
  have hκinj : Function.Injective κ := by
    rw [hκ]
    exact hΛ.comp (statedSpMap_injective (algebraMap (GaloisField 2 f) Ω) 3)
  let P : Subgroup (StatedSp 3 (GaloisField 2 f)) :=
    ((R.subgroupOf G0).map η).comap κ
  have hPmap : P.map κ = (R.subgroupOf G0).map η :=
    (comap_map_eq_and_card κ hκinj ((R.subgroupOf G0).map η) hRbar).1
  have hPcard : Nat.card P = Nat.card (GaloisField 2 f) := by
    rw [(comap_map_eq_and_card κ hκinj ((R.subgroupOf G0).map η) hRbar).2, hcard]
  have hPle : P.map (statedSpMap (algebraMap (GaloisField 2 f) Ω) 3) ≤
      ((Symplectic.rootDatum 3 Ω).rootGroup β).map (MulAut.conj vΩ).toMonoidHom :=
    comap_map_le_of_comp_injective (statedSpMap (algebraMap (GaloisField 2 f) Ω) 3) Λ hΛ κ hκ
      ((R.subgroupOf G0).map η)
      (((Symplectic.rootDatum 3 Ω).rootGroup β).map (MulAut.conj vΩ).toMonoidHom) hplus
  obtain ⟨β', hβ', u, hProot⟩ :=
    singleRootRecognition_unconditional hPcard hβ vΩ hPle
  refine ⟨β', ?_, ?_⟩
  · exact hβ'
  · have hRbarEq : (R.subgroupOf G0).map η =
        (((ggU .PSp 3 f).D.rootGroup β').map (MulAut.conj u).toMonoidHom).map κ := by
      rw [← hPmap, hProot]
      rfl
    exact ggRootVia_of_injective_range_lift G0 K R hKG hRG η hη (ggU .PSp 3 f) κ hκinj
      hκrange β' u hRbarEq

end CFSG.StandardType.F4ExplicitPos.Sp6NeighbourRoot

end

end
