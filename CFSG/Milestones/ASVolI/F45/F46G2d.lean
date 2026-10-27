module

public import CFSG.Milestones.ASVolI.F45.F46G2dIota
public import CFSG.Milestones.ASVolI.F45.Core
public import CFSG.Milestones.ASVolI.F45.L3
public import CFSG.Milestones.ASVolI.F45.Sp4
public import CFSG.Milestones.ASVolI.F45.U
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F45.F46G2dEight

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section Main


theorem burnsideF46_g2d_lieFactsAll : burnsideF45_LieFactsAll :=
  burnsideF45_lieFactsAll_of_classical
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_L3 hyp hp _)
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_Sp4 hyp hp _)
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_U4 hyp hp _)
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_U5 hyp hp _)

theorem burnsideF46_g2d_C7 {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2d 2 1 ⊤ M₁ M₂) :
    IsLieExtAmalgam M₁ M₂ → ∀ u : (incl M₁ M₂).Γ, (incl M₁ M₂).PathTrans u (GLKind.G2d.m + 1) := by
  rintro ⟨κ', p', f', Gp', hκ', hyp'⟩ u
  have hS := burnsideF46_g2d_lieFactsAll κ' hκ' p' f' E Gp' M₁ M₂ hyp'
    (burnsideF4a_prime_of_isGenLie hyp'.model)
  have hm : κ'.m = GLKind.G2d.m := burnsideF45_polygon_m_eq hS.poly (burnsideF46_g2d_poly hyp)
  have := hS.trans u
  rwa [show (burnsideF45_setting hyp' (burnsideF4a_prime_of_isGenLie hyp'.model)
    (burnsideF45_three_le_m κ')).m = κ'.m from rfl, hm] at this

theorem burnsideF46_g2d : ∀ (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 .G2d p f Gp M₁ M₂ → ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
    ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ → burnsideF4b_F46Body .G2d p Gp M₁ M₂ β ι := by
  intro p f E _ Gp M₁ M₂ hyp Y _ β hβ ι hι
  subst hι
  obtain ⟨hp2, hf1, -⟩ := hyp.model
  subst hp2 hf1
  have hGp : Gp = ⊤ := hyp.canonical (Or.inl rfl)
  subst hGp
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have D := burnsideF46_g2d_data hyp β hβ
  have hthree := burnsideF4a_F46_three β hβ (incl M₁ M₂) (incl_faithful M₁ M₂)
  refine ⟨fun a => ⟨fun hext => ?_, fun _ => ?_⟩, hthree.1, hthree.2, ?_, ?_⟩
  · exact pathTrans_transfer β hβ (incl M₁ M₂) (incl_faithful M₁ M₂) (GLKind.G2d.m + 1)
      (burnsideF46_g2d_C7 hyp hext) a
  · exact ⟨fun ha => D.transPt ha, fun ha => ⟨D.transLn ha, D.twoOrb_line ha,
      fun q₁ hq₁ q₂ hq₂ he => D.paths_trans hq₁ hq₂ he⟩⟩
  · intro n hn a q hq
    refine ⟨fun _ hex => ?_, fun hnm => D.six hnm hq⟩
    have hidx := D.four hn (fun h => hex ⟨⟨rfl, Or.inl rfl⟩, h⟩) hq
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [hidx, hj, RankTwoAmalgam.pathNum_odd, burnsideF4b_qv_mul]
      rfl
    · rw [hidx, hj, RankTwoAmalgam.pathNum_even, burnsideF4b_qv_mul]
      rfl
  · intro a q hq
    refine ⟨?_, D.dist_m hq, fun r hr => ⟨?_, D.dist_m hr⟩, ?_⟩
    · rcases D.five a hq with h | ⟨ha, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨⟨rfl, Or.inl rfl⟩, ha, h1, h2⟩
    · show β.graph.dist (r 0) (r 6) = 6
      rw [hr.1]
      exact D.dist_m hr
    · rcases D.alt hq with hi | hb
      · exact Or.inl hi
      · cases ha : CosetGeom.vtype a
        · obtain ⟨hiso, htr, hcard⟩ := D.eight_point ha hq hb
          exact Or.inr (Or.inr (Or.inr ⟨⟨rfl, rfl⟩, rfl, hiso, htr, hcard, hb⟩))
        · obtain ⟨hc, h2, hcard⟩ := D.eight_line ha hq hb
          exact Or.inr (Or.inl ⟨hc, h2, hcard.trans (by rw [ha]; rfl), hb⟩)

end Main

end CFSG.ASVolI
