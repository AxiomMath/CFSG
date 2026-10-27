module

public import CFSG.Milestones.ASVolI.F45.F46TitsIota
public import CFSG.Milestones.ASVolI.F45.F46TitsBeta
public import CFSG.Milestones.ASVolI.F45.Core
public import CFSG.Milestones.ASVolI.F45.L3
public import CFSG.Milestones.ASVolI.F45.Sp4
public import CFSG.Milestones.ASVolI.F45.U
import all CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section Data


variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF46_data (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) : burnsideF46_Data β (Qx 2 ⊤ β) (Ql 2 ⊤ β) := by
  haveI : Finite E := hyp.finite
  have T := burnsideF45_titsData hyp
  have hι := incl_faithful M₁ M₂
  obtain ⟨b₀, P⟩ := T.pt
  obtain ⟨lab, A⟩ := T.aff
  exact
    { hyp := (burnsideF46_titsModel hyp).titsHyp hβ
      qOne := (burnsideF46_q hyp).1
      qTwo := (burnsideF46_q hyp).2
      qn := burnsideF4b_QNormalized 2 inferInstance β
      qx_le := burnsideF46_Qx_le_stv β 2 ⊤
      ql_le := burnsideF46_Ql_le_stv β 2 ⊤
      fix_x := (burnsideF46_Q_fix hyp β).1
      fix_l := (burnsideF46_Q_fix hyp β).2
      compl_l := fun q hq => burnsideF4b_transfer_l hβ hι (by norm_num) _
        (burnsideF46_iota_line_compl hyp) hq
      idx_x := fun q hq => burnsideF46_transfer_x_idx hβ hι (by norm_num) _ 2
        (burnsideF46_iota_point_idx hyp) hq
      card_x := fun q hq => burnsideF46_transfer_x_card hβ hι 2 (by norm_num)
        (fun q' hq' => T.point_card_stabPath hq') hq
      nontriv_x := fun q hq => burnsideF46_transfer_x_nontriv hβ hι
        (fun q' hq' => P.nontriv T.poly hq') hq
      aff := burnsideF46_affLab_transfer_x hβ hι A
      two_orb := burnsideF46_twoOrb_transfer_l hβ hι T.line_orbits }

end Data

section LieFacts


theorem burnsideF46_lieFactsAll : burnsideF45_LieFactsAll :=
  burnsideF45_lieFactsAll_of_classical
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_L3 hyp hp _)
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_Sp4 hyp hp _)
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_U4 hyp hp _)
    (fun _ _ _ _ _ _ _ hyp hp => burnsideF45_facts45L_U5 hyp hp _)

end LieFacts

section Main


theorem burnsideF46_C7 {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) :
    IsLieExtAmalgam M₁ M₂ → ∀ u : (incl M₁ M₂).Γ, (incl M₁ M₂).PathTrans u (GLKind.Tits.m + 1) := by
  rintro ⟨κ', p', f', Gp', hκ', hyp'⟩ u
  have hS := burnsideF46_lieFactsAll κ' hκ' p' f' E Gp' M₁ M₂ hyp'
    (burnsideF4a_prime_of_isGenLie hyp'.model)
  have hm : κ'.m = 8 := burnsideF45_polygon_m_eq hS.poly (burnsideF45_titsData hyp).poly
  have := hS.trans u
  rwa [show (burnsideF45_setting hyp' (burnsideF4a_prime_of_isGenLie hyp'.model)
    (burnsideF45_three_le_m κ')).m = κ'.m from rfl, hm] at this

theorem burnsideF46_tits : ∀ (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 .Tits p f Gp M₁ M₂ → ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
    ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ → burnsideF4b_F46Body .Tits p Gp M₁ M₂ β ι := by
  intro p f E _ Gp M₁ M₂ hyp Y _ β hβ ι hι
  subst hι
  obtain ⟨hp2, hf1, -⟩ := hyp.model
  subst hp2
  subst hf1
  have hGp : Gp = ⊤ := hyp.canonical (Or.inr rfl)
  subst hGp
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have D := burnsideF46_data hyp β hβ
  have hthree := burnsideF4a_F46_three β hβ (incl M₁ M₂) (incl_faithful M₁ M₂)
  unfold burnsideF4b_F46Body
  refine ⟨fun a => ⟨fun hext => ?_, fun _ => ⟨fun ha => D.transPt ha, fun ha =>
    ⟨D.transLn ha, D.twoOrb_line ha, fun q₁ h₁ q₂ h₂ he => D.paths_trans h₁ h₂ he⟩⟩⟩,
    hthree.1, hthree.2, ?_, ?_⟩
  ·
    exact pathTrans_transfer β hβ (incl M₁ M₂) (incl_faithful M₁ M₂) _
      (burnsideF46_C7 hyp hext) a
  ·
    intro n hn a q hq
    refine ⟨fun _ hex => ?_, fun hnm => D.six hnm hq⟩
    have hex' : ¬ (CosetGeom.vtype a = true ∧ n = 8) := fun h =>
      hex ⟨⟨rfl, Or.inr rfl⟩, h.1, h.2⟩
    have hidx := D.four hn hex' hq
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [hidx, hj, RankTwoAmalgam.pathNum_odd, burnsideF4b_qv_mul]
      rfl
    · rw [hidx, hj, RankTwoAmalgam.pathNum_even, burnsideF4b_qv_mul]
      rfl
  ·
    intro a q hq
    refine ⟨?_, D.dist_m hq, fun r hr => ⟨?_, D.dist_m hr⟩, ?_⟩
    · rcases D.five a hq with h | ⟨ha, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨⟨rfl, Or.inr rfl⟩, ha, h1, h2⟩
    · show β.graph.dist (r 0) (r 8) = 8
      rw [hr.1]
      exact D.dist_m hr
    · rcases D.alt hq with hi | hb
      · exact Or.inl hi
      · rcases Bool.eq_false_or_eq_true (CosetGeom.vtype a) with ha | ha
        · obtain ⟨hc, h2, hcard⟩ := D.eight_line ha hq hb
          exact Or.inr (Or.inl ⟨hc, h2, hcard, hb⟩)
        · obtain ⟨hD, htr, hcard⟩ := D.eight_point ha hq hb
          exact Or.inr (Or.inr (Or.inl ⟨⟨rfl, rfl⟩, ha, hD, htr, hcard, hb⟩))

end Main

end CFSG.ASVolI
