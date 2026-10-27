module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowTriGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)

local instance triMainNeZeroE6 : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

theorem triQ_check :
    triOverlapB triRootA4 triRootEps = true ∧ triOverlapB triRootA4 (-triRootEps) = true ∧
    triOverlapB triRootG3 triRootEps = true ∧ triOverlapB triRootG3 (-triRootEps) = true ∧
    triOverlapB triRootA4 triRootG3 = true ∧ triOverlapB triRootA4 (-triRootG3) = true ∧
    permLattice TwistTag.E6.perm (-triRootEps) = -triRootEps ∧
    permLattice TwistTag.E6.perm (-triRootG3) = -triRootG3 := by
  decide +kernel


theorem pinnedX_triRootEps_mul_ne_tri {K : Type} [Field K] [CharP K 2] :
    pinnedX TwistTag.E6.tag K triRootEps 1 * pinnedX TwistTag.E6.tag K (-triRootEps) 1 ≠
      pinnedX TwistTag.E6.tag K (-triRootEps) 1 * pinnedX TwistTag.E6.tag K triRootEps 1 := by
  obtain ⟨-, -, -, -, ⟨a2, a2'⟩, ⟨g2, g2'⟩, -, -, -⟩ := triTransport_check
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hA4single⟩ := triRoots_check
  have hrA4 := isRoot_of_triRootB triIsRoot_check.1
  have hrG3 := isRoot_of_triRootB triIsRoot_check.2.1
  have key : ∀ {β β' β'' : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag β →
      twistedE6RelAct triWord2 β = β' → twistedE6RelAct triWord2 β' = β'' →
      pinnedX TwistTag.E6.tag K β'' 1 =
        (twistedE6RelWeyl K triWord2 * twistedE6RelWeyl K triWord2) *
          pinnedX TwistTag.E6.tag K β 1 *
            (twistedE6RelWeyl K triWord2 * twistedE6RelWeyl K triWord2)⁻¹ := by
    intro β β' β'' hβ h₁ h₂
    have hβ' : IsRoot TwistTag.E6.tag β' := by
      rw [← h₁]
      exact CFSG.SeitzReduction.IsRoot.twistedE6RelAct hβ triWord2
    rw [show (twistedE6RelWeyl K triWord2 * twistedE6RelWeyl K triWord2) *
        pinnedX TwistTag.E6.tag K β 1 *
          (twistedE6RelWeyl K triWord2 * twistedE6RelWeyl K triWord2)⁻¹ =
        twistedE6RelWeyl K triWord2 * (twistedE6RelWeyl K triWord2 *
          pinnedX TwistTag.E6.tag K β 1 * (twistedE6RelWeyl K triWord2)⁻¹) *
            (twistedE6RelWeyl K triWord2)⁻¹ by group,
      twistedE6RelWeyl_conj_pinnedX triWord2 hβ, h₁, twistedE6RelWeyl_conj_pinnedX triWord2 hβ',
      h₂]
  intro h
  apply not_commute_xUnit_yUnit (τ := TwistTag.E6.tag) (K := K) 3
  rw [← pinnedX_single, ← pinnedX_neg_single, ← hA4single]
  refine commute_of_commute_conj_tri
    (g := twistedE6RelWeyl K triWord2 * twistedE6RelWeyl K triWord2) ?_
  rw [← key hrA4 a2 g2, ← key (CFSG.LieType.Chevalley.IsRoot.neg hrA4) a2' g2']
  exact h

theorem twistedE6TwoTriangleInput_of_overlapFacts (hO : TwistedE6TwoOverlapFacts) :
    TwistedE6TwoTriangleInput := by
  intro k K _ _ _ hk hK σ hσ A hA hA3 _
  have : Finite K := finite_of_card hK
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have hι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card hk hσ)
  obtain ⟨⟨t2, t2'⟩, ⟨t3, t3'⟩, ⟨e2, e2'⟩, ⟨e3, e3'⟩, ⟨a2, a2'⟩, ⟨g2, g2'⟩, ⟨a3, a3'⟩, -, -⟩ :=
    triTransport_check
  obtain ⟨hA4mem, hG3mem, hρA4, hρG3, hρE, hA4one, hG3one, hEone, -, -, -⟩ := triRoots_check
  obtain ⟨qE2, qE2', qE3, qE3', qG3, qG3', hρE', hρG3'⟩ := triQ_check
  have hrA4 := isRoot_of_triRootB triIsRoot_check.1
  have hrG3 := isRoot_of_triRootB triIsRoot_check.2.1
  have hrE := isRoot_of_triRootB triIsRoot_check.2.2.1
  have hθ : thetaRankOneGroup (algebraMap k K) ≤
      TwistedE6Pilot.rootRankOneGroup (algebraMap k K) e6HighestRoot :=
    (thetaRankOneGroup_eq_rootRankOneGroup_tri _).le
  have hX₂ := map_conj_le_rootRankOneGroup_tri hA triWord2 t2 t2'
  have hX₃ := map_conj_le_rootRankOneGroup_tri hA triWord3 t3 t3'
  have hJA4 := rootRankOneGroup_le_su6Levi_tri (σ := σ) hι hrA4 hA4one hρA4
  have hJG3 := rootRankOneGroup_le_su6Levi_tri (σ := σ) hι hrG3 hG3one hρG3
  obtain ⟨Y, hYmap, hY⟩ : ∃ Y : Subgroup (ModGL TwistTag.E6.tag K),
      Y.map (MulAut.conj (twistedE6RelWeyl K triWord2)).toMonoidHom =
        A.map (MulAut.conj (twistedE6RelWeyl K triWord3)).toMonoidHom ∧
      Y ≤ TwistedE6Pilot.rootRankOneGroup (algebraMap k K) triRootA4 := by
    refine ⟨_, map_comap_eq_self_of_surjective (MulAut.conj _).surjective _, ?_⟩
    have h := comap_mono (f := (MulAut.conj (twistedE6RelWeyl K triWord2)).toMonoidHom) hX₃
    rwa [← map_conj_rootRankOneGroup_tri (algebraMap k K) triWord2 hrA4 a2 a2',
      comap_map_eq_self_of_injective (MulAut.conj _).injective] at h
  have hc₂ : Nat.card (A.map (MulAut.conj (twistedE6RelWeyl K triWord2)).toMonoidHom) = 3 :=
    (card_map_of_injective (f := (MulAut.conj (twistedE6RelWeyl K triWord2)).toMonoidHom)
      (MulAut.conj _).injective).trans (hA3.trans (by norm_num))
  have hc₃ : Nat.card (A.map (MulAut.conj (twistedE6RelWeyl K triWord3)).toMonoidHom) = 3 :=
    (card_map_of_injective (f := (MulAut.conj (twistedE6RelWeyl K triWord3)).toMonoidHom)
      (MulAut.conj _).injective).trans (hA3.trans (by norm_num))
  have hcY : Nat.card Y = 3 := by
    rw [← card_map_of_injective (f := (MulAut.conj (twistedE6RelWeyl K triWord2)).toMonoidHom)
      (MulAut.conj _).injective, hYmap, hc₃]
  obtain ⟨hs₂, hr₂⟩ := hO k K hk hK σ hσ triRootA4 hA4mem _ hX₂ hc₂
  obtain ⟨hs₃, hr₃⟩ := hO k K hk hK σ hσ triRootG3 hG3mem _ hX₃ hc₃
  obtain ⟨hsY, hrY⟩ := hO k K hk hK σ hσ triRootA4 hA4mem Y hY hcY
  have hO23 : perfectCore ((su6Levi σ).map
      (MulAut.conj (twistedE6RelWeyl K triWord2)).toMonoidHom ⊓
        centralizer (A.map (MulAut.conj (twistedE6RelWeyl K triWord3)).toMonoidHom :
          Set (ModGL TwistTag.E6.tag K))) =
      (perfectCore (su6Levi σ ⊓ centralizer (Y : Set (ModGL TwistTag.E6.tag K)))).map
        (MulAut.conj (twistedE6RelWeyl K triWord2)).toMonoidHom := by
    rw [← hYmap]
    exact perfectCore_map_inf_centralizer_tri _ _ _
  obtain ⟨n₂, hn₂⟩ : ∃ n : graphFixedRootGroup TwistTag.E6 K σ,
      (n : ModGL TwistTag.E6.tag K) = twistedE6RelWeyl K triWord2 :=
    ⟨⟨twistedE6RelWeyl K triWord2, twistedE6RelWeyl_mem σ triWord2⟩, rfl⟩
  obtain ⟨n₃, hn₃⟩ : ∃ n : graphFixedRootGroup TwistTag.E6 K σ,
      (n : ModGL TwistTag.E6.tag K) = twistedE6RelWeyl K triWord3 :=
    ⟨⟨twistedE6RelWeyl K triWord3, twistedE6RelWeyl_mem σ triWord3⟩, rfl⟩
  refine ⟨n₂, n₃, pinnedX TwistTag.E6.tag K triRootEps 1,
    pinnedX TwistTag.E6.tag K (-triRootEps) 1, ?_⟩
  rw [hn₂, hn₃, hO23]
  refine ⟨hX₂.trans hJA4, hX₃.trans hJG3,
    hA.trans (hθ.trans (rootRankOneGroup_le_map_su6Levi_tri hι triWord2 hrE hEone hρE e2 e2')),
    hX₃.trans (rootRankOneGroup_le_map_su6Levi_tri hι triWord2 hrA4 hA4one hρA4 a2 a2'),
    hA.trans (hθ.trans (rootRankOneGroup_le_map_su6Levi_tri hι triWord3 hrE hEone hρE e3 e3')),
    hX₂.trans (rootRankOneGroup_le_map_su6Levi_tri hι triWord3 hrA4 hA4one hρA4 a3 a3'),
    hs₂, hs₃, isSimpleGroup_map_tri hsY (MulAut.conj _).injective,
    pinnedX_mem_of_triOverlapB hr₂ qE2 hρE (map_one σ),
    pinnedX_mem_of_triOverlapB hr₃ qE3 hρE (map_one σ), ?_,
    pinnedX_mem_of_triOverlapB hr₂ qE2' hρE' (map_one σ),
    pinnedX_mem_of_triOverlapB hr₃ qE3' hρE' (map_one σ), ?_,
    pinnedX_triRootEps_mul_ne_tri, graphFixedRootGroup_le_sup_tri hK hσ hr₂ hr₃ hrY⟩
  · refine ⟨_, pinnedX_mem_of_triOverlapB hrY qG3 hρG3 (map_one σ), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [twistedE6RelWeyl_conj_pinnedX triWord2 hrG3, g2]
  · refine ⟨_, pinnedX_mem_of_triOverlapB hrY qG3' hρG3' (map_one σ), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [twistedE6RelWeyl_conj_pinnedX triWord2 (CFSG.LieType.Chevalley.IsRoot.neg hrG3), g2']

end CFSG.SeitzReduction.TwistedE6Pilot
