module

public import CFSG.Quasithin.H13.NQCatKG68Singer
public import CFSG.Quasithin.H13.NQCatLieCartanD4
public import CFSG.Quasithin.H13.NQCatLieCentralD4

public section

namespace CFSG.Quasithin.H13.KG68.Singer.D4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
  CFSG.Quasithin.B42D4 CFSG.Quasithin.H13.NQCat

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem cartanSingerCover_d4
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    CartanSingerCover ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : CharP K 2 := charP_two_of_card hn hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  have hσ3' : σ ^ 3 = 1 := pow_three_equiv σ hσ3
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  obtain ⟨-, ⟨e, he⟩, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3'
  have he' : ∀ p, (e p : ModGL TwistTag.D4.tag K) = trialityTorusHom σ p := fun p => he p.1 p.2
  obtain ⟨-, -, -, hsc⟩ := library_facts σ fa0 singleton_ne_univ_fa0
  have hUP : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ P0 σ :=
    graphFixedPosUnipotent_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
  have hQU : Q0 σ ≤ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedPosUnipotent _
  refine cartanSingerCover_of_le hUC hUsyl (graphFixedRootTorus_le _ _ _)
    graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent ?_
    (fun c d h => ox₆_inj σ hσ3 h) (ox₆_zero σ hσ3)
    (fun c => hUC ((ox_data σ hσ3).2.1.2.2.2.2.2 c))
    (fun c t ht =>
      (Subgroup.mem_centralizer_iff.1 (LieCentral.D4.ox₆_mem_centralizer σ hσ3 c) t ht).symm)
    (fun g hg hgc => ?_) (fun h hh => ?_) (fun b => ?_)
  · rw [graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent,
      CFSG.LieType.Chevalley.graphFixedRootBorel_eq_sup σ.surjective, sup_comm]
    exact σ.surjective
  · have hgC : g ∈ Subgroup.centralizer (Q0 σ : Set (ModGL TwistTag.D4.tag K)) :=
      Subgroup.mem_centralizer_iff.2 fun q hq => (hgc q (hQU hq)).symm
    obtain ⟨f, hf⟩ := D4Center.eq_ox₆_of_mem_center_a0 σ hσ3 ⟨hsc ⟨hUP hg, hgC⟩, hgC⟩
    exact ⟨f, hf.symm⟩
  · obtain ⟨p, hp⟩ := e.surjective ⟨h, hh⟩
    have hh' : h = trialityTorusHom σ p := by rw [← he', hp]
    refine ⟨p.2, fun c => ?_⟩
    rw [hh']
    exact LieCartan.D4.torus_ab_ox₆ σ hσ3 _ _ c
  · refine ⟨e (1, b), (e (1, b)).2, fun c => ?_⟩
    rw [he']
    exact LieCartan.D4.torus_ab_ox₆ σ hσ3 1 b c

end CFSG.Quasithin.H13.KG68.Singer.D4
