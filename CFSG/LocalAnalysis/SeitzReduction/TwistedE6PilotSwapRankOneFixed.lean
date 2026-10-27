module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapRankOne
public import CFSG.RankThree.Chevalley.EvenTrialityElementaryNine
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignLevi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

local instance twistedE6PilotSwapRankOneFixedNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

variable {K : Type} [Field K]


theorem twistHom_rankOneHom' (t : TwistTag) (σ : K →+* K) (i : Fin t.tag.rank) (g : SL2 K) :
    twistHom t K σ (rankOneHom t K i g) =
      rankOneHom t K (t.perm i) (SpecialLinearGroup.map σ g) := by
  have h := SL2_hom_ext (φ := (twistHom t K σ).comp (rankOneHom t K i))
    (ψ := (rankOneHom t K (t.perm i)).comp (SpecialLinearGroup.map σ))
    (fun s => by simp only [MonoidHom.comp_apply, rankOneHom_uSL, twistHom_xUnit, map_uSL])
    (fun u => by simp only [MonoidHom.comp_apply, rankOneHom_HSL, twistHom_torusElt, map_HSL])
    (by simp only [MonoidHom.comp_apply, rankOneHom_WSL, twistHom_weylElt_one, map_WSL])
  exact DFunLike.congr_fun h g

theorem rankOneHom_injective_of_charTwo [CharP K 2] (t : TwistTag) (i : Fin t.tag.rank) :
    Function.Injective (rankOneHom t K i) :=
  CFSG.RankThree.Chevalley.injective_of_ker_scalar_of_charTwo
    (exceptional_ordinary_rank_one_central_image (τ := t.tag) (K := K) i).choose_spec.2.2.2.2.2.1

@[expose] def nodeAlpha4 : Fin TwistTag.E6.tag.rank := ⟨3, by decide⟩

theorem relNodeSet_one : relNodeSet ({1} : Finset (Fin Tag.F4.rank)) = {nodeAlpha4} := by
  decide

theorem relLevi_one_eq_range : relLevi K {1} = (rankOneHom TwistTag.E6 K nodeAlpha4).range := by
  rw [relLevi, ← F4Pilot.closure_xUnit_yUnit_eq_rootSpan, rankOneHom_range, relNodeSet_one]
  congr 1
  ext g
  simp only [Finset.coe_singleton, Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq,
    Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨c, rfl | rfl⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨c, Or.inl rfl⟩
    · exact ⟨c, Or.inr rfl⟩

theorem perm_nodeAlpha4 : TwistTag.E6.perm nodeAlpha4 = nodeAlpha4 := by decide

theorem orbit_relOrbit_one_card : (TwistTag.E6.orbit (relOrbit 1)).card = 1 := by decide

theorem orbitMin_relOrbit_one : TwistTag.E6.orbitMin (relOrbit 1) = nodeAlpha4 := by decide

theorem orbitRankOneHom_relOrbit_one (σ : K →+* K)
    (g : SL2 (orbitField TwistTag.E6 K σ (relOrbit 1))) :
    orbitRankOneHom TwistTag.E6 K σ (relOrbit 1) g =
      rankOneHom TwistTag.E6 K nodeAlpha4
        (SpecialLinearGroup.map (orbitField TwistTag.E6 K σ (relOrbit 1)).subtype g) := by
  rw [orbitRankOneHom_apply, orbit_relOrbit_one_card, orbitMin_relOrbit_one]
  simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    pow_zero, Equiv.Perm.coe_one, id_eq]
  rfl

theorem relLevi_one_inf_C0_le [CharP K 2] (σ : K →+* K) :
    relLevi K {1} ⊓ graphFixedRootGroup TwistTag.E6 K σ ≤ relRankOne σ 1 := by
  rintro x ⟨hx, hxC⟩
  rw [relLevi_one_eq_range] at hx
  obtain ⟨g, rfl⟩ := hx
  have hF := ((mem_twistedFixedGroup_iff_twistHom (t := TwistTag.E6) (K := K) (σ := σ)).1
    (graphFixedRootGroup_le TwistTag.E6 K σ hxC)).2
  rw [twistHom_rankOneHom', perm_nodeAlpha4] at hF
  have hg := rankOneHom_injective_of_charTwo TwistTag.E6 nodeAlpha4 hF
  have hmem : ∀ i j, (g : Matrix (Fin 2) (Fin 2) K) i j ∈ orbitField TwistTag.E6 K σ (relOrbit 1) :=
    fun i j => by
      rw [mem_orbitField, orbit_relOrbit_one_card, pow_one]
      have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) i j) hg
      simpa using this
  set g' : SL2 (orbitField TwistTag.E6 K σ (relOrbit 1)) :=
    ⟨Matrix.of fun i j => ⟨(g : Matrix (Fin 2) (Fin 2) K) i j, hmem i j⟩, by
      apply Subtype.val_injective
      have h1 := g.2
      rw [Matrix.det_fin_two] at h1 ⊢
      simpa using h1⟩ with hg'
  have hmap : SpecialLinearGroup.map (orbitField TwistTag.E6 K σ (relOrbit 1)).subtype g' = g := by
    ext i j
    rfl
  rw [relRankOne_eq_range]
  refine ⟨g', ?_⟩
  rw [orbitRankOneHom_relOrbit_one, hmap]

theorem orbitRankOneHom_relOrbit_one_injective [CharP K 2] (σ : K →+* K) :
    Function.Injective (orbitRankOneHom TwistTag.E6 K σ (relOrbit 1)) := by
  intro g h hgh
  rw [orbitRankOneHom_relOrbit_one, orbitRankOneHom_relOrbit_one] at hgh
  have h1 := rankOneHom_injective_of_charTwo TwistTag.E6 nodeAlpha4 hgh
  ext i j
  have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) i j) h1
  simpa using this

theorem isSimpleGroup_relRankOne_one [Finite K] [CharP K 2] (σ : K →+* K)
    (hq : 4 ≤ Nat.card (orbitField TwistTag.E6 K σ (relOrbit 1))) :
    IsSimpleGroup (relRankOne σ 1) := by
  have : CharP (orbitField TwistTag.E6 K σ (relOrbit 1)) 2 :=
    Subfield.charP (orbitField TwistTag.E6 K σ (relOrbit 1)) 2
  have : IsSimpleGroup (SL2 (orbitField TwistTag.E6 K σ (relOrbit 1))) :=
    CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup hq
  have e := MonoidHom.ofInjective (orbitRankOneHom_relOrbit_one_injective (K := K) σ)
  rw [← relRankOne_eq_range] at e
  exact e.symm.isSimpleGroup

theorem perfectCore_C0_inf_centralizer_one [Finite K] [CharP K 2] (σ : K →+* K)
    {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A) (hperf : ⁅relRankOne σ 1, relRankOne σ 1⁆ =
      relRankOne σ 1) :
    CFSG.Quasithin.perfectCore (graphFixedRootGroup TwistTag.E6 K σ ⊓
        centralizer (relLeviTorus K A {1} : Set (ModGL TwistTag.E6.tag K))) = relRankOne σ 1 := by
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect
    (le_inf (relRankOne_le_C0 σ 1) (relRankOne_le_centralizer σ A 1)) hperf)
  rw [perfectCore_C0_inf_centralizer_relLeviTorus σ hA (by decide)]
  exact (CFSG.Quasithin.perfectCore_le _).trans (relLevi_one_inf_C0_le σ)

end CFSG.SeitzReduction.TwistedE6Pilot
