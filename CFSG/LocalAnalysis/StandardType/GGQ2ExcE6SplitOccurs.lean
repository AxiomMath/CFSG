module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitOccursDict
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitLabel
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreRawBot
public import CFSG.LocalAnalysis.StandardType.GGFamSubnormal
public import CFSG.LocalAnalysis.StandardType.GGLangGammaComponent
public import CFSG.LocalAnalysis.StandardType.GGFamTameSharp
public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGFamTrivialGamma
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreOccursDict
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav CFSG.StandardType.TableCRes

noncomputable section

private theorem ggLinImage_bot_eq_bot {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    ggLinImage (p := p) ι ⊥ = ⊥ := by
  ext v
  rw [mem_ggLinImage, Submodule.mem_bot, Subgroup.mem_bot]
  constructor
  · intro hv
    have h1 : Additive.toMul (ι.symm v) = 1 := Subtype.ext (by simpa using hv)
    have h2 : ι.symm v = 0 := by simpa using h1
    rw [← ι.apply_symm_apply v, h2, map_zero]
  · intro hv
    rw [hv]
    simp

private theorem exists_rootDiagUnit_ne_one_of_ne_bot {L : Type} [Field L]
    {A : Subgroup (ModGL .E6 L)} {a : ↥A → Fin Tag.E6.rank → Lˣ}
    (ha : ∀ u, rootDiagUnit .E6 (a u) = u) (hA0 : A ≠ ⊥) :
    ∃ u : ↥A, rootDiagUnit .E6 (a u) ≠ 1 := by
  by_contra h
  push Not at h
  exact hA0 ((Subgroup.eq_bot_iff_forall A).2 fun x hx => by
    have hx1 : (⟨x, hx⟩ : ↥A) = 1 := Subtype.ext ((ha ⟨x, hx⟩).symm.trans (h ⟨x, hx⟩))
    simpa using congrArg (fun y : ↥A => (y : ModGL .E6 L)) hx1)


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .E6 L p}
  {T₀ : Subgroup (ModGL .E6 L)}

private theorem e6Split_Γ_quasisimple_and_component_univ (hS : E6SplitLangTwo S) :
    CFSG.Open.IsQuasisimple ↥S.Γ ∧
      e6SplitComponent S (Finset.univ : Finset (ExcRaw.Root 1)) = S.Γ := by
  have : CharP L 2 :=
    CFSG.StandardType.LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1)
      (by rw [hS.1, pow_one])
  obtain ⟨-, -, -, -, hΓ, -⟩ := famTrivial_Γ_data (Or.inl rfl) S
  have hperf : ⁅S.Γ, S.Γ⁆ = S.Γ := by
    have hh : Subgroup.map S.Γ.subtype (commutator ↥S.Γ) = S.Γ := by
      rw [hΓ.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [show commutator ↥S.Γ = ⁅(⊤ : Subgroup ↥S.Γ), (⊤ : Subgroup ↥S.Γ)⁆ from rfl,
      Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at hh
    exact hh
  refine ⟨hΓ, commutator_rootSpan_inf_Γ_eq S ?_ hperf⟩
  intro γ hγ
  obtain ⟨i, hi⟩ := exists_mem_e6SplitCodeRoots_singleton hγ
  exact (mem_e6SplitCodeRoots_iff hi).2 (Finset.mem_univ i)

theorem isComponentOf_e6SplitComponent_of_occurs (hS : E6SplitLangTwo S)
    (d : E6SplitDatum S T₀) {A : Subgroup (ModGL .E6 L)} (hA : A ≤ T₀)
    {c : Finset (ExcRaw.Root 1)} (hadm : ExcRaw.admissible 1 c)
    (hc : ExcRaw.occurs 1 (ggLinImage (p := 3) d.coord A) c) :
    IsComponentOf (e6SplitComponent S c) (S.Γ ⊓ Subgroup.centralizer (A : Set (ModGL .E6 L))) := by
  classical
  have : CharP L 2 :=
    CFSG.StandardType.LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1)
      (by rw [hS.1, pow_one])
  by_cases hA0 : A = ⊥
  · subst A
    rw [ggLinImage_bot_eq_bot] at hc
    obtain rfl : c = Finset.univ := (ExcRaw.occurs_bot_iff (1 : Fin 6) c).1 hc
    obtain ⟨hΓ, hcomp⟩ := e6Split_Γ_quasisimple_and_component_univ hS
    rw [hcomp]
    exact (isComponentOf_Γ_inf_centralizer_bot_iff S hΓ S.Γ).2 rfl
  · obtain ⟨a, ha, hT, hap⟩ := exists_family_of_le_fullThreeTorus (hA.trans d.le_fullThreeTorus)
    have h1 := exists_rootDiagUnit_ne_one_of_ne_bot ha hA0
    obtain ⟨j, hR⟩ := E6SplitDatum.exists_kernelComponent_of_occurs hS d hA ha hc
    have hRc : rationalComponentM S.ρ S.Γ (famCharHom a) j = e6SplitComponent S c :=
      rationalComponentM_eq_e6SplitComponent j hR
    have hC : Subgroup.centralizer (Set.range fun u => rootDiagUnit .E6 (a u)) =
        Subgroup.centralizer (A : Set (ModGL .E6 L)) := centralizer_range_excFamily ha
    have hlabel := componentLabel_e6Split_eq_label hS hT j hc hR
      (n := componentOrbitLength S.ρ (componentRoots (famCharHom a) j)) (by rw [hS.1])
    have hΛ : CFSG.Assembly.LargeEvenInLambda2
        (componentLabel (compRank (componentRoots (famCharHom a) j))
          (componentRoots (famCharHom a) j).ncard
          (twistKindOf S.ρ (componentRoots (famCharHom a) j))
          (componentOrbitLength S.ρ (componentRoots (famCharHom a) j))) := by
      rw [hlabel]
      exact hadm.2
    have hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) j) :=
      isQuasisimple_rationalComponentM_of_lambda2 (Or.inl rfl) S Nat.prime_three (by norm_num)
        hT hap h1 j (n := componentOrbitLength S.ρ (componentRoots (famCharHom a) j))
        (by rw [hS.1]) hΛ
    have hsub := langFamSubnormal_of_mem_torus S hT j
    refine ⟨?_, ?_, ?_⟩
    · rw [← hRc, ← hC]
      exact hsub.1
    · rw [← hRc, ← hC]
      exact (CFSG.Assembly.IsSubnormal.iff_subgroupOf hsub.1).2 hsub.2
    · rw [← hRc]
      exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩

theorem exists_e6SplitCode_of_isComponentOf (hS : E6SplitLangTwo S) (d : E6SplitDatum S T₀)
    {A : Subgroup (ModGL .E6 L)} (hA : A ≤ T₀) {X : Subgroup (ModGL .E6 L)}
    (hX : IsComponentOf X (S.Γ ⊓ Subgroup.centralizer (A : Set (ModGL .E6 L)))) :
    ∃ c : Finset (ExcRaw.Root 1), ExcRaw.admissible 1 c ∧
      ExcRaw.occurs 1 (ggLinImage (p := 3) d.coord A) c ∧ X = e6SplitComponent S c := by
  classical
  have : CharP L 2 :=
    CFSG.StandardType.LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1)
      (by rw [hS.1, pow_one])
  by_cases hA0 : A = ⊥
  · subst A
    obtain ⟨hΓ, hcomp⟩ := e6Split_Γ_quasisimple_and_component_univ hS
    have hXΓ : X = S.Γ := (isComponentOf_Γ_inf_centralizer_bot_iff S hΓ X).1 hX
    refine ⟨Finset.univ, ExcRaw.admissible_univ (1 : Fin 6), ?_, by rw [hXΓ, hcomp]⟩
    rw [ggLinImage_bot_eq_bot]
    exact (ExcRaw.occurs_bot_iff (1 : Fin 6) Finset.univ).2 rfl
  · obtain ⟨a, ha, hT, hap⟩ := exists_family_of_le_fullThreeTorus (hA.trans d.le_fullThreeTorus)
    have h1 := exists_rootDiagUnit_ne_one_of_ne_bot ha hA0
    have hC : Subgroup.centralizer (Set.range fun u => rootDiagUnit .E6 (a u)) =
        Subgroup.centralizer (A : Set (ModGL .E6 L)) := centralizer_range_excFamily ha
    have hXopen : CFSG.Open.IsComponentOf X
        (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit .E6 (a u))) := by
      rw [hC]
      exact CFSG.Assembly.isComponentOf_iff_open.1 hX
    have hTame : ∀ i : KernelComponent (famCharHom a),
        CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
          Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
      fun i => langFamTame_of_prime (Or.inl rfl) S Nat.prime_three (by norm_num) hT hap h1 i
    obtain ⟨j, hXj, hq⟩ := exists_eq_rationalComponentM_of_isComponentOf_gen S Nat.prime_three
      (Or.inr (Or.inl rfl)) (by norm_num) hT hap h1 hTame hXopen
    obtain ⟨c, hocc, hr⟩ := E6SplitDatum.exists_occurs_of_kernelComponent hS d hA ha j
    have hR : rationalComponentM S.ρ S.Γ (famCharHom a) j = e6SplitComponent S c :=
      rationalComponentM_eq_e6SplitComponent j hr
    have hKasm : CFSG.Assembly.IsComponentOf (rationalComponentM S.ρ S.Γ (famCharHom a) j)
        (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit .E6 (a u))) := by
      have hsub := langFamSubnormal_of_mem_torus S hT j
      exact ⟨hsub.1, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hsub.1).2 hsub.2,
        ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩⟩
    have hK : CFSG.Open.IsComponentOf (rationalComponentM S.ρ S.Γ (famCharHom a) j)
        (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit .E6 (a u))) :=
      CFSG.Assembly.isComponentOf_iff_open.1 hKasm
    have hspan : rationalComponentM S.ρ S.Γ (famCharHom a) j ≤
        rootSpan .E6 L (rationalRootsM S.ρ (famCharHom a) j) :=
      (Subgroup.commutator_le_self _).trans inf_le_left
    obtain ⟨n, hn, hlab⟩ := langFamilyCompLabel_exc (Or.inl rfl) S Nat.prime_three
      (by norm_num) a hT hap hK j hspan
    have hlabel := componentLabel_e6Split_eq_label hS hT j hocc hr hn
    refine ⟨c, ⟨⟨ggLinImage (p := 3) d.coord A, hocc⟩, ?_⟩, hocc, hXj.trans hR⟩
    rw [← hlabel]
    exact hlab.1

theorem e6SplitCoreOccurs_holds : E6SplitCoreOccurs := by
  intro L _ _ p S hS T₀ d A hA X
  exact ⟨exists_e6SplitCode_of_isComponentOf hS d hA, fun ⟨c, hadm, hc, hX⟩ =>
    hX ▸ isComponentOf_e6SplitComponent_of_occurs hS d hA hadm hc⟩

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
