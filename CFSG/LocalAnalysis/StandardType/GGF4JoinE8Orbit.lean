module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcCore
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelected
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcOrbit
import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors
import CFSG.LieType.Chevalley.RootComponentType
import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourKac

public section

namespace CFSG.StandardType.F4JoinE8

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.StandardType.LieKnownR2.ExcPos CFSG.LieType.AlgebraicGroups
open CFSG.Open (StatedLieTag)

theorem not_guarded_of_labelIso_typeA {lab lab' : LargeEvenLabel}
    (hg : GuardedLargeEvenLabel lab) (hi : GGLabelIso lab lab')
    (ht : lab'.tag = .A ∨ lab'.tag = .twA) (hr : lab'.rank ≤ 4) : False := by
  unfold GGLabelIso at hi
  unfold GuardedLargeEvenLabel at hg
  rcases hi with rfl | ⟨-, h2, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · rcases hg with ⟨h | h, -⟩ | ⟨h | h, -⟩ | (h | h | h | h | h) | ⟨h, h5, -⟩ <;>
      rcases ht with ht | ht <;> first | omega | (rw [ht] at h; exact absurd h (by decide))
  · rcases ht with ht | ht <;> rcases h2 with h2 | h2 <;>
      (rw [ht] at h2; exact absurd h2 (by decide))
  all_goals
    rw [h] at hg
    simp at hg

section Cert


variable {G : Type} [Group G] {n f p : ℕ} {ψ : (ggU .E8 n f).K →* G}
  {G₀ L : Subgroup G} {x : G}

theorem orbit_eq_one_E8 (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center ↥G₀ = ⊥)
    (hLG0 : L ≤ G₀)
    (F : ExcLangFrame .E8 n f p ψ G₀ (Subgroup.zpowers x) (Subgroup.zpowers x) x)
    {i : KernelComponent (rootCharHom (F.coord x))}
    (hT : rootDiagUnit (langTag .E8) (F.coord x) ∈ F.setup.D.torus)
    (hap : ∀ j, F.coord x j ^ p = 1) (h1 : rootDiagUnit (langTag .E8) (F.coord x) ≠ 1)
    (hqs : CFSG.IsQuasisimple
      ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i))
    (hL : (L.subgroupOf G₀).map F.η =
      rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) (hg : GuardedLargeEvenLabel lab) :
    componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1 ∧
      4 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i) ∧
      (compRank (componentRoots (rootCharHom (F.coord x)) i) = 4 →
        (componentRoots (rootCharHom (F.coord x)) i).ncard = 24) := by
  have hτ : langTag StatedLieTag.E8 = Tag.E8 := rfl
  have hΨ : IsRootComponent (componentRoots (rootCharHom (F.coord x)) i) :=
    isRootComponent_componentRoots i
  have hne : (componentRoots (rootCharHom (F.coord x)) i).Nonempty := by
    obtain ⟨⟨α, hα⟩, rfl⟩ := Quotient.exists_rep i
    exact ⟨α, hα, rfl⟩
  have hsr := LangRat.componentOrbitLength_mul_compRank_le F.setup hT i
  have hs0 := (outer_componentOrbitLength_spec F.setup hT i).1
  have h8 : (langTag StatedLieTag.E8).rank = 8 := rfl
  have hhigh : 5 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i) →
      componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1 := by
    intro h5
    by_contra hne1
    have h2 : 2 ≤ componentOrbitLength F.setup.ρ
        (componentRoots (rootCharHom (F.coord x)) i) := by omega
    have := Nat.mul_le_mul_right (compRank (componentRoots (rootCharHom (F.coord x)) i)) h2
    omega
  obtain ⟨tD, -, htD, hsl, -, hcard, hN⟩ :=
    exists_dynkinType (Or.inr (Or.inr (Or.inr hτ))) hΨ hne
  have hr : compRank (componentRoots (rootCharHom (F.coord x)) i) = tD.rank := by
    rw [CFSG.HardMathSupport.Timmesfeld.RootAut.compRank_eq_card hΨ, hcard]
  cases tD with
  | A m =>
    rw [TauCeti.DynkinType.rank_A] at hr
    rw [TauCeti.DynkinType.numRoots_A] at hN
    by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i)
    · exact ⟨hhigh h5, by omega, fun h4 => by omega⟩
    · exfalso
      have hm0 : 0 < m := by
        have := TauCeti.DynkinType.rank_pos htD
        rwa [TauCeti.DynkinType.rank_A] at this
      have hA : 1 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i) ∧
          (componentRoots (rootCharHom (F.coord x)) i).ncard =
            compRank (componentRoots (rootCharHom (F.coord x)) i) *
              (compRank (componentRoots (rootCharHom (F.coord x)) i) + 1) :=
        ⟨by omega, by rw [hN, hr]⟩
      obtain ⟨lab', -, hrank', hinn, hsu, hRL⟩ :=
        TablePThreeKG.rationalLabel_typeA F.setup hp hT hap h1 i hA hqs
      have hkind : twistKind F.setup.ρ (rootCharHom (F.coord x)) i = .inner ∨
          twistKind F.setup.ρ (rootCharHom (F.coord x)) i = .suN := by
        unfold twistKind
        split_ifs with h₁ h₂ h₃ h₄
        · exact Or.inl rfl
        · exfalso
          rcases h₂ with ⟨h6, -⟩ | ⟨h4, h24, -⟩
          · omega
          · have hm4 : m = 4 := by omega
            subst hm4
            omega
        · exfalso
          obtain ⟨h4, h24⟩ := h₃
          have hm4 : m = 4 := by omega
          subst hm4
          rw [hr] at h24
          omega
        · exact Or.inr rfl
        · exact Or.inl rfl
      have htag : lab'.tag = .A ∨ lab'.tag = .twA := hkind.imp hinn hsu
      obtain ⟨hlab', hhas'⟩ := hRL
      have hηinj : Function.Injective F.η := (MonoidHom.ker_eq_bot_iff _).1 (F.ker_η.trans hZ)
      let ηL : ↥L →* ModGL (langTag StatedLieTag.E8) GGL := F.η.comp (Subgroup.inclusion hLG0)
      have hηLinj : Function.Injective ηL := hηinj.comp (Subgroup.inclusion_injective hLG0)
      have hηLrange : ηL.range =
          rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i := by
        rw [← hL]
        ext y
        constructor
        · rintro ⟨l, rfl⟩
          exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hLG0 l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
        · rintro hy
          obtain ⟨g, hg', rfl⟩ := Subgroup.mem_map.1 hy
          exact ⟨⟨g, Subgroup.mem_subgroupOf.1 hg'⟩, rfl⟩
      let e : ↥L ≃* ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i) :=
        (MonoidHom.ofInjective hηLinj).trans (MulEquiv.subgroupCongr hηLrange)
      let eZ := QuotientGroup.congr (Subgroup.center ↥L)
        (Subgroup.center ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i)) e
        (Subgroup.map_center_eq e)
      have hhasL := ggHasLabel_of_mulEquiv eZ.symm hhas'
      have hi := ggLabelRigidInput_holds lab lab' _ hlab hlab' hhas hhasL
      exact not_guarded_of_labelIso_typeA hg hi htag (by omega)
  | D m =>
    rw [TauCeti.DynkinType.rank_D] at hr
    rw [TauCeti.DynkinType.numRoots_D] at hN
    by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i)
    · exact ⟨hhigh h5, by omega, fun h4 => by omega⟩
    · have hm4 : m = 4 := by
        have := TauCeti.DynkinType.valid_D.1 htD
        omega
      subst hm4
      have hpL : ((p : ℕ) : GGL) ≠ 0 := RCKRP.rck_natCast_ne_zero_GGL hp hp2
      have hTp : rootDiagUnit (langTag StatedLieTag.E8) (F.coord x) ^ p = 1 :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
      have hc : (componentRoots (rootCharHom (F.coord x)) i).ncard = 24 := by
        rw [hN]
      let S : LangSetup Tag.E8 GGL 5 := F.setup
      have hTS : rootDiagUnit Tag.E8 (F.coord x) ∈ S.D.torus := hT
      have hTpS : rootDiagUnit Tag.E8 (F.coord x) ^ p = 1 := hTp
      obtain ⟨-, -, hρ⟩ := S.d4_pinnedT_of_prime hp hpL
        CFSG.HardMathSupport.Timmesfeld.CrossChar.facts_E8 kacCount_E8_four
        (by decide) (by decide)
        (fun y hy => far_d4_E8 y fun z hz => by
          have h := hy z hz
          rwa [CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.Adj, extRoot_eq_extRootOf] at h)
        ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hTS hTpS i
        hr hc
      have hfin : (componentRoots (rootCharHom (F.coord x)) i).Finite :=
        (finite_setOf_isRoot (langTag StatedLieTag.E8)).subset fun γ hγ => hγ.1.1
      exact ⟨componentOrbitLength_eq_one hfin hρ, by omega, fun _ => hc⟩
  | E6 =>
    rw [TauCeti.DynkinType.rank_E6] at hr
    exact ⟨hhigh (by omega), by omega, fun h4 => by omega⟩
  | E7 =>
    rw [TauCeti.DynkinType.rank_E7] at hr
    exact ⟨hhigh (by omega), by omega, fun h4 => by omega⟩
  | E8 =>
    rw [TauCeti.DynkinType.rank_E8] at hr
    exact ⟨hhigh (by omega), by omega, fun h4 => by omega⟩
  | B m => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_B m)
  | C m => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_C m)
  | F4 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_F4
  | G2 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_G2

end Cert

end CFSG.StandardType.F4JoinE8

end
