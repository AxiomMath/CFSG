module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcCore
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcOrbit
import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel

public section

namespace CFSG.StandardType.FieldTwoExc

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.StandardType.LieKnownR2.ExcPos CFSG.LieType.AlgebraicGroups
open CFSG.Open (StatedLieTag)

section Shapes

theorem ncard_eq_two_of_compRank_eq_one
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) (h1 : compRank Ψ = 1) :
    Ψ.ncard = 2 := by
  obtain ⟨t, ht, hsl, hr, hN⟩ := exists_dynkinType_compRank hτ hΨ (by omega)
  rw [hN]
  cases t with
  | A n =>
    rw [TauCeti.DynkinType.rank_A] at hr
    rw [TauCeti.DynkinType.numRoots_A, ← hr, h1]
  | B n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_B n)
  | C n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_C n)
  | D n =>
    rw [TauCeti.DynkinType.rank_D] at hr
    have := TauCeti.DynkinType.valid_D.1 ht
    omega
  | E6 => rw [TauCeti.DynkinType.rank_E6] at hr; omega
  | E7 => rw [TauCeti.DynkinType.rank_E7] at hr; omega
  | E8 => rw [TauCeti.DynkinType.rank_E8] at hr; omega
  | F4 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_F4
  | G2 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_G2

variable {τ : Tag} {L : Type} [Field L]

theorem four_le_compRank_of_twoD {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} {i : KernelComponent χ}
    (h : twistKind ρ χ i = .twoD) : 4 ≤ compRank (componentRoots χ i) := by
  unfold twistKind at h
  split_ifs at h with h1 h2 h3 h4
  exact h3.1

theorem exc_cases {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} {i : KernelComponent χ}
    (h : twistKind ρ χ i = .exc) :
    (compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
      (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
        ¬ twistInner (componentRoots χ i)
          ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]) ∧
        ¬ twistInner (componentRoots χ i)
          ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ (componentRoots χ i)])) := by
  unfold twistKind at h
  split_ifs at h with h1 h2
  rcases h2 with h2 | ⟨h4, h24, hsq⟩
  · exact Or.inl h2
  · exact Or.inr ⟨h4, h24, h1, hsq⟩

theorem typeA_of_compRank_le_three
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ} {i : KernelComponent χ}
    (hstd : RCKRP.RCKADEShape ρ χ i) (h3 : compRank (componentRoots χ i) ≤ 3) :
    1 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) + 1) := by
  rcases hstd with h | ⟨-, h2, hn⟩ | hsu | ⟨-, h4, -⟩ | htw | ⟨-, hE⟩ | hex
  · exact ⟨by omega, by
      rw [ncard_eq_two_of_compRank_eq_one hτ (isRootComponent_componentRoots i) h, h]⟩
  · exact ⟨by omega, hn⟩
  · obtain ⟨h2, hn⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.suN_rank_ncard hsu
    exact ⟨by omega, hn⟩
  · omega
  · have := four_le_compRank_of_twoD htw
    omega
  · rcases hE with ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ <;> omega
  · rcases exc_cases hex with ⟨h6, -⟩ | ⟨h4, -⟩ <;> omega

end Shapes

section Orbit


variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {n : ℕ} {ψ : (ggU t n 1).K →* G}
  {G₀ L : Subgroup G} {x : G}

omit
  [Finite G] in
theorem orbit_eq_one_of_two_mul_lt
    (F : ExcLangFrame t n 1 3 ψ G₀ (Subgroup.zpowers x) (Subgroup.zpowers x) x)
    {i : KernelComponent (rootCharHom (F.coord x))}
    (hT : rootDiagUnit (langTag t) (F.coord x) ∈ F.setup.D.torus)
    (hr : (langTag t).rank < 2 * compRank (componentRoots (rootCharHom (F.coord x)) i)) :
    componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1 := by
  have hsr := LangRat.componentOrbitLength_mul_compRank_le F.setup hT i
  have hs0 := (outer_componentOrbitLength_spec F.setup hT i).1
  by_contra hne
  have h2 : 2 ≤ componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) := by
    omega
  have := Nat.mul_le_mul_right (compRank (componentRoots (rootCharHom (F.coord x)) i)) h2
  omega

theorem orbit_eq_one_of_typeA {B Bs : Subgroup G} {D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hLG0 : L ≤ G₀) (hZ : Subgroup.center ↥G₀ = ⊥)
    (F : ExcLangFrame t n 1 3 ψ G₀ (Subgroup.zpowers x) (Subgroup.zpowers x) x)
    {i : KernelComponent (rootCharHom (F.coord x))}
    (hT : rootDiagUnit (langTag t) (F.coord x) ∈ F.setup.D.torus)
    (hap : ∀ j, F.coord x j ^ 3 = 1) (h1 : rootDiagUnit (langTag t) (F.coord x) ≠ 1)
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i))
    (hL : (L.subgroupOf G₀).map F.η =
      rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i)
    (hA : 1 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i) ∧
      (componentRoots (rootCharHom (F.coord x)) i).ncard =
        compRank (componentRoots (rootCharHom (F.coord x)) i) *
          (compRank (componentRoots (rootCharHom (F.coord x)) i) + 1)) :
    componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1 ∧
      2 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i) ∧
      (twistKind F.setup.ρ (rootCharHom (F.coord x)) i = .suN →
        3 ≤ compRank (componentRoots (rootCharHom (F.coord x)) i)) := by
  have hηinj : Function.Injective F.η := (MonoidHom.ker_eq_bot_iff _).1 (F.ker_η.trans hZ)
  let ηL : ↥L →* ModGL (langTag t) GGL := F.η.comp (Subgroup.inclusion hLG0)
  have hηLinj : Function.Injective ηL := hηinj.comp (Subgroup.inclusion_injective hLG0)
  have hηLrange : ηL.range =
      rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i := by
    rw [← hL]
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hLG0 l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
    · rintro hy
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨g, Subgroup.mem_subgroupOf.1 hg⟩, rfl⟩
  let e : ↥L ≃* ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i) :=
    (MonoidHom.ofInjective hηLinj).trans (MulEquiv.subgroupCongr hηLrange)
  let eZ := QuotientGroup.congr (Subgroup.center ↥L)
    (Subgroup.center ↥(rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord x)) i)) e
    (Subgroup.map_center_eq e)
  obtain ⟨c, hc, hc1, hcne, -, -, hhasc⟩ := hC.exists_markedModel_and_hasLabel_of_qTwo hq
  obtain ⟨lab, hdeg, hrank, hinn, hsu, hRL⟩ :=
    TablePThreeKG.rationalLabel_typeA F.setup Nat.prime_three hT hap h1 i hA hqs
  have hn1 : lab.n = 1 := by
    obtain ⟨hlab, hhas⟩ := hRL
    have hhasL := ggHasLabel_of_mulEquiv eZ.symm hhas
    have hi := ggLabelRigidInput_holds c lab _ hc hlab hhasc hhasL
    rcases hi.n_cases with h | ⟨ht', hr⟩ | hdouble
    · rw [← h, hc1]
    · exfalso
      apply hcne
      cases c
      simp only [LargeEvenLabel.mk.injEq] at ht' hr hc1 ⊢
      exact ⟨ht', hr, hc1⟩
    · have := hlab.1
      omega
  have hΛ := hRL.1
  have hq2 : F.setup.D.q = 2 := F.q_eq
  have hs1 : componentOrbitLength F.setup.ρ (componentRoots (rootCharHom (F.coord x)) i) = 1 := by
    rw [hn1, hq2, pow_one] at hdeg
    exact (Nat.pow_right_injective (le_refl 2) (hdeg.symm.trans (pow_one 2).symm))
  refine ⟨hs1, ?_, fun hk => ?_⟩
  · by_contra hlt
    have hr1 : compRank (componentRoots (rootCharHom (F.coord x)) i) = 1 := by
      have := hA.1
      omega
    have htag := hinn
      (CFSG.LocalAnalysis.GLTheoremA.RationalModel.twistKind_eq_inner_of_compRank_eq_one
        F.setup i hr1)
    obtain ⟨tag, rk, nn⟩ := lab
    simp only at htag hrank hn1
    subst htag hn1
    simp [LargeEvenInLambda2, hrank, hr1] at hΛ
  · by_contra hlt
    have hr2 : compRank (componentRoots (rootCharHom (F.coord x)) i) = 2 := by
      have := (CFSG.HardMathSupport.Timmesfeld.CrossChar.suN_rank_ncard hk).1
      omega
    have htag := hsu hk
    obtain ⟨tag, rk, nn⟩ := lab
    simp only at htag hrank hn1
    subst htag hn1
    simp [LargeEvenInLambda2, hrank, hr2] at hΛ


end Orbit

end CFSG.StandardType.FieldTwoExc

end
