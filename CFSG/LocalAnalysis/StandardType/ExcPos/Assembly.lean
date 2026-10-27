module

public import CFSG.LocalAnalysis.StandardType.ExcPos.RankOneJoint
public import CFSG.LocalAnalysis.StandardType.ExcPos.NeighbourComponent

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
import CFSG.LocalAnalysis.StandardType.ExcPos.PacketBasic
import CFSG.LocalAnalysis.StandardType.ExcPos.ContainingComponent
import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors
import CFSG.LocalAnalysis.StandardType.ExcPos.StrictNeighbourAlt
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ExcPosBasics
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace ExcPacket

variable
  {X : Type} [Group X] {τ : Tag} {f p : ℕ} {G₀ B₁ D J : Subgroup X} {x : X}
  {R Rm : Subgroup X} (P : ExcPacket τ f p G₀ B₁ D J x R Rm)

private theorem excAsm_eq_containingComponent {e : X}
    (hker : kernelRoots P.chiD ⊆ kernelRoots (P.chiAt e)) {iK : KernelComponent (P.chiAt e)}
    (hsub : P.rootsJ ⊆ componentRoots (P.chiAt e) iK) :
    iK = containingComponent hker P.iJ :=
  eq_containingComponent_of_mem hker P.α_mem (hsub P.α_mem)

theorem componentOrbitLength_eq_one_of_b_eq_one (hDB : D ≤ B₁) {e : X} (he : e ∈ D)
    {iK : KernelComponent (P.chiAt e)} (hsub : P.rootsJ ⊆ componentRoots (P.chiAt e) iK)
    (hb : P.b = 1) : componentOrbitLength P.ρ (componentRoots (P.chiAt e) iK) = 1 := by
  rw [excAsm_eq_containingComponent P (P.kernelRoots_chiD_subset hDB he) hsub]
  exact componentOrbitLength_containingComponent_eq_one _ (P.mapsTo_rho_chiAt he)
    P.frob.iform_eq hb

theorem componentOrbitLength_eq_one_of_b_eq_two (hτ : τ = .E6) (hDB : D ≤ B₁) {e : X}
    (he : e ∈ D) {iK : KernelComponent (P.chiAt e)}
    (hsub : P.rootsJ ⊆ componentRoots (P.chiAt e) iK)
    (hne : componentRoots (P.chiAt e) iK ≠ P.rootsJ) (hrank : 2 ≤ compRank P.rootsJ)
    (hb : P.b = 2) : componentOrbitLength P.ρ (componentRoots (P.chiAt e) iK) = 1 := by
  have hker := P.kernelRoots_chiD_subset hDB he
  obtain rfl := excAsm_eq_containingComponent P hker hsub
  obtain ⟨i₂, h₂⟩ := exists_image_componentRoots P.mapsTo_rho_chiD P.frob.iform_eq P.iJ
  have hK₂ := containingComponent_equivariant hker (P.mapsTo_rho_chiAt he) P.frob.iform_eq h₂
  by_cases hstab : containingComponent hker P.iJ = containingComponent hker i₂
  · have himg : (P.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) ''
        componentRoots (P.chiAt e) (containingComponent hker P.iJ) =
          componentRoots (P.chiAt e) (containingComponent hker P.iJ) := by
      rw [hK₂, ← hstab]
    exact componentOrbitLength_eq_one (kernelRoots_finite.subset fun _ h => h.1)
      fun γ hγ => himg.subset (Set.mem_image_of_mem _ hγ)
  · exfalso
    have hij : P.iJ ≠ i₂ := by
      rintro rfl
      exact P.image_rootsJ_ne_of_b_eq_two hb h₂
    have hcard : (componentRoots P.chiD P.iJ).ncard = (componentRoots P.chiD i₂).ncard := by
      rw [← h₂, Set.ncard_image_of_injective _ P.ρ.injective]
    obtain ⟨hr₁, -, hr₂, -⟩ := twE6_twoOrbit_is_A2_pair hτ P.chiD hij hrank hcard
    rcases twE6_strictNeighbour_orbit_one hτ P.chiD (P.chiAt e) hstab hr₁ hr₂
        (componentRoots_subset_containingComponent hker P.iJ)
        (componentRoots_subset_containingComponent hker i₂) with h | h
    · exact hne h.symm
    · apply hne
      apply Set.image_injective.mpr P.ρ.injective
      rw [hK₂, ← h, ← h₂]
      rfl

end ExcPacket


private theorem excAsm_packet (hU1a : ExcU1a) (hU1b : ExcU1b) (hUR : ExcUR)
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X} (hH : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) :
    ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 t n f p ψ R Rm ∧
      ∃ P : ExcPacket (GGFinModel.langTag t) f p G₀ B₁ D J x R Rm, P.b = 2 → t = .twistedE6 := by
  have hsplit : t = .E6 ∨ t = .E7 ∨ t = .E8 → ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧
      GGRootPosG0 t n f p ψ R Rm ∧
      ∃ P : ExcPacket (GGFinModel.langTag t) f p G₀ B₁ D J x R Rm, P.b = 2 → t = .twistedE6 := by
    intro h
    obtain ⟨R, Rm, hRJ, hRmJ, hpos, P, hb⟩ := hU1a t h X n f ψ p G₀ B₁ D J L x hH
    exact ⟨R, Rm, hRJ, hRmJ, hpos, P, fun h2 => by omega⟩
  rcases ht with h | h | h | rfl
  · exact hsplit (Or.inl h)
  · exact hsplit (Or.inr (Or.inl h))
  · exact hsplit (Or.inr (Or.inr h))
  · by_cases hres : p = 3 ∧ 3 ∣ 2 ^ f + 1 ∧ ¬ 9 ∣ 2 ^ f + 1
    · obtain ⟨R, Rm, hRJ, hRmJ, hpos, P, -⟩ :=
        hUR X n f ψ p G₀ B₁ D J L x hH hres.1 hres.2.1 hres.2.2
      exact ⟨R, Rm, hRJ, hRmJ, hpos, P, fun _ => rfl⟩
    · obtain ⟨R, Rm, hRJ, hRmJ, hpos, ⟨P⟩⟩ := hU1b X n f ψ p G₀ B₁ D J L x hH hres
      exact ⟨R, Rm, hRJ, hRmJ, hpos, P, fun _ => rfl⟩

theorem excNbr_of_packet (hUK : ExcUK) (hU3 : ExcU3) (hU5 : ExcU5) (hU7 : ExcU7)
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X} (hH : GGSixPosHyp t n f ψ p G₀ B₁ D J L x)
    {R Rm : Subgroup X} (hRJ : R ≤ J) (hRmJ : Rm ≤ J) (hpos : GGRootPosG0 t n f p ψ R Rm)
    (P : ExcPacket (GGFinModel.langTag t) f p G₀ B₁ D J x R Rm)
    (hb : P.b = 2 → t = .twistedE6) :
    ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
      Odd (Nat.card (Subgroup.center ↥K)) → K = G₀ ∨ GGThmSRangeAt K R := by
  intro e he he1 K hKG₀ hKcomp hJK hKne hKodd
  by_cases hKG : K = G₀
  · exact Or.inl hKG
  refine Or.inr (exc_neighbour_in_range K R ?_)
  have hDB : D ≤ B₁ := hH.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨iK, hsub, hspan, heq⟩ :=
    hUK t ht X n f ψ p G₀ B₁ D J L x hH R Rm P e he he1 K hKG₀ hKcomp hJK hKodd
  have hne : componentRoots (P.chiAt e) iK ≠ P.rootsJ := fun h => hKne (heq h)
  have hrank : 2 ≤ compRank P.rootsJ := hU3 t ht X n f ψ p G₀ B₁ D J L x hH R Rm P
  rcases P.b_eq_one_or_two with hb1 | hb2
  · exact hU5 t ht X n f ψ p G₀ B₁ D J L x hH R Rm P hRJ hRmJ hpos hb1 e he he1 K hKG₀ hKcomp
      hJK hKne hKodd hKG iK hsub hne hspan
      (P.componentOrbitLength_eq_one_of_b_eq_one hDB he hsub hb1) hrank
      (strictNeighbour_not_a3Case hH he hKG₀ hKcomp hJK hKne hKodd)
  · obtain rfl := hb hb2
    obtain ⟨β, hf, hβ, h2β, hvia⟩ := hU7 X n f ψ p G₀ B₁ D J L x hH R Rm P hRJ hRmJ hpos hb2
      e he he1 K hKG₀ hKcomp hJK hKne hKodd hKG iK hsub hne hspan
      (P.componentOrbitLength_eq_one_of_b_eq_two rfl hDB he hsub hne hrank hb2) hrank
    exact Or.inr (Or.inr (Or.inl ⟨f, β, hf, hβ, h2β, hvia⟩))

theorem ggSixExcPosExplicit_of_units
    (hU1a : ExcU1a) (hU1b : ExcU1b) (hUR : ExcUR)
    (hU5 : ExcU5) (hU7 : ExcU7)
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) :
    GGSixExcPosExplicit t := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hH
  obtain ⟨R, Rm, hRJ, hRmJ, hpos, P, hb⟩ := excAsm_packet hU1a hU1b hUR ht hH
  exact ⟨R, Rm, hRJ, hRmJ, hpos,
    excNbr_of_packet excUK_holds excU3_holds hU5 hU7 ht hH hRJ hRmJ hpos P hb⟩

end CFSG.StandardType.LieKnownR2.ExcPos

end
