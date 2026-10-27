module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcLang
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RCKC1 CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag IsElemAbelian)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

@[expose] def RCKFirstPassAt
    {X : Type} [Group X] (t : StatedLieTag) (f p : ℕ) (G₀ A B₁ D J K : Subgroup X) (e : X)
    (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL))
    (η : ↥G₀ →* ModGL (langTag t) GGL) (E' : Subgroup (ModGL (langTag t) GGL))
    (S : LangSetup (langTag t) GGL 5) (a : Fin (langTag t).rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) : Prop :=
  RCKBridgeFrame t f p G₀ A θ A' ∧ IsToralSubgroup (langTag t) GGL A' ∧ K ≤ G₀ ∧
    η.ker = Subgroup.center ↥G₀ ∧ η.range = S.Γ ∧ S.D.q = 2 ^ f ∧ S.D.Φ = ggPhi t f ∧
    η = (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp θ ∧
    E' = A'.map (MulAut.conj S.D.g0⁻¹).toMonoidHom ∧ E' ≤ S.D.torus ∧
    IsElemAbelian p E' ∧
    (∀ d ∈ A, ∃ a' ∈ E', GGLiePartner G₀ η d a') ∧
    rootDiagUnit (langTag t) a ∈ E' ∧ rootDiagUnit (langTag t) a ≠ 1 ∧ (∀ j, a j ^ p = 1) ∧
    GGLiePartner G₀ η e (rootDiagUnit (langTag t) a) ∧
    ((K.subgroupOf G₀).map η) = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
    CFSG.Assembly.IsQuasisimple ↥K ∧ Odd (Nat.card (Subgroup.center ↥K)) ∧
    B₁ ≤ Subgroup.normalizer (K : Set X) ∧
    ∃ d ∈ D, d ∉ Subgroup.zpowers e ∧ IsComponentOf J (K ⊓ Subgroup.centralizer {d})

theorem rckExc_firstPass
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (ht : GGExcFive t) (hcfg : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    (hframe : RCKToralFrame t f p G₀ A) :
    ∃ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL))
      (η : ↥G₀ →* ModGL (langTag t) GGL) (E' : Subgroup (ModGL (langTag t) GGL))
      (S : LangSetup (langTag t) GGL 5) (a : Fin (langTag t).rank → GGLˣ)
      (i : KernelComponent (rootCharHom a)),
      RCKFirstPassAt t f p G₀ A B₁ D J K e θ A' η E' S a i := by
  obtain ⟨θ, A', hfr, hT⟩ := hframe
  obtain ⟨η, E', S, a, i, w, hker, hrange, hq, hΦ, -, hη, hE', hEt, hEel, -, hfwd, -, hrE, hr1,
    hap, hpe, hK, hqs⟩ := rckExc_lang_component_of_toralFrame ht hcfg hfr hT
  obtain ⟨hB1N, hd⟩ := rckRP_stepA hcfg
  have hcfg' := hcfg
  unfold RCKRPConfig at hcfg'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hKcomp, -, hoddK⟩ := hcfg'
  have hKG : K ≤ G₀ := hKcomp.1.trans inf_le_left
  exact ⟨θ, A', η, E', S, a, i, hfr, hT, hKG, hker, hrange, hq, hΦ, hη, hE', hEt, hEel, hfwd, hrE,
    hr1, hap, hpe, hK, hqs, hKcomp.2.2, hoddK, hB1N, hd⟩

end CFSG.StandardType.RCKRP
