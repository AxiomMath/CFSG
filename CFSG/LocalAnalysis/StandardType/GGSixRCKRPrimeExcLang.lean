module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpLang

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RCKC1 CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem rckExc_lang_component_of_toralFrame
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (ht : GGExcFive t) (hcfg : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    {θ : ↥G₀ →* ModGL (langTag t) GGL} {A' : Subgroup (ModGL (langTag t) GGL)}
    (hfr : RCKBridgeFrame t f p G₀ A θ A') (hT : IsToralSubgroup (langTag t) GGL A') :
    ∃ (η : ↥G₀ →* ModGL (langTag t) GGL) (E' : Subgroup (ModGL (langTag t) GGL))
      (S : LangSetup (langTag t) GGL 5) (a : Fin (langTag t).rank → GGLˣ)
      (i : KernelComponent (rootCharHom a)) (w : WeylGroup (langTag t)),
      η.ker = Subgroup.center ↥G₀ ∧
      η.range = S.Γ ∧
      S.D.q = 2 ^ f ∧
      S.D.Φ = ggPhi t f ∧
      S.D.n = canonicalRep (coxeterSystem (langTag t)) GGL w ∧
      η = (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp θ ∧
      E' = A'.map (MulAut.conj S.D.g0⁻¹).toMonoidHom ∧
      E' ≤ S.D.torus ∧
      IsElemAbelian p E' ∧
      Nat.card E' = Nat.card A ∧
      (∀ d ∈ A, ∃ a' ∈ E', GGLiePartner G₀ η d a') ∧
      (∀ a' ∈ E', ∃ d ∈ A, GGLiePartner G₀ η d a') ∧
      rootDiagUnit (langTag t) a ∈ E' ∧
      rootDiagUnit (langTag t) a ≠ 1 ∧
      (∀ j, a j ^ p = 1) ∧
      GGLiePartner G₀ η e (rootDiagUnit (langTag t) a) ∧
      ((K.subgroupOf G₀).map η) = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
    hp4, hSC, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
    hJnotA6, hRJ, hRmJ, hRootJ, heD, he1, hKcomp, hJK, hOddK⟩ := hcfg
  obtain ⟨hθker, hθrange, hA'le, hA'el, hA'card, hfwd, hbwd⟩ := hfr
  exact rckExc_lang_component_core ht hGG hp hp2 hAnorm hAc (hB1A (hDB1 heD)) he1 hKcomp θ A'
    hθker hθrange hA'le hA'el hA'card hfwd hbwd hT

end CFSG.StandardType.RCKRP
