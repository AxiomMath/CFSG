module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthALRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthD4Excl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthD4Unreal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthD4Mark
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthD4Comp
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

theorem ggOrth_caseD4
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    (hFix : GGSecFiveFixInput) (hRQ : GGReflRealizedQFourNbrInput) (hTBJ : GGSecFiveTBJTypeD4Input)
    (hKSL : GGSecFiveOrthKSLInput) (hD4 : GGSecFiveOrthD4ExclInput) (hd : Module.finrank (ZMod 3) V = 5)
    (hD : GGWeylOfType 3 (ggCoxeterMatrixD 4) (ggAutomizer L Bs)) (hpres : GGOrthPres L .POmegaPlus 4) : False := by
  obtain ⟨c₁, c₂, y, K, hne, _hc₁, hc₂, hnb, hLcls, ⟨s, hsK, hsr, hsc⟩, _hKW, _hKG2,
    _hJK, _hJL, _hLK, _hKL, _hWA, hB⟩ := GGOrthSetup.exists_nbr S hL hP hPump hFix
  have hunreal : ¬ GGRealized 3 Bs s :=
    ggOrthD4_unreal S hL hP hd hc₂ hne hLcls hsr hsc
  obtain ⟨hx3, hxnorm, hnoncent, hmark⟩ := ggOrthD4_marking S hRQ hnb hsK hsr hunreal
  have hcomp : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({x} : Set G) ⊓ K) :=
    ggOrthD4_component S hL hP hnb
  obtain ⟨f, ψ, hadm, _hrank, hker, hrange, h3⟩ := hpres
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf1 : 1 ≤ f := hadm.2.1
    have hlt : f < 2 := by omega
    interval_cases f
    norm_num at h3
  have hmodel : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 f :=
    hTBJ G 3 B Bs x L D J 𝒦 S.cfg S.split f ψ hadm hker hrange
  obtain ⟨m, hm8, _hcen, ⟨e⟩⟩ :=
    hKSL G K J x hx3 hxnorm hnoncent hmark hcomp ⟨f, hf2, hmodel⟩
  exact hD4 G 3 B Bs x L D J 𝒦 S.cfg S.split S.fixA rfl V Q S.nondeg ι hd S.orth hD y K hnb
    ⟨m, hm8, ⟨e⟩⟩ hcomp ⟨f, hf2, hmodel⟩ hB

end CFSG.StandardType.OrthF3

end
