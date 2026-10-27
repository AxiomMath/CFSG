module

public import CFSG.RepresentationTheory.SzMartineau.LemmaTwo
public import CFSG.RepresentationTheory.SzMartineau.Ext
public import CFSG.RepresentationTheory.SzMartineau.CompRed
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof
public import CFSG.RankThree.GF2n.Tim77Prop24TwoSz

public section

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

theorem martineauSzInput_holds :
    CFSG.RankThree.GF2n.MartineauSzInput := by
  intro a ha V _ _ _ ρ ⟨g₀, hg₀, hfpf⟩
  have hg₀5 : g₀ ^ 5 = 1 := by
    rw [← hg₀]
    exact pow_orderOf_eq_one g₀
  refine exists_decomp_of_simple_of_cocycle (act := natAct a) (g₀ := g₀) hg₀5 ?_ ?_
    V ρ hfpf
  · intro W _ _ _ ρW hfpfW hnt hsimple
    simpa only [natAct_apply] using
      szFpfSimpleNatural_of_certificate a ha W ρW ⟨g₀, hg₀, hfpfW⟩ hnt hsimple
  · intro Y hY
    exact addCocycle_eq_coboundary_of (a := a)
      (fun c _ Y hY => isTwistedCocycle_eq_coboundary ha c hY) Y hY

end CFSG.RepresentationTheory.SzMartineau
