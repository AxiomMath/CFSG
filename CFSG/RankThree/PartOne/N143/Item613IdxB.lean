module

public import CFSG.RankThree.PartOne.N143.Item613IdxDefs
public import CFSG.RankThree.PartOne.N143X.Item613Plane
public import CFSG.RankThree.PartOne.N143X.InnerPlaneClassical
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.RankThree.PartOne.S11c.OddClassicalPlane
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartOne.N143X.InnerPlaneG2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Census3
  CFSG.RankThree.PartOne.N143X TauCeti
open scoped commutatorElement

theorem item613AtIdx_of_inner_planes {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hpl : ∀ p : ℕ, p.Prime → 5 ≤ p → Subgroup.center X = ⊥ →
      ∀ (E' : Subgroup (MulAut X)) (U : Subgroup X), PlaneOn p E' U →
        E' ≤ (MulAut.conj : X →* MulAut X).range → PlaneCentralizes E' U) :
    Item613AtIdx X := by
  intro p hp hp7 E hE hcard hex
  obtain ⟨S, hS1, hS2, hEN, hSE⟩ := hex
  exfalso
  have : IsElementaryAbelian p E := hE
  have hnab := SPOR.nonabelian_of_plane hp hcard
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_simple hnab
  exact item613_false_of_inner_planes hZ hp (by omega) (hpl p hp (by omega) hZ) hcard hS1 hS2
    hEN hSE

theorem item613Idx_item2 : Item613IdxFor Census3.ThmThreeItem2 := by
  intro X _ _ hs h
  obtain ⟨q, hq2, -, hA | hU⟩ := h
  · obtain ⟨hv, ⟨e⟩⟩ := hA
    have hmod : StatedClassicalModel X .PSL 3 q.p q.exponent :=
      statedClassicalModel_of_isoLie_A (r := 2) hv e
    refine item613AtIdx_of_inner_planes ?_
    intro p hp hp5 hZ E' U hplane hE
    exact planeCentralizes_inner_psl hZ (by norm_num) (by norm_num) q.prime_p hq2 hmod hplane hE
      degreeFourPlane
  · obtain ⟨hv, ⟨e⟩⟩ := hU
    have hmod : StatedClassicalModel X .PSU 3 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    refine item613AtIdx_of_inner_planes ?_
    intro p hp hp5 hZ E' U hplane hE
    exact planeCentralizes_inner_psu hZ (by norm_num) (by norm_num) q.prime_p hq2 hmod hplane hE
      degreeFourPlane

theorem item613Idx_item4
    : Item613IdxFor Census3.ThmThreeItem4 := by
  intro X _ _ hs h
  obtain ⟨q, hq2, -, hG | hB | hU | hA⟩ := h
  · obtain ⟨hv, ⟨e⟩⟩ := hG
    have hmod : ChevalleyExceptionalModel X .G2 q.p q.exponent :=
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e
        (CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_of_odd q hv hq2)
    refine item613AtIdx_of_inner_planes ?_
    intro p hp hp5 hZ E' U hplane hE
    exact planeCentralizes_inner_G2 q.prime_p hq2 hmod hplane hE
  · obtain ⟨hv, ⟨e⟩⟩ := hB
    have hmod : StatedClassicalModel X .PSp 2 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    refine item613AtIdx_of_inner_planes ?_
    intro p hp hp5 hZ E' U hplane hE
    exact planeCentralizes_inner_psp_four hZ q.prime_p hq2 hmod hplane hE degreeFourPlane
  · obtain ⟨hv, ⟨e⟩⟩ := hU
    have hmod : StatedClassicalModel X .PSU 4 q.p q.exponent :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    refine item613AtIdx_of_inner_planes ?_
    intro p hp hp5 hZ E' U hplane hE
    exact planeCentralizes_inner_psu hZ (by norm_num) (by norm_num) q.prime_p hq2 hmod hplane hE
      degreeFourPlane
  · obtain ⟨hv, ⟨e⟩⟩ := hA
    have hmod : StatedClassicalModel X .PSL 4 q.p q.exponent :=
      statedClassicalModel_of_isoLie_A (r := 3) hv e
    refine item613AtIdx_of_inner_planes ?_
    intro p hp hp5 hZ E' U hplane hE
    exact planeCentralizes_inner_psl hZ (by norm_num) (by norm_num) q.prime_p hq2 hmod hplane hE
      degreeFourPlane

end CFSG.RankThree.PartOne.N143
