module

public import CFSG.RankThree.PartOne.K133X.CharTwo
public import CFSG.RankThree.PartOne.K133X.Cent
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.Sporadic.Schreier.LargeReeExcl
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.RankThree.PartOne.K133X

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification TauCeti CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.OutStructure CFSG.RankThree.PartOne.S13K
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem reeTitsModel_twistedF4_of_isoLie {X : Type} [Group X] {m : ℕ} (hiso : IsoLie X (.reeF4 m)) :
    1 ≤ m ∧ ReeTitsModel X .twistedF4 2 (2 * m + 1) := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  let e : X ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩ := e0
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  have hm1 : 1 ≤ m :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  exact ⟨hm1, ⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
    ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
      ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩

theorem generalizedFitting_subgroup_eq_top_of_simple' {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] :
    GeneralizedFitting.subgroup X = ⊤ :=
  (CFSG.generalizedFitting_eq_componentClassification X).symm.trans
    (CFSG.Adapters.generalizedFitting_eq_top_of_isSimpleGroup X)

theorem charTwoCent_twistedF4 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hne : ∃ a b : X, a * b ≠ b * a) {f : ℕ} (hmodel : ReeTitsModel X .twistedF4 2 f) :
    CharTwoCent X := by
  intro u hu2
  have hF : GeneralizedFitting.subgroup X = ⊤ := generalizedFitting_subgroup_eq_top_of_simple'
  let eF : GeneralizedFitting.subgroup X ≃* X :=
    (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
  have hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X) := eF.isSimpleGroup
  have hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hne
    exact ⟨eF.symm x, eF.symm y, fun h => hxy (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hmodelF : ReeTitsModel (GeneralizedFitting.subgroup X) .twistedF4 2 f :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv eF hmodel
  have hno := Sporadic.Schreier.LargeReeExcl.CTU_catalog_large_Ree_Tits_check X hsimple hnab
    .twistedF4 f (.inl rfl) hmodelF
  have hcore : CFSG.oddCore ↥(Subgroup.centralizer ({u} : Set X)) = ⊥ := by
    by_contra h
    exact hno ⟨u, hu2, h⟩
  have hcomp : CatLeaf.InvolutionCentralizersComponentFree X :=
    CatLeaf.involutionCentralizersComponentFree_reeTits (.inl rfl) hmodel
  exact isCharacteristicP_two_of_oddCore_noComponent hcore (hcomp u hu2)

theorem goodResV_twistedF4 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hne : ∃ a b : X, a * b ≠ b * a) {m : ℕ} (hiso : IsoLie X (.reeF4 m)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : GoodResV p X := by
  obtain ⟨-, hmodel⟩ := reeTitsModel_twistedF4_of_isoLie hiso
  exact goodResV_of_charTwoCent hp hp2 (center_eq_bot_of_simple_of_nonabelian hne)
    (outPNice_twistedF4 hp hmodel).toChain (charTwoCent_twistedF4 hne hmodel)

theorem kf133ResMaxAt_leaf7_nine (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf7 9) := by
  refine KF133ResMaxAt.of_goodResV hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨m, hiso⟩ := hX
  exact goodResV_twistedF4 hne hiso hp (by omega)

end CFSG.RankThree.PartOne.K133X
