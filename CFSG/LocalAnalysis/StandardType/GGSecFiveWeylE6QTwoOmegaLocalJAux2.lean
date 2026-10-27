module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalJAux
public import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerShape
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDickson
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.LieType.SteinbergBRBlockParabolicDInf
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.C2PushThree
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCPrimary
open Polynomial Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isComponentOf_map_rPlusEquiv (hK : Nat.card K = 2) {Bs L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {D J : Subgroup G} (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    {e : G} (heD : e ∈ D) (heL : e ∈ L) (he1 : e ≠ 1)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    CFSG.Open.IsComponentOf
      (((J.subgroupOf L).map (qMap (K := K) θ)).map
        (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4)).toMonoidHom)
      (Subgroup.centralizer
        (Set.singleton (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap (K := K) θ ⟨e, heL⟩)) :
          Set ↥(CFSG.RankThree.Classical2.orthDerived
            (TableBOrth.qPlusForm K 4)))) := by
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  have h := isComponentOf_map_qMap hZ2 hBs hcard hcardE hx1 hLx hBL hDB hDcard hxD hJ
    heD heL he1 θ
  have h' := CFSG.isComponentOf_map_mulEquiv
    (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4)) h
  have hEq : Subgroup.centralizer ({(qMap (K := K) θ ⟨e, heL⟩)} :
        Set (OrthRest.RPlus K 4)) =
      Subgroup.centralizer (Set.singleton (qMap (K := K) θ ⟨e, heL⟩)) := rfl
  rw [hEq] at h'
  have hmap : Subgroup.map (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4)).toMonoidHom
      (Subgroup.centralizer (Set.singleton (qMap (K := K) θ ⟨e, heL⟩))) =
        Subgroup.centralizer (Set.singleton
          (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap (K := K) θ ⟨e, heL⟩))) :=
    map_centralizer_singleton_mulEquiv _ _
  rw [hmap] at h'
  exact h'

theorem isComponentOf_map_projOrth (hK : Nat.card K = 2) {Bs L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {D J : Subgroup G} (hDB : D ≤ Bs) (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    {e : G} (heD : e ∈ D) (heL : e ∈ L) (he1 : e ≠ 1)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    CFSG.Open.IsComponentOf
      ((((J.subgroupOf L).map (qMap (K := K) θ)).map
        (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4)).toMonoidHom).map
          (CFSG.RankThree.PartOne.piOrth (TableBOrth.qPlusForm K 4)))
      (Subgroup.centralizer
        (Set.singleton (CFSG.RankThree.PartOne.piOrth (TableBOrth.qPlusForm K 4)
          (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap (K := K) θ ⟨e, heL⟩))) :
          Set (CFSG.RankThree.Classical2.ProjOrthDerived
            (TableBOrth.qPlusForm K 4)))) := by
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  have h := isComponentOf_map_rPlusEquiv hK hZ2 hBs hcard hcardE hx1 hLx hBL hDB hDcard hxD
    hJ heD heL he1 θ
  have hQ := TableBOrth.nondegenerate_qPlusForm (K := K) 4
  let eT : ↥(CFSG.RankThree.Classical2.orthDerived (TableBOrth.qPlusForm K 4)) ≃*
      CFSG.RankThree.Classical2.ProjOrthDerived (TableBOrth.qPlusForm K 4) :=
    MulEquiv.ofBijective (CFSG.RankThree.PartOne.piOrth (TableBOrth.qPlusForm K 4))
      ⟨CFSG.RankThree.PartOne.piOrth_injective hQ, CFSG.RankThree.PartOne.piOrth_surjective⟩
  have h' := CFSG.isComponentOf_map_mulEquiv eT h
  have hmap : Subgroup.map eT.toMonoidHom
      (Subgroup.centralizer (Set.singleton
        (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap (K := K) θ ⟨e, heL⟩)))) =
        Subgroup.centralizer (Set.singleton (eT
          (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap (K := K) θ ⟨e, heL⟩)))) :=
    map_centralizer_singleton_mulEquiv _ _
  rw [hmap] at h'
  exact h'

theorem exists_totallySingular_three_qPlusForm :
    ∃ T : Submodule K (Fin 4 ⊕ Fin 4 → K), Module.finrank K T = 3 ∧
      ∀ v ∈ T, TableBOrth.qPlusForm K 4 v = 0 := by
  classical
  let v : Fin 3 → (Fin 4 ⊕ Fin 4 → K) := fun i =>
    Pi.single (Sum.inl ⟨i.val, by omega⟩) (1 : K)
  have hli : LinearIndependent K v := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h1 := congrFun hg (Sum.inl ⟨i.val, by omega⟩)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, Pi.single_apply] at h1
    rw [Finset.sum_eq_single_of_mem i hi] at h1
    · simpa using h1
    · intro j hj hji
      rw [if_neg]
      · ring
      · intro h
        exact hji (Fin.ext (by simpa using congrArg Fin.val (Sum.inl_injective h))).symm
  have hsupp : ∀ x ∈ Submodule.span K (Set.range v), ∀ k : Fin 4, x (Sum.inr k) = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩ k
      simp [v]
    · intro k; simp
    · intro a b _ _ ha hb k
      simp [ha k, hb k]
    · intro c a _ ha k
      simp [ha k]
  refine ⟨Submodule.span K (Set.range v), ?_, ?_⟩
  · rw [finrank_span_eq_card hli]
    simp
  · intro x hx
    rw [TableBOrth.qPlusForm, CFSG.LieType.Universal.Spin.quadPlus_apply]
    exact Finset.sum_eq_zero fun k _ => by rw [hsupp x hx k, mul_zero]

theorem orderOf_rPlusEquiv_qMap_of_mem_Bs (hK : Nat.card K = 2) {Bs L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    {D : Subgroup G} (hDB : D ≤ Bs) {e : G} (heD : e ∈ D) (heL : e ∈ L) (he1 : e ≠ 1)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    orderOf (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap (K := K) θ ⟨e, heL⟩)) = 3 := by
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  have he3 : e ^ 3 = 1 := hBs.2 e (hDB heD)
  have heord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hq3 : (qMap (K := K) θ ⟨e, heL⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨e, heL⟩ : ↥L) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using he3
    rw [h3, map_one]
  have hqne : qMap (K := K) θ ⟨e, heL⟩ ≠ 1 := by
    intro hq
    have heZ : (⟨e, heL⟩ : ↥L) ∈ Subgroup.center L := by
      have hmem : (⟨e, heL⟩ : ↥L) ∈ (qMap (K := K) θ).ker := by
        rw [MonoidHom.mem_ker]; exact hq
      rwa [qMap_ker] at hmem
    let eZ : ↥(Subgroup.center L) := ⟨⟨e, heL⟩, heZ⟩
    have h3 : orderOf eZ = 3 := by
      rw [← Subgroup.orderOf_coe eZ, ← Subgroup.orderOf_coe (eZ : ↥L)]
      exact heord
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZ2) eZ
    rw [h3] at hk
    rcases k with _ | k
    · norm_num at hk
    · rw [pow_succ] at hk
      have hdvd : 2 ∣ 3 := by
        simpa [hk] using dvd_mul_right 2 (2 ^ k)
      norm_num at hdvd
  have hordq : orderOf (qMap (K := K) θ ⟨e, heL⟩) = 3 := orderOf_eq_prime hq3 hqne
  calc orderOf (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4) (qMap (K := K) θ ⟨e, heL⟩))
      = orderOf (qMap (K := K) θ ⟨e, heL⟩) :=
        orderOf_injective (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4)).toMonoidHom
          (OrthTorus.rPlusEquiv K (by norm_num : 1 ≤ 4)).injective _
    _ = 3 := hordq

theorem fixedSpace_omPlusLin_cases (hK : Nat.card K = 2)
    {x' : ↥(CFSG.RankThree.Classical2.orthDerived (TableBOrth.qPlusForm K 4))}
    (hx3 : orderOf x' = 3)
    {L' : Subgroup (CFSG.RankThree.Classical2.ProjOrthDerived (TableBOrth.qPlusForm K 4))}
    (hL' : CFSG.Open.IsComponentOf L'
      (Subgroup.centralizer
        (Set.singleton (CFSG.RankThree.PartOne.piOrth (TableBOrth.qPlusForm K 4) x') :
          Set (CFSG.RankThree.Classical2.ProjOrthDerived (TableBOrth.qPlusForm K 4))))) :
    (Module.finrank K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
          (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) = 0 ∧
      L' = CFSG.RankThree.PartOne.KCOrthogonal.componentImage (TableBOrth.qPlusForm K 4)
        (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (X ^ 2 + X + 1) ∧
      CFSG.IsQuasisimple
        ↥(CFSG.RankThree.PartOne.KCOrthogonal.specialBlock (TableBOrth.qPlusForm K 4)
          (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (X ^ 2 + X + 1))) ∨
    (Module.finrank K
        (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
          (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) = 6 ∧
      L' = CFSG.RankThree.PartOne.KCOrthogonal.fixedComponentImage (TableBOrth.qPlusForm K 4)
        (x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) := by
  classical
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  have hQ := TableBOrth.nondegenerate_qPlusForm (K := K) 4
  have hdim : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 2 * 4 := by simp
  have hV : CFSG.GroupTheory.WeirSylow.IsPlusType (TableBOrth.qPlusForm K 4) ↔ Even 4 := by
    constructor
    · intro _; norm_num
    · intro _; simpa [TableBOrth.qPlusForm] using
        (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 4)
  have hT := exists_totallySingular_three_qPlusForm (K := K)
  obtain ⟨hx, -, hmem, s, hs, hsm, htype⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.dims_of_orderOf_three (Or.inl hK) hQ hdim hV
      x' hx3
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) :=
    ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hmem⟩
  have hm1 : 1 ≤ primaryMultiplicity ((x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).toLinearMap (X ^ 2 + X + 1) :=
    hx.primaryMultiplicity_pos hmem
  haveI : Nontrivial (Fin 4 ⊕ Fin 4 → K) := by
    obtain ⟨U, hU, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K)
      (lt_of_lt_of_le (by norm_num : 0 < 3) (hU ▸ Submodule.finrank_le U))
  rcases CFSG.HardMathSupport.Dickson.Bal207.OrthFix.inner_comp_cases (Or.inl hK) hQ
    x' hx3 hL' with
    ⟨-, hq, hLJ⟩ | ⟨F, hFq, hFle, hFn, hG4, hLG⟩
  · have hm4 : 4 ≤ primaryMultiplicity ((x' : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).toLinearMap (X ^ 2 + X + 1) :=
      (CFSG.HardMathSupport.Dickson.Bal207.OrthFix.specialBlock_phi_type (Or.inl hK) hx hmem
        hq).1 hK
    refine Or.inl ⟨?_, hLJ, hq⟩
    rw [hs]
    omega
  · have hs3 : 3 ≤ s := by
      by_contra hlt
      refine CFSG.HardMathSupport.Dickson.Bal207.OrthFix.fixed_not_small hQ hx hs htype ?_
        hFq hFle hFn
      rcases Nat.lt_or_ge s 2 with h2 | h2
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, hK⟩
    have hs4 : s ≤ 3 := by omega
    have hs_eq : s = 3 := by omega
    refine Or.inr ⟨?_, ?_⟩
    · rw [hs, hs_eq]
    · rw [hLG, hG4.resolve_left (by omega)]
      rfl

end CFSG.StandardType.E6QTwo

end
