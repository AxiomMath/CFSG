module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
public import CFSG.LocalAnalysis.StandardType.GGK1CoverBij
public import CFSG.LocalAnalysis.StandardType.GGK1Cover
public import CFSG.LocalAnalysis.StandardType.GGFamLabelIndex
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFam
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6TwoThree
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenE6ThreeLang
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6Heisenberg
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddNeThree
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6ThreeDiagTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCriterion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.E6ThreePlaneComp
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful
public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTorus
public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
public import CFSG.LieType.SeitzGeneration.OuterSpPair
public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
public import CFSG.LieType.SeitzGeneration.RootPairSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCyc
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KF4.EvenDescent

public section

namespace CFSG.StandardType.GGK0MarkedComponents

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem map_fixed_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi) :
    (ggFixSub phi).map M.iota =
      M.setup.Γ ⊓ Subgroup.centralizer {rootDiagUnit M.tau M.a} := by
  rw [TCJ.tcj_ggFixSub_eq_fixSubgroup]
  have hcompat : ∀ r, M.iota (phi r) =
      rootDiagUnit M.tau M.a * M.iota r * (rootDiagUnit M.tau M.a)⁻¹ := by
    intro r
    have hc := M.modelAction_compat ⟨rootDiagUnit M.tau M.a, M.a_model⟩ r
    simpa only [M.action_eq] using hc
  rw [CFSG.LocalAnalysis.GLTheoremA.S267.Gen.map_fixSubgroup_eq_of_embedding
    M.iota M.iota_inj phi (rootDiagUnit M.tau M.a) hcompat, M.iota_range]

theorem component_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    (j : Fin M.row.D.orbits.length) (hj : M.row.D.orbits[j].qs = true) :
    IsComponentOf (coreFactor M.setup M.iota M.a (M.repr j)) (ggFixSub phi) ∧
      (coreFactor M.setup M.iota M.a (M.repr j)).map M.iota =
        rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j) := by
  have hc := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.isComponentOf_rationalComponent
    M.setup M.a_torus (M.repr j) (M.qs j hj)
  rw [← map_fixed_of_realization M] at hc
  exact isComponentOf_comap_of_injective M.iota M.iota_inj
    ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mpr hc)

theorem coreFactor_injective_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    {j k : Fin M.row.D.orbits.length} (hj : M.row.D.orbits[j].qs = true)
    (hk : M.row.D.orbits[k].qs = true)
    (heq : coreFactor M.setup M.iota M.a (M.repr j) =
      coreFactor M.setup M.iota M.a (M.repr k)) : j = k := by
  classical
  have hcomp : rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j) =
      rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr k) := by
    rw [← (component_of_realization M j hj).2, ← (component_of_realization M k hk).2, heq]
  let af : PUnit → Fin M.tau.rank → Omegaˣ := fun _ => M.a
  have hker : kernelRoots (TableCRes.famCharHom af) = kernelRoots (rootCharHom M.a) :=
    TableCRes.kernelRoots_famChar_punit_eq M.a
  obtain ⟨i, hi⟩ := TableCRes.exists_componentRoots_eq hker.symm (M.repr j)
  obtain ⟨i', hi'⟩ := TableCRes.exists_componentRoots_eq hker.symm (M.repr k)
  have hRj : TableCRes.rationalRootsM M.setup.ρ (TableCRes.famCharHom af) i =
      rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr j) := by
    exact TableCRes.rationalRootsM_eq_of_componentRoots_eq M.setup.ρ hi.symm
  have hRk : TableCRes.rationalRootsM M.setup.ρ (TableCRes.famCharHom af) i' =
      rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr k) := by
    exact TableCRes.rationalRootsM_eq_of_componentRoots_eq M.setup.ρ hi'.symm
  have hrank := TableCRes.rationalRootsM_eq_of_quasisimple_le_rootSpan M.setup
    (a := af) (fun _ => M.a_torus) i i' (M.qs j hj)
    (by rw [hRj]; exact (Subgroup.commutator_le_self _).trans inf_le_left)
    (by rw [hRk, hcomp]; exact (Subgroup.commutator_le_self _).trans inf_le_left)
  have hRootEq : rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr j) =
      rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr k) := by
    rw [hRj, hRk] at hrank
    exact hrank
  by_contra hne
  have hd := M.orbit_distinct j k hne
  obtain ⟨γ, hγ⟩ := TableCRes.tc_componentRoots_nonempty (M.repr j)
  have hγR : γ ∈ rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr j) :=
    ⟨0, γ, hγ, rfl⟩
  exact Set.disjoint_left.mp hd hγR (hRootEq ▸ hγR)

theorem exists_component_position_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi) (hτ : M.tau ≠ .G2)
    {K : Subgroup R} (hK : IsComponentOf K (ggFixSub phi)) :
    ∃ j : Fin M.row.D.orbits.length, M.row.D.orbits[j].qs = true ∧
      K = coreFactor M.setup M.iota M.a (M.repr j) := by
  have hKi : IsComponentOf (K.map M.iota) ((ggFixSub phi).map M.iota) :=
    isComponentOf_map_of_injective M.iota M.iota_inj hK
  rw [map_fixed_of_realization M] at hKi
  have hKiOpen :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mp hKi
  obtain ⟨i, hqi, heq⟩ := LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
    M.setup hτ hp (CharP.cast_ne_zero_of_ne_of_prime Omega hp hp2.symm)
    M.a_torus M.a_pow M.a_ne hKiOpen
  obtain ⟨j, hR⟩ := M.orbit_cover i
  have hCompEq : rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) i =
      rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j) := by
    unfold rationalComponent rationalSpan
    rw [hR]
  have hqj : CFSG.IsQuasisimple
      (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)) := hCompEq ▸ hqi
  have hj : M.row.D.orbits[j].qs = true := by
    by_contra hnot
    have hfalse : M.row.D.orbits[j].qs = false := Bool.eq_false_of_not_eq_true hnot
    have hs := M.solvable j hfalse
    have := hs
    have : Group.IsPerfect (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)) :=
      hqj.1
    have : Nontrivial
        (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hqj
    have : Group.IsSolvable
        (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)) :=
      Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (Subgroup.commutator_le_self
          (rationalSpan M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j))))
    exact Group.IsPerfect.not_isSolvable
      (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)) inferInstance
  refine ⟨j, hj, ?_⟩
  have hMap : K.map M.iota = (coreFactor M.setup M.iota M.a (M.repr j)).map M.iota := by
    rw [(component_of_realization M j hj).2, heq, hCompEq]
  have := congrArg (Subgroup.comap M.iota) hMap
  simpa only [Subgroup.comap_map_eq_self_of_injective M.iota_inj] using this


theorem compBij_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi) :
    GGKacCompBij M.row.D R phi := by
  have hτ : M.tau ≠ .G2 := by
    rw [← M.tau_eq]
    cases M.row.T <;> simp [absTag]
  classical
  let f : {j : Fin M.row.D.orbits.length // M.row.D.orbits[j].qs = true} →
      {K : Subgroup R // IsComponentOf K (ggFixSub phi)} :=
    fun j => ⟨coreFactor M.setup M.iota M.a (M.repr j.1),
      (component_of_realization M j.1 j.2).1⟩
  have hfInj : Function.Injective f := by
    intro j k heq
    apply Subtype.ext
    exact coreFactor_injective_of_realization M j.2 k.2 (congrArg Subtype.val heq)
  have hfSurj : Function.Surjective f := by
    intro K
    obtain ⟨j, hj, hK⟩ := exists_component_position_of_realization hp hp2 M hτ K.2
    exact ⟨⟨j, hj⟩, Subtype.ext hK.symm⟩
  let e := Equiv.ofBijective f ⟨hfInj, hfSurj⟩
  refine ⟨e.symm, ?_⟩
  intro K
  have hFactor : coreFactor M.setup M.iota M.a (M.repr (e.symm K).1) = K.1 :=
    congrArg Subtype.val (e.apply_symm_apply K)
  have hLabel := (M.label (e.symm K).1 (e.symm K).2).2
  change coreFactor M.setup M.iota M.a (M.repr (e.symm K).1) = K.1 at hFactor
  rw [hFactor] at hLabel
  exact hLabel

theorem cover_compBij_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    {L : Type} [Group L] [Finite L] (psi : L →* R)
    (hpsi : Function.Surjective psi) (hker : psi.ker ≤ Subgroup.center L)
    (e : MulAut L) (hInd : ∀ l, phi (psi l) = psi (e l)) :
    GGKacCompBij M.row.D L e :=
  ggK1_cover_bij psi hpsi hker e phi hInd (compBij_of_realization hp hp2 M)

theorem comps_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi) :
    GGK1Comps lab.n M.row.D R phi := by
  classical
  obtain ⟨f, hf⟩ := compBij_of_realization hp hp2 M
  refine ⟨?_, ?_⟩
  · intro K hK
    let j := f ⟨K, hK⟩
    refine ⟨M.row.D.orbits[j.1], List.getElem_mem j.1.isLt, j.2, ?_,
      (M.label j.1 j.2).1, hf ⟨K, hK⟩⟩
    rw [M.field_exp]
    exact dvd_mul_left lab.n (M.orbitNodes j.1).length
  · intro o ho hqs
    obtain ⟨j, hj, hjo⟩ := List.mem_iff_getElem.mp ho
    let i : {i : Fin M.row.D.orbits.length // M.row.D.orbits[i].qs = true} :=
      ⟨⟨j, hj⟩, by change M.row.D.orbits[j].qs = true; simpa only [hjo] using hqs⟩
    refine ⟨(f.symm i).1, (f.symm i).2, ?_⟩
    have h := hf (f.symm i)
    change GGHasLabel M.row.D.orbits[(f (f.symm i)).1].lab
      (↥(f.symm i).1 ⧸ Subgroup.center ↥(f.symm i).1) at h
    have hPos := congrArg
      (fun k : {k : Fin M.row.D.orbits.length // M.row.D.orbits[k].qs = true} =>
        M.row.D.orbits[k.1]) (f.apply_symm_apply i)
    change M.row.D.orbits[(f (f.symm i)).1] = M.row.D.orbits[j] at hPos
    have hPos' := hPos.trans hjo
    simpa only [hPos'] using h

theorem cover_comps_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    {L : Type} [Group L] [Finite L] (psi : L →* R)
    (hpsi : Function.Surjective psi) (hker : psi.ker ≤ Subgroup.center L)
    (e : MulAut L) (hep : e ^ p = 1) (hInd : ∀ l, phi (psi l) = psi (e l)) :
    (∀ J : Subgroup L, IsComponentOf J (ggFixSub e) →
      ∃ o ∈ M.row.D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
        GGHasLabel o.lab (J ⧸ Subgroup.center J)) ∧
    (∀ o ∈ M.row.D.orbits, o.qs = true → ∃ J : Subgroup L,
      IsComponentOf J (ggFixSub e) ∧ GGHasLabel o.lab (J ⧸ Subgroup.center J)) :=
  ggK1_cover_comp psi hpsi hker e hep phi hInd (comps_of_realization hp hp2 M)

end CFSG.StandardType.GGK0MarkedComponents
