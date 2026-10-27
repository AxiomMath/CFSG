module

public import CFSG.LocalAnalysis.StandardType.GGE6R1FieldTwo
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableCHolds
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecD
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Inner
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ2D4
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1625Pieces
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart14
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SuN
public import CFSG.Quasithin.Background.G1Basic

public section
namespace CFSG.StandardType.E6R16OppFieldTwo
open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587 CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.S2MathAs1E6Companion1625
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem compRank_repr_eq_four
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin M.row.D.orbits.length) (hL : LargeEvenInLambda2 lab) (hj : ∀ k, k = j)
    (hqs : M.row.D.orbits[j].qs = true)
    (hrow : GGE6ThreeR16OppLabels1585 lab M.row.D.orbits[j].lab) :
    compRank (componentRoots (rootCharHom M.a) (M.repr j)) = 4 := by
  classical
  obtain ⟨hT, hdata⟩ := e6RowTableR16Opp_holds lab R I phi M j hL hj hqs hrow
  obtain ⟨hs, hrho⟩ := hdata
  have hraw : M.row.rawComponentOrbits = [[[2, 3, 4, 5]]] := by
    unfold KacRow.rawComponentOrbits
    rw [hT, hs, hrho]
    decide +kernel
  have hnodes : M.orbitNodes j = [[2, 3, 4, 5]] := by
    have hmem : M.orbitNodes j ∈ M.row.rawComponentOrbits :=
      (List.Perm.mem_iff M.orbitNodes_perm).mp (List.mem_ofFn.mpr ⟨j, rfl⟩)
    simpa only [hraw, List.mem_singleton] using hmem
  have hmarks : M.row.diagram.marks.length = 7 := by
    change (k0DiagOf M.row.T).marks.length = 7
    rw [hT]
    rfl
  have hZero : ∀ i : Fin M.row.diagram.marks.length,
      i.val ∈ (M.orbitNodes j).headD [] ↔ M.row.s.getD i.val 0 = 0 := by
    intro i
    have hAll : ∀ k : Fin 7, k.val ∈ [2,3,4,5] ↔ M.row.s.getD k.val 0 = 0 := by
      rw [hs]
      decide +kernel
    have hi : i.val < 7 := hmarks ▸ i.isLt
    simpa only [hnodes,List.headD_cons] using hAll ⟨i.val,hi⟩
  rw [S2MathAs1E6Companion1625.compRank_eq_zeroCount_of_repr_zero_nodes M hT j hZero,hmarks,hs]
  decide +kernel

theorem frobLinear_sq_eq_one
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (hT : M.row.T = .E6) (hrho : M.row.rho = [0, 6, 2, 5, 4, 3, 1]) :
    ∀ x, M.frobLinear (M.frobLinear x) = x := by
  have hEps : M.epsilon * M.epsilon = 1 := by
    rw [M.epsilon_eq]
    split_ifs <;> norm_num
  have hInvol : ∀ i, M.row.nodePerm (M.row.nodePerm i) = i := by
    intro i
    apply Fin.ext
    rw [← M.row.rho_apply, ← M.row.rho_apply]
    have hAll : ∀ k : Fin 7, ([0, 6, 2, 5, 4, 3, 1] : List ℕ).getD
        (([0, 6, 2, 5, 4, 3, 1] : List ℕ).getD k.val 0) 0 = k.val := by decide +kernel
    have hLen : M.row.diagram.marks.length = 7 := by
      change (k0DiagOf M.row.T).marks.length = 7
      rw [hT]
      rfl
    have hlt : i.val < 7 := hLen ▸ i.isLt
    rw [hrho]
    exact hAll ⟨i.val, hlt⟩
  have hNode : ∀ i, M.frobLinear (M.frobLinear (M.nodeMap (Pi.single i 1))) = M.nodeMap (Pi.single i 1) := by
    intro i
    rw [M.frob_nodes, map_smul, M.frob_nodes, smul_smul, hEps, one_smul, hInvol]
  intro x
  obtain ⟨v,rfl⟩ := M.nodeMap_surj x
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin M.row.diagram.marks.length → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [hv, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, map_smul, hNode]

theorem kind_twoD_of_rank_four_label
    {τ : Tag} (hTau : τ = .E6)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ 1)
    (hInv : ∀ gamma ∈ componentRoots (rootCharHom a) i, S.ρ (S.ρ gamma) = gamma)
    (hlabel : GGHasLabel ⟨.twD,4,1⟩
      (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
        Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    twistKind S.ρ (rootCharHom a) i = .twoD := by
  subst hTau
  classical
  have hpL : ((3 : ℕ) : L) ≠ 0 := by rw [Ne,CharP.cast_eq_zero_iff L 2];norm_num
  have hTp : rootDiagUnit .E6 a ^ 3 = 1 := by
    change rootDiagUnitHom .E6 L a ^ 3 = 1
    rw [← map_pow, show a ^ 3 = 1 from funext hap, map_one]
  have hcD : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) * (compRank (componentRoots (rootCharHom a) i)-1) := by rw [hr,hc]
  have hNotInner : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]) := by
    intro hi
    have hD := GGK0LQ.lq_rec_D (Or.inl rfl) S Nat.prime_three hpL hT hTp i (by omega) hcD hi hQ
    have hD' : GGHasLabel ⟨.D,4,1⟩
        (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
          Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by simpa only [hr] using hD
    have hIso := ggLabelRigidInput_holds ⟨.twD,4,1⟩ ⟨.D,4,1⟩ _
      (by simp [LargeEvenInLambda2]) (by simp [LargeEvenInLambda2]) hlabel hD'
    simp [GGLabelIso] at hIso
  have hInner2 : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2*componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]) := by
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    intro gamma hg
    rw [hs,Nat.mul_one,one_smul,Function.iterate_succ_apply',Function.iterate_one]
    exact hInv gamma hg
  unfold twistKind
  rw [if_neg hNotInner,if_neg (by simp only [hr,hc];simp [hInner2]),if_pos ⟨by omega,hcD⟩]

theorem component_ncard_eq_twentyFour
    {τ : Tag} (hTau : τ = .E6) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {a : Fin τ.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (hall : (kernelRoots (rootCharHom a)).ncard = 24) (i : KernelComponent (rootCharHom a)) :
    (componentRoots (rootCharHom a) i).ncard = 24 := by
  subst hTau
  have h3 : ((3 : ℕ) : L) ≠ 0 := by rw [Ne,CharP.cast_eq_zero_iff L 2];norm_num
  exact (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.d4t2_class_of_card h3 hap hall i).2

theorem root_rho_sq_eq_self
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (hT : M.row.T = .E6) (hrho : M.row.rho = [0,6,2,5,4,3,1])
    (gamma : Fin M.tau.rank → ℤ) (hg : IsRoot M.tau gamma) :
    M.setup.ρ (M.setup.ρ gamma) = gamma := by
  have h1 := M.frob_roots gamma hg
  have h2 := M.frob_roots (M.setup.ρ gamma) ((M.setup.frob.isRoot_iff gamma).mpr hg)
  calc M.setup.ρ (M.setup.ρ gamma) = M.frobLinear (M.setup.ρ gamma) := h2.symm
    _ = M.frobLinear (M.frobLinear gamma) := by rw [h1]
    _ = gamma := frobLinear_sq_eq_one M hT hrho gamma

theorem b2SatQ2On_r16Opp_holds (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B2SatQ2On Omega GGE6ThreeR16OppLabels1585 := by
  intro lab R _ I phi M j hL hj hqs hrow hn z hz hzModel hcomm
  have hTag : lab.tag = .E6 ∧ M.row.D.orbits[j].lab = ⟨.twD, 4, 1⟩ := by
    obtain ⟨hAmb, hComp⟩ := hrow
    rcases hAmb with ⟨h,hdvd⟩ | ⟨h,hdvd⟩
    · exact ⟨h,by simpa only [hn] using hComp⟩
    · norm_num [hn] at hdvd
  obtain ⟨ht,hsVec,hrho⟩ := e6RowTableR16Opp_holds lab R I phi M j hL hj hqs hrow
  have htau : M.tau = .E6 := by rw [← M.tau_eq,ht];rfl
  have hField : M.row.D.orbits[j].lab.n = lab.n := by rw [hTag.2,hn]
  have hs1 : componentOrbitLength M.setup.ρ (componentRoots (rootCharHom M.a) (M.repr j)) = 1 := by
    have h := M.field_exp j
    rw [hField,hn] at h
    rw [M.orbit_length]
    simpa using h.symm
  have hq : M.setup.D.q = 2 := by rw [M.q_eq,hn];norm_num
  have hQ : M.setup.D.q ^ componentOrbitLength M.setup.ρ (componentRoots (rootCharHom M.a) (M.repr j)) = 2^1 := by rw [hq,hs1]
  have hRank := compRank_repr_eq_four M j hL hj hqs hrow
  have hKernel24 : (kernelRoots (rootCharHom M.a)).ncard = 24 := by
    apply kernel_ncard_eq_twentyFour_of_zeroCount_eq_four M ht
    have hLen : M.row.diagram.marks.length = 7 := by change (k0DiagOf M.row.T).marks.length = 7;rw [ht];rfl
    rw [hLen,hsVec]
    decide +kernel
  have hComp24 := component_ncard_eq_twentyFour htau M.a_pow hKernel24 (M.repr j)
  have hInv : ∀ gamma ∈ componentRoots (rootCharHom M.a) (M.repr j),
      M.setup.ρ (M.setup.ρ gamma) = gamma := fun gamma hg =>
    root_rho_sq_eq_self M ht hrho gamma ((isRootComponent_componentRoots (M.repr j)).isRoot gamma hg)
  have hLabel := CFSG.StandardType.E6R1FieldTwo.rationalComponent_label M j hqs
  rw [hTag.2] at hLabel
  have hkind := kind_twoD_of_rank_four_label htau M.setup M.a_torus M.a_pow (M.repr j) hRank hComp24 hs1 hQ hInv hLabel
  have hRat : ∀ x ∈ rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j),
      Commute z x := by
    intro x hx
    have hxGamma : x ∈ M.setup.Γ := (le_trans (Subgroup.commutator_le_self _) inf_le_right) hx
    rw [← M.iota_range] at hxGamma
    obtain ⟨y, hyx⟩ := MonoidHom.mem_range.mp hxGamma
    have hy : y ∈ component M j := by
      change M.iota y ∈ rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)
      rwa [hyx]
    rw [← hyx]
    exact hcomm y hy
  have hcheck : RootOps.tableCheck M.tau = true := by rw [htau]; exact RootOps.tableCheck_E6
  have hGeom := commute_rootSpan_of_commute_component_twoD_four_two M.setup
    (Or.inl htau) hcheck hq M.a_torus (M.repr j) hkind hRank hs1 z hRat
  have hle : rootSpan M.tau Omega (componentRoots (rootCharHom M.a) (M.repr j)) ≤
      Subgroup.centralizer ({z} : Set (ModGL M.tau Omega)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hGeom x hx).symm.eq
  have hOrbit := CFSG.StandardType.F4ExplicitPos.OrbitKernel.rootSpan_rationalRoots_le_centralizer_of_fixed
    M.setup (M.repr j) hzModel.2 hle
  have hKernel : kernelSpan M ≤ Subgroup.centralizer ({z} : Set (ModGL M.tau Omega)) := by
    rw [kernelSpan, ← iSup_componentRootSpan]
    refine iSup_le fun c => ?_
    obtain ⟨k, hk⟩ := M.orbit_cover c
    rw [hj k] at hk
    have hIncl : componentRoots (rootCharHom M.a) c ⊆
        rationalRoots M.setup.ρ (rootCharHom M.a) c := by
      intro beta hbeta
      exact ⟨0, beta, hbeta, rfl⟩
    exact (rootSpan_mono hIncl).trans (hk ▸ hOrbit)
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hKernel hy)).symm

end CFSG.StandardType.E6R16OppFieldTwo
