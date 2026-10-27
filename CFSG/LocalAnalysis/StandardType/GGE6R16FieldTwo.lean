module
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ2D4
public import CFSG.LocalAnalysis.StandardType.GGE6R16OppFieldTwo
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableBHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreePointwise
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632B1Rows

public section
namespace CFSG.StandardType.E6R16FieldTwo
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
    (hrow : GGE6ThreeR16Labels1585 lab M.row.D.orbits[j].lab) :
    compRank (componentRoots (rootCharHom M.a) (M.repr j)) = 4 := by
  classical
  obtain ⟨hT, hdata⟩ := e6RowTableR16_holds lab R I phi M j hL hj hqs hrow
  obtain ⟨hs, hrho⟩ := hdata
  have hraw : M.row.rawComponentOrbits = [[[2, 3, 4, 5]]] := by
    unfold KacRow.rawComponentOrbits
    rcases hrho with h | h <;> rw [hT,hs,h] <;> decide +kernel
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

theorem commute_kernelSpan_of_commute_component
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin M.row.D.orbits.length) (hL : LargeEvenInLambda2 lab) (hj : ∀ k, k = j)
    (hqs : M.row.D.orbits[j].qs = true)
    (hrow : GGE6ThreeR16Labels1585 lab M.row.D.orbits[j].lab) (hn : lab.n = 1)
    (z : ModGL M.tau Omega) (hzModel : z ∈ M.setup.D.model)
    (hcomm : ∀ x ∈ component M j, Commute z (M.iota x)) :
    ∀ y ∈ kernelSpan M, Commute z y := by
  obtain ⟨hT,hsVec,hrho⟩ := e6RowTableR16_holds lab R I phi M j hL hj hqs hrow
  have hTau : M.tau = .E6 := by rw [← M.tau_eq,hT];rfl
  have hLab : M.row.D.orbits[j].lab = ⟨.triD4,0,1⟩ := by
    simpa only [hn] using hrow.2
  have hField : M.row.D.orbits[j].lab.n = lab.n := by rw [hLab,hn]
  have hs1 : componentOrbitLength M.setup.ρ (componentRoots (rootCharHom M.a) (M.repr j)) = 1 := by
    have h := M.field_exp j
    rw [hField,hn] at h
    rw [M.orbit_length]
    simpa using h.symm
  have hq : M.setup.D.q = 2 := by rw [M.q_eq,hn];norm_num
  have hQ : M.setup.D.q ^ componentOrbitLength M.setup.ρ
      (componentRoots (rootCharHom M.a) (M.repr j)) = 2^1 := by rw [hq,hs1]
  have hRank := compRank_repr_eq_four M j hL hj hqs hrow
  have hKernel24 : (kernelRoots (rootCharHom M.a)).ncard = 24 := by
    apply kernel_ncard_eq_twentyFour_of_zeroCount_eq_four M hT
    have hLen : M.row.diagram.marks.length = 7 := by
      change (k0DiagOf M.row.T).marks.length = 7
      rw [hT]
      rfl
    rw [hLen,hsVec]
    decide +kernel
  have hCard := E6R16OppFieldTwo.component_ncard_eq_twentyFour hTau M.a_pow hKernel24 (M.repr j)
  have hNotInner : ¬ twistInner (componentRoots (rootCharHom M.a) (M.repr j)) M.setup.ρ := by
    intro hi
    have h3 : ((3 : ℕ) : Omega) ≠ 0 := by
      rw [Ne,CharP.cast_eq_zero_iff Omega 2]
      norm_num
    have hPow : rootDiagUnit M.tau M.a ^ 3 = 1 := by
      change rootDiagUnitHom M.tau Omega M.a ^ 3 = 1
      rw [← map_pow,show M.a ^ 3 = 1 from funext M.a_pow,map_one]
    have hInner : twistInner (componentRoots (rootCharHom M.a) (M.repr j))
        ((M.setup.ρ : (Fin M.tau.rank → ℤ) → _)^[componentOrbitLength M.setup.ρ
          (componentRoots (rootCharHom M.a) (M.repr j))]) := by
      simpa only [hs1,Function.iterate_one] using hi
    have hD := GGK0LQ.lq_rec_D (Or.inl hTau) M.setup Nat.prime_three h3 M.a_torus hPow
      (M.repr j) (by omega) (by rw [hRank,hCard]) hInner hQ
    have hLabel := E6R1FieldTwo.rationalComponent_label M j hqs
    rw [hLab] at hLabel
    have hD' : GGHasLabel ⟨.D,4,1⟩
        (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j) ⧸
          Subgroup.center (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j))) := by
      simpa only [hRank] using hD
    have hIso := ggLabelRigidInput_holds ⟨.triD4,0,1⟩ ⟨.D,4,1⟩ _
      (by simp [LargeEvenInLambda2]) (by simp [LargeEvenInLambda2]) hLabel hD'
    simp [GGLabelIso] at hIso
  have hRat : ∀ x ∈ rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j), Commute z x := by
    intro x hx
    have hxGamma : x ∈ M.setup.Γ := (le_trans (Subgroup.commutator_le_self _) inf_le_right) hx
    rw [← M.iota_range] at hxGamma
    obtain ⟨y,hyx⟩ := MonoidHom.mem_range.mp hxGamma
    have hy : y ∈ component M j := by
      change M.iota y ∈ rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)
      rwa [hyx]
    rw [← hyx]
    exact hcomm y hy
  have hCheck : RootOps.tableCheck M.tau = true := by rw [hTau];exact RootOps.tableCheck_E6
  have hGeom := commute_rootSpan_of_commute_component_outer_d4_two M.setup (Or.inl hTau)
    hCheck hq M.a_torus (M.repr j) hRank hCard hs1 hNotInner z hRat
  have hle : rootSpan M.tau Omega (componentRoots (rootCharHom M.a) (M.repr j)) ≤
      Subgroup.centralizer ({z} : Set (ModGL M.tau Omega)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hGeom x hx).symm.eq
  have hOrbit := CFSG.StandardType.F4ExplicitPos.OrbitKernel.rootSpan_rationalRoots_le_centralizer_of_fixed
    M.setup (M.repr j) hzModel.2 hle
  have hKernel : kernelSpan M ≤ Subgroup.centralizer ({z} : Set (ModGL M.tau Omega)) := by
    rw [kernelSpan,← iSup_componentRootSpan]
    refine iSup_le fun c => ?_
    obtain ⟨k,hk⟩ := M.orbit_cover c
    rw [hj k] at hk
    have hIncl : componentRoots (rootCharHom M.a) c ⊆ rationalRoots M.setup.ρ (rootCharHom M.a) c := by
      intro beta hbeta
      exact ⟨0,beta,hbeta,rfl⟩
    exact (rootSpan_mono hIncl).trans (hk ▸ hOrbit)
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hKernel hy)).symm

theorem b2SatQ2On_r16_holds (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B2SatQ2On Omega GGE6ThreeR16Labels1585 := by
  intro lab R _ I phi M j hL hj hqs hrow hn z _hzConn hzModel hcomm
  exact commute_kernelSpan_of_commute_component M j hL hj hqs hrow hn z hzModel hcomm

theorem mem_conn_of_fix_component
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin M.row.D.orbits.length) (hL : LargeEvenInLambda2 lab) (hj : ∀ k, k = j)
    (hqs : M.row.D.orbits[j].qs = true)
    (hrow : GGE6ThreeR16Labels1585 lab M.row.D.orbits[j].lab) (hn : lab.n = 1)
    {u : MulAut R} (hu : u ∈ centralizerGroup M)
    (hfix : ∀ x ∈ component M j, u x = x) : u ∈ conn M := by
  have hC := ((b1aOn_holds Omega) lab R I phi M j hL hj hqs).1
  rw [hC] at hu
  obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.mp hu
  have hz' := Subgroup.mem_subgroupOf.mp hz
  have hcomm : ∀ x ∈ component M j, Commute (z : ModGL M.tau Omega) (M.iota x) := by
    intro x hx
    have h := M.modelAction_compat z x
    rw [hzu, hfix x hx] at h
    exact mul_inv_eq_iff_eq_mul.mp h.symm
  have hRoot := commute_kernelSpan_of_commute_component M j hL hj hqs hrow hn z z.2 hcomm
  have hTau : M.tau = .E6 := by
    have ht := (e6RowTableR16_holds lab R I phi M j hL hj hqs hrow).1
    rw [← M.tau_eq, ht]
    rfl
  have hzCentre := E6Pointwise.mem_connectedCentre_of_geom_commute_kernelSpan M hTau hz'.1 hRoot
  have hzConn : z ∈ ((connectedCentralizer M ⊓ M.setup.D.model).subgroupOf M.setup.D.model) := by
    exact Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.map_subtype_le (Subgroup.center (connectedCentralizer M))) hzCentre, z.2⟩
  exact Subgroup.mem_map.mpr ⟨z, hzConn, hzu⟩

theorem b3On_r16_q2_holds (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B3On Omega (fun lab labJ => GGE6ThreeR16Labels1585 lab labJ ∧ lab.n = 1) := by
  intro lab R _ I phi M j hL hj hqs hrow u hu hnot hInner
  obtain ⟨d, hd, hdu⟩ := hInner
  have hB1 := ((b1On_r16_holds Omega) lab R I phi M j hL hj hqs hrow.1).1
  have hdI : (MulAut.conj d : MulAut R) ∈ innerComponent M j :=
    Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
  have hdConn := hB1.innerComponent_le hdI
  have hdC := hB1.conn_le hdConn
  have hvC : (MulAut.conj d)⁻¹ * u ∈ centralizerGroup M :=
    mul_mem (inv_mem hdC) hu
  have hvfix : ∀ x ∈ component M j, ((MulAut.conj d)⁻¹ * u) x = x := by
    intro x hx
    rw [MulAut.mul_apply, hdu x hx, MulAut.conj_inv_apply]
    group
  have hvConn := mem_conn_of_fix_component M j hL hj hqs hrow.1 hrow.2 hvC hvfix
  apply hnot
  have hProd := mul_mem hdConn hvConn
  simpa only [mul_inv_cancel_left] using hProd

end CFSG.StandardType.E6R16FieldTwo
