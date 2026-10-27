module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialUnitaryOrbit
public import CFSG.LocalAnalysis.StandardType.GGE6ThreePointwise
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632WeylDatum
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632B1Rows
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section
namespace CFSG.StandardType.E6R3FieldTwo

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587 CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.S2MathAs1E6Companion1625
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem commute_kernelSpan_of_r3
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin M.row.D.orbits.length) (hL : LargeEvenInLambda2 lab) (hj : ∀ k, k = j)
    (hqs : M.row.D.orbits[j].qs = true)
    (hrow : GGE6ThreeR3Labels1585 lab M.row.D.orbits[j].lab) (hn : lab.n = 1)
    (z : ModGL M.tau Omega) (hz : z ∈ geomCentralizer M)
    (hzF : M.setup.D.step z = z)
    (hcomm : ∀ x ∈ component M j, Commute z (M.iota x)) :
    ∀ y ∈ kernelSpan M, Commute z y := by
  obtain ⟨hT, hsVec, _⟩ := e6RowTableR3_holds lab R I phi M j hL hj hqs hrow
  have hTau : M.tau = .E6 := by rw [← M.tau_eq, hT]; rfl
  have hChar : rootCharHom M.a ≠ 1 := by
    obtain ⟨gamma, _, hgamma⟩ := exists_rootChar_ne_one M.a_ne
    intro he
    have h := DFunLike.congr_fun he (Multiplicative.ofAdd gamma)
    change rootChar M.a gamma = 1 at h
    exact hgamma h
  have hKernel18 : (kernelRoots (rootCharHom M.a)).ncard = 18 := by
    apply kernel_ncard_eq_eighteen_of_zeroCount_eq_six M hT
    · have hLen : M.row.diagram.marks.length = 7 := by
        change (k0DiagOf M.row.T).marks.length = 7
        rw [hT]
        rfl
      rw [hLen, hsVec]
      decide +kernel
    · exact hChar
  have h3 : ((3 : ℕ) : Omega) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff Omega 2]
    norm_num
  have hAllSix : ∀ (tau : Tag), tau = .E6 →
      ∀ (a : Fin tau.rank → Omegaˣ), (∀ k, a k ^ 3 = 1) →
      (kernelRoots (rootCharHom a)).ncard = 18 →
      ∀ c : KernelComponent (rootCharHom a), (componentRoots (rootCharHom a) c).ncard = 6 := by
    intro tau htau
    subst tau
    intro a ha h18
    obtain ⟨c, hc, hSix⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.kernel_classes_of_ncard_eighteen
        h3 ha h18
    intro d
    obtain ⟨k, rfl⟩ := hc.2 d
    exact hSix k
  have hSix := hAllSix M.tau hTau M.a M.a_pow hKernel18 (M.repr j)
  have hField : M.row.D.orbits[j].lab.n = 3 * lab.n := by
    rcases hrow with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  have hLen : (M.orbitNodes j).length = 3 := by
    have h := M.field_exp j
    rw [hField, hn] at h
    simpa using h.symm
  have hs3 : componentOrbitLength M.setup.ρ (componentRoots (rootCharHom M.a) (M.repr j)) = 3 := by
    rw [M.orbit_length, hLen]
  have hq : M.setup.D.q = 2 := by rw [M.q_eq, hn]; norm_num
  have hcover : ∀ c : KernelComponent (rootCharHom M.a),
      rationalRoots M.setup.ρ (rootCharHom M.a) c =
        rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr j) := by
    intro c
    obtain ⟨k, hk⟩ := M.orbit_cover c
    rwa [hj k] at hk
  have hRat : ∀ x ∈ rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j), Commute z x := by
    intro x hx
    have hxGamma : x ∈ M.setup.Γ := (le_trans (Subgroup.commutator_le_self _) inf_le_right) hx
    rw [← M.iota_range] at hxGamma
    obtain ⟨y, hyx⟩ := MonoidHom.mem_range.mp hxGamma
    have hy : y ∈ component M j := by
      change M.iota y ∈ rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)
      rwa [hyx]
    rw [← hyx]
    exact hcomm y hy
  change z ∈ toralCentralizer M.tau Omega M.a at hz
  change ∀ y ∈ rootSpan M.tau Omega (kernelRoots (rootCharHom M.a)), Commute z y
  exact commute_kernelSpan_of_geom_unitary_orbit_three M.setup hTau M.a_torus M.a_pow M.a_ne
    (M.repr j) hSix hs3 hq hcover z hz hzF hRat

theorem b3On_r3_holds (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B3On Omega (fun lab labJ => GGE6ThreeR3Labels1585 lab labJ ∧ lab.n = 1) := by
  intro lab R _ I phi M j hL hj hqs hrow u hu hnot hInner
  have hB1 := ((b1On_r3_holds Omega) lab R I phi M j hL hj hqs hrow.1).1
  obtain ⟨d, hd, hAct⟩ := hInner
  have hdConn : MulAut.conj d ∈ conn M :=
    hB1.innerComponent_le (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)
  have hdC := hB1.conn_le hdConn
  let v : MulAut R := (MulAut.conj d)⁻¹ * u
  have hvC : v ∈ centralizerGroup M := mul_mem (inv_mem hdC) hu
  have hvFix : ∀ x ∈ component M j, v x = x := by
    intro x hx
    change (MulAut.conj d)⁻¹ (u x) = x
    have hxAct : u x = MulAut.conj d x := hAct x hx
    rw [hxAct]
    exact (MulAut.conj d).symm_apply_apply x
  rw [hB1.centralizerGroup_eq] at hvC
  obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.mp hvC
  have hz' := Subgroup.mem_subgroupOf.mp hz
  have hcomm : ∀ x ∈ component M j, Commute (z : ModGL M.tau Omega) (M.iota x) := by
    intro x hx
    have h := M.modelAction_compat z x
    rw [hzu, hvFix x hx] at h
    exact mul_inv_eq_iff_eq_mul.mp h.symm
  have hKernel := commute_kernelSpan_of_r3 M j hL hj hqs hrow.1 hrow.2 z hz'.1 hz'.2.2 hcomm
  have hTau : M.tau = .E6 := by
    have hT := (e6RowTableR3_holds lab R I phi M j hL hj hqs hrow.1).1
    rw [← M.tau_eq, hT]
    rfl
  have hCent := E6Pointwise.mem_connectedCentre_of_geom_commute_kernelSpan M hTau hz'.1 hKernel
  have hzConn : (z : ModGL M.tau Omega) ∈ connectedCentralizer M := by
    obtain ⟨w, _, hwz⟩ := Subgroup.mem_map.mp hCent
    exact hwz ▸ w.property
  have hvConn : v ∈ conn M := by
    exact Subgroup.mem_map.mpr ⟨z, Subgroup.mem_subgroupOf.mpr ⟨hzConn, z.property⟩, hzu⟩
  apply hnot
  have h := mul_mem hdConn hvConn
  simpa only [v, mul_inv_cancel_left] using h

end CFSG.StandardType.E6R3FieldTwo
