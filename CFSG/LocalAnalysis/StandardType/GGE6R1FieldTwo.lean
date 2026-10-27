module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableAHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1625Pieces
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighCharElem
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ2TwoD
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart14
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632WeylDatum
public import CFSG.LocalAnalysis.StandardType.GGFamD4IndexAux
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecA
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecD
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGK0MarkedComponents
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3T

public section

namespace CFSG.StandardType.E6R1FieldTwo
open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587 CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.S2MathAs1E6Companion1625
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn


theorem rationalComponent_label
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin M.row.D.orbits.length) (hqs : M.row.D.orbits[j].qs = true) :
    GGHasLabel M.row.D.orbits[j].lab
      (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j) ⧸
        Subgroup.center (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j))) := by
  let Q := rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)
  have hmap : (component M j).map M.iota = Q :=
    (GGK0MarkedComponents.component_of_realization M j hqs).2
  let e : component M j ≃* Q :=
    ((component M j).equivMapOfInjective M.iota M.iota_inj).trans (MulEquiv.subgroupCongr hmap)
  exact ggHasLabel_quotCenter_of_mulEquiv e (M.label j hqs).2

set_option synthInstance.maxSize 1024 in
private theorem rank_five_kac_count :
    ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
      m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3 →
      ∀ x ∈ zlC m0 m1 m2 m3 m4 m5,
        (cmpF (zlC m0 m1 m2 m3 m4 m5) x).card = 5 →
        szF (zlC m0 m1 m2 m3 m4 m5) x = 30 ∨
          szF (zlC m0 m1 m2 m3 m4 m5) x = 40 := by
  decide +kernel


theorem compRank_repr_eq_five
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin M.row.D.orbits.length) (hL : LargeEvenInLambda2 lab) (hj : ∀ k, k = j)
    (hqs : M.row.D.orbits[j].qs = true)
    (hrow : GGE6ThreeR1Labels1585 lab M.row.D.orbits[j].lab) :
    compRank (componentRoots (rootCharHom M.a) (M.repr j)) = 5 := by
  classical
  obtain ⟨hT, hdata⟩ := e6RowTableR1_holds lab R I phi M j hL hj hqs hrow
  obtain ⟨hs, hrho⟩ := hdata
  have hraw : M.row.rawComponentOrbits = [[[0, 2, 3, 4, 5]]] := by
    rcases hs with hs | hs
    · unfold KacRow.rawComponentOrbits
      rw [hT, hs, hrho]
      decide +kernel
    · unfold KacRow.rawComponentOrbits
      rw [hT, hs, hrho]
      decide +kernel
  have hnodes : M.orbitNodes j = [[0, 2, 3, 4, 5]] := by
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
    have hAll : ∀ k : Fin 7, k.val ∈ [0,2,3,4,5] ↔ M.row.s.getD k.val 0 = 0 := by
      rcases hs with h | h <;> rw [h] <;> decide +kernel
    have hi : i.val < 7 := hmarks ▸ i.isLt
    simpa only [hnodes,List.headD_cons] using hAll ⟨i.val,hi⟩
  rw [S2MathAs1E6Companion1625.compRank_eq_zeroCount_of_repr_zero_nodes M hT j hZero,hmarks]
  rcases hs with h | h <;> rw [h] <;> decide +kernel

theorem e6_rank_five_count
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hr : compRank (componentRoots (rootCharHom a) i) = 5) :
    (componentRoots (rootCharHom a) i).ncard = 30 ∨
      (componentRoots (rootCharHom a) i).ncard = 40 := by
  have h3 : ((3 : ℕ) : L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff L 2]
    norm_num
  obtain ⟨zeta, w, m0, m1, m2, m3, m4, m5, hzeta, hsum, hchar, hdata⟩ := kac_class_data h3 hap
  obtain ⟨x, hx, hroots, hcard, hrank, hproper⟩ := hdata i
  have h5 := hrank.symm.trans hr
  rw [hcard]
  exact rank_five_kac_count m0 m1 m2 m3 m4 m5 hsum x hx h5

theorem e6_kind_twoD_of_rank_five_label
    {τ : Tag} (hτ : τ = .E6)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 5)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ 1)
    (hlabel : GGHasLabel ⟨.twD, 5, 1⟩
      (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
        Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    twistKind S.ρ (rootCharHom a) i = .twoD := by
  subst hτ
  classical
  have hpL : ((3 : ℕ) : L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff L 2]
    norm_num
  have hTp : rootDiagUnit .E6 a ^ 3 = 1 := by
    change rootDiagUnitHom .E6 L a ^ 3 = 1
    rw [← map_pow, show a ^ 3 = 1 from funext hap, map_one]
  have hcounts := e6_rank_five_count hap i hr
  have badA (h : GGHasLabel ⟨.A, 5, 1⟩
      (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
        Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))) : False := by
    have hIso := ggLabelRigidInput_holds ⟨.twD, 5, 1⟩ ⟨.A, 5, 1⟩ _
      (by simp [LargeEvenInLambda2]) (by simp [LargeEvenInLambda2]) hlabel h
    simp [GGLabelIso] at hIso
  have badSU (h : GGHasLabel ⟨.twA, 5, 1⟩
      (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
        Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))) : False := by
    have hIso := ggLabelRigidInput_holds ⟨.twD, 5, 1⟩ ⟨.twA, 5, 1⟩ _
      (by simp [LargeEvenInLambda2]) (by simp [LargeEvenInLambda2]) hlabel h
    simp [GGLabelIso] at hIso
  have badD (h : GGHasLabel ⟨.D, 5, 1⟩
      (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
        Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))) : False := by
    have hIso := ggLabelRigidInput_holds ⟨.twD, 5, 1⟩ ⟨.D, 5, 1⟩ _
      (by simp [LargeEvenInLambda2]) (by simp [LargeEvenInLambda2]) hlabel h
    simp [GGLabelIso] at hIso
  cases hk : twistKind S.ρ (rootCharHom a) i with
  | inner =>
      have hi := twistInner_of_twistKind_eq_innerT S
        CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hk
      rcases hcounts with h30 | h40
      · have hcA : (componentRoots (rootCharHom a) i).ncard =
            compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) + 1) := by
          rw [hr, h30]
        have h := GGK0LQ.lq_rec_A S Nat.prime_three hpL hT hTp i hk (by omega) hcA hQ
        exact (badA (by simpa only [hr] using h)).elim
      · have hcD : (componentRoots (rootCharHom a) i).ncard =
            2 * compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1) := by
          rw [hr, h40]
        have h := GGK0LQ.lq_rec_D (Or.inl rfl) S Nat.prime_three hpL hT hTp i
          (by omega) hcD hi hQ
        exact (badD (by simpa only [hr] using h)).elim
  | suN =>
      have h := GGK0LQ.lq_rec_SU S Nat.prime_three hpL hT hTp i hk hQ (by omega)
      exact (badSU (by simpa only [hr] using h)).elim
  | twoD => rfl
  | exc =>
      exfalso
      simp only [twistKind, hr] at hk
      split_ifs at hk <;> simp_all

theorem b2SatQ2On_r1_holds (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B2SatQ2On Omega GGE6ThreeR1Labels1585 := by
  intro lab R _ I phi M j hL hj hqs hrow hn z hz hzModel hcomm
  have hTag : lab.tag = .twE6 ∧ M.row.D.orbits[j].lab = ⟨.twD, 5, 1⟩ := by
    rcases hrow with ⟨h, hdvd, hcomp⟩ | ⟨h, hdvd, hcomp⟩
    · norm_num [hn] at hdvd
    · exact ⟨h, by simpa only [hn] using hcomp⟩
  have ht : M.row.T = .E6 := (e6RowTableR1_holds lab R I phi M j hL hj hqs hrow).1
  have htau : M.tau = .E6 := by
    rw [← M.tau_eq, ht]
    rfl
  have hField : M.row.D.orbits[j].lab.n = lab.n := by
    rw [hTag.2, hn]
  have hs1 : componentOrbitLength M.setup.ρ
      (componentRoots (rootCharHom M.a) (M.repr j)) = 1 := by
    have h := M.field_exp j
    rw [hField, hn] at h
    rw [M.orbit_length]
    simpa using h.symm
  have hq : M.setup.D.q = 2 := by rw [M.q_eq, hn]; norm_num
  have hQ : M.setup.D.q ^ componentOrbitLength M.setup.ρ
      (componentRoots (rootCharHom M.a) (M.repr j)) = 2 ^ 1 := by rw [hq, hs1]
  have hRank := compRank_repr_eq_five M j hL hj hqs hrow
  have hLabel := rationalComponent_label M j hqs
  rw [hTag.2] at hLabel
  have hkind : twistKind M.setup.ρ (rootCharHom M.a) (M.repr j) = .twoD := by
    exact e6_kind_twoD_of_rank_five_label htau M.setup M.a_torus M.a_pow
      (M.repr j) hRank hQ hLabel
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
  have hMem := twoD_two_mem_rationalComponent M.setup (Or.inr (Or.inl htau)) M.a_torus
    (M.repr j) hkind (by omega)
  have hGeom := commute_rootSpan_of_commute_component_twoD_two_of_tableCheck M.setup
    (Or.inl htau) hcheck hq M.a_torus (M.repr j) hkind (by omega) hMem z hRat
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

end CFSG.StandardType.E6R1FieldTwo
