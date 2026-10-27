module

public import CFSG.LocalAnalysis.StandardType.GGE6R4OppFieldTwo
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableBHolds
public import CFSG.LocalAnalysis.StandardType.GGFamLabelDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialUnitaryQ2
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.Quasithin.Background.G1Basic

public section
namespace CFSG.StandardType.E6R4FieldTwo

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587 CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.S2MathAs1E6Companion1625
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem e6_kind_suN_of_rank_five_label
    {tau : Tag} (htau : tau = .E6)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p0 : ℕ}
    (S : LangSetup tau L p0) {a : Fin tau.rank → Lˣ}
    (hT : rootDiagUnit tau a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit tau a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 5)
    (hq : S.D.q = 2) (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hlabel : GGHasLabel (⟨.twA, 5, 1⟩ : LargeEvenLabel)
      (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
        Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    twistKind S.ρ (rootCharHom a) i = .suN := by
  subst htau
  classical
  have hpL : ((3 : ℕ) : L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff L 2]
    norm_num
  have hTp : rootDiagUnit .E6 a ^ 3 = 1 := by
    change rootDiagUnitHom .E6 L a ^ 3 = 1
    rw [← map_pow, show a ^ 3 = 1 from funext hap, map_one]
  have hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ 1 := by rw [hq, hs]
  have hcounts := E6R1FieldTwo.e6_rank_five_count hap i hr
  by_cases hInner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])
  · have hk : twistKind S.ρ (rootCharHom a) i = .inner := by simp [twistKind, hInner]
    exfalso
    rcases hcounts with h30 | h40
    · have hA : (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1) := by rw [hr, h30]
      have h := GGK0LQ.lq_rec_A S Nat.prime_three hpL hT hTp i hk (by rw [hr]; decide) hA hQ
      rw [hr] at h
      have hh := ggLabelRigidInput_holds (⟨.twA, 5, 1⟩ : LargeEvenLabel) ⟨.A, 5, 1⟩ _
        (by simp [LargeEvenInLambda2]) (by simp [LargeEvenInLambda2]) hlabel h
      simp [GGLabelIso] at hh
    · have hD : (componentRoots (rootCharHom a) i).ncard = 2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1) := by rw [hr, h40]
      have h := GGK0LQ.lq_rec_D (Or.inl rfl) S Nat.prime_three hpL hT hTp i (by rw [hr]; decide) hD hInner hQ
      rw [hr] at h
      have hh := ggLabelRigidInput_holds (⟨.twA, 5, 1⟩ : LargeEvenLabel) ⟨.D, 5, 1⟩ _
        (by simp [LargeEvenInLambda2]) (by simp [LargeEvenInLambda2]) hlabel h
      simp [GGLabelIso] at hh
  · rcases hcounts with h30 | h40
    · simp only [twistKind, if_neg hInner, hr, h30]
      norm_num
    · exfalso
      have hD : (componentRoots (rootCharHom a) i).ncard = 2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1) := by rw [hr, h40]
      obtain ⟨e, he, hmod⟩ := CFSG.LocalAnalysis.GLTheoremA.I167.excRec_twoD_of_root_data S Nat.prime_three
        hT hap h1 i (by rw [hr]) hD hInner
      have hchar : ringChar L = 2 := ringChar.eq L 2
      have he1 : e = 1 := by
        rw [hchar, hq] at he
        exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using he)
      rw [hr, hchar, he1] at hmod
      have htwD : GGHasLabel (⟨.twD, 5, 1⟩ : LargeEvenLabel)
          (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
            Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
        (TableCRes.ggCompLabelAt_twD 5 1 (by decide) (by decide) hmod).2.2.1
      have hh := ggLabelRigidInput_holds (⟨.twA, 5, 1⟩ : LargeEvenLabel) ⟨.twD, 5, 1⟩ _
        (by simp [LargeEvenInLambda2]) (by simp [LargeEvenInLambda2]) hlabel htwD
      simp [GGLabelIso] at hh

theorem compRank_repr_eq_five
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin M.row.D.orbits.length) (hL : LargeEvenInLambda2 lab) (hj : ∀ k, k = j)
    (hqs : M.row.D.orbits[j].qs = true)
    (hrow : GGE6ThreeR4Labels1585 lab M.row.D.orbits[j].lab) (hn : lab.n = 1) :
    compRank (componentRoots (rootCharHom M.a) (M.repr j)) = 5 := by
  classical
  obtain ⟨ht, hs, _⟩ := e6RowTableR4_holds lab R I phi M j hL hj hqs hrow
  have hfield : M.row.D.orbits[j].lab.n = lab.n := by
    rcases hrow with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  have hs1 : componentOrbitLength M.setup.ρ (componentRoots (rootCharHom M.a) (M.repr j)) = 1 := by
    rw [M.orbit_length]
    have h := M.field_exp j
    rw [hfield, hn] at h
    simpa using h.symm
  have hr := S2MathAs1E6Companion1625.kernelRank_eq_zeroCount M ht
  have hmarks : M.row.diagram.marks.length = 7 := by
    change (k0DiagOf M.row.T).marks.length = 7
    rw [ht]
    rfl
  have hcount : (Finset.univ.filter (fun i : Fin M.row.diagram.marks.length =>
      M.row.s.getD i.val 0 = 0)).card = 5 := by
    rw [hmarks, hs]
    decide +kernel
  rw [← TableCRes.famD4Index_finrank_span_eq_compRank
    (isRootComponent_componentRoots (M.repr j)),
    E6R4OppFieldTwo.componentRoots_eq_kernelRoots_of_single_orbit_length_one M j hj hs1, hr, hcount]

theorem b2SatQ2On_r4_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    S2MathAs1E6Companion1625.B2SatQ2On Omega GGE6ThreeR4Labels1585 := by
  intro lab R _ I phi M j hL hj hqs hrow hn actor hActor hActorModel hcomm
  have hTag : lab.tag = .twE6 ∧ M.row.D.orbits[j].lab = ⟨.twA, 5, 1⟩ := by
    rcases hrow with ⟨_, hdvd, _⟩ | ⟨h, _, hcomp⟩
    · norm_num [hn] at hdvd
    · exact ⟨h, by simpa only [hn] using hcomp⟩
  have ht : M.row.T = .E6 := (e6RowTableR4_holds lab R I phi M j hL hj hqs hrow).1
  have htau : M.tau = .E6 := by rw [← M.tau_eq, ht]; rfl
  have hfield : M.row.D.orbits[j].lab.n = lab.n := by rw [hTag.2, hn]
  have hs : componentOrbitLength M.setup.ρ (componentRoots (rootCharHom M.a) (M.repr j)) = 1 := by
    rw [M.orbit_length]
    have h := M.field_exp j
    rw [hfield, hn] at h
    simpa using h.symm
  have hq : M.setup.D.q = 2 := by rw [M.q_eq, hn]; norm_num
  have hr := compRank_repr_eq_five M j hL hj hqs hrow hn
  have hlabel := E6R1FieldTwo.rationalComponent_label M j hqs
  rw [hTag.2] at hlabel
  have hkind := e6_kind_suN_of_rank_five_label htau M.setup M.a_torus M.a_pow M.a_ne
    (M.repr j) hr hq hs hlabel
  have hTp : rootDiagUnit M.tau M.a ^ 3 = 1 := by
    change rootDiagUnitHom M.tau Omega M.a ^ 3 = 1
    rw [← map_pow, show M.a ^ 3 = 1 from funext M.a_pow, map_one]
  have hpL : ((3 : ℕ) : Omega) ≠ 0 := by rw [Ne, CharP.cast_eq_zero_iff Omega 2]; norm_num
  obtain ⟨nu, psi, sigmaf, kappa, hnu, hpsi, hkappa, hnorm, hRoots⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved M.setup Nat.prime_three hpL hTp
      (M.repr j) (by rw [hr]; decide) (by obtain ⟨_, h⟩ := suN_rank_ncard hkind; exact h)
  have hCard := CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hpsi hkappa hnorm
  have hCard30 : (componentRoots (rootCharHom M.a) (M.repr j)).ncard = 30 := by
    obtain ⟨_, h⟩ := suN_rank_ncard hkind
    rw [hr] at h
    exact h
  have hnu4 : 4 ≤ nu := by
    have hCard' : 30 = nu * (nu - 1) := by simpa only [← hRoots, hCard30] using hCard
    by_contra hNot
    have hnu3 : nu = 3 := by omega
    norm_num [hnu3] at hCard'
  obtain ⟨pi, hpi⟩ := CFSG.HardMathSupport.Dickson.Sec6.ssexc_suN_perm M.setup M.a_torus
    (M.repr j) hkind hnu hpsi hkappa hnorm hRoots
  have hRat : ∀ x ∈ rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j), Commute actor x := by
    intro x hx
    have hxGamma : x ∈ M.setup.Γ := (le_trans (Subgroup.commutator_le_self _) inf_le_right) hx
    rw [← M.iota_range] at hxGamma
    obtain ⟨y, hyx⟩ := MonoidHom.mem_range.mp hxGamma
    have hy : y ∈ component M j := by
      change M.iota y ∈ rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)
      rwa [hyx]
    rw [← hyx]
    exact hcomm y hy
  have hZ : actor ∈ torusGroup M.tau Omega ⊔ rootSpan M.tau Omega (kernelRoots (rootCharHom M.a)) := by
    have hle : connectedCentralizer M ≤ torusGroup M.tau Omega ⊔ rootSpan M.tau Omega (kernelRoots (rootCharHom M.a)) := by
      unfold connectedCentralizer
      apply sup_le
      · rw [Subgroup.closure_le]
        rintro _ ⟨b, rfl⟩
        exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup b)
      · exact le_sup_right
    exact hle hActor
  have hOmega3 : M.zeta ^ 3 = 1 := by
    have h := pow_orderOf_eq_one M.zeta
    simpa only [M.zeta_order] using h
  have hOmegaNe : M.zeta ≠ 1 := by
    intro h
    have hOrder := M.zeta_order
    rw [h, orderOf_one] at hOrder
    norm_num at hOrder
  have hGeom := commute_rootSpan_of_commute_unitary_component_two M.setup M.a_torus (M.repr j) hs hq
    hnu4 psi hpsi hRoots pi hpi M.zeta hOmega3 hOmegaNe actor hZ hRat
  have hKernel : kernelSpan M = rootSpan M.tau Omega (componentRoots (rootCharHom M.a) (M.repr j)) := by
    rw [kernelSpan, E6R4OppFieldTwo.componentRoots_eq_kernelRoots_of_single_orbit_length_one M j hj hs]
  intro y hy
  exact hGeom y (hKernel ▸ hy)

end CFSG.StandardType.E6R4FieldTwo
