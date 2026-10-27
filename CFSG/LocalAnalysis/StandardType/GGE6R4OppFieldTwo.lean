module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreePointwise
public import CFSG.LocalAnalysis.StandardType.GGE6R1FieldTwo
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableCHolds
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonFactor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcRecDTwo
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet

public section

namespace CFSG.StandardType.E6R4OppFieldTwo

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587 CFSG.StandardType.E6Centralizer1585
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem componentRoots_eq_kernelRoots_of_single_orbit_length_one
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin M.row.D.orbits.length) (hj : ∀ k, k = j)
    (hs : componentOrbitLength M.setup.ρ (componentRoots (rootCharHom M.a) (M.repr j)) = 1) :
    componentRoots (rootCharHom M.a) (M.repr j) = kernelRoots (rootCharHom M.a) := by
  apply Set.Subset.antisymm
  · rintro beta ⟨hbeta, _⟩
    exact hbeta
  · intro beta hbeta
    let c : KernelComponent (rootCharHom M.a) := ⟦⟨beta, hbeta⟩⟧
    have hmem : beta ∈ componentRoots (rootCharHom M.a) c := ⟨hbeta, rfl⟩
    obtain ⟨k, hk⟩ := M.orbit_cover c
    rw [hj k] at hk
    have hr : beta ∈ rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr j) := by
      rw [← hk]
      exact ⟨0, beta, hmem, rfl⟩
    rwa [CFSG.StandardType.F4ExplicitPos.CommonFactor.rationalRoots_eq_componentRoots_of_orbitLength_one
      (M.repr j) hs] at hr

theorem compRank_repr_eq_five
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin M.row.D.orbits.length) (hL : LargeEvenInLambda2 lab) (hj : ∀ k, k = j)
    (hqs : M.row.D.orbits[j].qs = true)
    (hrow : GGE6ThreeR4OppLabels1585 lab M.row.D.orbits[j].lab) (hn : lab.n = 1) :
    compRank (componentRoots (rootCharHom M.a) (M.repr j)) = 5 := by
  classical
  obtain ⟨ht, hs, _⟩ := e6RowTableR4Opp_holds lab R I phi M j hL hj hqs hrow
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
    componentRoots_eq_kernelRoots_of_single_orbit_length_one M j hj hs1, hr, hcount]

theorem twistInner_of_rank_five_thirty_of_label_A5_two
    {tau : Tag} {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {p0 : ℕ} (S : LangSetup tau Omega p0) {a : Fin tau.rank → Omegaˣ}
    (hT : rootDiagUnit tau a ∈ S.D.torus) (hTp : rootDiagUnit tau a ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 5)
    (hc : (componentRoots (rootCharHom a) i).ncard = 30)
    (hq : S.D.q = 2) (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hlabel : GGHasLabel (⟨.A, 5, 1⟩ : LargeEvenLabel)
      (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
        Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin tau.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
  classical
  by_contra hnot
  have hk : twistKind S.ρ (rootCharHom a) i = .suN := by
    simp only [twistKind, if_neg hnot, hr, hc]
    norm_num
  have hpL : (3 : Omega) ≠ 0 := by
    have h2 : (2 : Omega) = 0 := CharTwo.two_eq_zero
    have h3 : (3 : Omega) = 1 := by calc
      (3 : Omega) = 2 + 1 := by norm_num
      _ = 1 := by rw [h2, zero_add]
    rw [h3]
    exact one_ne_zero
  have hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ 1 := by
    rw [hq, hs]
  have hu := GGK0LQ.lq_rec_SU S Nat.prime_three hpL hT hTp i hk hN (by rw [hr]; decide)
  rw [hr] at hu
  have hiso := ggLabelRigidInput_holds (⟨.A, 5, 1⟩ : LargeEvenLabel) ⟨.twA, 5, 1⟩
    (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
      Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (by simp [LargeEvenInLambda2]) (by simp [LargeEvenInLambda2]) hlabel hu
  norm_num [GGLabelIso] at hiso

theorem not_label_A5_two_of_rank_five_forty
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p0 : ℕ}
    (S : LangSetup .E6 L p0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit .E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 5)
    (hc : (componentRoots (rootCharHom a) i).ncard = 40)
    (hq : S.D.q = 2) (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hlabel : CFSG.StandardType.GGHasLabel (⟨.A, 5, 1⟩ : CFSG.Assembly.LargeEvenLabel)
      (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
        Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))) : False := by
  classical
  have hpL : (3 : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : (3 : L) = 1 := by calc
      (3 : L) = 2 + 1 := by norm_num
      _ = 1 := by rw [h2, zero_add]
    rw [h3]; exact one_ne_zero
  have hTp : rootDiagUnit .E6 a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    have ha : a ^ 3 = 1 := funext hap
    rw [ha, rootDiagUnit_one]
  have hD : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1) := by rw [hr, hc]
  have hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ 1 := by
    rw [hq, hs]
  by_cases hInner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · have hL := CFSG.StandardType.GGK0LQ.lq_rec_D (Or.inl rfl) S Nat.prime_three hpL hT hTp i
      (by rw [hr]; decide) hD hInner hN
    rw [hr] at hL
    have hh := CFSG.StandardType.ggLabelRigidInput_holds
      (⟨.A, 5, 1⟩ : CFSG.Assembly.LargeEvenLabel) ⟨.D, 5, 1⟩ _
      (by simp [CFSG.Assembly.LargeEvenInLambda2])
      (by simp [CFSG.Assembly.LargeEvenInLambda2]) hlabel hL
    norm_num [CFSG.StandardType.GGLabelIso] at hh
  · obtain ⟨e, he, hmod⟩ := CFSG.LocalAnalysis.GLTheoremA.I167.excRec_twoD_of_root_data S Nat.prime_three hT hap h1 i
      (by rw [hr]) hD hInner
    have hchar : ringChar L = 2 := ringChar.eq L 2
    have he1 : e = 1 := by
      rw [hchar, hq] at he
      have hinj := Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      exact hinj (by simpa using he)
    rw [hchar, he1, hr] at hmod
    have hcls := CFSG.StandardType.statedClassicalModel_of_hasLabel_typeA
      (by simp [CFSG.Assembly.LargeEvenInLambda2]) hlabel
    have hlin : CFSG.Blueprint.LieModel
        (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
          Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSL 6 2 1 :=
      Or.inl ⟨by decide, hcls⟩
    have hh := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique_classicalOrSuzuki
      (by decide : 3 ≤ 6) hlin (Or.inl (by decide)) hmod
    cases hh.1

theorem twistInner_of_rank_five_of_label_A5_two
    {tau : Tag} (htau : tau = .E6)
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {p0 : ℕ} (S : LangSetup tau Omega p0) {a : Fin tau.rank → Omegaˣ}
    (hT : rootDiagUnit tau a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit tau a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 5)
    (hq : S.D.q = 2) (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hlabel : GGHasLabel (⟨.A, 5, 1⟩ : LargeEvenLabel)
      (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
        Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin tau.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
  subst htau
  rcases E6R1FieldTwo.e6_rank_five_count hap i hr with h30 | h40
  · have hTp : rootDiagUnit .E6 a ^ 3 = 1 := by
      change rootDiagUnitHom .E6 Omega a ^ 3 = 1
      rw [← map_pow, show a ^ 3 = 1 from funext hap, map_one]
    exact twistInner_of_rank_five_thirty_of_label_A5_two S hT hTp i hr h30 hq hs hlabel
  · exact (not_label_A5_two_of_rank_five_forty S hT hap h1 i hr h40 hq hs hlabel).elim

theorem twistInner_r4Opp
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin M.row.D.orbits.length) (hL : LargeEvenInLambda2 lab) (hj : ∀ k, k = j)
    (hqs : M.row.D.orbits[j].qs = true)
    (hrow : GGE6ThreeR4OppLabels1585 lab M.row.D.orbits[j].lab) (hn : lab.n = 1) :
    twistInner (componentRoots (rootCharHom M.a) (M.repr j))
      ((M.setup.ρ : (Fin M.tau.rank → ℤ) → _)^[componentOrbitLength M.setup.ρ
        (componentRoots (rootCharHom M.a) (M.repr j))]) := by
  have hTag : lab.tag = .E6 ∧ M.row.D.orbits[j].lab = ⟨.A, 5, 1⟩ := by
    rcases hrow with ⟨h, _, hcomp⟩ | ⟨_, hdvd, _⟩
    · exact ⟨h, by simpa only [hn] using hcomp⟩
    · norm_num [hn] at hdvd
  have ht : M.row.T = .E6 := (e6RowTableR4Opp_holds lab R I phi M j hL hj hqs hrow).1
  have htau : M.tau = .E6 := by
    rw [← M.tau_eq, ht]
    rfl
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
  exact twistInner_of_rank_five_of_label_A5_two htau M.setup M.a_torus M.a_pow M.a_ne
    (M.repr j) hr hq hs hlabel

end CFSG.StandardType.E6R4OppFieldTwo
