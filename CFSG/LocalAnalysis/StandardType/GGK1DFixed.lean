module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEightBasic
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial Matrix
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial
  supportedBlock isometryCentralizer fixedSpace fixedBlockEquiv restrictFixed
  restrictFixed_injective restrictFixed_mem_orthogonalGroup mem_supportedBlock
  fixedSpace_eq_primaryComponent)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup mem_omegaGroup dicksonHom dicksonHom_apply)
open CFSG.RankThree.Classical2 (orthDerived)

private noncomputable def ggK1Df_omegaEquiv {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) :
    ↥(supportedBlock Q x (X - 1) ⊓ orthDerived Q) ≃*
      ↥(omegaGroup (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate) := by
  classical
  have horthOmega : orthDerived Q = omegaGroup Q hQ :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ)
      (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT)
  let A : Subgroup (V ≃ₗ[K] V) := supportedBlock Q x (X - 1) ⊓ orthDerived Q
  let A' : Subgroup ↥(supportedBlock Q x (X - 1)) :=
    A.subgroupOf (supportedBlock Q x (X - 1))
  have himage : A'.map (restrictFixed Q x) =
      omegaGroup (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate := by
    ext h
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg1 : (g : V ≃ₗ[K] V) ∈ orthDerived Q :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hg)).2
      have hω : (g : V ≃ₗ[K] V) ∈ omegaGroup Q hQ := horthOmega ▸ hg1
      rw [mem_omegaGroup] at hω
      rw [mem_omegaGroup]
      exact ⟨restrictFixed_mem_orthogonalGroup g,
        by rw [← hx.finrank_commSpace_eq_restrictFixed g.2]; exact hω.2⟩
    · intro hh
      have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) :=
        (mem_omegaGroup.mp hh).1
      let g : ↥(supportedBlock Q x (X - 1)) := (fixedBlockEquiv hx).symm ⟨h, hhO⟩
      have hcoe : restrictFixed Q x g = h :=
        congrArg Subtype.val ((fixedBlockEquiv hx).apply_symm_apply ⟨h, hhO⟩)
      refine ⟨g, ?_, hcoe⟩
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨g.2, ?_⟩)
      rw [horthOmega, mem_omegaGroup]
      refine ⟨(Subgroup.mem_inf.mp (mem_supportedBlock.mp g.2).1).1, ?_⟩
      rw [hx.finrank_commSpace_eq_restrictFixed g.2, hcoe]
      exact (mem_omegaGroup.mp hh).2
  exact (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
    ((Subgroup.equivMapOfInjective A' (restrictFixed Q x) (restrictFixed_injective hx)).trans
      (MulEquiv.subgroupCongr himage))

private noncomputable def ggK1Df_statedOmegaEquiv {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    ↥(StatedOmega Q₀) ≃* ↥(orthDerived Q) :=
  (Subgroup.equivMapOfInjective (StatedOmega Q₀)
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).injective).trans
    (MulEquiv.subgroupCongr (by
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ,
        Subgroup.map_comap_eq_self_of_surjective
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective]))

private theorem ggK1Df_isQuasisimple_commutator {G : Type*} [Group G] (A : Subgroup G)
    (h : CFSG.IsQuasisimple ↥A) : CFSG.IsQuasisimple ↥⁅A, A⁆ := by
  haveI : Group.IsPerfect ↥A := h.1
  have hc : ⁅A, A⁆ = A := by
    rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top, Subgroup.map_top,
      Subgroup.range_subtype]
  rw [hc]; exact h

private theorem ggK1Df_omegaGroup_commute_of_finrank_two {K W : Type} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup W] [Module K W] [FiniteDimensional K W] {R : QuadraticForm K W}
    (hR : R.polarBilin.Nondegenerate) (h2 : Module.finrank K W = 2) :
    ∀ a b : ↥(omegaGroup R hR), Commute a b := by
  intro a b
  have hδ : ∀ c : ↥(omegaGroup R hR),
      dicksonHom R hR ⟨c.1, (mem_omegaGroup.mp c.2).1⟩ = 1 := by
    intro c
    rw [dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
      ZMod.natCast_eq_zero_iff_even]
    exact (mem_omegaGroup.mp c.2).2
  apply Subtype.ext
  exact CFSG.RankThree.PartOne.KCOrthogonal.commute_of_dicksonHom_eq_one hR h2
    (mem_omegaGroup.mp a.2).1 (mem_omegaGroup.mp b.2).1 (hδ a) (hδ b)

theorem ggK1D_fixed_omega {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {m : ℕ} (hm : 3 ≤ m)
    (hW : Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 2 * m)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.restrict (primaryComponent x.toLinearMap (X - 1)))) :
    Nonempty (↥(supportedBlock Q x (X - 1) ⊓
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) ≃*
      StatedOmega (StatedQuadPlus m K)) := by
  classical
  have hR : (QuadraticMap.polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hWfix : Module.finrank K (fixedSpace x) = 2 * m := by
    rw [fixedSpace_eq_primaryComponent]; exact hW
  have hplusR : CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace x).subtype) := by
    rw [fixedSpace_eq_primaryComponent]; exact hplus
  obtain ⟨eIso⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hR hWfix hplusR
  have hTR : ∃ T : Submodule K (fixedSpace x), Module.finrank K T = 3 ∧
      ∀ v ∈ T, (Q.comp (fixedSpace x).subtype) v = 0 := by
    obtain ⟨-, T, hT3, hT0⟩ :=
      CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := m) hm
    refine ⟨T.map eIso.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq]; exact hT3
    · rintro v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      exact (eIso.symm.map_app w).trans (hT0 w hw)
  have hEqR : omegaGroup (Q.comp (fixedSpace x).subtype) hR =
      orthDerived (Q.comp (fixedSpace x).subtype) :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hTR)
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR)
  refine ⟨(ggK1Df_omegaEquiv hx hQ hT).trans ?_⟩
  exact (MulEquiv.subgroupCongr hEqR).trans
    ((CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr eIso).trans
      (ggK1Df_statedOmegaEquiv (Q := CFSG.LieType.Universal.Spin.quadPlus m K)
        (Q₀ := StatedQuadPlus m K) (CFSG.LieType.Universal.Spin.coe_quadPlus m K)).symm)

theorem ggK1D_fixed_omegaMinus {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {m : ℕ} (hm : 3 ≤ m)
    (hW : Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 2 * m)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.restrict (primaryComponent x.toLinearMap (X - 1)))) :
    ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (↥(supportedBlock Q x (X - 1) ⊓
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) ≃*
        StatedOmega (StatedQuadMinus m K b c)) := by
  classical
  have hR : (QuadraticMap.polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hWfix : Module.finrank K (fixedSpace x) = 2 * m := by
    rw [fixedSpace_eq_primaryComponent]; exact hW
  have hminusR : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace x).subtype) := by
    rw [fixedSpace_eq_primaryComponent]; exact hminus
  obtain hplusIso | ⟨b, c, hirr, ⟨he⟩⟩ :=
    CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus
      (Q.comp (fixedSpace x).subtype) hR (by omega) hWfix
  · exfalso
    exact hminusR (CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv hplusIso.some.symm
      (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K m))
  · by_cases hm4 : 4 ≤ m
    · have hTR : ∃ T : Submodule K (fixedSpace x), Module.finrank K T = 3 ∧
          ∀ v ∈ T, (Q.comp (fixedSpace x).subtype) v = 0 := by
        obtain ⟨-, T, hT3, hT0⟩ :=
          CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := m) hm4 hirr
        refine ⟨T.map he.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
        · rw [LinearEquiv.finrank_map_eq]; exact hT3
        · rintro v hv
          obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
          exact (he.symm.map_app w).trans (hT0 w hw)
      have hEqR : omegaGroup (Q.comp (fixedSpace x).subtype) hR =
          orthDerived (Q.comp (fixedSpace x).subtype) :=
        le_antisymm (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hTR)
          (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR)
      refine ⟨b, c, hirr, ⟨(ggK1Df_omegaEquiv hx hQ hT).trans ?_⟩⟩
      exact (MulEquiv.subgroupCongr hEqR).trans
        ((CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr he).trans
          (ggK1Df_statedOmegaEquiv (Q := CFSG.LieType.Universal.Spin.quadMinus m K b c)
            (Q₀ := StatedQuadMinus m K b c)
            (CFSG.LieType.Universal.Spin.coe_quadMinus (n := m) (K := K) b c)).symm)
    · have hm3 : m = 3 := by omega
      subst hm3
      have hts : ∀ U : Submodule K (fixedSpace x), Module.finrank K U = 3 →
          ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
        intro U hU
        by_contra h
        push Not at h
        exact hminusR ⟨U, by rw [hU, hWfix], h⟩
      have hEqR : omegaGroup (Q.comp (fixedSpace x).subtype) hR =
          orthDerived (Q.comp (fixedSpace x).subtype) :=
        le_antisymm
          (CFSG.SeitzReduction.OmegaPilot.omegaGroup_le_orthDerived_of_six hR
            (by rw [hWfix]) hts)
          (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR)
      refine ⟨b, c, hirr, ⟨(ggK1Df_omegaEquiv hx hQ hT).trans ?_⟩⟩
      exact (MulEquiv.subgroupCongr hEqR).trans
        ((CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr he).trans
          (ggK1Df_statedOmegaEquiv (Q := CFSG.LieType.Universal.Spin.quadMinus 3 K b c)
            (Q₀ := StatedQuadMinus 3 K b c)
            (CFSG.LieType.Universal.Spin.coe_quadMinus (n := 3) (K := K) b c)).symm)

theorem ggK1D_fixed_sl2 {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {m : ℕ} (hm : m = 2)
    (hW : Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 2 * m)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.restrict (primaryComponent x.toLinearMap (X - 1)))) :
    ∃ (E : Type) (_ : Field E) (_ : Fintype E), Fintype.card E = (Nat.card K) ^ 2 ∧
      Nonempty (↥(supportedBlock Q x (X - 1) ⊓
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) ≃*
        Matrix.SpecialLinearGroup (Fin 2) E) := by
  classical
  subst hm
  have hR : (QuadraticMap.polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hWfix : Module.finrank K (fixedSpace x) = 4 := by
    rw [fixedSpace_eq_primaryComponent]; norm_num at hW ⊢; exact hW
  have hminusR : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace x).subtype) := by
    rw [fixedSpace_eq_primaryComponent]; exact hminus
  have hts : ∀ U : Submodule K (fixedSpace x), Module.finrank K U = 2 →
      ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
    intro U hU
    by_contra h
    push Not at h
    exact hminusR ⟨U, by rw [hU, hWfix], h⟩
  obtain ⟨E, hE, hAlg, D, ψ, ρ, hψ, hρ, hinj, hρmem, hcomm, hsimple, hperf, hnonab, hcard,
    hidx, hnorm, hodd⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction
      (Q.comp (fixedSpace x).subtype) hR hWfix hts
  have hEqR : omegaGroup (Q.comp (fixedSpace x).subtype) hR =
      orthDerived (Q.comp (fixedSpace x).subtype) :=
    le_antisymm (CFSG.SeitzReduction.OmegaPilot.omegaGroup_le_orthDerived_of_four hR hWfix hts)
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR)
  letI : Field E := hE
  letI : Algebra K E := hAlg
  haveI : Finite E := D.finite_E
  refine ⟨E, hE, Fintype.ofFinite E, ?_, ?_⟩
  · rw [Fintype.card_eq_nat_card, D.card_E]
  · refine ⟨(ggK1Df_omegaEquiv hx hQ hT).trans ?_⟩
    exact (MulEquiv.subgroupCongr hEqR).trans
      ((MulEquiv.subgroupCongr hcomm).trans (MonoidHom.ofInjective hinj).symm)

theorem ggK1D_fixed_abelian {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {m : ℕ} (hm : m ≤ 1)
    (hW : Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 2 * m) :
    ∀ a ∈ supportedBlock Q x (X - 1) ⊓
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      ∀ b ∈ supportedBlock Q x (X - 1) ⊓
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
        Commute a b := by
  intro a ha b hb
  have hR : (QuadraticMap.polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hWfix : Module.finrank K (fixedSpace x) = 2 * m := by
    rw [fixedSpace_eq_primaryComponent]; exact hW
  have hcomm : Commute ((ggK1Df_omegaEquiv hx hQ hT) ⟨a, ha⟩)
      ((ggK1Df_omegaEquiv hx hQ hT) ⟨b, hb⟩) := by
    have hle2 : Module.finrank K (fixedSpace x) ≤ 2 := by rw [hWfix]; omega
    rcases eq_or_lt_of_le hle2 with h2 | hlt
    · exact ggK1Df_omegaGroup_commute_of_finrank_two hR h2 _ _
    · have h0 : Module.finrank K (fixedSpace x) = 0 := by omega
      haveI : Subsingleton (fixedSpace x) := Module.finrank_zero_iff.mp h0
      haveI : Subsingleton (fixedSpace x ≃ₗ[K] fixedSpace x) :=
        ⟨fun f g => LinearEquiv.ext fun v => Subsingleton.elim _ _⟩
      have hxy : ((ggK1Df_omegaEquiv hx hQ hT) ⟨a, ha⟩) =
          ((ggK1Df_omegaEquiv hx hQ hT) ⟨b, hb⟩) := Subsingleton.elim _ _
      rw [hxy]
  have h1 : (ggK1Df_omegaEquiv hx hQ hT) (⟨a, ha⟩ * ⟨b, hb⟩) =
      (ggK1Df_omegaEquiv hx hQ hT) (⟨b, hb⟩ * ⟨a, ha⟩) := by
    rw [map_mul, map_mul]
    exact hcomm.eq
  exact congrArg Subtype.val ((ggK1Df_omegaEquiv hx hQ hT).injective h1)

theorem ggK1D_tame_fixed {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hnot4 : ¬ (Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 4 ∧
      CFSG.GroupTheory.WeirSylow.IsPlusType
        (Q.restrict (primaryComponent x.toLinearMap (X - 1))))) :
    CFSG.IsQuasisimple ↥⁅supportedBlock Q x (X - 1) ⊓
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      supportedBlock Q x (X - 1) ⊓
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆⁆ ∨
    Group.IsSolvable ↥(supportedBlock Q x (X - 1) ⊓
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) := by
  classical
  have hR : (QuadraticMap.polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  obtain ⟨s, hs⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo
    (Q.comp (fixedSpace x).subtype) hR
  have hs2 : Module.finrank K (fixedSpace x) = 2 * s := by omega
  have hW : Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 2 * s := by
    rw [← fixedSpace_eq_primaryComponent]; exact hs2
  by_cases hs1 : s ≤ 1
  · right
    have hab := ggK1D_fixed_abelian hx hQ hT hs1 hW
    exact Group.isSolvable_of_comm fun a b => Subtype.ext (hab a a.2 b b.2).eq
  · left
    have hs2le : 2 ≤ s := by omega
    haveI : Nontrivial (fixedSpace x) :=
      Module.nontrivial_of_finrank_pos (R := K) (by omega)
    by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
        (Q.restrict (primaryComponent x.toLinearMap (X - 1)))
    · by_cases hs4 : s = 2
      · exfalso
        exact hnot4 ⟨by rw [hW, hs4], hplus⟩
      · have hs3 : 3 ≤ s := by omega
        obtain ⟨e⟩ := ggK1D_fixed_omega hx hQ hT hs3 hW hplus
        have hq : CFSG.IsQuasisimple (StatedOmega (StatedQuadPlus s K)) :=
          CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus (K := K) hs3
        exact ggK1Df_isQuasisimple_commutator _
          (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq)
    · by_cases hs4 : s = 2
      · have hminusR : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
            (Q.comp (fixedSpace x).subtype) := by
          rw [fixedSpace_eq_primaryComponent]; exact hplus
        have hWfix4 : Module.finrank K (fixedSpace x) = 4 := by
          rw [fixedSpace_eq_primaryComponent, hW, hs4]
        have hts4 : ∀ U : Submodule K (fixedSpace x), Module.finrank K U = 2 →
            ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
          intro U hU
          by_contra h
          push Not at h
          exact hminusR ⟨U, by rw [hU, hWfix4], h⟩
        have hEqR4 : omegaGroup (Q.comp (fixedSpace x).subtype) hR =
            orthDerived (Q.comp (fixedSpace x).subtype) :=
          le_antisymm
            (CFSG.SeitzReduction.OmegaPilot.omegaGroup_le_orthDerived_of_four hR hWfix4 hts4)
            (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR)
        have hq4 : CFSG.IsQuasisimple
            ↥(omegaGroup (Q.comp (fixedSpace x).subtype) hR) :=
          CFSG.LocalCores.isQuasisimple_of_mulEquiv
            (MulEquiv.subgroupCongr hEqR4).symm
            (CFSG.SeitzReduction.OmegaPilot.isQuasisimple_orthDerived_of_four
              hR hWfix4 hts4).1
        exact ggK1Df_isQuasisimple_commutator _
          (CFSG.LocalCores.isQuasisimple_of_mulEquiv
            (ggK1Df_omegaEquiv hx hQ hT).symm hq4)
      · have hs3 : 3 ≤ s := by omega
        obtain ⟨b, c, hirr, ⟨e⟩⟩ := ggK1D_fixed_omegaMinus hx hQ hT hs3 hW hplus
        by_cases hs3eq : s = 3
        · have hminusR : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
              (Q.comp (fixedSpace x).subtype) := by
            rw [fixedSpace_eq_primaryComponent]; exact hplus
          have hWfix6 : Module.finrank K (fixedSpace x) = 6 := by
            rw [fixedSpace_eq_primaryComponent, hW, hs3eq]
          have hts6 : ∀ U : Submodule K (fixedSpace x), Module.finrank K U = 3 →
              ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
            intro U hU
            by_contra h
            push Not at h
            exact hminusR ⟨U, by rw [hU, hWfix6], h⟩
          have hEqR6 : omegaGroup (Q.comp (fixedSpace x).subtype) hR =
              orthDerived (Q.comp (fixedSpace x).subtype) :=
            le_antisymm
              (CFSG.SeitzReduction.OmegaPilot.omegaGroup_le_orthDerived_of_six hR hWfix6 hts6)
              (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR)
          have hq6 : CFSG.IsQuasisimple
              ↥(omegaGroup (Q.comp (fixedSpace x).subtype) hR) :=
            CFSG.LocalCores.isQuasisimple_of_mulEquiv
              (MulEquiv.subgroupCongr hEqR6).symm
              (CFSG.SeitzReduction.OmegaPilot.isQuasisimple_orthDerived_of_six
                hR hWfix6 hts6).1
          exact ggK1Df_isQuasisimple_commutator _
            (CFSG.LocalCores.isQuasisimple_of_mulEquiv
              (ggK1Df_omegaEquiv hx hQ hT).symm hq6)
        · have hs4' : 4 ≤ s := by omega
          have hq : CFSG.IsQuasisimple (StatedOmega (StatedQuadMinus s K b c)) :=
            CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadMinus (n := s) (K := K)
              hs4' hirr
          exact ggK1Df_isQuasisimple_commutator _
            (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq)

end CFSG.StandardType

end
