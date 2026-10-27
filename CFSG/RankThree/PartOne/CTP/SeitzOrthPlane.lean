module

public import CFSG.ClassicalGroups.Orthogonal.RootCenters
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityData
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.RankThree.PartOne.CTP

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def orthCentralizerSpan (Ã : Subgroup (orthDerived Q)) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {g : V ≃ₗ[K] V | g ∈ orthDerived Q ∧
    ∃ x ∈ Ã.map (orthDerived Q).subtype, x ≠ 1 ∧ g * x = x * g}

theorem orthCentralizerSpan_le_orthogonalGroup (Ã : Subgroup (orthDerived Q)) :
    orthCentralizerSpan Q Ã ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨hg, -⟩
  exact orthDerived_le_orthogonalGroup Q hg

section Plane

variable [Finite K] [FiniteDimensional K V] {p : ℕ} {Ã : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem eichler_mem_orthCentralizerSpan (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    {e w : V} (he : e ∈ planeFixSpace Ã) {x : orthDerived Q} (hxÃ : x ∈ Ã) (hx1 : x ≠ 1)
    (hxw : ((x : orthDerived Q) : V ≃ₗ[K] V) w = w) :
    eichler Q e w ∈ orthCentralizerSpan Q Ã := by
  refine Subgroup.subset_closure ⟨hEΩ (eichler_mem_elementaryGroup Q e w),
    ((x : orthDerived Q) : V ≃ₗ[K] V), ⟨x, hxÃ, rfl⟩, ?_, ?_⟩
  · intro h
    exact hx1 (Subtype.ext h)
  · have hxe : ((x : orthDerived Q) : V ≃ₗ[K] V) e = e := he _ ⟨x, hxÃ, rfl⟩
    have hconj := eichler_conj (Q := Q) (orthDerived_le_orthogonalGroup Q x.2) e w
    rw [hxe, hxw] at hconj
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

omit [Finite K] [FiniteDimensional K V] in
theorem eichler_mem_orthCentralizerSpan_of_fix (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    {e w : V} {x : orthDerived Q} (hxÃ : x ∈ Ã) (hx1 : x ≠ 1)
    (hxe : ((x : orthDerived Q) : V ≃ₗ[K] V) e = e)
    (hxw : ((x : orthDerived Q) : V ≃ₗ[K] V) w = w) :
    eichler Q e w ∈ orthCentralizerSpan Q Ã := by
  refine Subgroup.subset_closure ⟨hEΩ (eichler_mem_elementaryGroup Q e w),
    ((x : orthDerived Q) : V ≃ₗ[K] V), ⟨x, hxÃ, rfl⟩, ?_, ?_⟩
  · intro h
    exact hx1 (Subtype.ext h)
  · have hconj := eichler_conj (Q := Q) (orthDerived_le_orthogonalGroup Q x.2) e w
    rw [hxe, hxw] at hconj
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

open _root_.Classical in
theorem isRootCenter_of_mem_planeFix (hp : p.Prime) (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    (hK : KernelLineData Q p Ã) {e : V} (he : e ∈ planeFixSpace Ã) (hQe : Q e = 0)
    (he0 : e ≠ 0) : IsRootCenter Q (orthCentralizerSpan Q Ã) e := by
  refine ⟨he0, hQe, fun w hw => ?_⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  set H := orthCentralizerSpan Q Ã with hH
  obtain ⟨x₀, hx₀Ã, hx₀1⟩ : ∃ x : orthDerived Q, x ∈ Ã ∧ x ≠ 1 := by
    have : Nontrivial ↥Ã := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hK.card]
      exact Nat.one_lt_pow two_ne_zero hp.one_lt)
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥Ã)
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have step1 : ∀ (M : {M : Subgroup Ã // Nat.card M = p}) (w : V), w ∈ lineSpace M.1 →
      polar Q e w = 0 ∧ eichler Q e w ∈ H := by
    intro M w hw
    refine ⟨?_, ?_⟩
    · have := hK.orth none (some M) (by simp) e he w hw
      simpa using this
    · obtain ⟨a, haM, ha1⟩ : ∃ a : ↥Ã, a ∈ M.1 ∧ a ≠ 1 := by
        have : Nontrivial ↥M.1 := Finite.one_lt_card_iff_nontrivial.mp (by
          rw [M.2]; exact hp.one_lt)
        obtain ⟨a, ha⟩ := exists_ne (1 : ↥M.1)
        exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
      refine eichler_mem_orthCentralizerSpan hEΩ he a.2 (fun h => ha1 (Subtype.ext h)) ?_
      exact (inf_le_left : lineSpace M.1 ≤ lineFixSpace M.1) hw _
        ⟨(a : orthDerived Q), ⟨a, haM, rfl⟩, rfl⟩
  have step2 : ∀ w' ∈ ⨆ M : {M : Subgroup Ã // Nat.card M = p}, lineSpace M.1,
      polar Q e w' = 0 ∧ eichler Q e w' ∈ H := by
    intro w' hw'
    refine Submodule.iSup_induction (fun M : {M : Subgroup Ã // Nat.card M = p} => lineSpace M.1)
      (motive := fun w' => polar Q e w' = 0 ∧ eichler Q e w' ∈ H) hw' ?_ ?_ ?_
    · intro M w hw
      exact step1 M w hw
    · exact ⟨polar_zero_right Q e, by rw [eichler_zero_right]; exact H.one_mem⟩
    · intro a b ha hb
      refine ⟨by rw [polar_add_right, ha.1, hb.1, add_zero], ?_⟩
      rw [← eichler_mul ha.1 hb.1]
      exact H.mul_mem ha.2 hb.2
  have htop : w ∈ planeFixSpace Ã ⊔ ⨆ M : {M : Subgroup Ã // Nat.card M = p}, lineSpace M.1 := by
    have h1 : ⨆ i, innerSummand p Ã i = ⊤ := hK.internal.submodule_iSup_eq_top
    rw [iSup_option] at h1
    rw [show planeFixSpace Ã ⊔ ⨆ M : {M : Subgroup Ã // Nat.card M = p}, lineSpace M.1 = ⊤ from h1]
    exact Submodule.mem_top
  obtain ⟨w₀, hw₀, w', hw', rfl⟩ := Submodule.mem_sup.1 htop
  have hpw' := (step2 w' hw').1
  have hpw₀ : polar Q e w₀ = 0 := by
    rw [polar_add_right, hpw', add_zero] at hw
    exact hw
  have hE₀ : eichler Q e w₀ ∈ H :=
    eichler_mem_orthCentralizerSpan hEΩ he hx₀Ã hx₀1 (hw₀ _ ⟨x₀, hx₀Ã, rfl⟩)
  rw [← eichler_mul hpw₀ hpw']
  exact H.mul_mem hE₀ (step2 w' hw').2

theorem elementaryGroup_le_orthCentralizerSpan_of_hypPair (hp : p.Prime)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : KernelLineData Q p Ã) (P : HypPair Q) (he : P.e ∈ planeFixSpace Ã)
    (hf : P.f ∈ planeFixSpace Ã) : elementaryGroup Q ≤ orthCentralizerSpan Q Ã := by
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  exact elementaryGroup_le_of_hypPair hQ (orthCentralizerSpan_le_orthogonalGroup Ã) P
    (isRootCenter_of_mem_planeFix hp hEΩ hK he P.Q_e P.e_ne_zero)
    (isRootCenter_of_mem_planeFix hp hEΩ hK hf P.Q_f P.f_ne_zero)

end Plane

end CFSG.RankThree.PartOne.CTP
