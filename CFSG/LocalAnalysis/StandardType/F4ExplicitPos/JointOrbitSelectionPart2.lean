module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointOrbitSelectionPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.JointOrbitSelection
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
open CFSG.Assembly
open CFSG.StandardType.F4ExplicitPos.FamilyPosition
open CFSG.LieType.Steinberg.Adjoint
open Matrix
open scoped commutatorElement Pointwise
variable {τ : Tag} {L : Type} [Field L]

section PerfectJoint
variable {K : Type} [Field K] {ι : Type}

theorem f4_perfect_le_familyKernel
    (a : ι → Fin Tag.F4.rank → Kˣ)
    {P : Subgroup (ModGL Tag.F4 K)}
    (hP : P ≤ familyCentralizer Tag.F4 K a) (hperf : ⁅P, P⁆ = P) :
    P ≤ rootSpan Tag.F4 K (familyKernel a) := by
  have hN : Group.IsSolvable ↥(monomialSubgroup Tag.F4 K) :=
    f4_isSolvable_monomialSubgroup (K := K)
  have hY : Group.IsSolvable ↥(familyWeylSubgroup (K := K) a) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (familyWeylSubgroup_le_monomialSubgroup (K := K) a))
  have hPMY : P ≤ familyGroup (K := K) a ⊔ familyWeylSubgroup (K := K) a := by
    intro g hg
    obtain ⟨w, hw, m, hm, rfl⟩ := f4_familyCentralizer_le_mul (K := K) a (hP hg)
    exact mul_mem (Subgroup.mem_sup_left hm)
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨w, hw, rfl⟩))
  have hPM : P ≤ familyGroup (K := K) a :=
    perfect_le_left_of_solvable_right
      (familyWeylSubgroup_le_normalizer_familyGroup (K := K) a) hperf hPMY
  calc P = ⁅P, P⁆ := hperf.symm
    _ ≤ ⁅familyGroup (K := K) a, familyGroup (K := K) a⁆ :=
        Subgroup.commutator_mono hPM hPM
    _ ≤ rootSpan Tag.F4 K (familyKernel a) :=
        CFSG.StandardType.LayerExc.commutator_torus_sup_rootSpan_le
          (K := K) (S := familyKernel a) (fun α hα => hα.1)

theorem pair_familyKernel_eq_kernelRoots_jointChar (a₁ a₂ : Fin Tag.F4.rank → Kˣ) :
    familyKernel ![a₁, a₂] = kernelRoots (jointChar a₁ a₂) := by
  ext α
  simp only [familyKernel, kernelRoots, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hroot, hα⟩
    have h0 := hα 0
    have h1 := hα 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨hroot, ?_⟩
    rw [jointChar_apply, Prod.mk_eq_one]
    exact ⟨h0, h1⟩
  · rintro ⟨hroot, hα⟩
    refine ⟨hroot, fun i => ?_⟩
    have hα' := (Prod.mk_eq_one.1 ((jointChar_apply a₁ a₂
      (Multiplicative.ofAdd α)).symm.trans hα))
    fin_cases i
    · show rootChar a₁ (Multiplicative.toAdd (Multiplicative.ofAdd α)) = 1
      exact hα'.1
    · show rootChar a₂ (Multiplicative.toAdd (Multiplicative.ofAdd α)) = 1
      exact hα'.2

theorem familyCentralizer_pair_closure (a₁ a₂ : Fin Tag.F4.rank → Kˣ) :
    familyCentralizer Tag.F4 K ![a₁, a₂] =
      adjointGroup Tag.F4 K ⊓
        Subgroup.centralizer
          ((Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
            Subgroup (ModGL Tag.F4 K)) : Set (ModGL Tag.F4 K)) := by
  ext g
  rw [mem_familyCentralizer]
  simp only [Subgroup.mem_inf, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Subgroup.centralizer_closure]
  constructor
  · rintro ⟨hg, h1, h2⟩
    refine ⟨hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact (Subgroup.mem_centralizer_iff.1 (conj_eq_iff_mem_centralizer.1 h1)) _ (by simp)
    · exact (Subgroup.mem_centralizer_iff.1 (conj_eq_iff_mem_centralizer.1 h2)) _ (by simp)
  · rintro ⟨hg, hc⟩
    refine ⟨hg, ?_, ?_⟩
    · exact conj_eq_iff_mem_centralizer.2
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (by simp)) hc)
    · exact conj_eq_iff_mem_centralizer.2
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (by simp)) hc)

theorem pair_familyCentralizer_eq_centralizer (a₁ a₂ : Fin Tag.F4.rank → Kˣ) :
    familyCentralizer Tag.F4 K ![a₁, a₂] =
      adjointGroup Tag.F4 K ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
          Set (ModGL Tag.F4 K)) := by
  rw [familyCentralizer_pair_closure, Subgroup.centralizer_closure]

theorem f4_perfect_le_jointRootSpan
    (a₁ a₂ : Fin Tag.F4.rank → Kˣ)
    {P : Subgroup (ModGL Tag.F4 K)}
    (hP : P ≤ familyCentralizer Tag.F4 K ![a₁, a₂]) (hperf : ⁅P, P⁆ = P) :
    P ≤ rootSpan Tag.F4 K (kernelRoots (jointChar a₁ a₂)) := by
  have h := f4_perfect_le_familyKernel (K := K) (a := ![a₁, a₂]) hP hperf
  rwa [pair_familyKernel_eq_kernelRoots_jointChar] at h

theorem f4_perfect_le_jointRootSpan_of_centralizer
    (a₁ a₂ : Fin Tag.F4.rank → Kˣ)
    {P : Subgroup (ModGL Tag.F4 K)}
    (hP : P ≤ adjointGroup Tag.F4 K ⊓
      Subgroup.centralizer ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
        Set (ModGL Tag.F4 K)))
    (hperf : ⁅P, P⁆ = P) :
    P ≤ rootSpan Tag.F4 K (kernelRoots (jointChar a₁ a₂)) := by
  rw [← pair_familyCentralizer_eq_centralizer (K := K) a₁ a₂] at hP
  exact f4_perfect_le_jointRootSpan a₁ a₂ hP hperf

end PerfectJoint

theorem comp_le_or_commutator_eq_bot {G : Type*} [Group G]
    {X K U : Subgroup G} [Finite ↥X] (hK : IsComponentOf K X) (hU : IsSubnormal U X) :
    K ≤ U ∨ ⁅K, U⁆ = ⊥ := by
  have hUX : U ≤ X := hU.le
  have hK' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hK.1).1 hK
  rcases CFSG.LocalCores.component_subnormal_subgroup hK' hU.subgroupOf with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hK.1 h)
  · right
    have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rwa [inf_of_le_left hUX] at this

theorem isSubnormal_of_le_of_le' {G : Type*} [Group G] {K C M : Subgroup G}
    (h : IsSubnormal K C) (hKM : K ≤ M) (hMC : M ≤ C) : IsSubnormal K M := by
  have := h.inf M
  rwa [inf_eq_left.2 hKM, inf_eq_right.2 hMC] at this

theorem exists_noncomm_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Assembly.IsQuasisimple Q) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Q = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => h b a
  have := hQ.2.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (QuotientGroup.eq.2 (by rw [hc]; trivial))

theorem component_le_jointOrbitRootSpan_of_perfect
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    [Finite D.model]
    (a₁ a₂ : Fin Tag.F4.rank → Lˣ)
    (h₁ : rootDiagUnit Tag.F4 a₁ ∈ D.torus) (h₂ : rootDiagUnit Tag.F4 a₂ ∈ D.torus)
    (hperfjoint : ∀ {P : Subgroup (ModGL Tag.F4 L)},
      P ≤ adjointGroup Tag.F4 L ⊓ Subgroup.centralizer
        ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} : Set (ModGL Tag.F4 L)) →
      ⁅P, P⁆ = P → P ≤ rootSpan Tag.F4 L (kernelRoots (jointChar a₁ a₂)))
    (K : Subgroup (ModGL Tag.F4 L))
    (hK : IsComponentOf K (D.Γ ⊓ Subgroup.centralizer
      ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} : Set (ModGL Tag.F4 L)))) :
    ∃ i : KernelComponent (jointChar a₁ a₂),
      K ≤ rootSpan Tag.F4 L
        (ratOrbit (fun u => ρ u) (componentRoots (jointChar a₁ a₂) i)) := by
  classical
  set χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* Lˣ × Lˣ := jointChar a₁ a₂ with hχ
  have hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ := by
    rintro γ ⟨hγroot, hγχ⟩
    rw [hχ, jointChar_apply] at hγχ
    obtain ⟨h1', h2'⟩ := Prod.mk_eq_one.1 hγχ
    have h1'' : rootChar a₁ γ = 1 := h1'
    have h2'' : rootChar a₂ γ = 1 := h2'
    refine ⟨(hρ.isRoot_iff γ).2 hγroot, ?_⟩
    rw [hχ, jointChar_apply, Prod.mk_eq_one]
    refine ⟨?_, ?_⟩
    · show rootChar a₁ (ρ γ) = 1
      rw [hρ.rootChar_eq a₁ h₁ γ hγroot, h1'', one_pow]
    · show rootChar a₂ (ρ γ) = 1
      rw [hρ.rootChar_eq a₂ h₂ γ hγroot, h2'', one_pow]
  have hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ := hρ.iform_eq
  have hΓle : D.Γ ≤ D.model := Subgroup.commutator_le_self D.model
  have hΓ : D.Γ ≤ adjointGroup Tag.F4 L := hΓle.trans inf_le_left
  have hΓfix : ∀ x ∈ D.Γ, D.step x = x := fun x hx => (hΓle hx).2
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
  have hKmodel : K ≤ D.model := (hK.1.trans inf_le_left).trans hΓle
  have : Finite D.model := ‹Finite D.model›
  have : Finite ↥K :=
    Finite.of_injective (Subgroup.inclusion hKmodel) (Subgroup.inclusion_injective _)
  have hKadj : K ≤ adjointGroup Tag.F4 L ⊓ Subgroup.centralizer
      ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} : Set (ModGL Tag.F4 L)) :=
    fun x hx => ⟨hΓ (hK.1 hx).1, (hK.1 hx).2⟩
  have hKU : K ≤ rootSpan Tag.F4 L (kernelRoots χ) := by
    rw [hχ]
    exact hperfjoint hKadj hKperf
  have : Finite (kernelRoots χ) := ((finite_setOf_isRoot Tag.F4).subset fun α h => h.1).to_subtype
  have : Finite (KernelComponent χ) := inferInstance
  have : Finite (Set.range fun i => ratOrbit (fun u => ρ u) (componentRoots χ i)) :=
    (Set.finite_range _).to_subtype
  let A : Set.range (fun i => ratOrbit (fun u => ρ u) (componentRoots χ i)) →
      Subgroup (ModGL Tag.F4 L) := fun O => rootSpan Tag.F4 L O.1
  have hc : ∀ O O', O ≠ O' → ∀ x ∈ A O, ∀ y ∈ A O', Commute x y := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
    exact f4_ratOrbit_commute_rootSpan hker hform (fun h => hne (Subtype.ext h))
  have hF : ∀ O, ∀ x ∈ A O, D.step x ∈ A O := by
    rintro ⟨_, i, rfl⟩ x hx
    exact ratOrbit_step_mem_rootSpan D hρ
      (fun γ hγ => (ratOrbit_subset_kernelRoots hker i hγ).1)
      (ratOrbit_mapsTo i) hx
  have hU : ⨆ O, A O = rootSpan Tag.F4 L (kernelRoots χ) := by
    refine le_antisymm (iSup_le fun O => ?_) ?_
    · obtain ⟨_, i, rfl⟩ := O
      exact rootSpan_mono (ratOrbit_subset_kernelRoots hker i)
    · refine le_trans (iSup_componentRootSpan L (χ := χ)).ge (iSup_le fun i => ?_)
      have h : componentRootSpan L χ i ≤ A ⟨_, i, rfl⟩ :=
        rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩
      exact h.trans (le_iSup A ⟨_, i, rfl⟩)
  have hAadj : ∀ O, A O ≤ adjointGroup Tag.F4 L := fun O => rootSpan_le_adjointGroup L O.1
  have h1 := perfect_le_iSup_inf_fixed D.step A hc hF hKperf (hKU.trans hU.ge)
    fun x hx => hΓfix x (Subgroup.mem_inf.1 (hK.1 hx)).1
  have hc2 : ∀ O O', O ≠ O' → ∀ x ∈ A O ⊓ D.step.eqLocus (MonoidHom.id _),
      ∀ y ∈ A O' ⊓ D.step.eqLocus (MonoidHom.id _), Commute x y :=
    fun O O' hne x hx y hy => hc O O' hne x hx.1 y hy.1
  have h2 : K ≤ ⨆ O, A O ⊓ D.Γ := by
    refine (perfect_le_iSup_commutator (fun O => A O ⊓ D.step.eqLocus (MonoidHom.id _)) hc2
      hKperf h1).trans (iSup_mono fun O => le_inf ?_ ?_)
    · exact (Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (Subgroup.commutator_le_self _)
    · exact Subgroup.commutator_mono (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
        (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
  have hker₁ : ∀ i γ, γ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i) → rootChar a₁ γ = 1 := by
    intro i γ hγ
    have h := (ratOrbit_subset_kernelRoots hker i hγ).2
    rw [hχ, jointChar_apply] at h
    exact (Prod.mk_eq_one.1 h).1
  have hker₂ : ∀ i γ, γ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i) → rootChar a₂ γ = 1 := by
    intro i γ hγ
    have h := (ratOrbit_subset_kernelRoots hker i hγ).2
    rw [hχ, jointChar_apply] at h
    exact (Prod.mk_eq_one.1 h).2
  have hcent : ∀ O, A O ≤ Subgroup.centralizer
      ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} : Set (ModGL Tag.F4 L)) := by
    rintro ⟨_, i, rfl⟩ x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases (Set.mem_insert_iff.1 hy) with rfl | hy
    · exact (Subgroup.mem_centralizer_iff.1 (rootSpan_le_centralizer a₁
        (fun γ hγ => ⟨(ratOrbit_subset_kernelRoots hker i hγ).1, hker₁ i γ hγ⟩) hx)) _
        (Set.mem_singleton _)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.1 (rootSpan_le_centralizer a₂
        (fun γ hγ => ⟨(ratOrbit_subset_kernelRoots hker i hγ).1, hker₂ i γ hγ⟩) hx)) _
        (Set.mem_singleton _)
  set P' : Subgroup (ModGL Tag.F4 L) := ⨆ O, A O ⊓ D.Γ with hP'
  have hP'X : P' ≤ D.Γ ⊓ Subgroup.centralizer
      ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} : Set (ModGL Tag.F4 L)) :=
    iSup_le fun O => le_inf inf_le_right (inf_le_left.trans (hcent O))
  have hKP' : K ≤ P' := h2
  have : Finite ↥P' := Finite.of_injective
    (Subgroup.inclusion (((hP'X.trans inf_le_left).trans hΓle) : P' ≤ D.model))
    (Subgroup.inclusion_injective _)
  have hKcomp : IsComponentOf K P' :=
    ⟨hKP', isSubnormal_of_le_of_le' hK.2.1 hKP' hP'X, hK.2.2⟩
  have hnorm : ∀ O, ((A O ⊓ D.Γ).subgroupOf P').Normal := by
    intro O
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_iSup (fun O => A O ⊓ D.Γ) O)]
    refine iSup_le fun O' => ?_
    by_cases hOO : O' = O
    · rw [hOO]; exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (A O ⊓ D.Γ : Set (ModGL Tag.F4 L)))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hc O O' (Ne.symm hOO) y hy.1 x hx.1).eq
  have hsub : ∀ O, IsSubnormal (A O ⊓ D.Γ) P' := fun O =>
    IsSubnormal.step (le_iSup (fun O => A O ⊓ D.Γ) O) (hnorm O) (IsSubnormal.refl P')
  have hex : ∃ O, K ≤ A O ⊓ D.Γ := by
    by_contra hcon
    push Not at hcon
    have hcomm' : ∀ O, ⁅K, A O ⊓ D.Γ⁆ = ⊥ := fun O =>
      (comp_le_or_commutator_eq_bot hKcomp (hsub O)).resolve_left (hcon O)
    have hP'c : P' ≤ Subgroup.centralizer (K : Set (ModGL Tag.F4 L)) :=
      iSup_le fun O => Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((Subgroup.commutator_comm _ _).trans (hcomm' O))
    have hKc : K ≤ Subgroup.centralizer (K : Set (ModGL Tag.F4 L)) := hKP'.trans hP'c
    obtain ⟨x, y, hxy⟩ := exists_noncomm_of_isQuasisimple hK.2.2
    exact hxy (Subtype.ext (Subgroup.mem_centralizer_iff.1 (hKc y.2) x x.2))
  obtain ⟨⟨_, i, rfl⟩, hKi⟩ := hex
  exact ⟨i, hKi.trans inf_le_left⟩

theorem f4_component_le_jointOrbitRootSpan
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    [Finite D.model]
    (a₁ a₂ : Fin Tag.F4.rank → Lˣ)
    (h₁ : rootDiagUnit Tag.F4 a₁ ∈ D.torus) (h₂ : rootDiagUnit Tag.F4 a₂ ∈ D.torus)
    (K : Subgroup (ModGL Tag.F4 L))
    (hK : IsComponentOf K (D.Γ ⊓ Subgroup.centralizer
      ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} : Set (ModGL Tag.F4 L)))) :
    ∃ i : KernelComponent (jointChar a₁ a₂),
      K ≤ rootSpan Tag.F4 L
        (ratOrbit (fun u => ρ u) (componentRoots (jointChar a₁ a₂) i)) :=
  component_le_jointOrbitRootSpan_of_perfect D ρ hρ a₁ a₂ h₁ h₂
    (fun hP hperf => f4_perfect_le_jointRootSpan_of_centralizer (K := L) a₁ a₂ hP hperf)
    K hK

end CFSG.StandardType.F4ExplicitPos.JointOrbitSelection

end

end
