module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CyclicImplementersPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankThreeInner
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointRankOrbit
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart1

@[expose] public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement Pointwise

namespace CFSG.StandardType.F4ExplicitPos.NativePinFinal
attribute [local irreducible] CFSG.LieType.Chevalley.kernelRoots
  CFSG.LieType.Chevalley.torusGroup CFSG.Blueprint.Chevalley.rootSubgroup

theorem step_pinnedX_F4
    {Ω : Type} [Field Ω] (D : LangDatum Tag.F4 Ω) :
    ∃ ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ),
      (∀ γ, IsRoot Tag.F4 (ρ γ) ↔ IsRoot Tag.F4 γ) ∧
      (∀ γ, ρ (-γ) = -ρ γ) ∧
      (∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) ∧
      ∀ γ, IsRoot Tag.F4 γ → ∃ μ : Ω, μ ≠ 0 ∧
        ∀ c : Ω, D.step (pinnedX Tag.F4 Ω γ c) =
          pinnedX Tag.F4 Ω (ρ γ) (μ * c ^ D.q) := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  have hP1 : P = 1 := by
    rcases hP with h | ⟨t, ht, rfl⟩
    · exact h
    · exact absurd ht (by cases t <;> decide)
  obtain ⟨w, hn⟩ := D.n_weyl
  refine ⟨MulAction.toPerm w, fun γ => ?_, fun γ => ?_, fun γ δ => ?_, fun γ hγ => ?_⟩
  · simp only [MulAction.toPerm_apply]; exact isRoot_smul_iff w
  · simp only [MulAction.toPerm_apply]; exact smul_neg w γ
  · simp only [MulAction.toPerm_apply]; exact iform_smul w γ δ
  · obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv Ω w hγ
    refine ⟨ε, ?_, fun c => ?_⟩
    · intro h0; rw [h0, mul_zero] at hε; exact zero_ne_one hε
    · have hs : D.step (pinnedX Tag.F4 Ω γ c) =
          D.n * D.Φ (pinnedX Tag.F4 Ω γ c) * D.n⁻¹ := by
        simp [LangDatum.step, MulAut.conj_apply]
      have he : Units.map (entrywiseHom Fr) (pinnedX Tag.F4 Ω γ c) =
          pinnedX Tag.F4 Ω γ (Fr c) := Units.ext (entrywise_pinnedX_native Fr γ c)
      rw [hs, hΦ, hP1, one_mul, inv_one, mul_one, hn, he, hFr, h]
      rfl

theorem map_rootSpan_le_of_forall_native
    {τ : Tag} {L : Type} [Field L]
    {φ : ModGL τ L →* ModGL τ L} {S T : Set (Fin τ.rank → ℤ)}
    (h : ∀ γ ∈ S, ∀ c : L, φ (pinnedX τ L γ c) ∈ rootSpan τ L T) :
    (rootSpan τ L S).map φ ≤ rootSpan τ L T := by
  simp only [rootSpan, Subgroup.map_iSup]
  refine iSup₂_le fun γ hγ => ?_
  rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  exact h γ hγ c

theorem langDatum_q_pos
    {τ : Tag} {Ω : Type} [Field Ω] (D : LangDatum τ Ω) : 0 < D.q := by
  by_contra h
  have h0 : D.q = 0 := Nat.eq_zero_of_not_pos h
  obtain ⟨Fr, hFr, -⟩ := D.steinberg
  have h1 := hFr 0
  rw [h0, pow_zero] at h1
  exact one_ne_zero (h1.symm.trans (map_zero Fr))

theorem step_pinnedX_F4_perm
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (D : LangDatum Tag.F4 Ω)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ) :
    ∃ ρ₀ : Equiv.Perm (Fin Tag.F4.rank → ℤ),
      (∀ γ, IsRoot Tag.F4 γ → ρ γ = ρ₀ γ) ∧
      (∀ γ, IsRoot Tag.F4 γ → ∃ μ : Ω, μ ≠ 0 ∧
        ∀ c : Ω, D.step (pinnedX Tag.F4 Ω γ c) =
          pinnedX Tag.F4 Ω (ρ₀ γ) (μ * c ^ D.q)) := by
  obtain ⟨ρ₀, hρ₀root, -, -, hρ₀par⟩ := step_pinnedX_F4 D
  have hqpos : 0 < D.q := langDatum_q_pos D
  refine ⟨ρ₀, fun γ hγ => ?_, hρ₀par⟩
  have h1 : (rootSubgroup Tag.F4 Ω γ).map D.step = rootSubgroup Tag.F4 Ω (ρ γ) :=
    hρ.map_rootSubgroup γ hγ
  have h2 : (rootSubgroup Tag.F4 Ω γ).map D.step = rootSubgroup Tag.F4 Ω (ρ₀ γ) := by
    obtain ⟨μ, hμ0, hμ⟩ := hρ₀par γ hγ
    refine map_rootSubgroup_eq_of_forall (g := fun c => μ * c ^ D.q) ?_ ?_
    · intro d
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (μ⁻¹ * d) hqpos
      refine ⟨c, ?_⟩
      show μ * c ^ D.q = d
      rw [hc, ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]
    · exact hμ
  exact eq_of_rootSubgroup_eq ((hρ.isRoot_iff γ).2 hγ) ((hρ₀root γ).2 hγ) (h1.symm.trans h2)

theorem step_eq_frobTwistGL_F4
    {Ω : Type} [Field Ω] [CharP Ω 2] (D : LangDatum Tag.F4 Ω) (f : ℕ)
    (hq : D.q = 2 ^ f) :
    ∃ Q : ModGL Tag.F4 Ω, (∀ g, D.step g = frobTwistGL Tag.F4 Ω 2 f Q g) ∧
      Q ∈ Subgroup.normalizer (torusGroup Tag.F4 Ω : Set (ModGL Tag.F4 Ω)) := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  have hP1 : P = 1 := by
    rcases hP with h | ⟨t, ht, rfl⟩
    · exact h
    · exact absurd ht (by cases t <;> decide)
  obtain ⟨w, hn⟩ := D.n_weyl
  refine ⟨D.n * P, fun g => ?_, ?_⟩
  · rw [frobTwistGL_apply]
    show D.n * D.Φ g * D.n⁻¹ =
      (D.n * P) * entrywiseFrobGL Tag.F4 Ω 2 f g * (D.n * P)⁻¹
    have hFrE : Fr = iterateFrobenius Ω 2 f := by
      ext c; rw [hFr, iterateFrobenius_def, hq]
    rw [hΦ g, hFrE]
    group
  · rw [hP1, mul_one, hn]
    exact canonicalRep_mem_normalizer w

theorem frobTwistGL_F4_stable
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (D : LangDatum Tag.F4 Ω) (f : ℕ) (Q : ModGL Tag.F4 Ω)
    (hstep : ∀ g, D.step g = frobTwistGL Tag.F4 Ω 2 f Q g)
    (hQnorm : Q ∈ Subgroup.normalizer (torusGroup Tag.F4 Ω : Set (ModGL Tag.F4 Ω)))
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) :
    ∀ g ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ),
      frobTwistGL Tag.F4 Ω 2 f Q g ∈
        torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ) := by
  have : PerfectRing Ω 2 := IsAlgClosed.perfectRing Ω 2
  intro g hg
  rw [← hstep]
  have hnormT : torusGroup Tag.F4 Ω ≤ Subgroup.normalizer
      (rootSpan Tag.F4 Ω (kernelRoots χ) : Set (ModGL Tag.F4 Ω)) :=
    torusGroup_le_normalizer_rootSpan (K := Ω) (fun _ hα => isRoot_of_mem_kernelRoots (L := Ω) hα)
  have hcoe : (↑(torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ)) :
      Set (ModGL Tag.F4 Ω)) =
      (torusGroup Tag.F4 Ω : Set (ModGL Tag.F4 Ω)) *
        (rootSpan Tag.F4 Ω (kernelRoots χ) : Set (ModGL Tag.F4 Ω)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnormT
  have hg' : g ∈ (torusGroup Tag.F4 Ω : Set (ModGL Tag.F4 Ω)) *
      (rootSpan Tag.F4 Ω (kernelRoots χ) : Set (ModGL Tag.F4 Ω)) := by
    rw [← hcoe]; exact hg
  obtain ⟨t, ht, r, hr, rfl⟩ := Set.mem_mul.1 hg'
  rw [map_mul]
  refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
  · rw [hstep t, ← map_frobTwistGL_torusGroup (τ := Tag.F4) (k := Ω) (p := 2) f (Q := Q) hQnorm]
    exact ⟨t, ht, rfl⟩
  · have hmap : (rootSpan Tag.F4 Ω (kernelRoots χ)).map D.step ≤
        rootSpan Tag.F4 Ω (kernelRoots χ) := by
      refine map_rootSpan_le_of_forall_native fun γ hγ c => ?_
      have hmem : D.step (pinnedX Tag.F4 Ω γ c) ∈ (rootSubgroup Tag.F4 Ω γ).map D.step :=
        Subgroup.mem_map_of_mem _ (mem_rootSubgroup.2 ⟨c, rfl⟩)
      rw [hρ.map_rootSubgroup γ (isRoot_of_mem_kernelRoots (L := Ω) hγ)] at hmem
      exact rootSubgroup_le_rootSpan (hker γ hγ) hmem
    exact hmap ⟨r, hr, rfl⟩

theorem exists_pin_F4_rho_native
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (D : LangDatum Tag.F4 Ω) (f : ℕ) (hq : D.q = 2 ^ f)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (i : KernelComponent χ) (hinner : twistInner (componentRoots χ i) ρ) :
    ∃ (σ : Ω ≃+* Ω) (y : ModGL Tag.F4 Ω), (∀ c, σ c = c ^ D.q) ∧
      y ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (componentRoots χ i) ∧
      ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots χ i), y * D.step g * y⁻¹ = frobGL σ g := by
  classical
  have h2 : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
  obtain ⟨ρ₀, hρeq, hρ₀par⟩ := step_pinnedX_F4_perm D ρ hρ
  obtain ⟨w, hw, hwγ⟩ := hinner
  let σ : Ω ≃+* Ω := iterateFrobeniusEquiv Ω 2 f
  have hσc : ∀ c, σ c = c ^ D.q := by
    intro c
    rw [iterateFrobeniusEquiv_def, hq]
  have hφpin : ∀ γ ∈ componentRoots χ i, ∃ m : Ω, m ≠ 0 ∧
      ∀ c : Ω, D.step (pinnedX Tag.F4 Ω γ c) = pinnedX Tag.F4 Ω (w • γ) (m * σ c) := by
    intro γ hγ
    have hγr : IsRoot Tag.F4 γ := isRoot_of_mem_componentRoots hγ
    obtain ⟨μ, hμ0, hμ⟩ := hρ₀par γ hγr
    refine ⟨μ, hμ0, fun c => ?_⟩
    rw [hμ c, ← hρeq γ hγr, hwγ γ hγ, hσc]
  obtain ⟨y, hyS, hpin⟩ := exists_pin_of_two (τ := Tag.F4) h2 i σ D.step hw hφpin
  exact ⟨σ, y, hσc, hyS, hpin⟩

theorem conj_normalizes_component_native
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (j : KernelComponent χ) {z : ModGL Tag.F4 Ω}
    (hz : z ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ))
    (g : ModGL Tag.F4 Ω) :
    g ∈ rootSpan Tag.F4 Ω (componentRoots χ j) ↔
      z * g * z⁻¹ ∈ rootSpan Tag.F4 Ω (componentRoots χ j) := by
  obtain ⟨g₀, hg₀, hg₀'⟩ :=
    CyclicImplementers.exists_mem_componentRootSpan_conj_eq_of_mem_Z_good
      (χ := χ) j hz
  constructor
  · intro hx
    rw [hg₀' g hx]
    exact mul_mem (mul_mem hg₀ hx) (inv_mem hg₀)
  · intro hx
    have hz' : z⁻¹ ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ) := inv_mem hz
    obtain ⟨g₁, hg₁, hg₁'⟩ :=
      CyclicImplementers.exists_mem_componentRootSpan_conj_eq_of_mem_Z_good
        (χ := χ) j hz'
    have hconj : z⁻¹ * (z * g * z⁻¹) * (z⁻¹)⁻¹ = g := by group
    have hthis := hg₁' (z * g * z⁻¹) hx
    rw [hconj] at hthis
    rw [hthis]
    exact mul_mem (mul_mem hg₁ hx) (inv_mem hg₁)

theorem exists_untwist_one_step_native
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (D : LangDatum Tag.F4 Ω) (f : ℕ) (hf : 1 ≤ f) (hq : D.q = 2 ^ f)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (i : KernelComponent χ)
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hinner : twistInner (componentRoots χ i) ρ) :
    ∃ (σ : Ω ≃+* Ω) (z : ModGL Tag.F4 Ω), (∀ c, σ c = c ^ D.q) ∧
      z ∈ Zsub χ ∧ normalizesAll χ z ∧
      ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots χ i),
        D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
  classical
  have hpinres : ∃ (σ : Ω ≃+* Ω) (y : ModGL Tag.F4 Ω), (∀ c, σ c = c ^ D.q) ∧
      y ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (componentRoots χ i) ∧
      ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots χ i), y * D.step g * y⁻¹ = frobGL σ g :=
    exists_pin_F4_rho_native (Ω := Ω) (χ := χ) D f hq ρ hρ i hinner
  rcases hpinres with ⟨σ, y, hσc, hyS, hpin⟩
  have hle : rootSpan Tag.F4 Ω (componentRoots χ i) ≤
      rootSpan Tag.F4 Ω (kernelRoots χ) :=
    rootSpan_mono fun γ hγ => mem_kernelRoots_of_mem_componentRoots (L := Ω) hγ
  have hyZ : y ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ) :=
    (sup_le_sup_left hle _) hyS
  obtain ⟨Q, hstep, hQnorm⟩ := step_eq_frobTwistGL_F4 D f hq
  have hFZ : ∀ g ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ),
      frobTwistGL Tag.F4 Ω 2 f Q g ∈
        torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ) :=
    frobTwistGL_F4_stable (χ := χ) D f Q hstep hQnorm ρ hρ hker
  have hlang : ∃ z ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ),
      frobTwistGL Tag.F4 Ω 2 f Q z = z * y :=
    CFSG.StandardType.F4ExplicitPos.ConnectedJoint.exists_frobTwist_eq_mul_torus_sup_rootSpan_no117
      (τ := Tag.F4) (k := Ω) (p := 2) (S := kernelRoots χ) f hf Q hFZ y hyZ
  rcases hlang with ⟨z, hzZ, hzF⟩
  have hnorm : normalizesAll (χ := χ) z := by
    intro j g
    exact conj_normalizes_component_native (χ := χ) j hzZ g
  have hgoal : ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
    intro g hg
    have h1 : D.step z = z * y := by rw [hstep]; exact hzF
    have h2 : D.step (z * g * z⁻¹) = D.step z * D.step g * (D.step z)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [h2, h1]
    rw [show (z * y) * D.step g * (z * y)⁻¹ = z * (y * D.step g * y⁻¹) * z⁻¹ by group]
    rw [hpin g hg]
  refine ⟨σ, z, hσc, ?_, hnorm, hgoal⟩
  show z ∈ Zsub χ
  exact hzZ

theorem f4_exists_untwist_one_step_rankThree_native
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [CharP Ω 2]
    (D : LangDatum Tag.F4 Ω) (f : ℕ) (hf : 1 ≤ f) (hq : D.q = 2 ^ f)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    {p : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) (hpΩ : (p : Ω) ≠ 0)
    {a : Fin Tag.F4.rank → Ωˣ} (ha : rootDiagUnit Tag.F4 a ∈ D.torus)
    (hap : rootDiagUnit Tag.F4 a ^ p = 1) (ha1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (v : WeylGroup Tag.F4) (J : Set (Fin Tag.F4.rank))
      (σ : Ω ≃+* Ω) (z : ModGL Tag.F4 Ω),
      (J = CFSG.HardMathSupport.Solomon.Coordinator.LieComp.f4LeviB3 ∨
        J = CFSG.ComponentClassification.CatLeafProof.f4LeviC3) ∧
      componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J ∧
      (∀ c, σ c = c ^ D.q) ∧
      z ∈ Zsub (rootCharHom a) ∧ normalizesAll (rootCharHom a) z ∧
      ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots (rootCharHom a) i),
        D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
  classical
  obtain ⟨v, J, hJ, hshape, hr, hc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4_rank_ge_three_component_is_levi
      hp hp2 hpΩ hap ha1 i h3
  have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
  obtain ⟨hstable, -⟩ :=
    JointRankOrbit.f4_cyclic_componentOrbitLength_eq_one_of_rank_ge_two
      D ρ hρ a ha i h2
  have hstable' : (fun γ => ρ γ) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := hstable
  obtain ⟨u, hu, huγ⟩ :=
    CFSG.StandardType.F4ExplicitPos.RankThreeInner.f4_rankThree_component_rho_isInner
      hρ i hr hc hstable'
  have hWle : componentWeylGroup (componentRoots (rootCharHom a) i) ≤
      Subgroup.closure {s : WeylGroup Tag.F4 |
        ∃ γ ∈ componentRoots (rootCharHom a) i, s = rootReflection γ} := by
    rw [componentWeylGroup]
    exact Subgroup.closure_mono
      (by rintro _ ⟨β, hβ, rfl⟩; exact ⟨β, simpleRoots_subset hβ, rfl⟩)
  have hinner : twistInner (componentRoots (rootCharHom a) i) ρ := ⟨u, hWle hu, huγ⟩
  have hker : ∀ γ ∈ kernelRoots (rootCharHom a), ρ γ ∈ kernelRoots (rootCharHom a) := by
    intro γ hγ
    have hγroot : IsRoot Tag.F4 γ := isRoot_of_mem_kernelRoots (L := Ω) hγ
    have hγ1 : rootChar a γ = 1 := by
      rw [kernelRoots] at hγ
      exact hγ.2
    rw [kernelRoots]
    refine ⟨(hρ.isRoot_iff γ).2 hγroot, ?_⟩
    show rootChar a (ρ γ) = 1
    rw [hρ.rootChar_eq a ha γ hγroot, hγ1, one_pow]
  obtain ⟨σ, z, hσc, hzZ, hnorm, hgoal⟩ :=
    exists_untwist_one_step_native (χ := rootCharHom a) D f hf hq ρ hρ i hker hinner
  refine ⟨v, J, σ, z, hJ, hshape, hσc, ?_, ?_, ?_⟩
  · exact hzZ
  · exact hnorm
  · exact hgoal

theorem Zsub_eq
    {Ω : Type} [Field Ω] {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M) :
    Zsub χ = torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ) := by
  ext z
  constructor
  · intro h; exact h
  · intro h; exact h

theorem mem_Zsub_iff
    {Ω : Type} [Field Ω] {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M) (z : ModGL Tag.F4 Ω) :
    z ∈ Zsub χ ↔ z ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ) :=
  Iff.intro (fun h => h) (fun h => h)

theorem Zsub_le_adjointGroup
    {Ω : Type} [Field Ω] {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M) :
    Zsub χ ≤ adjointGroup Tag.F4 Ω := by
  rw [Zsub_eq]
  exact sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
    (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup Ω (kernelRoots χ))

theorem normalizesAll_iff
    {Ω : Type} [Field Ω] {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M) (z : ModGL Tag.F4 Ω) :
    normalizesAll χ z ↔ ∀ j : KernelComponent χ, ∀ g : ModGL Tag.F4 Ω,
      g ∈ rootSpan Tag.F4 Ω (componentRoots χ j) ↔
        z * g * z⁻¹ ∈ rootSpan Tag.F4 Ω (componentRoots χ j) :=
  Iff.intro (fun h j g => h j g) (fun h j g => h j g)

theorem normalizesAll_apply
    {Ω : Type} [Field Ω] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M} {z : ModGL Tag.F4 Ω}
    (h : normalizesAll χ z) (j : KernelComponent χ) (g : ModGL Tag.F4 Ω) :
    g ∈ rootSpan Tag.F4 Ω (componentRoots χ j) ↔
      z * g * z⁻¹ ∈ rootSpan Tag.F4 Ω (componentRoots χ j) :=
  h j g

end CFSG.StandardType.F4ExplicitPos.NativePinFinal

end

end
