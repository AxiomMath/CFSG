module

public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.Blueprint.ChevalleyRootArtifact

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 RootSpace

@[expose] def supp1356 : Set (Fin Tag.E6.rank) := {0, 2, 4, 5}

@[expose] def supp13 : Set (Fin Tag.E6.rank) := {0, 2}

@[expose] def supp56 : Set (Fin Tag.E6.rank) := {4, 5}

theorem mem_supp1356 (i : Fin Tag.E6.rank) : i ∈ supp1356 ↔ i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 5 := by
  simp [supp1356]

theorem mem_supp13 (i : Fin Tag.E6.rank) : i ∈ supp13 ↔ i = 0 ∨ i = 2 := by
  simp [supp13]

theorem mem_supp56 (i : Fin Tag.E6.rank) : i ∈ supp56 ↔ i = 4 ∨ i = 5 := by
  simp [supp56]

theorem ncard_parabolicRoots_supp13 : (parabolicRoots Tag.E6 supp13).ncard = 6 :=
  ncard_parabolicRoots_eq mem_supp13 (by decide +kernel)

theorem ncard_parabolicRoots_supp56 : (parabolicRoots Tag.E6 supp56).ncard = 6 :=
  ncard_parabolicRoots_eq mem_supp56 (by decide +kernel)

theorem ncard_parabolicRoots_supp1356 : (parabolicRoots Tag.E6 supp1356).ncard = 12 :=
  ncard_parabolicRoots_eq mem_supp1356 (by decide +kernel)

theorem finite_parabolicRoots (J : Set (Fin Tag.E6.rank)) : (parabolicRoots Tag.E6 J).Finite :=
  (finite_setOf_isRoot Tag.E6).subset fun _ h => h.1

theorem exists_graph_transport {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    {z : Fin Tag.E6.rank → ZMod p} {w : WeylGroup Tag.E6}
    (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x) :
    ∃ u : WeylGroup Tag.E6, ∃ J : Set (Fin Tag.E6.rank),
      (u • ·) '' rootKernel z = parabolicRoots Tag.E6 J ∧ (∀ i, i ∈ J ↔ e6Rho i ∈ J) ∧
      u * w * e6WeylTwist u⁻¹ ∈
        Subgroup.closure {s | ∃ i, s = simple Tag.E6 i ∧ i ∈ J} := by
  classical
  have : Fintype (dualWeylStabilizer z) := Fintype.ofFinite _
  set r' := graphAvgColumn (avgColumn (dualWeylStabilizer z) (intLift z)) w
  have hkey : ∀ α, IsRoot Tag.E6 α → (charVal r' α = 0 ↔ α ∈ rootKernel z) := fun α hα =>
    charVal_graphAvgColumn_eq_zero_iff hp5 hb hα
  have hbfix : weylAct Tag.E6 w (e6TwistIsometry (dualVector r')) = dualVector r' :=
    weylAct_twist_dualVector_eq (charVal_graphAvgColumn_graph hb)
  obtain ⟨w₁, Y, hY, hy'⟩ := exists_weylAct_mem_dominantCone (dualVector r')
  set u := w₁⁻¹ with hu
  have huy : weylAct Tag.E6 u (dualVector r') = Y := by
    rw [hy', ← weylAct_mul_apply, hu, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]
  set J : Set (Fin Tag.E6.rank) := {i | inner ℝ (ofLattice (Pi.single i 1)) Y = 0} with hJdef
  have hinner : ∀ α : Fin Tag.E6.rank → ℤ,
      inner ℝ (ofLattice (u • α)) Y = ((charVal r' α : ℤ) : ℝ) := fun α => by
    rw [← huy, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map,
      inner_ofLattice_dualVector]
  have hΦ : (u • ·) '' rootKernel z = parabolicRoots Tag.E6 J := by
    ext β
    constructor
    · rintro ⟨α, hα, rfl⟩
      refine ⟨IsRoot.smul hα.1 u, fun i hi => ?_⟩
      have h0 : inner ℝ (ofLattice (u • α)) Y = 0 := by
        rw [hinner, (hkey α hα.1).2 hα, Int.cast_zero]
      exact (inner_root_eq_zero_iff hY (IsRoot.smul hα.1 u)).1 h0 i hi
    · rintro ⟨hβ, hsupp⟩
      have h0 : inner ℝ (ofLattice β) Y = 0 :=
        (inner_root_eq_zero_iff hY hβ).2 fun i hi => hsupp i hi
      refine ⟨u⁻¹ • β, ?_, smul_inv_smul u β⟩
      have hα : IsRoot Tag.E6 (u⁻¹ • β) := IsRoot.smul hβ u⁻¹
      refine (hkey _ hα).1 ?_
      have := hinner (u⁻¹ • β)
      rw [smul_inv_smul, h0] at this
      exact_mod_cast this.symm
  set a := u * w * e6WeylTwist u⁻¹ with ha_def
  have h1 : weylAct Tag.E6 u⁻¹ Y = dualVector r' := by
    rw [← huy, ← weylAct_mul_apply, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]
  have haψ : weylAct Tag.E6 a (e6TwistIsometry Y) = Y := by
    calc weylAct Tag.E6 a (e6TwistIsometry Y)
        = weylAct Tag.E6 u (weylAct Tag.E6 w
            (weylAct Tag.E6 (e6WeylTwist u⁻¹) (e6TwistIsometry Y))) := by
          rw [ha_def, weylAct_mul_apply, weylAct_mul_apply]
      _ = weylAct Tag.E6 u (weylAct Tag.E6 w (e6TwistIsometry (weylAct Tag.E6 u⁻¹ Y))) := by
          rw [e6TwistIsometry_weylAct]
      _ = Y := by rw [h1, hbfix, huy]
  have hψdom : e6TwistIsometry Y ∈ dominantCone Tag.E6 := fun i => by
    rw [inner_single_e6TwistIsometry]
    exact hY _
  have hψY : e6TwistIsometry Y = Y := by
    have h := weylAct_eq_of_mem_dominantCone hψdom (g := a) (by rw [haψ]; exact hY)
    rw [haψ] at h
    exact h.symm
  have haY : weylAct Tag.E6 a Y = Y := by
    have h := haψ
    rwa [hψY] at h
  have hJρ : ∀ i, i ∈ J ↔ e6Rho i ∈ J := fun i => by
    simp only [hJdef, Set.mem_ofPred_eq]
    rw [← inner_single_e6TwistIsometry, hψY]
  have ha : a ∈ Subgroup.closure
      {s | ∃ i, s = simple Tag.E6 i ∧ inner ℝ (ofLattice (Pi.single i 1)) Y = 0} := by
    rw [← weylStabilizer_eq_closure_simple hY]
    exact haY
  exact ⟨u, J, hΦ, hJρ, ha⟩

theorem supp1356_check : ∀ S : Finset (Fin Tag.E6.rank), (∀ i, i ∈ S ↔ e6Rho i ∈ S) →
    (Finset.univ.filter fun m : Fin 72 => ∀ i, i ∉ S → e6RootVec m i = 0).card = 12 →
    (∃ m ∈ Finset.univ.filter fun m : Fin 72 => ∀ i, i ∉ S → e6RootVec m i = 0,
      ∃ m₁ ∈ Finset.univ.filter fun m : Fin 72 => ∀ i, i ∉ S → e6RootVec m i = 0,
      ∃ m₂ ∈ Finset.univ.filter fun m : Fin 72 => ∀ i, i ∉ S → e6RootVec m i = 0,
      ∃ m₃ ∈ Finset.univ.filter fun m : Fin 72 => ∀ i, i ∉ S → e6RootVec m i = 0,
        m₁ ≠ m₂ ∧ m₁ ≠ m₃ ∧ m₂ ≠ m₃ ∧ e6Form (e6RootVec m) (e6RootVec m₁) = 0 ∧
          e6Form (e6RootVec m) (e6RootVec m₂) = 0 ∧ e6Form (e6RootVec m) (e6RootVec m₃) = 0) →
    S = {0, 2, 4, 5} := by
  decide +kernel

theorem e6RootVec_mem_filter {J : Set (Fin Tag.E6.rank)} [DecidablePred (· ∈ J)]
    {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ parabolicRoots Tag.E6 J) :
    ∃ m ∈ Finset.univ.filter fun m : Fin 72 => ∀ i, i ∉ J.toFinset → e6RootVec m i = 0,
      e6RootVec m = α := by
  obtain ⟨m, hm⟩ := isRoot_iff_exists_e6RootVec.1 hα.1
  refine ⟨m, Finset.mem_filter.2 ⟨Finset.mem_univ m, fun i hi => ?_⟩, hm⟩
  rw [Set.mem_toFinset] at hi
  rw [hm]
  exact hα.2 i hi

theorem eq_supp1356 {J : Set (Fin Tag.E6.rank)} (hJρ : ∀ i, i ∈ J ↔ e6Rho i ∈ J)
    {g : WeylGroup Tag.E6}
    (hg : (g • ·) '' parabolicRoots Tag.E6 supp1356 = parabolicRoots Tag.E6 J) :
    J = supp1356 := by
  classical
  have hS : ∀ i, i ∈ J.toFinset ↔ e6Rho i ∈ J.toFinset := fun i => by
    rw [Set.mem_toFinset, Set.mem_toFinset]
    exact hJρ i
  have hcard : (parabolicRoots Tag.E6 J).ncard = 12 := by
    rw [← hg, Set.ncard_image_of_injective _ (MulAction.injective g),
      ncard_parabolicRoots_supp1356]
  have hcard' : (Finset.univ.filter fun m : Fin 72 =>
      ∀ i, i ∉ J.toFinset → e6RootVec m i = 0).card = 12 := by
    rw [← hcard]
    exact (ncard_parabolicRoots_eq (P := fun i => i ∈ J.toFinset)
      (fun i => (Set.mem_toFinset).symm) rfl).symm
  have hmem : ∀ x ∈ parabolicRoots Tag.E6 supp1356, g • x ∈ parabolicRoots Tag.E6 J :=
    fun x hx => hg ▸ ⟨x, hx, rfl⟩
  have hx₀ : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 supp1356 :=
    single_mem_parabolicRoots_E6 (by simp [supp1356])
  have hx₄ : (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 supp1356 :=
    single_mem_parabolicRoots_E6 (by simp [supp1356])
  have hx₅ : (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 supp1356 :=
    single_mem_parabolicRoots_E6 (by simp [supp1356])
  have hx₄₅ : (Pi.single 4 1 + Pi.single 5 1 : Fin Tag.E6.rank → ℤ) ∈
      parabolicRoots Tag.E6 supp1356 := by
    refine ⟨isRoot_iff_mem_artifactRoots.2 (by decide +kernel), fun i hi => ?_⟩
    rw [mem_supp1356] at hi
    have h4 : i ≠ 4 := fun h => hi (Or.inr (Or.inr (Or.inl h)))
    have h5 : i ≠ 5 := fun h => hi (Or.inr (Or.inr (Or.inr h)))
    simp [h4, h5]
  obtain ⟨m, hm, hme⟩ := e6RootVec_mem_filter (hmem _ hx₀)
  obtain ⟨m₁, hm₁, hme₁⟩ := e6RootVec_mem_filter (hmem _ hx₄)
  obtain ⟨m₂, hm₂, hme₂⟩ := e6RootVec_mem_filter (hmem _ hx₅)
  obtain ⟨m₃, hm₃, hme₃⟩ := e6RootVec_mem_filter (hmem _ hx₄₅)
  have hform : ∀ x y : Fin Tag.E6.rank → ℤ, e6Form (g • x) (g • y) = e6Form x y := fun x y => by
    rw [← iform_eq_e6Form, ← iform_eq_e6Form, iform_smul]
  have hne : ∀ {k l : Fin 72}, ∀ {x y : Fin Tag.E6.rank → ℤ}, e6RootVec k = g • x →
      e6RootVec l = g • y → x ≠ y → k ≠ l := fun hk hl hxy hkl =>
    hxy (MulAction.injective g (hk.symm.trans ((congrArg e6RootVec hkl).trans hl)))
  have hS' := supp1356_check J.toFinset hS hcard' ⟨m, hm, m₁, hm₁, m₂, hm₂, m₃, hm₃,
    hne hme₁ hme₂ (by decide +kernel), hne hme₁ hme₃ (by decide +kernel),
    hne hme₂ hme₃ (by decide +kernel),
    by rw [hme, hme₁, hform]; decide +kernel, by rw [hme, hme₂, hform]; decide +kernel,
    by rw [hme, hme₃, hform]; decide +kernel⟩
  ext i
  rw [← Set.mem_toFinset, hS', mem_supp1356]
  simp

theorem supp13_maps_rho : ∀ m : Fin 72, (∀ i, ¬(i = 0 ∨ i = 2) → e6RootVec m i = 0) →
    ∀ i, ¬(i = 4 ∨ i = 5) → permLattice e6Rho (e6RootVec m) i = 0 := by
  decide +kernel

theorem supp56_maps_rho : ∀ m : Fin 72, (∀ i, ¬(i = 4 ∨ i = 5) → e6RootVec m i = 0) →
    ∀ i, ¬(i = 0 ∨ i = 2) → permLattice e6Rho (e6RootVec m) i = 0 := by
  decide +kernel

theorem supp13_maps_simple : ∀ j : Fin Tag.E6.rank, (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5) →
    ∀ m : Fin 72, (∀ i, ¬(i = 0 ∨ i = 2) → e6RootVec m i = 0) →
      ∀ i, ¬(i = 0 ∨ i = 2) → reflect Tag.E6 j (e6RootVec m) i = 0 := by
  decide +kernel

theorem supp56_maps_simple : ∀ j : Fin Tag.E6.rank, (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5) →
    ∀ m : Fin 72, (∀ i, ¬(i = 4 ∨ i = 5) → e6RootVec m i = 0) →
      ∀ i, ¬(i = 4 ∨ i = 5) → reflect Tag.E6 j (e6RootVec m) i = 0 := by
  decide +kernel

theorem supp13_not_orth : ∀ m m' : Fin 72, (∀ i, ¬(i = 0 ∨ i = 2) → e6RootVec m i = 0) →
    (∀ i, ¬(i = 0 ∨ i = 2) → e6RootVec m' i = 0) → e6Form (e6RootVec m) (e6RootVec m') ≠ 0 := by
  decide +kernel

theorem supp13_supp56_orth : ∀ m m' : Fin 72, (∀ i, ¬(i = 0 ∨ i = 2) → e6RootVec m i = 0) →
    (∀ i, ¬(i = 4 ∨ i = 5) → e6RootVec m' i = 0) → e6Form (e6RootVec m) (e6RootVec m') = 0 := by
  decide +kernel

theorem supp1356_split : ∀ m : Fin 72,
    (∀ i, ¬(i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 5) → e6RootVec m i = 0) →
      (∀ i, ¬(i = 0 ∨ i = 2) → e6RootVec m i = 0) ∨
        (∀ i, ¬(i = 4 ∨ i = 5) → e6RootVec m i = 0) := by
  decide +kernel

theorem maps_parabolicRoots {f : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ}
    {S T : Set (Fin Tag.E6.rank)} {P Q : Fin Tag.E6.rank → Prop} (hS : ∀ i, i ∈ S ↔ P i)
    (hT : ∀ i, i ∈ T ↔ Q i) (hroot : ∀ x, IsRoot Tag.E6 x → IsRoot Tag.E6 (f x))
    (h : ∀ m : Fin 72, (∀ i, ¬P i → e6RootVec m i = 0) → ∀ i, ¬Q i → f (e6RootVec m) i = 0) :
    ∀ x ∈ parabolicRoots Tag.E6 S, f x ∈ parabolicRoots Tag.E6 T := by
  intro x hx
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hx.1
  refine ⟨hroot _ hx.1, fun i hi => h m (fun j hj => hx.2 j ((hS j).not.2 hj)) i
    ((hT i).not.1 hi)⟩

theorem rho_mem_supp56 {x : Fin Tag.E6.rank → ℤ} (hx : x ∈ parabolicRoots Tag.E6 supp13) :
    permLattice e6Rho x ∈ parabolicRoots Tag.E6 supp56 :=
  maps_parabolicRoots mem_supp13 mem_supp56
    (fun _ h => h.permLattice TwistTag.E6.cartan_perm) supp13_maps_rho x hx

theorem rho_mem_supp13 {x : Fin Tag.E6.rank → ℤ} (hx : x ∈ parabolicRoots Tag.E6 supp56) :
    permLattice e6Rho x ∈ parabolicRoots Tag.E6 supp13 :=
  maps_parabolicRoots mem_supp56 mem_supp13
    (fun _ h => h.permLattice TwistTag.E6.cartan_perm) supp56_maps_rho x hx

theorem image_supp_of_mem_closure {a : WeylGroup Tag.E6}
    (ha : a ∈ Subgroup.closure {s | ∃ i, s = simple Tag.E6 i ∧ i ∈ supp1356}) :
    (a • ·) '' parabolicRoots Tag.E6 supp13 = parabolicRoots Tag.E6 supp13 ∧
      (a • ·) '' parabolicRoots Tag.E6 supp56 = parabolicRoots Tag.E6 supp56 := by
  have hgen : ∀ j ∈ supp1356, ∀ T ∈ [supp13, supp56],
      (simple Tag.E6 j • ·) '' parabolicRoots Tag.E6 T = parabolicRoots Tag.E6 T := by
    intro j hj T hT
    have hj' : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 5 := (mem_supp1356 j).1 hj
    have hmaps : ∀ x ∈ parabolicRoots Tag.E6 T, simple Tag.E6 j • x ∈ parabolicRoots Tag.E6 T := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl
      · exact maps_parabolicRoots mem_supp13 mem_supp13 (fun x h => IsRoot.smul h _)
          (fun m hm i hi => by rw [simple_smul]; exact supp13_maps_simple j hj' m hm i hi)
      · exact maps_parabolicRoots mem_supp56 mem_supp56 (fun x h => IsRoot.smul h _)
          (fun m hm i hi => by rw [simple_smul]; exact supp56_maps_simple j hj' m hm i hi)
    refine Set.Subset.antisymm (by rintro _ ⟨x, hx, rfl⟩; exact hmaps x hx) fun x hx => ?_
    refine ⟨simple Tag.E6 j • x, hmaps x hx, ?_⟩
    simp only
    rw [← mul_smul, simple_mul_simple_self, one_smul]
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl, hj⟩ := hx
    exact ⟨hgen j hj supp13 (by simp), hgen j hj supp56 (by simp)⟩
  | one => simp
  | mul x y _ _ hx hy =>
    refine ⟨?_, ?_⟩
    · rw [show (fun z => (x * y) • z) = (fun z => x • z) ∘ fun z => y • z by
        funext z; exact mul_smul x y z, Set.image_comp, hy.1, hx.1]
    · rw [show (fun z => (x * y) • z) = (fun z => x • z) ∘ fun z => y • z by
        funext z; exact mul_smul x y z, Set.image_comp, hy.2, hx.2]
  | inv x _ hx =>
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hx.1]
      rw [Set.image_image]
      simp
    · conv_lhs => rw [← hx.2]
      rw [Set.image_image]
      simp

theorem image_supp13_cases {g : WeylGroup Tag.E6}
    (hg : (g • ·) '' parabolicRoots Tag.E6 supp1356 = parabolicRoots Tag.E6 supp1356) :
    (g • ·) '' parabolicRoots Tag.E6 supp13 = parabolicRoots Tag.E6 supp13 ∨
      (g • ·) '' parabolicRoots Tag.E6 supp13 = parabolicRoots Tag.E6 supp56 := by
  have hsub13 : parabolicRoots Tag.E6 supp13 ⊆ parabolicRoots Tag.E6 supp1356 :=
    parabolicRoots_mono (by intro i; simp [supp13, supp1356]; tauto)
  have hsplit : ∀ y ∈ parabolicRoots Tag.E6 supp1356,
      y ∈ parabolicRoots Tag.E6 supp13 ∨ y ∈ parabolicRoots Tag.E6 supp56 := by
    intro y hy
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hy.1
    rcases supp1356_split m (fun i hi => hy.2 i ((mem_supp1356 i).not.2 hi)) with h | h
    · exact Or.inl ⟨hy.1, fun i hi => h i ((mem_supp13 i).not.1 hi)⟩
    · exact Or.inr ⟨hy.1, fun i hi => h i ((mem_supp56 i).not.1 hi)⟩
  have hform : ∀ x y : Fin Tag.E6.rank → ℤ, e6Form (g • x) (g • y) = e6Form x y := fun x y => by
    rw [← iform_eq_e6Form, ← iform_eq_e6Form, iform_smul]
  have hnot : ∀ x ∈ parabolicRoots Tag.E6 supp13, ∀ y ∈ parabolicRoots Tag.E6 supp13,
      e6Form x y ≠ 0 := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hx.1
    obtain ⟨m', rfl⟩ := isRoot_iff_exists_e6RootVec.1 hy.1
    exact supp13_not_orth m m' (fun i hi => hx.2 i ((mem_supp13 i).not.2 hi))
      (fun i hi => hy.2 i ((mem_supp13 i).not.2 hi))
  have horth : ∀ x ∈ parabolicRoots Tag.E6 supp13, ∀ y ∈ parabolicRoots Tag.E6 supp56,
      e6Form x y = 0 := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hx.1
    obtain ⟨m', rfl⟩ := isRoot_iff_exists_e6RootVec.1 hy.1
    exact supp13_supp56_orth m m' (fun i hi => hx.2 i ((mem_supp13 i).not.2 hi))
      (fun i hi => hy.2 i ((mem_supp56 i).not.2 hi))
  have hin : ∀ x ∈ parabolicRoots Tag.E6 supp13, g • x ∈ parabolicRoots Tag.E6 supp1356 :=
    fun x hx => hg ▸ ⟨x, hsub13 hx, rfl⟩
  have hcard : ((g • ·) '' parabolicRoots Tag.E6 supp13).ncard = 6 := by
    rw [Set.ncard_image_of_injective _ (MulAction.injective g), ncard_parabolicRoots_supp13]
  by_cases h : ∃ x ∈ parabolicRoots Tag.E6 supp13, g • x ∈ parabolicRoots Tag.E6 supp13
  · left
    obtain ⟨x, hx, hgx⟩ := h
    have hsub : (g • ·) '' parabolicRoots Tag.E6 supp13 ⊆ parabolicRoots Tag.E6 supp13 := by
      rintro _ ⟨y, hy, rfl⟩
      rcases hsplit _ (hin y hy) with h' | h'
      · exact h'
      · exact absurd (by rw [← hform]; exact horth _ hgx _ h') (hnot x hx y hy)
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, ncard_parabolicRoots_supp13])
      (finite_parabolicRoots _)
  · right
    push Not at h
    have hsub : (g • ·) '' parabolicRoots Tag.E6 supp13 ⊆ parabolicRoots Tag.E6 supp56 := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hsplit _ (hin y hy)).resolve_left (h y hy)
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, ncard_parabolicRoots_supp56])
      (finite_parabolicRoots _)

theorem E6_large_prime_two_A2_graph_stabilizers_exchange_components {p : ℕ} [Fact p.Prime]
    (hp5 : 5 < p) (z : Fin Tag.E6.rank → ZMod p) (_hz : z ≠ 0) (v : WeylGroup Tag.E6)
    (hv : (v • ·) '' rootKernel z = parabolicRoots Tag.E6 supp1356) (w : WeylGroup Tag.E6)
    (hb : (((rhoMatrix * weylMatrix w⁻¹).map (Int.cast : ℤ → ZMod p)).transpose).mulVec z = z) :
    (fun x => w • permLattice e6Rho x) '' ((v⁻¹ • ·) '' parabolicRoots Tag.E6 supp13) =
        (v⁻¹ • ·) '' parabolicRoots Tag.E6 supp56 ∧
      (fun x => w • permLattice e6Rho x) '' ((v⁻¹ • ·) '' parabolicRoots Tag.E6 supp56) =
        (v⁻¹ • ·) '' parabolicRoots Tag.E6 supp13 := by
  have hb' := graph_dual_fixed_iff.1 hb
  obtain ⟨u, J, hΦ, hJρ, ha⟩ := exists_graph_transport hp5 hb'
  have hg : ((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 supp1356 = parabolicRoots Tag.E6 J := by
    rw [← hv, Set.image_image, ← hΦ]
    congr 1
    funext x
    rw [mul_smul, inv_smul_smul]
  have hJ : J = supp1356 := eq_supp1356 hJρ hg
  subst hJ
  obtain ⟨ha13, ha56⟩ := image_supp_of_mem_closure ha
  set a := u * w * e6WeylTwist u⁻¹ with ha_def
  have hrel : ∀ x, u • (w • permLattice e6Rho x) = a • permLattice e6Rho (u • x) := fun x => by
    rw [ha_def, mul_smul, mul_smul, e6WeylTwist_smul, permLattice_e6Rho_e6Rho, inv_smul_smul]
  set b : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ := fun x => w • permLattice e6Rho x
  have hb_inj : Function.Injective b := fun x y h => by
    have h' := congrArg (fun t => permLattice e6Rho (w⁻¹ • t)) h
    simp only [b, inv_smul_smul, permLattice_e6Rho_e6Rho] at h'
    exact h'
  have hmapsto : ∀ {S T : Set (Fin Tag.E6.rank)},
      (∀ y ∈ parabolicRoots Tag.E6 S, permLattice e6Rho y ∈ parabolicRoots Tag.E6 T) →
      (a • ·) '' parabolicRoots Tag.E6 T = parabolicRoots Tag.E6 T →
      ∀ x ∈ (u⁻¹ • ·) '' parabolicRoots Tag.E6 S, b x ∈ (u⁻¹ • ·) '' parabolicRoots Tag.E6 T := by
    intro S T hρ haT x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨u • b (u⁻¹ • y), ?_, inv_smul_smul u _⟩
    show u • (w • permLattice e6Rho (u⁻¹ • y)) ∈ parabolicRoots Tag.E6 T
    rw [hrel, smul_inv_smul, ← haT]
    exact ⟨_, hρ y hy, rfl⟩
  have hcard6 : ∀ {S : Set (Fin Tag.E6.rank)}, (parabolicRoots Tag.E6 S).ncard = 6 →
      ((u⁻¹ • ·) '' parabolicRoots Tag.E6 S).ncard = 6 := fun h => by
    rw [Set.ncard_image_of_injective _ (MulAction.injective u⁻¹), h]
  have hex : ∀ {S T : Set (Fin Tag.E6.rank)}, (parabolicRoots Tag.E6 S).ncard = 6 →
      (parabolicRoots Tag.E6 T).ncard = 6 →
      (∀ y ∈ parabolicRoots Tag.E6 S, permLattice e6Rho y ∈ parabolicRoots Tag.E6 T) →
      (a • ·) '' parabolicRoots Tag.E6 T = parabolicRoots Tag.E6 T →
      b '' ((u⁻¹ • ·) '' parabolicRoots Tag.E6 S) = (u⁻¹ • ·) '' parabolicRoots Tag.E6 T := by
    intro S T hS hT hρ haT
    refine Set.eq_of_subset_of_ncard_le (by rintro _ ⟨x, hx, rfl⟩; exact hmapsto hρ haT x hx) ?_
      ((finite_parabolicRoots T).image _)
    rw [Set.ncard_image_of_injective _ hb_inj, hcard6 hS, hcard6 hT]
  have hu13 := hex ncard_parabolicRoots_supp13 ncard_parabolicRoots_supp56
    (fun y hy => rho_mem_supp56 hy) ha56
  have hu56 := hex ncard_parabolicRoots_supp56 ncard_parabolicRoots_supp13
    (fun y hy => rho_mem_supp13 hy) ha13
  have hg' : ((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 supp1356 =
      parabolicRoots Tag.E6 supp1356 := hg
  have htrans : ∀ S : Set (Fin Tag.E6.rank), (v⁻¹ • ·) '' parabolicRoots Tag.E6 S =
      (u⁻¹ • ·) '' (((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 S) := fun S => by
    rw [Set.image_image]
    congr 1
    funext x
    rw [mul_smul, inv_smul_smul]
  have hdisj : parabolicRoots Tag.E6 supp13 ≠ parabolicRoots Tag.E6 supp56 := by
    intro h
    have hmem : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 supp13 :=
      single_mem_parabolicRoots_E6 (by simp [supp13])
    rw [h] at hmem
    exact absurd (hmem.2 0 (by simp [supp56])) (by simp)
  have h56cases : ((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 supp56 =
      parabolicRoots Tag.E6 supp13 ∨ ((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 supp56 =
      parabolicRoots Tag.E6 supp56 := by
    have hunion : parabolicRoots Tag.E6 supp1356 =
        parabolicRoots Tag.E6 supp13 ∪ parabolicRoots Tag.E6 supp56 := by
      ext y
      constructor
      · intro hy
        obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hy.1
        rcases supp1356_split m (fun i hi => hy.2 i ((mem_supp1356 i).not.2 hi)) with h | h
        · exact Or.inl ⟨hy.1, fun i hi => h i ((mem_supp13 i).not.1 hi)⟩
        · exact Or.inr ⟨hy.1, fun i hi => h i ((mem_supp56 i).not.1 hi)⟩
      · rintro (hy | hy)
        · exact parabolicRoots_mono (by intro i; simp [supp13, supp1356]; tauto) hy
        · exact parabolicRoots_mono (by intro i; simp [supp56, supp1356]; tauto) hy
    have hdisj' : Disjoint (parabolicRoots Tag.E6 supp13) (parabolicRoots Tag.E6 supp56) := by
      rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hy.1
      have := supp13_supp56_orth m m (fun i hi => hy.2 i ((mem_supp13 i).not.2 hi))
        (fun i hi => hy'.2 i ((mem_supp56 i).not.2 hi))
      rw [← iform_eq_e6Form] at this
      exact absurd this (by
        rw [iform_eq_e6Form]
        exact supp13_not_orth m m (fun i hi => hy.2 i ((mem_supp13 i).not.2 hi))
          (fun i hi => hy.2 i ((mem_supp13 i).not.2 hi)))
    have himage := hg'
    rw [hunion, Set.image_union] at himage
    rcases image_supp13_cases hg' with h | h
    · right
      rw [h] at himage
      have hdisjimg : Disjoint (((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 supp13)
          (((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 supp56) :=
        (Set.disjoint_image_iff (MulAction.injective _)).2 hdisj'
      rw [h] at hdisjimg
      refine Set.eq_of_subset_of_ncard_le (fun y hy => ?_) ?_ (finite_parabolicRoots _)
      · have hy' : y ∈ parabolicRoots Tag.E6 supp13 ∪ parabolicRoots Tag.E6 supp56 := by
          rw [← hunion, ← hg', hunion, Set.image_union]
          exact Or.inr hy
        rcases hy' with hy' | hy'
        · exact absurd hy (Set.disjoint_left.1 hdisjimg hy')
        · exact hy'
      · rw [Set.ncard_image_of_injective _ (MulAction.injective _)]
    · left
      have hdisjimg : Disjoint (((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 supp13)
          (((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 supp56) :=
        (Set.disjoint_image_iff (MulAction.injective _)).2 hdisj'
      rw [h] at hdisjimg
      refine Set.eq_of_subset_of_ncard_le (fun y hy => ?_) ?_ (finite_parabolicRoots _)
      · have hy' : y ∈ parabolicRoots Tag.E6 supp13 ∪ parabolicRoots Tag.E6 supp56 := by
          rw [← hunion, ← hg', hunion, Set.image_union]
          exact Or.inr hy
        rcases hy' with hy' | hy'
        · exact hy'
        · exact absurd hy (Set.disjoint_left.1 hdisjimg hy')
      · rw [Set.ncard_image_of_injective _ (MulAction.injective _), ncard_parabolicRoots_supp13,
          ncard_parabolicRoots_supp56]
  rcases image_supp13_cases hg' with h13 | h13
  · have h56 : ((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 supp56 =
        parabolicRoots Tag.E6 supp56 := by
      rcases h56cases with h | h
      · exfalso
        apply hdisj
        have := (Set.image_injective.2 (MulAction.injective (u * v⁻¹))) (h13.trans h.symm)
        rw [this]
      · exact h
    rw [htrans, htrans, h13, h56]
    exact ⟨hu13, hu56⟩
  · have h56 : ((u * v⁻¹) • ·) '' parabolicRoots Tag.E6 supp56 =
        parabolicRoots Tag.E6 supp13 := by
      rcases h56cases with h | h
      · exact h
      · exfalso
        apply hdisj
        have := (Set.image_injective.2 (MulAction.injective (u * v⁻¹))) (h13.trans h.symm)
        rw [this]
    rw [htrans, htrans, h13, h56]
    exact ⟨hu56, hu13⟩

end CFSG.RankThree.Lattice
