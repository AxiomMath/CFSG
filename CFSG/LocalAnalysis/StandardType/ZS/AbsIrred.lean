module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma exists_span_singleton_of_finrank_eq_one {L : Submodule (ZMod p) U}
    (hrank : Module.finrank (ZMod p) L = 1) :
    ∃ u : U, u ≠ 0 ∧ L = Submodule.span (ZMod p) {u} := by
  have hne : L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrank
    omega
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff L).mp hne
  exact ⟨u, hu0, eq_span_singleton_of_mem_of_finrank_eq_one hrank hu hu0⟩

private lemma exists_smul_id_of_forall_submodule_eq_bot_or_top
    (hall : ∀ W : Submodule (ZMod p) U, W = ⊥ ∨ W = ⊤) (T : Module.End (ZMod p) U) :
    ∃ c : ZMod p, T = c • LinearMap.id := by
  by_cases hu : ∃ u : U, u ≠ 0
  · obtain ⟨u, hu0⟩ := hu
    have hspan : Submodule.span (ZMod p) {u} = ⊤ := by
      rcases hall (Submodule.span (ZMod p) {u}) with h | h
      · exfalso
        have : u = 0 := by
          have hmem : u ∈ Submodule.span (ZMod p) {u} := Submodule.mem_span_singleton_self u
          rw [h] at hmem
          simpa using hmem
        exact hu0 this
      · exact h
    obtain ⟨c, hc⟩ : ∃ c : ZMod p, T u = c • u := by
      have : T u ∈ Submodule.span (ZMod p) {u} := by rw [hspan]; trivial
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
      exact ⟨c, hc.symm⟩
    let K : Submodule (ZMod p) U := LinearMap.ker (T - c • LinearMap.id)
    have huK : u ∈ K := by
      rw [LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      exact sub_eq_zero.mpr hc
    have hKne : K ≠ ⊥ := by
      intro h
      exact hu0 (by simpa using (h ▸ huK : u ∈ (⊥ : Submodule (ZMod p) U)))
    have hKtop : K = ⊤ := (hall K).resolve_left hKne
    refine ⟨c, ?_⟩
    apply LinearMap.ext
    intro w
    have hwK : w ∈ K := by rw [hKtop]; trivial
    rw [LinearMap.mem_ker] at hwK
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      using hwK
  · refine ⟨0, LinearMap.ext fun v => ?_⟩
    have hv : v = 0 := not_not.mp (not_exists.mp hu v)
    simp [hv]

private lemma eq_smul_id_of_eigenvector {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    {T : Module.End (ZMod p) U} {c : ZMod p} {u : U} (hu0 : u ≠ 0) (hu : T u = c • u)
    (hT : ∀ a ∈ A, T ∘ₗ (a : U →ₗ[ZMod p] U) = (a : U →ₗ[ZMod p] U) ∘ₗ T) :
    T = c • LinearMap.id := by
  let K : Submodule (ZMod p) U := LinearMap.ker (T - c • LinearMap.id)
  have hKinv : ∀ a ∈ A, ∀ w ∈ K, a w ∈ K := by
    intro a ha w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have hTwa : T (a w) = a (T w) := by
      have := congrArg (fun f : U →ₗ[ZMod p] U => f w) (hT a ha)
      simpa using this
    have hw' : T w = c • w := by
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
        using hw
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hTwa, hw', map_smul]
    simp
  have huK : u ∈ K := by
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact sub_eq_zero.mpr hu
  have hKne : K ≠ ⊥ := by
    intro h
    exact hu0 (by simpa using (h ▸ huK : u ∈ (⊥ : Submodule (ZMod p) U)))
  rcases hirr K hKinv with hbot | htop
  · exact absurd hbot hKne
  · apply LinearMap.ext
    intro w
    have hwK : w ∈ K := by rw [htop]; trivial
    rw [LinearMap.mem_ker] at hwK
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      using hwK

theorem absIrred_of_finrank_range_eq_one {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ A)
    (hrank : Module.finrank (ZMod p) (LinearMap.range ((r : U →ₗ[ZMod p] U) - LinearMap.id)) = 1) :
    AbsIrred p A := by
  refine ⟨hirr, ?_⟩
  intro T hT
  let rL : U →ₗ[ZMod p] U := (r : U →ₗ[ZMod p] U) - LinearMap.id
  obtain ⟨u, hu0, hL⟩ := exists_span_singleton_of_finrank_eq_one hrank
  have hcomp : T.comp rL = rL.comp T := by
    simp only [rL, LinearMap.comp_sub, LinearMap.sub_comp, hT r hr, LinearMap.comp_id,
      LinearMap.id_comp]
  have hTL : ∀ w ∈ LinearMap.range rL, T w ∈ LinearMap.range rL := by
    rintro w ⟨x, rfl⟩
    exact ⟨T x, by rw [← LinearMap.comp_apply, ← hcomp, LinearMap.comp_apply]⟩
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, T u = c • u := by
    have := hTL u (by rw [hL]; exact Submodule.mem_span_singleton_self u)
    rw [hL] at this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨c, hc.symm⟩
  exact ⟨c, eq_smul_id_of_eigenvector hirr hu0 hc hT⟩

theorem absIrred_of_reflGen {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤) :
    AbsIrred p A := by
  by_cases hrefl : ∃ t ∈ A, IsRefl p t
  · obtain ⟨t, htA, ht⟩ := hrefl
    exact absIrred_of_finrank_range_eq_one hirr htA ht.2
  · have hA : A = ⊥ := by
      rw [hgen]
      have hS : {t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsRefl p t} = ∅ := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        exact ⟨fun h => hrefl ⟨t, h.1, h.2⟩, False.elim⟩
      rw [hS, Subgroup.closure_empty]
    have hall : ∀ W : Submodule (ZMod p) U, W = ⊥ ∨ W = ⊤ := fun W =>
      hirr W (fun a ha w hw => by
        rw [hA, Subgroup.mem_bot] at ha
        simpa [ha] using hw)
    have hbot : AbsIrred p (⊥ : Subgroup (U ≃ₗ[ZMod p] U)) :=
      ⟨fun W _ => hall W, fun T _ => exists_smul_id_of_forall_submodule_eq_bot_or_top hall T⟩
    rw [hA]
    exact hbot

private lemma center_commute {A : Subgroup (U ≃ₗ[ZMod p] U)} (z : Subgroup.center A) :
    ∀ a ∈ A, (z : U →ₗ[ZMod p] U) ∘ₗ (a : U →ₗ[ZMod p] U)
      = (a : U →ₗ[ZMod p] U) ∘ₗ (z : U →ₗ[ZMod p] U) := by
  intro a ha
  have h := (Subgroup.mem_center_iff.mp z.2) ⟨a, ha⟩
  have h2 : (z : U ≃ₗ[ZMod p] U) * a = a * (z : U ≃ₗ[ZMod p] U) := by
    simpa using (congrArg (fun w : ↥A => (w : U ≃ₗ[ZMod p] U)) h).symm
  simpa only [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp] using
    congrArg (fun e : U ≃ₗ[ZMod p] U => (e : U →ₗ[ZMod p] U)) h2

private noncomputable def centerScalar {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : AbsIrred p A)
    (z : Subgroup.center A) : ZMod p :=
  Classical.choose (hA.2 (z : U →ₗ[ZMod p] U) (center_commute z))

private lemma centerScalar_spec {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : AbsIrred p A)
    (z : Subgroup.center A) : (z : U →ₗ[ZMod p] U) = centerScalar hA z • LinearMap.id :=
  Classical.choose_spec (hA.2 (z : U →ₗ[ZMod p] U) (center_commute z))

private lemma centerScalar_apply {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : AbsIrred p A)
    (z : Subgroup.center A) (u : U) : (z : U ≃ₗ[ZMod p] U) u = centerScalar hA z • u := by
  have := congrArg (fun f : U →ₗ[ZMod p] U => f u) (centerScalar_spec hA z)
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap] using this

private lemma centerScalar_ne_zero {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : AbsIrred p A)
    {u : U} (hu0 : u ≠ 0) (z : Subgroup.center A) : centerScalar hA z ≠ 0 := by
  intro hz
  have hzu : (z : U ≃ₗ[ZMod p] U) u = 0 := by rw [centerScalar_apply hA z u, hz, zero_smul]
  exact hu0 ((z : U ≃ₗ[ZMod p] U).injective (by rw [hzu, map_zero]))

private lemma centerScalar_eq_of {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : AbsIrred p A)
    {u : U} (hu0 : u ≠ 0) {z : Subgroup.center A} {c : ZMod p}
    (hc : (z : U →ₗ[ZMod p] U) = c • LinearMap.id) : centerScalar hA z = c := by
  have h1 := centerScalar_apply hA z u
  have h2 : (z : U ≃ₗ[ZMod p] U) u = c • u := by
    have := congrArg (fun f : U →ₗ[ZMod p] U => f u) hc
    simpa only [LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap] using this
  have hsub : (centerScalar hA z - c) • u = 0 := by rw [sub_smul, h1.symm.trans h2, sub_self]
  rcases smul_eq_zero.mp hsub with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hu0

private lemma centerScalar_mul {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : AbsIrred p A)
    {u : U} (hu0 : u ≠ 0) (z₁ z₂ : Subgroup.center A) :
    centerScalar hA (z₁ * z₂) = centerScalar hA z₁ * centerScalar hA z₂ := by
  refine centerScalar_eq_of hA hu0 ?_
  calc ((z₁ * z₂ : Subgroup.center A) : U →ₗ[ZMod p] U)
      = (z₁ : U →ₗ[ZMod p] U) * (z₂ : U →ₗ[ZMod p] U) := by
        rw [show ((z₁ * z₂ : Subgroup.center A) : U →ₗ[ZMod p] U)
            = (((z₁ * z₂ : Subgroup.center A) : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) from rfl,
          show (((z₁ * z₂ : Subgroup.center A) : U ≃ₗ[ZMod p] U))
            = (z₁ : U ≃ₗ[ZMod p] U) * (z₂ : U ≃ₗ[ZMod p] U) from rfl,
          LinearEquiv.coe_toLinearMap_mul]
    _ = (centerScalar hA z₁ • LinearMap.id) * (centerScalar hA z₂ • LinearMap.id) := by
        rw [centerScalar_spec hA z₁, centerScalar_spec hA z₂]
    _ = (centerScalar hA z₁ * centerScalar hA z₂) • LinearMap.id := by
        ext v
        simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]

private lemma centerScalar_one {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : AbsIrred p A)
    {u : U} (hu0 : u ≠ 0) : centerScalar hA 1 = 1 :=
  centerScalar_eq_of hA hu0 (by ext v; simp)

private lemma card_center_dvd_of_ne_zero {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : AbsIrred p A)
    {u : U} (hu0 : u ≠ 0) : Nat.card (Subgroup.center A) ∣ p - 1 := by
  let f : Subgroup.center A →* (ZMod p)ˣ :=
    { toFun := fun z => Units.mk0 (centerScalar hA z) (centerScalar_ne_zero hA hu0 z)
      map_one' := by
        apply Units.ext
        rw [Units.val_mk0, Units.val_one]
        exact centerScalar_one hA hu0
      map_mul' := fun z₁ z₂ => by
        apply Units.ext
        rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0,
          centerScalar_mul hA hu0] }
  have hf_inj : Function.Injective f := by
    intro z₁ z₂ h
    have hsc : centerScalar hA z₁ = centerScalar hA z₂ :=
      congrArg (fun w : (ZMod p)ˣ => (w : ZMod p)) h
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hlin : (z₁ : U →ₗ[ZMod p] U) = (z₂ : U →ₗ[ZMod p] U) := by
      rw [centerScalar_spec hA z₁, centerScalar_spec hA z₂, hsc]
    simpa using congrArg (fun g : U →ₗ[ZMod p] U => g v) hlin
  have hdiv := Subgroup.card_dvd_of_injective f hf_inj
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rwa [hcard] at hdiv

theorem card_center_dvd_sub_one {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : AbsIrred p A) :
    Nat.card (Subgroup.center A) ∣ p - 1 := by
  by_cases hu : ∃ u : U, u ≠ 0
  · obtain ⟨u, hu0⟩ := hu
    exact card_center_dvd_of_ne_zero hA hu0
  · have hsub : Subsingleton U := by
      refine ⟨fun x y => ?_⟩
      rw [not_not.mp (not_exists.mp hu x), not_not.mp (not_exists.mp hu y)]
    have hsubc : Subsingleton (Subgroup.center A) :=
      ⟨fun x y => Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => hsub.elim _ _))⟩
    have hcard1 : Nat.card (Subgroup.center A) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsubc, ⟨1⟩⟩
    rw [hcard1]
    exact one_dvd _

end CFSG.StandardType.ZS
