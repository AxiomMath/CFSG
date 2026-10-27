module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer

public section

namespace CFSG.RankThree.GF2n.Smith81

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Prelim

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem nondeg_of_forall (h : ∀ v, (∀ w, polar Q v w = 0) → v = 0) :
    (polarBilin Q).Nondegenerate :=
  ⟨fun v hv => h v fun w => by simpa using hv w,
    fun w hw => h w fun v => by rw [polar_comm]; simpa using hw v⟩

private theorem polar_self_eq_zero_of_charTwo [CharP K 2] (Q : QuadraticForm K V) (v : V) :
    polar Q v v = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

end Prelim

section Irreducible

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def EichlerStable (Q : QuadraticForm K V) (u : V) (X : Submodule K V) : Prop :=
  ∀ a w : V, Q a = 0 → polar Q a w = 0 → polar Q u a = 0 → polar Q u w = 0 →
    ∀ x ∈ X, eichler Q a w x ∈ X

theorem eichler_diff_mem_of_stable {u : V} {X : Submodule K V} (hX : EichlerStable Q u X)
    {x : V} (hx : x ∈ X) {a w : V} (ha : Q a = 0) (haw : polar Q a w = 0)
    (hua : polar Q u a = 0) (huw : polar Q u w = 0) :
    polar Q x a • w - (polar Q x w + Q w * polar Q x a) • a ∈ X := by
  have h := X.sub_mem (hX a w ha haw hua huw x hx) hx
  rw [eichler_apply ha haw] at h
  convert h using 1
  abel

variable [FiniteDimensional K V]

theorem orth_le_of_eichlerStable (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ Module.finrank K V) {u : V} {X : Submodule K V} (hX : EichlerStable Q u X)
    {s : V} (hsX : s ∈ X) (hs : Q s = 0) (hus : polar Q u s = 0)
    (hsL : s ∉ Submodule.span K {u}) :
    LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) ≤ X := by
  obtain ⟨z', hz'P, hsz'⟩ : ∃ z' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (Submodule.span K {u}), polar Q s z' = 1 := by
    obtain ⟨z, hzP, hsz⟩ := exists_polar_ne_zero_of_not_mem hQ hsL
    exact ⟨(polar Q s z)⁻¹ • z, Submodule.smul_mem _ _ hzP, by
      rw [polar_smul_right_eq, inv_mul_cancel₀ hsz]⟩
  have huz' := mem_orth_span_single_iff.mp hz'P
  let P' := HypPair.ofPolarEqOne hs hsz'
  have hQu' : Q P'.f = 0 := P'.Q_f
  have hsu' : polar Q s P'.f = 1 := P'.polar_ef
  have hu'def : P'.f = z' - Q z' • s := rfl
  have hua : polar Q u P'.f = 0 := by
    rw [hu'def, polar_sub_right, polar_smul_right_eq, huz', hus]
    ring
  have hd : ∀ w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, P'.f}),
      w - (polar Q s w + Q w) • P'.f ∈ X := by
    intro w hw
    obtain ⟨huw, hu'w⟩ := mem_orth_span_pair_iff.mp hw
    have := eichler_diff_mem_of_stable hX hsX hQu' hu'w hua huw
    rwa [hsu', one_smul, mul_one] at this
  obtain ⟨w₁, hw₁, w₂, hw₂, h12⟩ :=
    exists_polar_ne_zero_of_finrank hQ (finrank_span_pair_le u P'.f) h5
  have hu'X : P'.f ∈ X := by
    have h3 := hd (w₁ + w₂) (Submodule.add_mem _ hw₁ hw₂)
    have h4 := X.sub_mem (X.sub_mem h3 (hd w₁ hw₁)) (hd w₂ hw₂)
    have h5' : polar Q w₁ w₂ • P'.f ∈ X := by
      have := X.neg_mem h4
      convert this using 1
      rw [polar_add_right, QuadraticMap.map_add Q w₁ w₂]
      module
    have h6 := X.smul_mem (polar Q w₁ w₂)⁻¹ h5'
    rwa [smul_smul, inv_mul_cancel₀ h12, one_smul] at h6
  have hRX : ∀ w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, P'.f}),
      w ∈ X := by
    intro w hw
    have := X.add_mem (hd w hw) (X.smul_mem (polar Q s w + Q w) hu'X)
    simpa using this
  intro p hp
  have hpu : polar Q u p = 0 := mem_orth_span_single_iff.mp hp
  have hpR : p - polar Q p P'.f • s ∈
      LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, P'.f}) := by
    rw [mem_orth_span_pair_iff]
    constructor
    · rw [polar_sub_right, polar_smul_right_eq, hus, hpu]
      ring
    · rw [polar_sub_right, polar_smul_right_eq, polar_comm Q P'.f s, hsu', polar_comm Q P'.f p]
      ring
  have := X.add_mem (hRX _ hpR) (X.smul_mem (polar Q p P'.f) hsX)
  simpa using this

theorem exists_singular_of_eichlerStable [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ Module.finrank K V) {u : V}
    (hQu : Q u = 0) {X : Submodule K V}
    (hXP : X ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}))
    (hX : EichlerStable Q u X) {y : V} (hyX : y ∈ X) (hyL : y ∉ Submodule.span K {u}) :
    ∃ s ∈ X, Q s = 0 ∧ polar Q u s = 0 ∧ s ∉ Submodule.span K {u} := by
  have hyu : polar Q u y = 0 := mem_orth_span_single_iff.mp (hXP hyX)
  by_cases hy0 : Q y = 0
  · exact ⟨y, hyX, hy0, hyu, hyL⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨m, hm, hQm, m', hm', hmm'⟩ :=
    exists_nonsingular_of_finrank hQ (finrank_span_pair_le u y) h5
  obtain ⟨hum, hym⟩ := mem_orth_span_pair_iff.mp hm
  obtain ⟨hum', hym'⟩ := mem_orth_span_pair_iff.mp hm'
  obtain ⟨a, ha⟩ : IsSquare (Q m / Q y) := FiniteField.isSquare_of_char_two (ringChar.eq K 2) _
  have hay : a ^ 2 * Q y = Q m := by
    have h1 : a * a * Q y = Q m / Q y * Q y := by rw [← ha]
    rw [div_mul_cancel₀ _ hy0] at h1
    rw [pow_two]
    exact h1
  obtain ⟨v, hv⟩ : ∃ v : V, v = a • y + m := ⟨_, rfl⟩
  have hQv : Q v = 0 := by
    rw [hv, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_left_eq, hym, hay]
    linear_combination (Q m) * h2
  have hvu : polar Q u v = 0 := by
    rw [hv, polar_add_right, polar_smul_right_eq, hyu, hum]
    ring
  have hyv : polar Q y v = 0 := by
    rw [hv, polar_add_right, polar_smul_right_eq, hym, polar_self_eq_two_mul]
    linear_combination (a * Q y) * h2
  have hyspan : y ∉ Submodule.span K {u, v} := by
    intro hy'
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hy'
    apply hy0
    rw [← hcd, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQu, hQv,
      polar_smul_left_eq, polar_smul_right_eq, hvu]
    ring
  obtain ⟨w, hw, hyw⟩ := exists_polar_ne_zero_of_not_mem hQ hyspan
  obtain ⟨huw, hvw⟩ := mem_orth_span_pair_iff.mp hw
  have hvX : v ∈ X := by
    have h := eichler_diff_mem_of_stable hX hyX hQv hvw hvu huw
    rw [hyv, zero_smul, mul_zero, add_zero, zero_sub] at h
    have h1 : polar Q y w • v ∈ X := by simpa using X.neg_mem h
    have h3 := X.smul_mem (polar Q y w)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hyw, one_smul] at h3
  refine ⟨v, hvX, hQv, hvu, fun hvL => ?_⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvL
  apply hmm'
  have hmeq : m = c • u - a • y := by
    rw [hc, hv]
    abel
  rw [hmeq, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hum', hym']
  ring

theorem eq_span_or_eq_orth_of_eichlerStable [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ Module.finrank K V) {u : V}
    (hQu : Q u = 0) (X : Submodule K V) (hLX : Submodule.span K {u} ≤ X)
    (hXP : X ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}))
    (hX : EichlerStable Q u X) :
    X = Submodule.span K {u} ∨
      X = LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) := by
  by_cases hXL : X = Submodule.span K {u}
  · exact Or.inl hXL
  refine Or.inr (le_antisymm hXP ?_)
  obtain ⟨y, hyX, hyL⟩ : ∃ y ∈ X, y ∉ Submodule.span K {u} := by
    by_contra hcon
    push Not at hcon
    exact hXL (le_antisymm hcon hLX)
  obtain ⟨s, hsX, hs, hus, hsL⟩ :=
    exists_singular_of_eichlerStable hQ h5 hQu hXP hX hyX hyL
  exact orth_le_of_eichlerStable hQ h5 hX hsX hs hus hsL

end Irreducible

section Lagrangian

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

private noncomputable def prodPolar (Q : QuadraticForm K V) : LinearMap.BilinForm K (V × V) :=
  (polarBilin Q).compl₁₂ (LinearMap.fst K V V) (LinearMap.snd K V V) +
    ((polarBilin Q).compl₁₂ (LinearMap.fst K V V) (LinearMap.snd K V V)).flip

private theorem prodPolar_apply (p p' : V × V) :
    prodPolar Q p p' = polar Q p.1 p'.2 + polar Q p'.1 p.2 := by
  simp [prodPolar]

private theorem prodPolar_nondegenerate (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0) :
    (prodPolar Q).Nondegenerate := by
  have hl : ∀ v, (∀ w, polar Q w v = 0) → v = 0 := fun v h =>
    hnd v fun w => by rw [polar_comm]; exact h w
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · refine Prod.ext (hnd _ fun w => ?_) (hl _ fun w => ?_)
    · simpa [prodPolar_apply] using hp (0, w)
    · simpa [prodPolar_apply] using hp (w, 0)
  · refine Prod.ext (hnd _ fun w => ?_) (hl _ fun w => ?_)
    · simpa [prodPolar_apply] using hp (0, w)
    · simpa [prodPolar_apply] using hp (w, 0)

theorem mem_of_forall_polar_prod_eq_zero (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0)
    {D : Submodule K (V × V)}
    (hts : ∀ p ∈ D, ∀ p' ∈ D, polar Q p.1 p'.2 + polar Q p'.1 p.2 = 0)
    (hdim : Module.finrank K V ≤ Module.finrank K D) {p' : V × V}
    (hp' : ∀ p ∈ D, polar Q p.1 p'.2 + polar Q p'.1 p.2 = 0) : p' ∈ D := by
  have hP := prodPolar_nondegenerate hnd
  have hle : D ≤ (prodPolar Q).orthogonal D := fun x hx => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    show prodPolar Q y x = 0
    rw [prodPolar_apply]
    exact hts y hy x hx
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hP D
  have h3 := Submodule.finrank_le D
  have h4 : Module.finrank K (V × V) = 2 * Module.finrank K V := by
    rw [Module.finrank_prod]; ring
  have heq : D = (prodPolar Q).orthogonal D :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  show prodPolar Q y p' = 0
  rw [prodPolar_apply]
  exact hp' y hy

end Lagrangian

section Counting

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem card_le_of_sub_one_mem_span (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0) {u : V}
    (hu0 : u ≠ 0) (hu : Q u = 0) (Γ : Finset (K × (V ≃ₗ[K] V)))
    (hΓ : ∀ t ∈ Γ, (∀ v, Q (t.2 v) = Q v) ∧ ∀ a, ∃ k : K, t.2 a - a = k • u) :
    Γ.card ≤ Nat.card K := by
  obtain ⟨w₀, hw₀⟩ : ∃ w, polar Q u w ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (hnd u h)
  have hw₀' : polar Q w₀ u ≠ 0 := by rwa [polar_comm]
  have key : ∀ t ∈ Γ, ∀ a, t.2 a = a := by
    intro t ht
    obtain ⟨hQt, hk⟩ := hΓ t ht
    have step : ∀ a, polar Q a u ≠ 0 → t.2 a = a := by
      intro a ha
      obtain ⟨k, hk⟩ := hk a
      have h1 : t.2 a = a + k • u := by rw [← hk]; abel
      have h2 := hQt a
      rw [h1, QuadraticMap.map_add Q, map_smul_eq_sq, hu, polar_smul_right_eq] at h2
      have h3 : k * polar Q a u = 0 := by linear_combination h2
      rw [(mul_eq_zero.mp h3).resolve_right ha, zero_smul, add_zero] at h1
      exact h1
    intro a
    by_cases ha : polar Q a u = 0
    · have h1 : polar Q (a + w₀) u ≠ 0 := by rwa [polar_add_left, ha, zero_add]
      have h2 := step _ h1
      rw [map_add, step w₀ hw₀'] at h2
      exact add_right_cancel h2
    · exact step a ha
  letI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun t => t.1) (fun _ _ => Finset.mem_univ _) ?_
  intro t₁ ht₁ t₂ ht₂ h
  exact Prod.ext h (LinearEquiv.ext fun a => by rw [key t₁ ht₁, key t₂ ht₂])

variable [CharP K 2] [FiniteDimensional K V]

theorem card_le_sq_of_fix_pair (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0)
    (hn : Module.finrank K V = 4) {u b g : V} (hu0 : u ≠ 0) (hu : Q u = 0)
    (hub : polar Q u b = 0) (hbu : b ∉ Submodule.span K {u}) (Γ : Finset (K × (V ≃ₗ[K] V)))
    (hΓ : ∀ t ∈ Γ, (∀ v, Q (t.2 v) = Q v) ∧ t.2 u = u ∧ t.2 b = b ∧
      ∃ k : K, t.2 g + t.1 • b - g = k • u) :
    Γ.card ≤ Nat.card K ^ 2 := by
  have hQ := nondeg_of_forall hnd
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb : polar Q b b = 0 := polar_self_eq_zero_of_charTwo Q b
  have huu : polar Q u u = 0 := polar_self_eq_zero hu
  have hbu' : polar Q b u = 0 := by rw [polar_comm]; exact hub
  have hli : LinearIndependent K ![u, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hbu
      have h1 : t • b = -(s • u) := eq_neg_of_add_eq_zero_right hst
      have : b = (-(t⁻¹ * s)) • u := by
        calc b = t⁻¹ • (t • b) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(t⁻¹ * s)) • u := by rw [h1, smul_neg, smul_smul, neg_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hu0, rfl⟩
  obtain ⟨g', hg'⟩ := exists_dual_family hQ hli
  have h00 : polar Q u (g' 0) = 1 := by simpa using hg' 0 0
  have h01 : polar Q u (g' 1) = 0 := by simpa using hg' 0 1
  have h10 : polar Q b (g' 0) = 0 := by simpa using hg' 1 0
  have h11 : polar Q b (g' 1) = 1 := by simpa using hg' 1 1
  set d := g' 1 with hd
  set c := g' 0 + polar Q (g' 0) d • b with hc
  have hud : polar Q u d = 0 := h01
  have hbd : polar Q b d = 1 := h11
  have hcu : polar Q u c = 1 := by
    rw [hc, polar_add_right, polar_smul_right_eq, h00, hub]; ring
  have hcb : polar Q b c = 0 := by
    rw [hc, polar_add_right, polar_smul_right_eq, h10, hbb]; ring
  have hcd : polar Q c d = 0 := by
    rw [hc, polar_add_left, polar_smul_left_eq, hbd]
    linear_combination (polar Q (g' 0) d) * h2
  have hdd : polar Q d d = 0 := polar_self_eq_zero_of_charTwo Q d
  have hdu : polar Q d u = 0 := by rw [polar_comm]; exact hud
  have hdb : polar Q d b = 1 := by rw [polar_comm]; exact hbd
  have hcu' : polar Q c u = 1 := by rw [polar_comm]; exact hcu
  have hcb' : polar Q c b = 0 := by rw [polar_comm]; exact hcb
  clear_value c d
  have hN : ∀ v, polar Q u v = 0 → polar Q b v = 0 → ∃ α β : K, α • u + β • b = v := by
    intro v h1 h2'
    set N : Submodule K V := Submodule.span K {u, b} with hNdef
    have hNdim : Module.finrank K N = 2 := by
      have h := finrank_span_eq_card hli
      have hr : Set.range ![u, b] = {u, b} := by
        ext x; simp [Fin.exists_fin_two, or_comm]
      rw [hr, Fintype.card_fin] at h
      exact h
    have hle : N ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) N := by
      intro x hx
      rw [mem_orth_iff]
      intro y hy
      obtain ⟨a, a', rfl⟩ := Submodule.mem_span_pair.mp hx
      obtain ⟨e, e', rfl⟩ := Submodule.mem_span_pair.mp hy
      simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, huu,
        hub, hbu', hbb]
      ring
    have hfin := LinearMap.BilinForm.finrank_orthogonal hQ N
    have heq : N = LinearMap.BilinForm.orthogonal (polarBilin Q) N :=
      Submodule.eq_of_le_of_finrank_le hle (by omega)
    have hv : v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) N :=
      mem_orth_span_pair_iff.mpr ⟨h1, h2'⟩
    rw [← heq] at hv
    obtain ⟨a, a', h⟩ := Submodule.mem_span_pair.mp hv
    exact ⟨a, a', h⟩
  have hspan : Submodule.span K ({u, b, c, d} : Set V) = ⊤ := by
    set M := Submodule.span K ({u, b, c, d} : Set V) with hM
    have hM0 : LinearMap.BilinForm.orthogonal (polarBilin Q) M = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [mem_orth_iff] at hv
      have hu' := hv u (Submodule.subset_span (by simp))
      have hb' := hv b (Submodule.subset_span (by simp))
      have hc' := hv c (Submodule.subset_span (by simp))
      have hd' := hv d (Submodule.subset_span (by simp))
      obtain ⟨α, β, rfl⟩ := hN v hu' hb'
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hcu', hcb'] at hc'
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hdu, hdb] at hd'
      have hα : α = 0 := by linear_combination hc'
      have hβ : β = 0 := by linear_combination hd'
      rw [hα, hβ, zero_smul, zero_smul, add_zero]
      exact Submodule.zero_mem _
    have h1 := LinearMap.BilinForm.finrank_orthogonal hQ M
    have h3 := Submodule.finrank_le M
    rw [hM0, finrank_bot] at h1
    exact Submodule.eq_top_of_finrank_eq (by omega)
  have hcoord : ∀ o : V ≃ₗ[K] V, (∀ v, Q (o v) = Q v) → o u = u → o b = b →
      o c = c + (polar Q (o c) d ^ 2 * Q b) • u + polar Q (o c) d • b ∧
      o d = d + polar Q (o c) d • u + polar Q (o d) d • b := by
    intro o ho hou hob
    have hpo := polar_map_of_mem (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ho)
    have e1 : ∀ x, polar Q u (o x) = polar Q u x := fun x => by
      simpa [hou] using hpo u x
    have e2 : ∀ x, polar Q b (o x) = polar Q b x := fun x => by
      simpa [hob] using hpo b x
    obtain ⟨α, β, hαβ⟩ := hN (o c - c) (by rw [polar_sub_right, e1, sub_self])
      (by rw [polar_sub_right, e2, sub_self])
    obtain ⟨α', β', hαβ'⟩ := hN (o d - d) (by rw [polar_sub_right, e1, sub_self])
      (by rw [polar_sub_right, e2, sub_self])
    have hoc : o c = c + (α • u + β • b) := by rw [hαβ]; abel
    have hod : o d = d + (α' • u + β' • b) := by rw [hαβ']; abel
    have hβ : polar Q (o c) d = β := by
      rw [hoc, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hcd, hud,
        hbd]
      ring
    have hβ' : polar Q (o d) d = β' := by
      rw [hod, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hdd, hud,
        hbd]
      ring
    have hQuad : Q (α • u + β • b) = β ^ 2 * Q b := by
      rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hu, polar_smul_left_eq,
        polar_smul_right_eq, hub]
      ring
    have hα : α = β ^ 2 * Q b := by
      have h := ho c
      rw [hoc, QuadraticMap.map_add Q, hQuad, polar_add_right, polar_smul_right_eq,
        polar_smul_right_eq, hcu', hcb'] at h
      linear_combination h - (β ^ 2 * Q b) * h2
    have hα' : α' = β := by
      have h := hpo c d
      rw [hoc, hod, hcd] at h
      simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, hcd,
        hcu', hcb', hud, hbd, huu, hub, hbu', hbb] at h
      linear_combination h - β * h2
    refine ⟨?_, ?_⟩
    · rw [hβ, ← hα, hoc]; abel
    · rw [hβ, hβ', ← hα', hod]; abel
  letI := Fintype.ofFinite K
  have hcard : Γ.card ≤ (Finset.univ : Finset (K × K)).card := by
    refine Finset.card_le_card_of_injOn
      (fun t => (polar Q (t.2 c) d, polar Q (t.2 d) d)) (fun _ _ => Finset.mem_univ _) ?_
    intro t₁ ht₁ t₂ ht₂ h
    obtain ⟨hQ₁, hu₁, hb₁, k₁, hk₁⟩ := hΓ t₁ ht₁
    obtain ⟨hQ₂, hu₂, hb₂, k₂, hk₂⟩ := hΓ t₂ ht₂
    have h1 : polar Q (t₁.2 c) d = polar Q (t₂.2 c) d := congrArg Prod.fst h
    have h2' : polar Q (t₁.2 d) d = polar Q (t₂.2 d) d := congrArg Prod.snd h
    obtain ⟨hc₁, hd₁⟩ := hcoord t₁.2 hQ₁ hu₁ hb₁
    obtain ⟨hc₂, hd₂⟩ := hcoord t₂.2 hQ₂ hu₂ hb₂
    have hoc : t₁.2 c = t₂.2 c := by rw [hc₁, hc₂, h1]
    have hod : t₁.2 d = t₂.2 d := by rw [hd₁, hd₂, h1, h2']
    have ho : t₁.2 = t₂.2 := by
      have hfun : (t₁.2 : V →ₗ[K] V) = (t₂.2 : V →ₗ[K] V) := by
        refine LinearMap.ext_on hspan ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact (hu₁.trans hu₂.symm)
        · exact (hb₁.trans hb₂.symm)
        · exact hoc
        · exact hod
      exact LinearEquiv.ext fun x => LinearMap.congr_fun hfun x
    have hμ : ∀ (t : K × (V ≃ₗ[K] V)) (k : K), t.2 g + t.1 • b - g = k • u →
        t.1 = polar Q g d - polar Q (t.2 g) d := by
      intro t k hk
      have := congrArg (fun z => polar Q z d) hk
      simp only [polar_sub_left, polar_add_left, polar_smul_left_eq, hbd, hud] at this
      linear_combination this
    refine Prod.ext ?_ ho
    rw [hμ t₁ k₁ hk₁, hμ t₂ k₂ hk₂, ho]
  refine hcard.trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_prod, Nat.card_eq_fintype_card, _root_.sq]

end Counting

section PerpLine

variable {K : Type*} [Field K] {ι : Type*}

@[expose] def perpLine (qU : QuadraticForm K (ι → K)) (u : ι → K) :
    Submodule K ((ι → K) × (ι → K)) where
  carrier := {p | polar qU p.1 u = 0 ∧ p.2 ∈ Submodule.span K {u}}
  add_mem' := by
    rintro p p' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨by rw [Prod.fst_add, polar_add_left, h1, h1', add_zero], Submodule.add_mem _ h2 h2'⟩
  zero_mem' := ⟨by simp, Submodule.zero_mem _⟩
  smul_mem' := by
    rintro c p ⟨h1, h2⟩
    exact ⟨by rw [Prod.smul_fst, polar_smul_left_eq, h1, mul_zero], Submodule.smul_mem _ _ h2⟩

theorem mem_perpLine {qU : QuadraticForm K (ι → K)} {u : ι → K} {p : (ι → K) × (ι → K)} :
    p ∈ perpLine qU u ↔ polar qU p.1 u = 0 ∧ p.2 ∈ Submodule.span K {u} :=
  Iff.rfl

end PerpLine

section Main

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {ι : Type*} [Fintype ι]

theorem snd_mem_span_of_eichlerStable {qU : QuadraticForm K (ι → K)}
    (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) (h5 : 5 ≤ Fintype.card ι) {u : ι → K}
    (hu0 : u ≠ 0) (hu : qU u = 0) {D : Submodule K ((ι → K) × (ι → K))}
    (hSu : ∀ p ∈ D, polar qU u p.2 = 0) (hSS : ∀ p ∈ D, ∀ p' ∈ D, polar qU p.2 p'.2 = 0)
    (hE : ∀ s w : ι → K, qU s = 0 → polar qU s w = 0 → polar qU s u = 0 → polar qU w u = 0 →
      ∀ p ∈ D, (eichler qU s w p.1, eichler qU s w p.2) ∈ D) :
    ∀ p ∈ D, p.2 ∈ Submodule.span K {u} := by
  have hQ := nondeg_of_forall hnd
  have hfin : 5 ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card K]; exact h5
  set S : Submodule K (ι → K) := D.map (LinearMap.snd K (ι → K) (ι → K)) with hS
  have hSmem : ∀ x, x ∈ S ↔ ∃ p ∈ D, p.2 = x := fun x => by simp [hS]
  set X : Submodule K (ι → K) := S ⊔ Submodule.span K {u} with hX
  have hLX : Submodule.span K {u} ≤ X := le_sup_right
  have hXP : X ≤ LinearMap.BilinForm.orthogonal (polarBilin qU) (Submodule.span K {u}) := by
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := (hSmem x).mp hx
      exact mem_orth_span_single_iff.mpr (hSu p hp)
    · intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [mem_orth_span_single_iff, polar_smul_right_eq, polar_self_eq_zero hu, mul_zero]
  have hXst : EichlerStable qU u X := by
    intro a w ha haw hua huw x hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    refine X.add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · obtain ⟨p, hp, rfl⟩ := (hSmem s).mp hs
      exact (hSmem _).mpr ⟨_, hE a w ha haw (by rw [polar_comm]; exact hua)
        (by rw [polar_comm]; exact huw) p hp, rfl⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
      rw [map_smul, eichler_apply_of_polar_eq_zero hua huw]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  rcases eq_span_or_eq_orth_of_eichlerStable hQ hfin hu X hLX hXP hXst with hX1 | hX1
  · intro p hp
    rw [← hX1]
    exact Submodule.mem_sup_left ((hSmem _).mpr ⟨p, hp, rfl⟩)
  · exfalso
    have hN : Module.finrank K (Submodule.span K {u}) ≤ 2 := by
      rw [finrank_span_singleton hu0]; norm_num
    obtain ⟨m₁, hm₁, m₂, hm₂, hm⟩ := exists_polar_ne_zero_of_finrank hQ hN hfin
    rw [← hX1] at hm₁ hm₂
    obtain ⟨s₁, hs₁, t₁, ht₁, rfl⟩ := Submodule.mem_sup.mp hm₁
    obtain ⟨s₂, hs₂, t₂, ht₂, rfl⟩ := Submodule.mem_sup.mp hm₂
    obtain ⟨p₁, hp₁, rfl⟩ := (hSmem s₁).mp hs₁
    obtain ⟨p₂, hp₂, rfl⟩ := (hSmem s₂).mp hs₂
    obtain ⟨c₁, rfl⟩ := Submodule.mem_span_singleton.mp ht₁
    obtain ⟨c₂, rfl⟩ := Submodule.mem_span_singleton.mp ht₂
    apply hm
    rw [polar_add_left, polar_add_right, polar_add_right, polar_smul_left_eq,
      polar_smul_right_eq, polar_smul_right_eq, polar_smul_left_eq, hSS p₁ hp₁ p₂ hp₂,
      polar_comm qU p₁.2 u, hSu p₁ hp₁, polar_self_eq_zero hu, hSu p₂ hp₂]
    ring

theorem eq_perpLine_of_stable_of_sq_lt {qU : QuadraticForm K (ι → K)}
    (hnd : ∀ v, (∀ w, polar qU v w = 0) → v = 0) (hn : 4 ≤ Fintype.card ι) {u : ι → K}
    (hu0 : u ≠ 0) (hu : qU u = 0) {D : Submodule K ((ι → K) × (ι → K))}
    (huD : ((u, 0) : (ι → K) × (ι → K)) ∈ D) (hts : ∀ p ∈ D, polar qU p.1 p.2 = 0)
    (hdim : Fintype.card ι ≤ Module.finrank K D)
    (hT : ∀ μ : K, ∀ p ∈ D, (p.1 + μ • p.2, p.2) ∈ D)
    (hE : ∀ s w : ι → K, qU s = 0 → polar qU s w = 0 → polar qU s u = 0 → polar qU w u = 0 →
      ∀ p ∈ D, (eichler qU s w p.1, eichler qU s w p.2) ∈ D)
    (hΓ : ∃ Γ : Finset (K × ((ι → K) ≃ₗ[K] (ι → K))), Nat.card K ^ 2 < Γ.card ∧
      ∀ t ∈ Γ, (∀ v, qU (t.2 v) = qU v) ∧ t.2 u = u ∧
        ∀ p ∈ D, ∃ c : K, (t.2 p.1 + t.1 • t.2 p.2 - p.1, t.2 p.2 - p.2) = c • ((u, 0) : _)) :
    D = perpLine qU u := by
  obtain ⟨Γ, hΓcard, hΓ⟩ := hΓ
  have hfinι : Module.finrank K (ι → K) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card K
  have hpol : ∀ p ∈ D, ∀ p' ∈ D, polar qU p.1 p'.2 + polar qU p'.1 p.2 = 0 := by
    intro p hp p' hp'
    have h := hts _ (D.add_mem hp hp')
    simp only [Prod.fst_add, Prod.snd_add, polar_add_left, polar_add_right, hts p hp,
      hts p' hp'] at h
    linear_combination h
  have hSb : ∀ p ∈ D, (p.2, (0 : ι → K)) ∈ D := by
    intro p hp
    have h := D.sub_mem (hT 1 p hp) hp
    have e : ((p.1 + (1 : K) • p.2, p.2) - p : (ι → K) × (ι → K)) = (p.2, 0) := by
      refine Prod.ext ?_ ?_ <;> simp
    rwa [e] at h
  have hSu : ∀ p ∈ D, polar qU u p.2 = 0 := by
    intro p hp
    simpa using hpol p hp _ huD
  have hSS : ∀ p ∈ D, ∀ p' ∈ D, polar qU p.2 p'.2 = 0 := by
    intro p hp p' hp'
    simpa using hpol p' hp' _ (hSb p hp)
  have hSK : ∀ p ∈ D, p.2 ∈ Submodule.span K {u} := by
    rcases (by omega : Fintype.card ι = 4 ∨ 5 ≤ Fintype.card ι) with h4 | h5
    · by_contra hcon
      push Not at hcon
      obtain ⟨p, hp, hpK⟩ := hcon
      have hle := card_le_sq_of_fix_pair (Q := qU) (g := p.1) hnd (by rw [hfinι, h4]) hu0 hu
        (hSu p hp) hpK Γ ?_
      · omega
      · intro t ht
        obtain ⟨hiso, hfixu, hc⟩ := hΓ t ht
        obtain ⟨k, hk⟩ := hc p hp
        rw [Prod.ext_iff] at hk
        simp only [Prod.smul_fst, Prod.smul_snd, smul_zero] at hk
        have hb : t.2 p.2 = p.2 := sub_eq_zero.mp hk.2
        refine ⟨hiso, hfixu, hb, k, ?_⟩
        rw [← hk.1, hb]
    · exact snd_mem_span_of_eichlerStable hnd h5 hu0 hu hSu hSS hE
  by_cases hz : ∀ p ∈ D, p.2 = 0
  ·
    exfalso
    have hD0 : ∀ a : ι → K, ((a, (0 : ι → K)) : (ι → K) × (ι → K)) ∈ D := by
      intro a
      refine mem_of_forall_polar_prod_eq_zero hnd hpol (by rw [hfinι]; exact hdim) ?_
      intro p hp
      simp [hz p hp]
    have hle := card_le_of_sub_one_mem_span hnd hu0 hu Γ fun t ht => by
      refine ⟨(hΓ t ht).1, fun a => ?_⟩
      obtain ⟨k, hk⟩ := (hΓ t ht).2.2 (a, 0) (hD0 a)
      rw [Prod.ext_iff] at hk
      simp only [Prod.smul_fst, map_zero, smul_zero, add_zero] at hk
      exact ⟨k, hk.1⟩
    have hqpos : 0 < Nat.card K := Nat.card_pos
    have := Nat.le_self_pow (n := 2) (by norm_num) (Nat.card K)
    omega
  ·
    push Not at hz
    obtain ⟨p₀, hp₀, hp₀0⟩ := hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hSK p₀ hp₀)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hp₀0 (by rw [← hc, zero_smul])
    set p₁ : (ι → K) × (ι → K) := c⁻¹ • p₀ with hp₁
    have hp₁D : p₁ ∈ D := D.smul_mem _ hp₀
    have hp₁2 : p₁.2 = u := by
      rw [hp₁, Prod.smul_snd, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hu₁ : polar qU p₁.1 u = 0 := by
      have := hts p₁ hp₁D
      rwa [hp₁2] at this
    have hperp : ∀ p ∈ D, polar qU p.1 u = 0 := by
      intro p hp
      obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp (hSK p hp)
      have h := hpol p hp p₁ hp₁D
      rw [hp₁2, ← hc', polar_smul_right_eq, hu₁, mul_zero, add_zero] at h
      exact h
    refine le_antisymm (fun p hp => ⟨hperp p hp, hSK p hp⟩) fun p' hp' => ?_
    refine mem_of_forall_polar_prod_eq_zero hnd hpol (by rw [hfinι]; exact hdim) ?_
    intro p hp
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp hp'.2
    obtain ⟨c'', hc''⟩ := Submodule.mem_span_singleton.mp (hSK p hp)
    rw [← hc', ← hc'', polar_smul_right_eq, polar_smul_right_eq, hperp p hp, hp'.1]
    ring

theorem eq_perpLine_of_stable {qU : QuadraticForm K (ι → K)}
    (hnd : ∀ v, (∀ w, QuadraticMap.polar qU v w = 0) → v = 0) (hn : 4 ≤ Fintype.card ι)
    (hq : 4 ≤ Nat.card K) {u : ι → K} (hu0 : u ≠ 0) (hu : qU u = 0)
    {D : Submodule K ((ι → K) × (ι → K))} (huD : ((u, 0) : (ι → K) × (ι → K)) ∈ D)
    (hts : ∀ p ∈ D, QuadraticMap.polar qU p.1 p.2 = 0)
    (hdim : Fintype.card ι ≤ Module.finrank K D)
    (hT : ∀ μ : K, ∀ p ∈ D, (p.1 + μ • p.2, p.2) ∈ D)
    (hE : ∀ s w : ι → K, qU s = 0 → QuadraticMap.polar qU s w = 0 →
      QuadraticMap.polar qU s u = 0 → QuadraticMap.polar qU w u = 0 →
      ∀ p ∈ D, (eichler qU s w p.1, eichler qU s w p.2) ∈ D)
    (hΓ : ∃ Γ : Finset (K × ((ι → K) ≃ₗ[K] (ι → K))),
      Nat.card K ^ (Fintype.card ι - 1) ≤ Γ.card ∧
      ∀ t ∈ Γ, (∀ v, qU (t.2 v) = qU v) ∧ t.2 u = u ∧
        ∀ p ∈ D, ∃ c : K, (t.2 p.1 + t.1 • t.2 p.2 - p.1, t.2 p.2 - p.2) = c • ((u, 0) : _)) :
    D = perpLine qU u := by
  obtain ⟨Γ, hcard, hΓ⟩ := hΓ
  refine eq_perpLine_of_stable_of_sq_lt hnd hn hu0 hu huD hts hdim hT hE ⟨Γ, ?_, hΓ⟩
  exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) (by omega)) hcard

end Main

end CFSG.RankThree.GF2n.Smith81
