module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmega
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthRat
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpAniso

public section

namespace CFSG.LocalAnalysis.WeakClosure81.OSeitz

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Heis

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem isRootCenter_of_heis {H : Subgroup (V ≃ₗ[K] V)} {X Y : Submodule K V} {x y : V}
    (hx0 : x ≠ 0) (hxQ : Q x = 0) (hyQ : Q y = 0) (hxy : polar Q x y = 0) (hxX : x ∈ X)
    (hyY : y ∈ Y) (hRx : ∀ d, (∀ z ∈ X, polar Q z d = 0) → eichler Q x d ∈ H)
    (hRy : ∀ d, (∀ z ∈ Y, polar Q z d = 0) → eichler Q y d ∈ H)
    (hspan : ∀ w, polar Q x w = 0 → ∃ c : K, ∀ z ∈ X, polar Q z (w - c • y) = 0)
    {u t : V} (hu : ∀ z ∈ X, polar Q z u = 0) (huy : polar Q y u = 0)
    (ht : ∀ z ∈ Y, polar Q z t = 0) (htx : polar Q x t = 0) (hut : polar Q u t ≠ 0) :
    IsRootCenter Q H x := by
  refine ⟨hx0, hxQ, fun w hw => ?_⟩
  obtain ⟨c, hc⟩ := hspan w hw
  have hxu : polar Q x u = 0 := hu x hxX
  have hyt : polar Q y t = 0 := ht y hyY
  have hcy : polar Q x (c • y) = 0 := by rw [polar_smul_right_eq, hxy, mul_zero]
  have hwc : polar Q x (w - c • y) = 0 := hc x hxX
  have hsplit : eichler Q x w = eichler Q x (w - c • y) * eichler Q x (c • y) := by
    rw [eichler_mul hwc hcy, sub_add_cancel]
  rw [hsplit]
  refine H.mul_mem (hRx _ hc) ?_
  set c' := c / polar Q u t with hc'
  have hcu : ∀ z ∈ X, polar Q z (c' • u) = 0 := fun z hz => by
    rw [polar_smul_right_eq, hu z hz, mul_zero]
  have key := CFSG.SignalizerFunctorTheorem.NonLocal.Orth.commutator_eichler_heis (Q := Q)
    (e₁ := x) (e₂ := y) (w := c' • u) (w' := t) hyQ hxy (hcu x hxX)
    (by rw [polar_smul_right_eq, huy, mul_zero]) htx hyt
  have hcoef : polar Q (c' • u) t • y = c • y := by
    rw [polar_smul_left_eq, hc', div_mul_cancel₀ c hut]
  rw [hcoef] at key
  rw [← key]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem (hRy t ht)) (hRx _ hcu)) (hRy t ht))
    (H.inv_mem (hRx _ hcu))

end Heis


section Radical

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

omit [Finite P] in
theorem closure_le_iSup_centralizer {E : Subgroup P} (h4 : Nat.card E = 4) :
    Subgroup.closure {k : P | k ∈ (⊤ : Subgroup P) ∧ ∃ F₀ : Subgroup P, F₀ ≤ E ∧
      F₀.relIndex E = 2 ∧ ∀ f ∈ F₀, f * k = k * f} ≤
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro k ⟨-, F₀, hF₀E, hF₀, hk⟩
  have hF₀ne : F₀ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.relIndex_bot_left, h4] at hF₀
    exact absurd hF₀ (by norm_num)
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF₀ne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hsub : (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} ≤
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} :=
    le_iSup₂_of_le a (hF₀E ha) (le_iSup_of_le ha1' le_rfl)
  exact hsub ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.mpr (hk a ha).symm⟩

theorem eichler_mem_of_stable (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    {E : Subgroup P} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) {X : Submodule K V}
    (hXQ : ∀ x ∈ X, Q x = 0)
    (hstab : ∀ g : elementaryGroup Q, π g ∈ E → ∀ w ∈ X, (g : V ≃ₗ[K] V) w ∈ X) {x d : V}
    (hx : x ∈ X) (hd : d ∈ qPerp Q X) :
    π ⟨eichler Q x d, eichler_mem_elementaryGroup Q x d⟩ ∈
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  classical
  have hfinV : Finite V := Module.finite_of_finite K
  have hfinGL : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  have hGO : elementaryGroup Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h4
    exact absurd h4 (by norm_num)
  set Qx : Subgroup (elementaryGroup Q) := (qRad Q X hXQ).comap (elementaryGroup Q).subtype
    with hQx
  have hnorm : ∀ e ∈ E, ∀ v ∈ Qx.map π, e * v * e⁻¹ ∈ Qx.map π := by
    intro e he v hv
    obtain ⟨g, rfl⟩ := hc.surjective e
    obtain ⟨q, hq, rfl⟩ := hv
    refine ⟨g * q * g⁻¹, ?_, by simp⟩
    have hgS : ∀ y ∈ X, ((g : elementaryGroup Q) : V ≃ₗ[K] V) y ∈ X := hstab g he
    have hgS' : ∀ y ∈ X, ((g : elementaryGroup Q) : V ≃ₗ[K] V)⁻¹ y ∈ X := fun y hy =>
      hstab g⁻¹ (by rw [map_inv]; exact E.inv_mem he) y hy
    exact qRad_conj_mem (hX := hXQ) (hGO g.2) hgS hgS' hq
  have hQp : ¬ 2 ∣ Nat.card (Qx.map π) := fun hd' =>
    not_dvd_card_comap_qRad_any (hX := hXQ) Nat.prime_two (by exact_mod_cast h2K) (elementaryGroup Q)
      (hd'.trans (Subgroup.card_map_dvd _ π))
  have hle := le_hyperClosure_of_normalized' Nat.prime_two hE hE1 hnorm hQp
  have hmem : (⟨eichler Q x d, eichler_mem_elementaryGroup Q x d⟩ : elementaryGroup Q) ∈ Qx :=
    eichler_mem_qRad (hX := hXQ) hx hd
  exact closure_le_iSup_centralizer h4 (hle (Subgroup.mem_map_of_mem _ hmem))

end Radical


section Pair

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem exists_orth_pair (φ : LinearMap.BilinForm K V) {U : Submodule K V}
    (hnd : ∀ z ∈ U, z ≠ 0 → ∃ v ∈ U, φ z v ≠ 0) {ε : K} (hε : ε * ε = 1)
    (hsym : ∀ p q, φ q p = ε * φ p q) {x y : V} (hxU : x ∈ U) (hyU : y ∈ U) (hxx : φ x x = 0)
    (hyy : φ y y = 0) (hxy : φ x y = 1) (hdim : ∃ p ∈ U, p ∉ Submodule.span K {x, y}) :
    ∃ u ∈ U, ∃ u' ∈ U, φ u x = 0 ∧ φ u y = 0 ∧ φ u' x = 0 ∧ φ u' y = 0 ∧ φ u u' ≠ 0 := by
  have hyx : φ y x = ε := by rw [hsym, hxy, mul_one]
  set pr : V → V := fun p => p - φ p y • x - (ε * φ p x) • y with hpr
  have hprU : ∀ p ∈ U, pr p ∈ U := fun p hp =>
    U.sub_mem (U.sub_mem hp (U.smul_mem _ hxU)) (U.smul_mem _ hyU)
  have hprx : ∀ p, φ (pr p) x = 0 := fun p => by
    simp only [hpr, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hxx, hyx]
    linear_combination -(φ p x) * hε
  have hpry : ∀ p, φ (pr p) y = 0 := fun p => by
    simp only [hpr, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hxy, hyy]
    ring
  obtain ⟨p, hpU, hp⟩ := hdim
  have hz0 : pr p ≠ 0 := by
    intro h
    apply hp
    have : p = φ p y • x + (ε * φ p x) • y := by
      have h' : p - φ p y • x - (ε * φ p x) • y = 0 := h
      linear_combination (norm := module) h'
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  obtain ⟨v, hvU, hv⟩ := hnd _ (hprU p hpU) hz0
  refine ⟨pr p, hprU p hpU, pr v, hprU v hvU, hprx p, hpry p, hprx v, hpry v, ?_⟩
  have e : φ (pr p) (pr v) = φ (pr p) v := by
    change φ (pr p) (v - φ v y • x - (ε * φ v x) • y) = _
    rw [map_sub, map_sub, map_smul, map_smul, hprx p, hpry p, smul_zero, smul_zero, sub_zero,
      sub_zero]
  rwa [e]

end Pair

section Lifts

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P : Type} [Group P] {π : elementaryGroup Q →* P}

theorem lift_eq_smul (hc : IsOrthogonalCover Q π) {E : Subgroup P} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {a b : elementaryGroup Q} (ha : π a ∈ E) (hb : π b ∈ E)
    (ha1 : π a ≠ 1) (hb1 : π b ≠ 1) (hab : π a ≠ π b) {g : elementaryGroup Q} (hg : π g ∈ E) :
    ∃ c : K, ∃ h : elementaryGroup Q, (h = 1 ∨ h = a ∨ h = b ∨ h = a * b) ∧
      ∀ v, (g : V ≃ₗ[K] V) v = c • (h : V ≃ₗ[K] V) v := by
  have key : ∀ h : elementaryGroup Q, π g = π h → ∃ c : K, ∀ v,
      (g : V ≃ₗ[K] V) v = c • (h : V ≃ₗ[K] V) v := by
    intro h hgh
    have hk : g * h⁻¹ ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, mul_inv_cancel]
    obtain ⟨c, hcv⟩ := mem_scalars.mp (hc.ker_scalar _ hk)
    refine ⟨c, fun v => ?_⟩
    have := hcv ((h : V ≃ₗ[K] V) v)
    rw [← this]
    change (g : V ≃ₗ[K] V) v = ((g : V ≃ₗ[K] V) * (h : V ≃ₗ[K] V)⁻¹) ((h : V ≃ₗ[K] V) v)
    simp
  rcases SpSeitz.mem_four hE h4 ha hb hg ha1 hb1 hab with h | h | h | h
  · obtain ⟨c, hc⟩ := key 1 (by rw [h, map_one])
    exact ⟨c, 1, Or.inl rfl, hc⟩
  · obtain ⟨c, hc⟩ := key a h
    exact ⟨c, a, Or.inr (Or.inl rfl), hc⟩
  · obtain ⟨c, hc⟩ := key b h
    exact ⟨c, b, Or.inr (Or.inr (Or.inl rfl)), hc⟩
  · obtain ⟨c, hc⟩ := key (a * b) (by rw [h, map_mul])
    exact ⟨c, a * b, Or.inr (Or.inr (Or.inr rfl)), hc⟩

theorem stab_of_ab (hc : IsOrthogonalCover Q π) {E : Subgroup P} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {a b : elementaryGroup Q} (ha : π a ∈ E) (hb : π b ∈ E)
    (ha1 : π a ≠ 1) (hb1 : π b ≠ 1) (hab : π a ≠ π b) {X : Submodule K V}
    (hXa : ∀ w ∈ X, (a : V ≃ₗ[K] V) w ∈ X) (hXb : ∀ w ∈ X, (b : V ≃ₗ[K] V) w ∈ X) :
    ∀ g : elementaryGroup Q, π g ∈ E → ∀ w ∈ X, (g : V ≃ₗ[K] V) w ∈ X := by
  intro g hg w hw
  obtain ⟨c, h, hh, hv⟩ := lift_eq_smul hc hE h4 ha hb ha1 hb1 hab hg
  rw [hv]
  refine X.smul_mem _ ?_
  rcases hh with rfl | rfl | rfl | rfl
  · exact hw
  · exact hXa w hw
  · exact hXb w hw
  · exact hXa _ (hXb w hw)

end Lifts


section D8

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

abbrev cGenV (π : elementaryGroup Q →* P) (E : Subgroup P) : Subgroup (V ≃ₗ[K] V) :=
  ((⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a}).comap π).map
    (elementaryGroup Q).subtype

omit [Finite K] [FiniteDimensional K V] [Finite P] in
theorem cGenV_le_orthogonalGroup (E : Subgroup P) :
    cGenV π E ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro _ ⟨g, -, rfl⟩
  exact elementaryGroup_le_orthogonalGroup Q g.2

theorem eichler_mem_cGenV (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    {E : Subgroup P} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) {X : Submodule K V}
    (hXQ : ∀ x ∈ X, Q x = 0)
    (hstab : ∀ g : elementaryGroup Q, π g ∈ E → ∀ w ∈ X, (g : V ≃ₗ[K] V) w ∈ X) {x : V}
    (hx : x ∈ X) (d : V) (hd : ∀ z ∈ X, polar Q z d = 0) : eichler Q x d ∈ cGenV π E :=
  ⟨⟨eichler Q x d, eichler_mem_elementaryGroup Q x d⟩,
    eichler_mem_of_stable hc h2K hE h4 hXQ hstab hx hd, rfl⟩

omit [Finite K] [FiniteDimensional K V] in
theorem span_pair_stable (T : V →ₗ[K] V) {u w : V} (h1 : T u ∈ Submodule.span K {u, w})
    (h2 : T w ∈ Submodule.span K {u, w}) :
    ∀ z ∈ Submodule.span K {u, w}, T z ∈ Submodule.span K {u, w} := by
  intro z hz
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hz
  rw [map_add, map_smul, map_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

theorem isRootCenter_dih (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    {E : Subgroup P} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) {a b : elementaryGroup Q}
    (ha : π a ∈ E) (hb : π b ∈ E) (ha1 : π a ≠ 1) (hb1 : π b ≠ 1) (hab : π a ≠ π b)
    (haa : ∀ v, (a : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v) = v)
    (hbb : ∀ v, (b : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = v)
    (hanti : ∀ v, (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = -(b : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v))
    {x x' : V} (hxa : (a : V ≃ₗ[K] V) x = x) (hx'a : (a : V ≃ₗ[K] V) x' = x') (hxQ : Q x = 0)
    (hx'Q : Q x' = 0) (hxx' : polar Q x x' = 1)
    (hdim : ∃ p, (a : V ≃ₗ[K] V) p = p ∧ p ∉ Submodule.span K {x, x'}) :
    IsRootCenter Q (cGenV π E) x := by
  set A : V ≃ₗ[K] V := (a : V ≃ₗ[K] V) with hA
  set B : V ≃ₗ[K] V := (b : V ≃ₗ[K] V) with hB
  have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q a.2
  have hBO : B ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q b.2
  have hpA := polar_map_of_mem hAO
  have hpB := polar_map_of_mem hBO
  have horth : ∀ v w, A v = v → A w = -w → polar Q v w = 0 := by
    intro v w hv hw
    have h := hpA v w
    rw [hv, hw, polar_neg_right] at h
    have : (2 : K) * polar Q v w = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left h2K
  have hBneg : ∀ v, A v = v → A (B v) = -B v := fun v hv => by rw [hanti, hv]
  have hpolxx : ∀ v, Q v = 0 → polar Q v v = 0 := fun v hv => by
    rw [polar_self, hv, smul_zero]
  have hplane : ∀ v, A v = v → Q v = 0 →
      (∀ z ∈ Submodule.span K {v, B v}, Q z = 0) ∧
      ∀ g : elementaryGroup Q, π g ∈ E → ∀ w ∈ Submodule.span K {v, B v},
        (g : V ≃ₗ[K] V) w ∈ Submodule.span K {v, B v} := by
    intro v hv hvQ
    have hBvQ : Q (B v) = 0 := by rw [map_of_mem hBO, hvQ]
    have hvBv : polar Q v (B v) = 0 := horth v (B v) hv (hBneg v hv)
    have hv1 : v ∈ Submodule.span K {v, B v} := Submodule.subset_span (by simp)
    have hv2 : B v ∈ Submodule.span K {v, B v} := Submodule.subset_span (by simp)
    refine ⟨fun z hz => ?_, stab_of_ab hc hE h4 ha hb ha1 hb1 hab
      (span_pair_stable (A : V →ₗ[K] V) (by simpa [hv] using hv1)
        (by simpa [hBneg v hv] using Submodule.neg_mem _ hv2))
      (span_pair_stable (B : V →ₗ[K] V) (by simpa using hv2) (by simpa [hbb] using hv1))⟩
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hz
    have h0 : polar Q (α • v) (β • B v) = 0 := by
      rw [polar_smul_left_eq, polar_smul_right_eq, hvBv, mul_zero, mul_zero]
    have h : polar Q (α • v) (β • B v) = Q (α • v + β • B v) - Q (α • v) - Q (β • B v) := rfl
    rw [QuadraticMap.map_smul, QuadraticMap.map_smul, hvQ, hBvQ, h0] at h
    linear_combination -h
  obtain ⟨hXQ, hXs⟩ := hplane x hxa hxQ
  obtain ⟨hYQ, hYs⟩ := hplane x' hx'a hx'Q
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [polar_zero_left] at hxx'
    exact zero_ne_one hxx'
  set U : Submodule K V := LinearMap.ker ((A : V →ₗ[K] V) - LinearMap.id) with hUdef
  have hU : ∀ v, v ∈ U ↔ A v = v := fun v => by simp [hUdef, sub_eq_zero]
  have hnd : ∀ z ∈ U, z ≠ 0 → ∃ v ∈ U, polarBilin Q z v ≠ 0 := by
    intro z hzU hz0
    have hzA := (hU z).1 hzU
    obtain ⟨w, hw⟩ : ∃ w, polar Q z w ≠ 0 := by
      by_contra h
      push Not at h
      exact hz0 (eq_zero_of_polar_eq_zero hc.nondegenerate h)
    refine ⟨(2 : K)⁻¹ • (w + A w), (hU _).2 ?_, ?_⟩
    · rw [map_smul, map_add, haa, add_comm]
    · have h1 := hpA z (A w)
      rw [hzA, haa] at h1
      rw [polarBilin_apply_apply, polar_smul_right_eq, polar_add_right, ← h1]
      intro h
      apply hw
      have : (2 : K)⁻¹ * (2 * polar Q z w) = 0 := by linear_combination h
      rw [← mul_assoc, inv_mul_cancel₀ h2K, one_mul] at this
      exact this
  obtain ⟨p, hpA', hp⟩ := hdim
  obtain ⟨u, huU, u', hu'U, hux, hux', hu'x, hu'x', huu'⟩ :=
    exists_orth_pair (polarBilin Q) hnd (ε := 1) (by norm_num)
      (fun p q => by simp [polarBilin_apply_apply, polar_comm]) ((hU x).2 hxa) ((hU x').2 hx'a)
      (hpolxx x hxQ) (hpolxx x' hx'Q) hxx' ⟨p, (hU p).2 hpA', hp⟩
  simp only [polarBilin_apply_apply] at hux hux' hu'x hu'x' huu'
  have huA := (hU u).1 huU
  have hu'A := (hU u').1 hu'U
  have hspan2 : ∀ {v : V} (f : V → K), f v = 0 → f (B v) = 0 →
      (∀ α β : K, f (α • v + β • B v) = α * f v + β * f (B v)) →
      ∀ z ∈ Submodule.span K {v, B v}, f z = 0 := by
    intro v f h1 h2 hlin z hz
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hz
    rw [hlin, h1, h2, mul_zero, mul_zero, add_zero]
  refine isRootCenter_of_heis (X := Submodule.span K {x, B x})
    (Y := Submodule.span K {x', B x'}) (y := B x') hx0 hxQ (by rw [map_of_mem hBO]; exact hx'Q)
    (horth x (B x') hxa (hBneg x' hx'a)) (Submodule.subset_span (by simp))
    (Submodule.subset_span (by simp))
    (fun d hd => eichler_mem_cGenV hc h2K hE h4 hXQ hXs (Submodule.subset_span (by simp)) d hd)
    (fun d hd => eichler_mem_cGenV hc h2K hE h4 hYQ hYs (Submodule.subset_span (by simp)) d hd)
    ?_ (u := u) (t := u') ?_ ?_ ?_ ?_ huu'
  · intro w hw
    refine ⟨polar Q (B x) w, fun z hz => ?_⟩
    refine hspan2 (v := x) (fun z => polar Q z (w - polar Q (B x) w • B x')) ?_ ?_ ?_ z hz
    · rw [polar_sub_right, polar_smul_right_eq, hw, horth x (B x') hxa (hBneg x' hx'a)]
      ring
    · rw [polar_sub_right, polar_smul_right_eq, hpB, hxx']
      ring
    · intro α β
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq]
  · refine hspan2 (v := x) (fun z => polar Q z u) ?_ ?_ ?_
    · rw [polar_comm]; exact hux
    · rw [polar_comm]; exact horth u (B x) huA (hBneg x hxa)
    · intro α β
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq]
  · rw [polar_comm]; exact horth u (B x') huA (hBneg x' hx'a)
  · refine hspan2 (v := x') (fun z => polar Q z u') ?_ ?_ ?_
    · rw [polar_comm]; exact hu'x'
    · rw [polar_comm]; exact horth u' (B x') hu'A (hBneg x' hx'a)
    · intro α β
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq]
  · rw [polar_comm]; exact hu'x

end D8


section Dim

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_le_two_mul_fixed (h2K : (2 : K) ≠ 0) (A : V →ₗ[K] V) (B : V ≃ₗ[K] V)
    (haa : ∀ v, A (A v) = v) (hanti : ∀ v, A (B v) = -B (A v)) :
    Module.finrank K V ≤ 2 * Module.finrank K (LinearMap.ker (A - LinearMap.id)) := by
  set U := LinearMap.ker (A - LinearMap.id) with hU
  set U' := LinearMap.ker (A + LinearMap.id) with hU'
  have hmU : ∀ v, v ∈ U ↔ A v = v := fun v => by simp [hU, sub_eq_zero]
  have hmU' : ∀ v, v ∈ U' ↔ A v = -v := fun v => by simp [hU', add_eq_zero_iff_eq_neg]
  have htop : U ⊔ U' = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    have hv : v = (2 : K)⁻¹ • (v + A v) + (2 : K)⁻¹ • (v - A v) := by
      have : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2K
      linear_combination (norm := module) (-1 : K) • this • v
    rw [hv]
    refine Submodule.add_mem_sup ((hmU _).2 ?_) ((hmU' _).2 ?_)
    · rw [map_smul, map_add, haa, add_comm]
    · rw [map_smul, map_sub, haa, ← smul_neg, neg_sub]
  have hle : Module.finrank K U' ≤ Module.finrank K U := by
    let f : U' →ₗ[K] U := (B : V →ₗ[K] V).restrict (p := U') (q := U) fun w hw => by
      rw [hmU] at ⊢
      rw [hmU'] at hw
      change A (B w) = B w
      rw [hanti, hw, map_neg, neg_neg]
    refine LinearMap.finrank_le_finrank_of_injective (f := f) fun w w' h => ?_
    have h' : B (w : V) = B (w' : V) := congrArg Subtype.val h
    exact Subtype.ext (B.injective h')
  have h1 := Submodule.finrank_add_le_finrank_add_finrank U U'
  rw [htop, finrank_top] at h1
  omega

end Dim

section D8Top

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

omit [Finite K] [FiniteDimensional K V] [Finite P] in
theorem top_le_of_elementaryGroup_le (hc : IsOrthogonalCover Q π) {E : Subgroup P}
    (hle : elementaryGroup Q ≤ cGenV π E) :
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  intro k _
  obtain ⟨g, rfl⟩ := hc.surjective k
  obtain ⟨h, hh, hhg⟩ := hle g.2
  have : h = g := Subtype.ext hhg
  rw [this] at hh
  exact hh

theorem top_le_of_dih (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    (hdim : 7 ≤ Module.finrank K V) {E : Subgroup P} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {a b : elementaryGroup Q} (ha : π a ∈ E) (hb : π b ∈ E)
    (ha1 : π a ≠ 1) (hb1 : π b ≠ 1) (hab : π a ≠ π b)
    (haa : ∀ v, (a : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v) = v)
    (hbb : ∀ v, (b : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = v)
    (hanti : ∀ v, (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = -(b : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v)) :
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  classical
  set A : V ≃ₗ[K] V := (a : V ≃ₗ[K] V) with hA
  have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q a.2
  set U : Submodule K V := LinearMap.ker ((A : V →ₗ[K] V) - LinearMap.id) with hUdef
  have hU : ∀ v, v ∈ U ↔ A v = v := fun v => by simp [hUdef, sub_eq_zero]
  have h3 : 3 ≤ Module.finrank K U := by
    have h := finrank_le_two_mul_fixed h2K (A : V →ₗ[K] V) (b : V ≃ₗ[K] V) haa hanti
    change Module.finrank K V ≤ 2 * Module.finrank K U at h
    omega
  have hndU : PolarNondegOn Q U := by
    intro z hzU hz
    by_contra hz0
    have hzA := (hU z).1 hzU
    obtain ⟨w, hw⟩ : ∃ w, polar Q z w ≠ 0 := by
      by_contra h
      push Not at h
      exact hz0 (eq_zero_of_polar_eq_zero hc.nondegenerate h)
    apply hw
    have h1 := polar_map_of_mem hAO z (A w)
    rw [hzA, haa] at h1
    have h2 := hz ((2 : K)⁻¹ • (w + A w)) ((hU _).2 (by rw [map_smul, map_add, haa, add_comm]))
    rw [polar_smul_right_eq, polar_add_right, ← h1] at h2
    have : (2 : K)⁻¹ * (2 * polar Q z w) = 0 := by linear_combination h2
    rw [← mul_assoc, inv_mul_cancel₀ h2K, one_mul] at this
    exact this
  obtain ⟨x, hxU, hx0, hxQ⟩ := OrthBlk.exists_singular_of_three_le_any (Q := Q) h3
  obtain ⟨x', hx'U, hx'Q, hxx'⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_partner_of_polarNondegOn hndU hxU hxQ hx0
  have hspan : ∃ p, A p = p ∧ p ∉ Submodule.span K {x, x'} := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ Submodule.span K {x, x'} := fun p hp => hcon p ((hU p).1 hp)
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank K (Submodule.span K ({x, x'} : Set V)) ≤ 2 := by
      have := finrank_span_finset_le_card (R := K) ({x, x'} : Finset V)
      rw [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans Finset.card_le_two
    omega
  have hrc := isRootCenter_dih hc h2K hE h4 ha hb ha1 hb1 hab haa hbb hanti ((hU x).1 hxU)
    ((hU x').1 hx'U) hxQ hx'Q hxx' hspan
  have hrc' := isRootCenter_dih hc h2K hE h4 ha hb ha1 hb1 hab haa hbb hanti ((hU x').1 hx'U)
    ((hU x).1 hxU) hx'Q hxQ (by rw [polar_comm]; exact hxx')
    (by rw [Set.pair_comm]; exact hspan)
  exact top_le_of_elementaryGroup_le hc (elementaryGroup_le_of_hypPair hc.nondegenerate
    (cGenV_le_orthogonalGroup E) ⟨x, x', hxQ, hx'Q, hxx'⟩ hrc hrc')

end D8Top


section Q8

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

abbrev eigN (A B : V ≃ₗ[K] V) (c μ : K) : Submodule K V :=
  LinearMap.ker ((A : V →ₗ[K] V) + c • (B : V →ₗ[K] V) - μ • LinearMap.id)

omit [Finite K] [FiniteDimensional K V] in
theorem mem_eigN {A B : V ≃ₗ[K] V} {c μ : K} {v : V} :
    v ∈ eigN A B c μ ↔ A v + c • B v = μ • v := by
  simp [eigN, sub_eq_zero]

theorem isRootCenter_quat (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    {E : Subgroup P} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) {a b : elementaryGroup Q}
    (ha : π a ∈ E) (hb : π b ∈ E) (ha1 : π a ≠ 1) (hb1 : π b ≠ 1) (hab : π a ≠ π b)
    (haa : ∀ v, (a : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v) = -v)
    (hbb : ∀ v, (b : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = -v)
    (hanti : ∀ v, (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = -(b : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v))
    {c μ : K} (hμ : μ * μ = -(1 + c * c)) (hμ0 : μ ≠ 0)
    (h3 : 3 ≤ Module.finrank K (eigN (a : V ≃ₗ[K] V) (b : V ≃ₗ[K] V) c μ)) {x : V}
    (hx : x ∈ eigN (a : V ≃ₗ[K] V) (b : V ≃ₗ[K] V) c μ) (hx0 : x ≠ 0) :
    IsRootCenter Q (cGenV π E) x ∧
      ∃ x' ∈ eigN (a : V ≃ₗ[K] V) (b : V ≃ₗ[K] V) c (-μ), Q x' = 0 ∧ polar Q x x' = 1 := by
  classical
  set A : V ≃ₗ[K] V := (a : V ≃ₗ[K] V) with hA
  set B : V ≃ₗ[K] V := (b : V ≃ₗ[K] V) with hB
  have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q a.2
  have hBO : B ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q b.2
  have hpA := polar_map_of_mem hAO
  have hpB := polar_map_of_mem hBO
  have hsA : ∀ v w, polar Q (A v) w = -polar Q v (A w) := fun v w => by
    have h := hpA v (A w)
    rw [haa, polar_neg_right] at h
    linear_combination -h
  have hsB : ∀ v w, polar Q (B v) w = -polar Q v (B w) := fun v w => by
    have h := hpB v (B w)
    rw [hbb, polar_neg_right] at h
    linear_combination -h
  have hBA : ∀ v, B (A v) = -A (B v) := fun v => by rw [hanti, neg_neg]
  set T : V →ₗ[K] V := (A : V →ₗ[K] V) ∘ₗ (B : V →ₗ[K] V) with hTdef
  have hT : ∀ v, T v = A (B v) := fun v => rfl
  have hBT : ∀ v, B (T v) = A v := fun v => by rw [hT, hBA, hbb, map_neg, neg_neg]
  have hAT : ∀ v, A (T v) = -B v := fun v => by rw [hT, haa]
  have hTT : ∀ v, T (T v) = -v := fun v => by rw [hT, hBT, haa]
  have hpT : ∀ v w, polar Q (T v) (T w) = polar Q v w := fun v w => by rw [hT, hT, hpA, hpB]
  have hsT : ∀ v w, polar Q (T v) w = -polar Q v (T w) := fun v w => by
    simp only [hT, hsA, hsB, hBA, polar_neg_right, neg_neg]
  have hmem := fun {μ' : K} {v : V} => (mem_eigN (A := A) (B := B) (c := c) (μ := μ') (v := v))
  have hTeig : ∀ {μ' : K} {v : V}, v ∈ eigN A B c μ' → T v ∈ eigN A B c (-μ') := by
    intro μ' v hv
    rw [hmem] at hv ⊢
    have h := congrArg (fun z => A (B z)) hv
    simp only [map_add, map_smul, hBA, haa, hbb, map_neg, neg_neg] at h
    rw [hAT, hBT, hT]
    linear_combination (norm := module) -h
  have hsN : ∀ v w, polar Q (A v + c • B v) w = -polar Q v (A w + c • B w) := fun v w => by
    rw [polar_add_left, polar_smul_left_eq, hsA, hsB, polar_add_right, polar_smul_right_eq]
    ring
  have htot : ∀ {μ' : K}, μ' ≠ 0 → ∀ v ∈ eigN A B c μ', ∀ w ∈ eigN A B c μ', polar Q v w = 0 := by
    intro μ' hμ' v hv w hw
    have h := hsN v w
    rw [hmem.1 hv, hmem.1 hw, polar_smul_left_eq, polar_smul_right_eq] at h
    have : (2 * μ') * polar Q v w = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2K hμ')
  have hsing : ∀ {μ' : K}, μ' ≠ 0 → ∀ v ∈ eigN A B c μ', Q v = 0 := by
    intro μ' hμ' v hv
    have h := htot hμ' v hv v hv
    have : (2 : K) * Q v = 0 := by rwa [polar_self, two_smul, ← two_mul] at h
    exact (mul_eq_zero.1 this).resolve_left h2K
  set M : V →ₗ[K] V := (A : V →ₗ[K] V) + c • (B : V →ₗ[K] V) with hMdef
  have hM : ∀ v, M v = A v + c • B v := fun v => rfl
  have hmemM : ∀ {μ' : K} {v : V}, v ∈ eigN A B c μ' ↔ M v = μ' • v := fun {μ' v} => by
    rw [hmem, hM]
  have hMM : ∀ w, M (M w) = (μ * μ) • w := fun w => by
    rw [hμ, hM, hM, map_add, map_add, map_smul, map_smul, haa, hbb, hanti]
    module
  have hdec : ∀ w, (2 * μ)⁻¹ • (M w + μ • w) ∈ eigN A B c μ ∧
      (2 * μ)⁻¹ • (μ • w - M w) ∈ eigN A B c (-μ) ∧
      w = (2 * μ)⁻¹ • (M w + μ • w) + (2 * μ)⁻¹ • (μ • w - M w) := by
    intro w
    have h2μ : (2 * μ)⁻¹ * (2 * μ) = 1 := inv_mul_cancel₀ (mul_ne_zero h2K hμ0)
    refine ⟨hmemM.2 ?_, hmemM.2 ?_, ?_⟩
    · rw [map_smul, map_add, map_smul, hMM]
      module
    · rw [map_smul, map_sub, map_smul, hMM]
      module
    · linear_combination (norm := module) (-1 : K) • h2μ • w
  have hplane : ∀ {μ' : K}, μ' * μ' = -(1 + c * c) → μ' ≠ 0 → ∀ v ∈ eigN A B c μ',
      (∀ z ∈ Submodule.span K {v, T v}, Q z = 0) ∧
      ∀ g : elementaryGroup Q, π g ∈ E → ∀ w ∈ Submodule.span K {v, T v},
        (g : V ≃ₗ[K] V) w ∈ Submodule.span K {v, T v} := by
    intro μ' hμ' hμ'0 v hv
    have hTv := hTeig hv
    have hvT : polar Q v (T v) = 0 := by
      have h := hsT v v
      rw [polar_comm] at h
      have : (2 : K) * polar Q v (T v) = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left h2K
    have hBv : B v = c • A v + μ' • T v := by
      have h := hmem.1 hTv
      rw [hAT, hBT] at h
      linear_combination (norm := module) -h
    have hAv : A v = (-μ'⁻¹) • v + (μ'⁻¹ * c) • T v := by
      have h := hmem.1 hv
      rw [hBv] at h
      have h2 : (-(μ' * μ')) • A v = μ' • v - (c * μ') • T v := by
        rw [hμ']
        linear_combination (norm := module) h
      have hne : -(μ' * μ') ≠ 0 := neg_ne_zero.2 (mul_ne_zero hμ'0 hμ'0)
      calc A v = (-(μ' * μ'))⁻¹ • ((-(μ' * μ')) • A v) := by
            rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
        _ = (-(μ' * μ'))⁻¹ • (μ' • v - (c * μ') • T v) := by rw [h2]
        _ = (-μ'⁻¹) • v + (μ'⁻¹ * c) • T v := by
            match_scalars <;> field_simp
    have hTvQ : Q (T v) = 0 := hsing (neg_ne_zero.2 hμ'0) _ hTv
    have hvQ : Q v = 0 := hsing hμ'0 v hv
    have h1 : v ∈ Submodule.span K {v, T v} := Submodule.subset_span (by simp)
    have h2 : T v ∈ Submodule.span K {v, T v} := Submodule.subset_span (by simp)
    have hAvS : A v ∈ Submodule.span K {v, T v} :=
      Submodule.mem_span_pair.2 ⟨-μ'⁻¹, μ'⁻¹ * c, hAv.symm⟩
    have hBvS : B v ∈ Submodule.span K {v, T v} := by
      rw [hBv]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hAvS) (Submodule.smul_mem _ _ h2)
    refine ⟨fun z hz => ?_, stab_of_ab hc hE h4 ha hb ha1 hb1 hab
      (span_pair_stable (A : V →ₗ[K] V) hAvS (by
        change A (T v) ∈ _
        rw [hAT]
        exact Submodule.neg_mem _ hBvS))
      (span_pair_stable (B : V →ₗ[K] V) hBvS (by
        change B (T v) ∈ _
        rw [hBT]
        exact hAvS))⟩
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hz
    have h0 : polar Q (α • v) (β • T v) = 0 := by
      rw [polar_smul_left_eq, polar_smul_right_eq, hvT, mul_zero, mul_zero]
    have h : polar Q (α • v) (β • T v) = Q (α • v + β • T v) - Q (α • v) - Q (β • T v) := rfl
    rw [QuadraticMap.map_smul, QuadraticMap.map_smul, hvQ, hTvQ, h0] at h
    linear_combination -h
  have hvTv : ∀ v, polar Q v (T v) = 0 := fun v => by
    have h := hsT v v
    rw [polar_comm] at h
    have : (2 : K) * polar Q v (T v) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2K
  have hμn : -μ ≠ 0 := neg_ne_zero.2 hμ0
  have hTx := hTeig hx
  have hTx0 : T x ≠ 0 := fun h => hx0 (by
    have := hTT x
    rw [h, map_zero] at this
    exact neg_eq_zero.1 this.symm)
  obtain ⟨w, hw⟩ : ∃ w, polar Q w (T x) ≠ 0 := by
    by_contra h
    push Not at h
    exact hTx0 (eq_zero_of_polar_eq_zero hc.nondegenerate fun z => by rw [polar_comm]; exact h z)
  obtain ⟨hw1, hw2, hw3⟩ := hdec w
  set wp := (2 * μ)⁻¹ • (M w + μ • w) with hwp
  set wm := (2 * μ)⁻¹ • (μ • w - M w) with hwm
  have hwpT : polar Q wp (T x) ≠ 0 := by
    intro h0
    apply hw
    rw [hw3, polar_add_left, h0, htot hμn _ hw2 _ hTx, add_zero]
  set y := (polar Q wp (T x))⁻¹ • wp with hydef
  have hy : y ∈ eigN A B c μ := Submodule.smul_mem _ _ hw1
  have hyT : polar Q y (T x) = 1 := by rw [polar_smul_left_eq, inv_mul_cancel₀ hwpT]
  set γ : LinearMap.BilinForm K V := (polarBilin Q).compl₂ T with hγdef
  have hγ : ∀ p q, γ p q = polar Q p (T q) := fun p q => rfl
  have hnd : ∀ z ∈ eigN A B c μ, z ≠ 0 → ∃ v ∈ eigN A B c μ, γ z v ≠ 0 := by
    intro z hz hz0
    obtain ⟨w', hw'⟩ : ∃ w', polar Q z w' ≠ 0 := by
      by_contra h
      push Not at h
      exact hz0 (eq_zero_of_polar_eq_zero hc.nondegenerate h)
    obtain ⟨hp1, hp2, hp3⟩ := hdec w'
    refine ⟨-T ((2 * μ)⁻¹ • (μ • w' - M w')), Submodule.neg_mem _ ?_, ?_⟩
    · have := hTeig hp2
      rwa [neg_neg] at this
    · rw [hγ, map_neg, hTT, neg_neg]
      intro h0
      apply hw'
      rw [hp3, polar_add_right, h0, htot hμ0 _ hz _ hp1, zero_add]
  have hsym : ∀ p q, γ q p = (-1) * γ p q := fun p q => by
    rw [hγ, hγ, polar_comm, hsT]
    ring
  have hspanle : ∃ p ∈ eigN A B c μ, p ∉ Submodule.span K {y, x} := by
    by_contra hcon
    push Not at hcon
    have hle : eigN A B c μ ≤ Submodule.span K {y, x} := fun p hp => hcon p hp
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank K (Submodule.span K ({y, x} : Set V)) ≤ 2 := by
      have := finrank_span_finset_le_card (R := K) ({y, x} : Finset V)
      rw [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans Finset.card_le_two
    omega
  obtain ⟨u, huU, u', hu'U, huy, hux, hu'y, hu'x, huu'⟩ :=
    exists_orth_pair γ hnd (ε := -1) (by norm_num) hsym hy hx (hvTv y) (hvTv x) hyT hspanle
  rw [hγ] at huy hux hu'y hu'x huu'
  obtain ⟨hXQ, hXs⟩ := hplane hμ hμ0 x hx
  obtain ⟨hYQ, hYs⟩ := hplane hμ hμ0 y hy
  have hspan2 : ∀ {v : V} (f : V → K), f v = 0 → f (T v) = 0 →
      (∀ α β : K, f (α • v + β • T v) = α * f v + β * f (T v)) →
      ∀ z ∈ Submodule.span K {v, T v}, f z = 0 := by
    intro v f h1 h2 hlin z hz
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hz
    rw [hlin, h1, h2, mul_zero, mul_zero, add_zero]
  have hlinp : ∀ (d : V) (v : V) (α β : K), polar Q (α • v + β • T v) d =
      α * polar Q v d + β * polar Q (T v) d := fun d v α β => by
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq]
  refine ⟨?_, ?_⟩
  swap
  · obtain ⟨w', hw'⟩ : ∃ w', polar Q x w' ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (eq_zero_of_polar_eq_zero hc.nondegenerate h)
    obtain ⟨hp1, hp2, hp3⟩ := hdec w'
    have hne : polar Q x ((2 * μ)⁻¹ • (μ • w' - M w')) ≠ 0 := by
      intro h0
      apply hw'
      rw [hp3, polar_add_right, h0, htot hμ0 _ hx _ hp1, zero_add]
    refine ⟨(polar Q x ((2 * μ)⁻¹ • (μ • w' - M w')))⁻¹ • ((2 * μ)⁻¹ • (μ • w' - M w')),
      Submodule.smul_mem _ _ hp2, ?_, ?_⟩
    · exact hsing hμn _ (Submodule.smul_mem _ _ hp2)
    · rw [polar_smul_right_eq, inv_mul_cancel₀ hne]
  refine isRootCenter_of_heis (X := Submodule.span K {x, T x}) (Y := Submodule.span K {y, T y})
    (y := y) hx0 (hsing hμ0 x hx) (hsing hμ0 y hy) (htot hμ0 x hx y hy)
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    (fun d hd => eichler_mem_cGenV hc h2K hE h4 hXQ hXs (Submodule.subset_span (by simp)) d hd)
    (fun d hd => eichler_mem_cGenV hc h2K hE h4 hYQ hYs (Submodule.subset_span (by simp)) d hd)
    ?_ (u := u) (t := T u') ?_ (htot hμ0 y hy u huU) ?_ ?_ huu'
  · intro w' hw'
    refine ⟨polar Q (T x) w', fun z hz => ?_⟩
    refine hspan2 (v := x) (fun z => polar Q z (w' - polar Q (T x) w' • y)) ?_ ?_
      (fun α β => hlinp _ x α β) z hz
    · rw [polar_sub_right, polar_smul_right_eq, hw', htot hμ0 x hx y hy]
      ring
    · rw [polar_sub_right, polar_smul_right_eq, polar_comm Q (T x) y, hyT]
      ring
  · refine hspan2 (v := x) (fun z => polar Q z u) (htot hμ0 x hx u huU) ?_
      (fun α β => hlinp _ x α β)
    rw [polar_comm]
    exact hux
  · refine hspan2 (v := y) (fun z => polar Q z (T u')) ?_ ?_ (fun α β => hlinp _ y α β)
    · have := hsym u' y
      rw [hγ, hγ, hu'y, mul_zero] at this
      exact this
    · rw [hpT]
      exact htot hμ0 y hy u' hu'U
  · have := hsym u' x
    rw [hγ, hγ, hu'x, mul_zero] at this
    exact this

end Q8


section Q8Top

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

omit [Finite K] in
theorem three_le_finrank_eigN (h2K : (2 : K) ≠ 0) (hdim : 7 ≤ Module.finrank K V)
    {A B : V ≃ₗ[K] V} (haa : ∀ v, A (A v) = -v) (hbb : ∀ v, B (B v) = -v)
    (hanti : ∀ v, A (B v) = -B (A v)) {c l : K} (hl : l * l = -(1 + c * c)) (hl0 : l ≠ 0) :
    3 ≤ Module.finrank K (eigN A B c l) := by
  set M : V →ₗ[K] V := (A : V →ₗ[K] V) + c • (B : V →ₗ[K] V) with hMdef
  have hM : ∀ v, M v = A v + c • B v := fun v => rfl
  have hBA : ∀ v, B (A v) = -A (B v) := fun v => by rw [hanti, neg_neg]
  set A' : V →ₗ[K] V := l⁻¹ • M with hA'
  have hA'a : ∀ v, A' v = l⁻¹ • M v := fun v => rfl
  have hMM : ∀ w, M (M w) = (l * l) • w := fun w => by
    rw [hl, hM, hM, map_add, map_add, map_smul, map_smul, haa, hbb, hanti]
    module
  have haa' : ∀ v, A' (A' v) = v := fun v => by
    rw [hA'a, hA'a, map_smul, hMM, smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * (l * l) = 1 by field_simp, one_smul]
  have hanti' : ∀ v, A' ((A * B) v) = -(A * B) (A' v) := fun v => by
    rw [hA'a, hA'a, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hM, hM]
    simp only [map_add, map_smul, map_neg, haa, hbb, hBA, neg_neg]
    module
  have h := finrank_le_two_mul_fixed h2K A' (A * B) haa' hanti'
  have heq : LinearMap.ker (A' - LinearMap.id) = eigN A B c l := by
    ext v
    rw [mem_eigN, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, hA'a,
      ← hM]
    constructor
    · intro h1
      calc M v = l • (l⁻¹ • M v) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
        _ = l • v := by rw [h1]
    · intro h1
      rw [h1, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  rw [heq] at h
  omega

theorem top_le_of_quat (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    (hdim : 7 ≤ Module.finrank K V) {E : Subgroup P} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {a b : elementaryGroup Q} (ha : π a ∈ E) (hb : π b ∈ E)
    (ha1 : π a ≠ 1) (hb1 : π b ≠ 1) (hab : π a ≠ π b)
    (haa : ∀ v, (a : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v) = -v)
    (hbb : ∀ v, (b : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = -v)
    (hanti : ∀ v, (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = -(b : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v)) :
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  obtain ⟨c, l, hl, hl0⟩ : ∃ c l : K, l * l = -(1 + c * c) ∧ l ≠ 0 := by
    by_cases hK : IsSquare (-1 : K)
    · obtain ⟨i, hi⟩ := hK
      refine ⟨0, i, by rw [← hi]; ring, ?_⟩
      rintro rfl
      rw [mul_zero] at hi
      exact one_ne_zero (neg_eq_zero.1 hi)
    · obtain ⟨s, t, hst⟩ := SpSeitz.exists_sq_add_sq h2K one_ne_zero one_ne_zero (1 : K)
      refine ⟨s, t, by linear_combination hst, ?_⟩
      rintro rfl
      exact hK ⟨s, by linear_combination -hst⟩
  have h3 := three_le_finrank_eigN h2K hdim haa hbb hanti hl hl0
  have h3' := three_le_finrank_eigN h2K hdim haa hbb hanti (c := c) (l := -l) (by rw [neg_mul_neg]; exact hl)
    (neg_ne_zero.2 hl0)
  have hne : eigN (a : V ≃ₗ[K] V) (b : V ≃ₗ[K] V) c l ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h3
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hrc, x', hx', hx'Q, hxx'⟩ :=
    isRootCenter_quat hc h2K hE h4 ha hb ha1 hb1 hab haa hbb hanti hl hl0 h3 hx hx0
  have hx'0 : x' ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hxx'
    exact zero_ne_one hxx'
  obtain ⟨hrc', -⟩ := isRootCenter_quat hc h2K hE h4 ha hb ha1 hb1 hab haa hbb hanti
    (c := c) (μ := -l) (by rw [neg_mul_neg]; exact hl) (neg_ne_zero.2 hl0) h3' hx' hx'0
  exact top_le_of_elementaryGroup_le hc (elementaryGroup_le_of_hypPair hc.nondegenerate
    (cGenV_le_orthogonalGroup E) ⟨x, x', hrc.2.1, hx'Q, hxx'⟩ hrc hrc')

end Q8Top


section LiftSigns

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P : Type} [Group P] {π : elementaryGroup Q →* P}

theorem sign_of_mem_ker (hc : IsOrthogonalCover Q π) [Nontrivial V] {g : elementaryGroup Q}
    (hg : g ∈ π.ker) : ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ v, (g : V ≃ₗ[K] V) v = ε • v := by
  obtain ⟨c, hcv⟩ := mem_scalars.mp (hc.ker_scalar g hg)
  obtain ⟨a₀, ha₀⟩ := CFSG.RankThree.PartOne.CTP.exists_anisotropic_of_nondegenerate hc.nondegenerate
  have h1 := map_of_mem (elementaryGroup_le_orthogonalGroup Q g.2) a₀
  rw [hcv, QuadraticMap.map_smul] at h1
  have hc2 : c * c = 1 := by
    have : (c * c - 1) * Q a₀ = 0 := by linear_combination h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right ha₀)
  exact ⟨c, mul_self_eq_one_iff.1 hc2, hcv⟩

theorem exists_two_of_card_four {E : Subgroup P} (h4 : Nat.card E = 4) :
    ∃ e₁ ∈ E, ∃ e₂ ∈ E, e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ := by
  classical
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have hne : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h4
    exact absurd h4 (by norm_num)
  obtain ⟨⟨e₁, he₁⟩, he₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have he₁1' : e₁ ≠ 1 := fun h => he₁1 (Subtype.ext h)
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun x : E => decide ((x : P) = 1)) := by
    intro x y hxy
    simp only at hxy
    by_cases hx : (x : P) = 1
    · have hy : (y : P) = 1 := by simpa [hx] using hxy.symm
      exact Subtype.ext (hx.trans hy.symm)
    · have hy : (y : P) ≠ 1 := by simpa [hx] using hxy.symm
      have hx' := hcon e₁ he₁ x x.2 he₁1' hx
      have hy' := hcon e₁ he₁ y y.2 he₁1' hy
      exact Subtype.ext (hx'.symm.trans hy')
  have := Nat.card_le_card_of_injective _ hinj
  rw [h4, Nat.card_eq_fintype_card, Fintype.card_bool] at this
  omega

theorem exists_lifts (hc : IsOrthogonalCover Q π) [Nontrivial V] {E : Subgroup P}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) :
    ∃ g₁ g₂ : elementaryGroup Q, π g₁ ∈ E ∧ π g₂ ∈ E ∧ π g₁ ≠ 1 ∧ π g₂ ≠ 1 ∧ π g₁ ≠ π g₂ ∧
      ∃ ε₁ ε₂ δ : K, (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ (δ = 1 ∨ δ = -1) ∧
        (∀ v, (g₁ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v) = ε₁ • v) ∧
        (∀ v, (g₂ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) = ε₂ • v) ∧
        ∀ v, (g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) = δ • (g₂ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v) := by
  obtain ⟨e₁, he₁, e₂, he₂, he₁1, he₂1, he₁₂⟩ := exists_two_of_card_four h4
  obtain ⟨g₁, rfl⟩ := hc.surjective e₁
  obtain ⟨g₂, rfl⟩ := hc.surjective e₂
  have hsq : ∀ g : elementaryGroup Q, π g ∈ E → g * g ∈ π.ker := fun g hg => by
    rw [MonoidHom.mem_ker, map_mul, ← _root_.sq]
    exact hE.2 _ hg
  obtain ⟨ε₁, hε₁, h₁⟩ := sign_of_mem_ker hc (hsq g₁ he₁)
  obtain ⟨ε₂, hε₂, h₂⟩ := sign_of_mem_ker hc (hsq g₂ he₂)
  have hcomm : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have := congrArg Subtype.val (hE.1.is_comm.comm ⟨π g₁, he₁⟩ ⟨π g₂, he₂⟩)
    simp only [Subgroup.coe_mul] at this
    rw [this]
    group
  obtain ⟨δ, hδ, hδv⟩ := sign_of_mem_ker hc hcomm
  refine ⟨g₁, g₂, he₁, he₂, he₁1, he₂1, he₁₂, ε₁, ε₂, δ, hε₁, hε₂, hδ, fun v => ?_, fun v => ?_,
    fun v => ?_⟩
  · have := h₁ v
    simpa using this
  · have := h₂ v
    simpa using this
  · have := hδv ((g₂ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v))
    simpa [mul_assoc] using this

end LiftSigns


section Dispatch

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

omit [Finite P] in
theorem mul_ne_one_of_ne {E : Subgroup P} (hE : IsElemAbelian 2 E) {x y : P} (hy : y ∈ E)
    (hxy : x ≠ y) : x * y ≠ 1 := by
  intro h
  apply hxy
  rw [eq_inv_of_mul_eq_one_left h]
  exact inv_eq_of_mul_eq_one_right (by rw [← _root_.sq]; exact hE.2 _ hy)

theorem top_le_of_anti (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    (hdim : 7 ≤ Module.finrank K V) {E : Subgroup P} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {g₁ g₂ : elementaryGroup Q} (h₁ : π g₁ ∈ E) (h₂ : π g₂ ∈ E)
    (h₁1 : π g₁ ≠ 1) (h₂1 : π g₂ ≠ 1) (h₁₂ : π g₁ ≠ π g₂) {ε₁ ε₂ : K}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hg₁ : ∀ v, (g₁ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v) = ε₁ • v)
    (hg₂ : ∀ v, (g₂ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) = ε₂ • v)
    (hanti : ∀ v, (g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) =
      -(g₂ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v)) :
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  have hanti' : ∀ v, (g₂ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v) =
      -(g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) := fun v => by rw [hanti, neg_neg]
  have h12E : π (g₁ * g₂) ∈ E := by rw [map_mul]; exact E.mul_mem h₁ h₂
  have h121 : π (g₁ * g₂) ≠ 1 := by rw [map_mul]; exact mul_ne_one_of_ne hE h₂ h₁₂
  have hmul : ∀ v, ((g₁ * g₂ : elementaryGroup Q) : V ≃ₗ[K] V) v =
      (g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) := fun v => rfl
  rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl
  · exact top_le_of_dih hc h2K hdim hE h4 h₁ h₂ h₁1 h₂1 h₁₂ (by simpa using hg₁)
      (by simpa using hg₂) hanti
  · refine top_le_of_dih hc h2K hdim hE h4 (b := g₁ * g₂) h₁ h12E h₁1 h121 ?_ (by simpa using hg₁)
      ?_ ?_
    · rw [map_mul]
      intro h
      exact h₂1 (by simpa using h.symm)
    · intro v
      simp [hg₁, hg₂, hanti', map_neg]
    · intro v
      simp [hg₁, hanti', map_neg]
  · refine top_le_of_dih hc h2K hdim hE h4 (a := g₂) (b := g₁ * g₂) h₂ h12E h₂1 h121 ?_
      (by simpa using hg₂) ?_ ?_
    · rw [map_mul]
      intro h
      apply h₁1
      have := congrArg (· * (π g₂)⁻¹) h
      simpa using this.symm
    · intro v
      simp [hg₁, hg₂, hanti', map_neg]
    · intro v
      simp [hg₂, hanti']
  · exact top_le_of_quat hc h2K hdim hE h4 h₁ h₂ h₁1 h₂1 h₁₂ (by simpa using hg₁)
      (by simpa using hg₂) hanti

omit [Finite K] [FiniteDimensional K V] [Finite P] in
theorem commute_of_lifts (hc : IsOrthogonalCover Q π) {E : Subgroup P} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {g₁ g₂ t : elementaryGroup Q} (h₁ : π g₁ ∈ E) (h₂ : π g₂ ∈ E)
    (h₁1 : π g₁ ≠ 1) (h₂1 : π g₂ ≠ 1) (h₁₂ : π g₁ ≠ π g₂)
    (ht₁ : ∀ v, (t : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v) = (g₁ : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) v))
    (ht₂ : ∀ v, (t : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) = (g₂ : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) v)) :
    ∀ g : elementaryGroup Q, π g ∈ E → g * t = t * g := by
  intro g hg
  obtain ⟨c, h, hh, hv⟩ := lift_eq_smul hc hE h4 h₁ h₂ h₁1 h₂1 h₁₂ hg
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  change (g : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) v) = (t : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v)
  rw [hv, hv, map_smul]
  congr 1
  rcases hh with rfl | rfl | rfl | rfl
  · rfl
  · exact (ht₁ v).symm
  · exact (ht₂ v).symm
  · change (g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) v)) =
      (t : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v))
    rw [ht₁, ht₂]

omit [Finite K] [FiniteDimensional K V] [Finite P] in
theorem hasCentralInvLift_of_comm (hc : IsOrthogonalCover Q π) {E : Subgroup P}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) {g₁ g₂ : elementaryGroup Q} (h₁ : π g₁ ∈ E)
    (h₂ : π g₂ ∈ E) (h₁1 : π g₁ ≠ 1) (h₂1 : π g₂ ≠ 1) (h₁₂ : π g₁ ≠ π g₂) {ε₁ ε₂ : K}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hg₁ : ∀ v, (g₁ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v) = ε₁ • v)
    (hg₂ : ∀ v, (g₂ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) = ε₂ • v)
    (hcomm : ∀ v, (g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) = (g₂ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v)) :
    HasCentralInvLift π E := by
  have hinv : ∀ t : elementaryGroup Q, (∀ v, (t : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) v) = v) →
      t * t = 1 := fun t ht => Subtype.ext (LinearEquiv.ext fun v => ht v)
  have hmul : ∀ v, ((g₁ * g₂ : elementaryGroup Q) : V ≃ₗ[K] V) v =
      (g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) := fun v => rfl
  rcases hε₁ with rfl | rfl
  · exact ⟨g₁, h₁, h₁1, hinv g₁ (by simpa using hg₁), commute_of_lifts hc hE h4 h₁ h₂ h₁1 h₂1 h₁₂
      (fun v => rfl) hcomm⟩
  rcases hε₂ with rfl | rfl
  · exact ⟨g₂, h₂, h₂1, hinv g₂ (by simpa using hg₂), commute_of_lifts hc hE h4 h₁ h₂ h₁1 h₂1 h₁₂
      (fun v => (hcomm v).symm) (fun v => rfl)⟩
  refine ⟨g₁ * g₂, by rw [map_mul]; exact E.mul_mem h₁ h₂,
    by rw [map_mul]; exact mul_ne_one_of_ne hE h₂ h₁₂, hinv _ fun v => ?_,
    commute_of_lifts hc hE h4 h₁ h₂ h₁1 h₂1 h₁₂ (fun v => ?_) (fun v => ?_)⟩
  · rw [hmul, hmul, ← hcomm ((g₂ : V ≃ₗ[K] V) v), hg₂]
    simp [hg₁]
  · rw [hmul, hmul, hg₁, ← hcomm, hg₁]
  · rw [hmul, hmul, hcomm]

end Dispatch

end CFSG.LocalAnalysis.WeakClosure81.OSeitz
