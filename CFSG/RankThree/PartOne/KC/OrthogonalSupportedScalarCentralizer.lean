module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarDefs
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial

section Elementary

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def ElementaryMapsMem (Q : QuadraticForm K V) (W : Submodule K V) : Prop :=
  ∀ P : HypPair Q, P.e ∈ W → P.f ∈ W → ∀ w ∈ W ⊓ P.perp, eichler Q P.e w ∈ supportedDerived Q W

variable {Q : QuadraticForm K V} {W : Submodule K V}

theorem polarNondegOn_of_nondegenerate (h : (polarBilin (Q.comp W.subtype)).Nondegenerate) :
    PolarNondegOn Q W := by
  intro x hx hxy
  have : (⟨x, hx⟩ : W) = 0 := h.1 ⟨x, hx⟩ fun y => by
    rw [polarBilin_apply_apply, polar_comp_subtype_eq]
    exact hxy y y.2
  exact congrArg Subtype.val this

theorem exists_hypPair_of_mem (h : (polarBilin (Q.comp W.subtype)).Nondegenerate) {e : V}
    (he : e ∈ W) (hQe : Q e = 0) (he0 : e ≠ 0) : ∃ P : HypPair Q, P.e = e ∧ P.f ∈ W := by
  obtain ⟨P', hP'⟩ := exists_hypPair h (e := (⟨e, he⟩ : W)) hQe
    (fun h0 => he0 (congrArg Subtype.val h0))
  exact ⟨⟨(P'.e : V), (P'.f : V), P'.Q_e, P'.Q_f, by
    rw [← polar_comp_subtype_eq]; exact P'.polar_ef⟩, congrArg Subtype.val hP', P'.f.2⟩

theorem exists_sub_smul_mem_suppPerp [FiniteDimensional K V] (hW3 : 3 ≤ finrank K W)
    {P : HypPair Q} (he : P.e ∈ W) (hf : P.f ∈ W) {z : V}
    (hz : ∀ w ∈ W ⊓ P.perp, eichler Q P.e w z = z) :
    ∃ a : K, z - a • P.e ∈ suppPerp Q W := by
  obtain ⟨u0, hu0U, hu0⟩ : ∃ u0 ∈ W ⊓ P.perp, u0 ≠ 0 := by
    have h := finrank_inf_perp_add_two P he hf
    have hpos : 0 < finrank K ↥(W ⊓ P.perp) := by omega
    obtain ⟨u0, hu0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨u0, u0.2, fun h0 => hu0 (Subtype.ext h0)⟩
  have hexp : ∀ w ∈ W ⊓ P.perp,
      polar Q z P.e • w = (polar Q z w + Q w * polar Q z P.e) • P.e := by
    intro w hw
    have hw' := HypPair.mem_perp.mp hw.2
    have h1 := hz w hw
    rw [eichler_apply P.Q_e hw'.1] at h1
    have h2 : polar Q z P.e • w - (polar Q z w + Q w * polar Q z P.e) • P.e = 0 := by
      linear_combination (norm := module) h1
    exact sub_eq_zero.mp h2
  have hb0 : polar Q z P.e = 0 := by
    by_contra hb0
    have h1 := hexp u0 hu0U
    have hu0e : u0 = ((polar Q z u0 + Q u0 * polar Q z P.e) / polar Q z P.e) • P.e := by
      calc u0 = (polar Q z P.e)⁻¹ • (polar Q z P.e • u0) := by rw [inv_smul_smul₀ hb0]
        _ = _ := by rw [h1, smul_smul, div_eq_inv_mul]
    have hf0 := (HypPair.mem_perp.mp hu0U.2).2
    rw [hu0e, polar_smul_right_eq, P.polar_fe, mul_one, div_eq_zero_iff] at hf0
    rcases hf0 with h | h
    · exact hu0 (by rw [hu0e, h, zero_div, zero_smul])
    · exact hb0 h
  have hperp0 : ∀ w ∈ W ⊓ P.perp, polar Q (P.proj z) w = 0 := by
    intro w hw
    have hw' := HypPair.mem_perp.mp hw.2
    have h1 := hexp w hw
    rw [hb0, zero_smul, mul_zero, add_zero] at h1
    have h2 : polar Q z w = 0 := by
      rcases smul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h P.e_ne_zero
    have h3 := congrArg (fun y => polar Q y w) (P.eq_add_proj z)
    simp only [polar_add_left, polar_smul_left_eq, hw'.1, hw'.2, mul_zero, zero_add] at h3
    rw [← h3]
    exact h2
  have hxperp : P.proj z ∈ suppPerp Q W := by
    rw [mem_suppPerp]
    intro y hy
    have hxP := HypPair.mem_perp.mp (P.proj_mem_perp z)
    have hproj : P.proj y ∈ W ⊓ P.perp :=
      ⟨W.sub_mem (W.sub_mem hy (W.smul_mem _ he)) (W.smul_mem _ hf), P.proj_mem_perp y⟩
    have h := congrArg (fun t => polar Q t (P.proj z)) (P.eq_add_proj y)
    simp only [polar_add_left, polar_smul_left_eq, hxP.1, hxP.2, mul_zero, zero_add] at h
    rw [h, polar_comm]
    exact hperp0 _ hproj
  refine ⟨polar Q z P.f, ?_⟩
  have h := P.eq_add_proj z
  rw [hb0, zero_smul, add_zero] at h
  have h' : z - polar Q z P.f • P.e = P.proj z := by
    linear_combination (norm := module) h
  rw [h']
  exact hxperp

theorem forall_fixed_iff_mem_suppPerp [FiniteDimensional K V]
    (hWnd : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hW3 : 3 ≤ finrank K W)
    (hsing : ∃ e ∈ W, e ≠ 0 ∧ Q e = 0) (hM : ElementaryMapsMem Q W) {v : V} :
    (∀ g ∈ supportedDerived Q W, g v = v) ↔ v ∈ suppPerp Q W := by
  constructor
  · intro hv
    obtain ⟨e0, he0W, he00, hQe0⟩ := hsing
    obtain ⟨P, hPe, hPf⟩ := exists_hypPair_of_mem hWnd he0W hQe0 he00
    have he : P.e ∈ W := hPe ▸ he0W
    have hW := polarNondegOn_of_nondegenerate hWnd
    obtain ⟨a, ha⟩ := exists_sub_smul_mem_suppPerp hW3 he hPf (z := v) fun w hw =>
      hv _ (hM P he hPf w hw)
    obtain ⟨b, hb⟩ := exists_sub_smul_mem_suppPerp (P := hypPairSwap P) hW3 hPf he (z := v)
      fun w hw => hv _ (hM (hypPairSwap P) hPf he w hw)
    have hb' : v - b • P.f ∈ suppPerp Q W := hb
    have hab : a • P.e - b • P.f ∈ suppPerp Q W := by
      have h := (suppPerp Q W).sub_mem hb' ha
      have h' : v - b • P.f - (v - a • P.e) = a • P.e - b • P.f := by abel
      rwa [h'] at h
    have hab0 : a • P.e - b • P.f = 0 :=
      Submodule.disjoint_def.mp (isCompl_suppPerp hW).disjoint _
        (W.sub_mem (W.smul_mem a he) (W.smul_mem b hPf)) hab
    have ha0 : a = 0 := by
      have h := congrArg (fun t => polar Q t P.f) hab0
      simp only [polar_sub_left, polar_smul_left_eq, P.polar_ef, P.polar_ff,
        polar_zero_left] at h
      linear_combination h
    have hb0 : b = 0 := by
      have h := congrArg (fun t => polar Q t P.e) hab0
      simp only [polar_sub_left, polar_smul_left_eq, P.polar_ee, P.polar_fe,
        polar_zero_left] at h
      linear_combination -h
    rwa [ha0, zero_smul, sub_zero] at ha
  · intro hv g hg
    exact supportedDerived_apply_perp hg hv

end Elementary

section Similarity

variable {K : Type*} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {W : Submodule K V} (F : V ≃+ V) (σ : K ≃+* K)

omit [Finite K] [FiniteDimensional K V] in
theorem polar_map_semilin {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {Q₂ : QuadraticForm K V₂} (e : V ≃+ V₂) (σ : K ≃+* K) (μ : K)
    (hFQ : ∀ v, Q₂ (e v) = μ * σ (Q v)) (x y : V) :
    polar Q₂ (e x) (e y) = μ * σ (polar Q x y) := by
  simp only [QuadraticMap.polar]
  rw [← map_add e, hFQ, hFQ, hFQ, map_sub, map_sub]
  ring

theorem exists_map_eq_of_mapsTo (S : Submodule K V) (hS : ∀ x ∈ S, F x ∈ S) {y : V} (hy : y ∈ S) :
    ∃ x ∈ S, F x = y := by
  have : Finite V := Module.finite_of_finite K
  let f : S → S := fun x => ⟨F x, hS x x.2⟩
  have hinj : Function.Injective f := fun a b h =>
    Subtype.ext (F.injective (congrArg Subtype.val h))
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hinj ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

section Commuting

variable (μ : K) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
  (hcomm : ∀ g ∈ supportedDerived Q W, ∀ v, F (g v) = g (F v))

omit [Finite K] [FiniteDimensional K V] in
include hcomm in
theorem map_mem_suppPerp_of_commute
    (hfix : ∀ v, (∀ g ∈ supportedDerived Q W, g v = v) → v ∈ suppPerp Q W) {v : V}
    (hv : v ∈ suppPerp Q W) : F v ∈ suppPerp Q W :=
  hfix _ fun g hg => by rw [← hcomm g hg v, supportedDerived_apply_perp hg hv]

include hFQ in
theorem map_mem_of_map_suppPerp (hQ : (polarBilin Q).Nondegenerate)
    (hperp : ∀ v ∈ suppPerp Q W, F v ∈ suppPerp Q W) {w : V} (hw : w ∈ W) : F w ∈ W := by
  have hWW : suppPerp Q (suppPerp Q W) = W :=
    LinearMap.BilinForm.orthogonal_orthogonal hQ (QuadraticMap.isSymm_polarBilin Q).isRefl W
  rw [← hWW, mem_suppPerp]
  intro v' hv'
  obtain ⟨v₀, hv₀, rfl⟩ := exists_map_eq_of_mapsTo F (suppPerp Q W) hperp hv'
  rw [polar_map_semilin F σ μ hFQ, polar_comm Q v₀ w, mem_suppPerp.mp hv₀ w hw, map_zero,
    mul_zero]

omit [Finite K] in
include hcomm in
theorem exists_eq_smul_of_singular
    (hWnd : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hW3 : 3 ≤ finrank K W)
    (hM : ElementaryMapsMem Q W) (hFW : ∀ x ∈ W, F x ∈ W) {e : V} (he : e ∈ W) (hQe : Q e = 0)
    (he0 : e ≠ 0) : ∃ c : K, F e = c • e := by
  obtain ⟨P, rfl, hPf⟩ := exists_hypPair_of_mem hWnd he hQe he0
  have hW := polarNondegOn_of_nondegenerate hWnd
  obtain ⟨a, ha⟩ := exists_sub_smul_mem_suppPerp hW3 he hPf (z := F P.e) fun w hw => by
    have hg := hM P he hPf w hw
    rw [← hcomm _ hg, eichler_apply_self]
  refine ⟨a, ?_⟩
  have h0 : F P.e - a • P.e = 0 :=
    Submodule.disjoint_def.mp (isCompl_suppPerp hW).disjoint _
      (W.sub_mem (hFW _ he) (W.smul_mem a he)) ha
  exact sub_eq_zero.mp h0

include hcomm hFQ in
theorem scalar_restriction_of_commute (hQ : (polarBilin Q).Nondegenerate)
    (hWnd : (polarBilin (Q.comp W.subtype)).Nondegenerate) (hW3 : 3 ≤ finrank K W)
    (hsing : ∃ e ∈ W, e ≠ 0 ∧ Q e = 0) (hM : ElementaryMapsMem Q W)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) :
    (∀ c, σ c = c) ∧ ∃ c : K, c ≠ 0 ∧ ∀ w ∈ W, F w = c • w := by
  have hW := polarNondegOn_of_nondegenerate hWnd
  have hfix : ∀ v, (∀ g ∈ supportedDerived Q W, g v = v) → v ∈ suppPerp Q W := fun v =>
    (forall_fixed_iff_mem_suppPerp hWnd hW3 hsing hM).mp
  have hFperp : ∀ v ∈ suppPerp Q W, F v ∈ suppPerp Q W := fun v hv =>
    map_mem_suppPerp_of_commute F hcomm hfix hv
  have hFW : ∀ x ∈ W, F x ∈ W := fun x hx => map_mem_of_map_suppPerp F σ μ hFQ hQ hFperp hx
  have hline : ∀ e ∈ W, e ≠ 0 → Q e = 0 → ∃ c : K, F e = c • e := fun e he he0 hQe =>
    exists_eq_smul_of_singular F hcomm hWnd hW3 hM hFW he hQe he0
  obtain ⟨e0, he0W, he00, hQe0⟩ := hsing
  obtain ⟨P, hPe, hPf⟩ := exists_hypPair_of_mem hWnd he0W hQe0 he00
  have heW : P.e ∈ W := hPe ▸ he0W
  obtain ⟨a, ha⟩ := hline P.e heW P.e_ne_zero P.Q_e
  obtain ⟨b, hb⟩ := hline P.f hPf P.f_ne_zero P.Q_f
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact P.e_ne_zero (F.injective (by rw [ha, zero_smul, map_zero]))
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact P.f_ne_zero (F.injective (by rw [hb, zero_smul, map_zero]))
  have hU : ∀ u ∈ W ⊓ P.perp, F u ∈ W ⊓ P.perp := by
    intro u hu
    have hu' := HypPair.mem_perp.mp hu.2
    refine ⟨hFW u hu.1, HypPair.mem_perp.mpr ⟨?_, ?_⟩⟩
    · have h := polar_map_semilin F σ μ hFQ P.e u
      rw [ha, polar_smul_left_eq, hu'.1, map_zero, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left ha0
    · have h := polar_map_semilin F σ μ hFQ P.f u
      rw [hb, polar_smul_left_eq, hu'.2, map_zero, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hb0
  have hkey : ∀ u ∈ W ⊓ P.perp, F u = a • u ∧ σ (Q u) * b = a * Q u := by
    intro u hu
    have hu' := HypPair.mem_perp.mp hu.2
    obtain ⟨hFuW, hFuP⟩ := hU u hu
    have hFu' := HypPair.mem_perp.mp hFuP
    have huf : polar Q u P.f = 0 := by rw [polar_comm]; exact hu'.2
    have hue : polar Q u P.e = 0 := by rw [polar_comm]; exact hu'.1
    have hFuf : polar Q (F u) P.f = 0 := by rw [polar_comm]; exact hFu'.2
    have hFue : polar Q (F u) P.e = 0 := by rw [polar_comm]; exact hFu'.1
    set q := Q u with hq
    have hsW : P.e + u - q • P.f ∈ W := W.sub_mem (W.add_mem heW hu.1) (W.smul_mem _ hPf)
    have hQs : Q (P.e + u - q • P.f) = 0 := by
      rw [sub_eq_add_neg, QuadraticMap.map_add Q (P.e + u) (-(q • P.f)),
        QuadraticMap.map_add Q P.e u, QuadraticMap.map_neg, map_smul_eq_sq, P.Q_e, P.Q_f,
        polar_neg_right, polar_smul_right_eq, polar_add_left, P.polar_ef, huf, hu'.1]
      ring
    have hs0 : P.e + u - q • P.f ≠ 0 := by
      intro h
      have h1 := congrArg (fun t => polar Q t P.f) h
      simp only [polar_sub_left, polar_add_left, polar_smul_left_eq, P.polar_ef, huf,
        P.polar_ff, polar_zero_left] at h1
      norm_num at h1
    obtain ⟨l, hl⟩ := hline _ hsW hs0 hQs
    have hFs : F (P.e + u - q • P.f) = a • P.e + F u - (σ q * b) • P.f := by
      rw [map_sub, map_add, hF q P.f, hb, ha, smul_smul]
    have hE := hFs.symm.trans hl
    have h1 : a = l := by
      have h := congrArg (fun t => polar Q t P.f) hE
      simp only [polar_sub_left, polar_add_left, polar_smul_left_eq, P.polar_ef, P.polar_ff,
        hFuf, huf] at h
      linear_combination h
    have h2 : σ q * b = a * q := by
      have h := congrArg (fun t => polar Q t P.e) hE
      simp only [polar_sub_left, polar_add_left, polar_smul_left_eq, P.polar_ee, P.polar_fe,
        hFue, hue] at h
      rw [← h1] at h
      linear_combination -h
    rw [← h1, h2] at hE
    exact ⟨by linear_combination (norm := module) hE, h2⟩
  obtain ⟨u0, hu0U, hu0⟩ : ∃ u0 ∈ W ⊓ P.perp, u0 ≠ 0 := by
    have h := finrank_inf_perp_add_two P heW hPf
    have hpos : 0 < finrank K ↥(W ⊓ P.perp) := by omega
    obtain ⟨u0, hu0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨u0, u0.2, fun h0 => hu0 (Subtype.ext h0)⟩
  have hσ : ∀ c, σ c = c := by
    intro c
    have h1 := (hkey (c • u0) (Submodule.smul_mem _ c hu0U)).1
    rw [hF, (hkey u0 hu0U).1, smul_smul, smul_smul] at h1
    have h2 : (σ c * a - a * c) • u0 = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr h1
    have h3 := (smul_eq_zero.mp h2).resolve_right hu0
    exact mul_right_cancel₀ ha0 (by linear_combination h3)
  obtain ⟨u1, hu1U, hQu1⟩ : ∃ u1 ∈ W ⊓ P.perp, Q u1 ≠ 0 := by
    have hreg : PolarNondegOn Q (W ⊓ P.perp) := PolarNondegOn.inf_perp hW P heW hPf
    obtain ⟨y, hyU, hy⟩ := hreg.exists_polar_ne_zero hu0U hu0
    by_cases h0 : Q u0 = 0
    · by_cases h1 : Q y = 0
      · refine ⟨u0 + y, add_mem hu0U hyU, ?_⟩
        rw [QuadraticMap.map_add Q u0 y, h0, h1, zero_add, zero_add]
        exact hy
      · exact ⟨y, hyU, h1⟩
    · exact ⟨u0, hu0U, h0⟩
  have hba : b = a := by
    have h := (hkey u1 hu1U).2
    rw [hσ] at h
    exact mul_left_cancel₀ hQu1 (by rw [h, mul_comm])
  refine ⟨hσ, a, ha0, fun z hz => ?_⟩
  have hproj : P.proj z ∈ W ⊓ P.perp :=
    ⟨W.sub_mem (W.sub_mem hz (W.smul_mem _ heW)) (W.smul_mem _ hPf), P.proj_mem_perp z⟩
  have h := congrArg F (P.eq_add_proj z)
  rw [map_add, map_add, hF, hF, ha, hb, (hkey _ hproj).1, hba] at h
  simp only [hσ] at h
  have h2 : a • z = a • (polar Q z P.f • P.e + polar Q z P.e • P.f + P.proj z) := by
    rw [← P.eq_add_proj z]
  rw [h, h2]
  module

end Commuting

end Similarity

end CFSG.RankThree.PartOne.KCOrthogonal
