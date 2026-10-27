module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthIso
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.StandardType.ZS

open QuadraticMap

noncomputable def owCr_coeff {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a : U) : U →ₗ[K] K :=
  (Q a)⁻¹ • (polarBilin Q).flip a

@[simp]
theorem owCr_coeff_apply {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a v : U) :
    owCr_coeff Q a v = (polarBilin Q v a) / Q a := by
  simp [owCr_coeff, div_eq_inv_mul]

noncomputable def owCr_orthRefl {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a : U) (ha : Q a ≠ 0) : U ≃ₗ[K] U :=
  LinearEquiv.ofInvolutive
    (LinearMap.id - (owCr_coeff Q a).smulRight a)
    (by
      intro v
      have hαa : owCr_coeff Q a a = 2 := by
        rw [owCr_coeff_apply, show polarBilin Q a a = 2 * Q a by
          rw [polarBilin_apply_apply, polar_self, two_smul]; ring]
        field_simp
      have hα : owCr_coeff Q a (v - owCr_coeff Q a v • a) = -owCr_coeff Q a v := by
        rw [map_sub, map_smul, hαa, smul_eq_mul]
        ring
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, hα]
      module)

@[simp]
theorem owCr_orthRefl_apply {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a : U) (ha : Q a ≠ 0) (v : U) :
    owCr_orthRefl Q a ha v = v - ((polarBilin Q v a) / Q a) • a := by
  change v - (owCr_coeff Q a v) • a = v - ((polarBilin Q v a) / Q a) • a
  rw [owCr_coeff_apply]

theorem owCr_orthRefl_self {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a : U) (ha : Q a ≠ 0) :
    owCr_orthRefl Q a ha a = -a := by
  rw [owCr_orthRefl_apply]
  rw [show polarBilin Q a a = 2 * Q a by
    rw [polarBilin_apply_apply, polar_self, two_smul]; ring]
  rw [mul_div_cancel_right₀ _ ha]
  module

theorem owCr_orthRefl_isIsom {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a : U) (ha : Q a ≠ 0) (v : U) :
    Q (owCr_orthRefl Q a ha v) = Q v := by
  rw [owCr_orthRefl_apply]
  set t : K := polarBilin Q v a / Q a with ht
  have ht' : t * Q a = polarBilin Q v a := by
    rw [ht, div_mul_cancel₀ _ ha]
  have hmain : Q (v - t • a) = Q v + t ^ 2 * Q a - t * polarBilin Q v a := by
    rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, QuadraticMap.map_smul,
      polar_smul_right, polarBilin_apply_apply]
    ring
  rw [hmain, ← ht']
  ring

theorem owCr_orthRefl_neg {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a : U) (ha : Q a ≠ 0) (h : Q (-a) ≠ 0) :
    owCr_orthRefl Q (-a) h = owCr_orthRefl Q a ha := by
  ext v
  rw [owCr_orthRefl_apply, owCr_orthRefl_apply, QuadraticMap.map_neg, polarBilin_apply_apply,
    polar_neg_right]
  simp only [polarBilin_apply_apply]
  module

theorem owCr_polarBilin_isom {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (g : U ≃ₗ[K] U) (hg : ∀ v, Q (g v) = Q v)
    (x y : U) : polarBilin Q (g x) (g y) = polarBilin Q x y := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar, ← map_add g, hg, hg, hg]

theorem owCr_orthRefl_conj {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (g : U ≃ₗ[K] U) (hg : ∀ v, Q (g v) = Q v)
    (a : U) (ha : Q a ≠ 0) (hga : Q (g a) ≠ 0) :
    g * owCr_orthRefl Q a ha * g⁻¹ = owCr_orthRefl Q (g a) hga := by
  ext v
  change g (owCr_orthRefl Q a ha (g.symm v)) = owCr_orthRefl Q (g a) hga v
  rw [owCr_orthRefl_apply, owCr_orthRefl_apply]
  simp only [map_sub, map_smul, LinearEquiv.apply_symm_apply]
  rw [← owCr_polarBilin_isom Q g hg (g.symm v) a, LinearEquiv.apply_symm_apply, hg a]

theorem owCr_smul_right_inj {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] {a : U} (ha : a ≠ 0) {c d : K} (h : c • a = d • a) : c = d := by
  have hzero : (c - d) • a = 0 := by rw [sub_smul, h, sub_self]
  rcases (smul_eq_zero.mp hzero) with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' ha

theorem owCr_factor_span_singleton {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] {f : U →ₗ[K] U} {a : U} (ha : a ≠ 0)
    (hf : f.range ≤ K ∙ a) : ∃ α : U →ₗ[K] K, ∀ v, f v = α v • a := by
  have hmem : ∀ v : U, ∃ c : K, c • a = f v := fun v =>
    (Submodule.le_span_singleton_iff.mp hf) (f v) (LinearMap.mem_range_self f v)
  refine ⟨{ toFun := fun v => Classical.choose (hmem v)
            map_add' := ?_
            map_smul' := ?_ }, fun v => (Classical.choose_spec (hmem v)).symm⟩
  · intro v w
    refine owCr_smul_right_inj ha ?_
    rw [add_smul]
    calc Classical.choose (hmem (v + w)) • a = f (v + w) := Classical.choose_spec (hmem (v + w))
      _ = f v + f w := map_add f v w
      _ = Classical.choose (hmem v) • a + Classical.choose (hmem w) • a := by
            rw [Classical.choose_spec (hmem v), Classical.choose_spec (hmem w)]
  · intro c v
    refine owCr_smul_right_inj ha ?_
    rw [smul_assoc]
    calc Classical.choose (hmem (c • v)) • a = f (c • v) := Classical.choose_spec (hmem (c • v))
      _ = c • f v := map_smul f c v
      _ = c • (Classical.choose (hmem v) • a) := by rw [Classical.choose_spec (hmem v)]

theorem owCr_refl_form {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (hQ : (polarBilin Q).Nondegenerate)
    (h2 : (2 : K) ≠ 0) {r : U ≃ₗ[K] U} (hr2 : r * r = 1)
    (hrk : Module.finrank K (LinearMap.range ((r : U →ₗ[K] U) - LinearMap.id)) = 1)
    (hisom : ∀ v, Q (r v) = Q v) :
    ∃ (a : U) (ha : Q a ≠ 0), r = owCr_orthRefl Q a ha := by
  let f : U →ₗ[K] U := (r : U →ₗ[K] U) - LinearMap.id
  have hf_apply : ∀ v, f v = r v - v := fun v => rfl
  have hrr : ∀ y, r (r y) = y := by
    intro y
    have h := LinearEquiv.mul_apply r r y
    rw [hr2] at h
    exact h.symm
  have hrk' : Module.finrank K f.range = 1 := hrk
  have hne : f.range ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hrk'
    exact Nat.zero_ne_one hrk'
  obtain ⟨a, ha_mem, ha_ne⟩ := Submodule.ne_bot_iff f.range |>.mp hne
  have hspan : f.range = K ∙ a := eq_span_singleton_of_mem_of_finrank_eq_one hrk' ha_mem ha_ne
  obtain ⟨α, hα⟩ := owCr_factor_span_singleton ha_ne (le_of_eq hspan)
  have hra : r a = -a := by
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp ha_mem
    have hay : a = r y - y := by rw [← hy, hf_apply]
    rw [hay, map_sub, hrr y]
    module
  have hαa : α a = -2 := by
    have hfa : f a = (-2 : K) • a := by rw [hf_apply, hra]; module
    refine owCr_smul_right_inj ha_ne ?_
    rw [← hα a, hfa]
  have hrel : ∀ v, α v * (α v * Q a + polarBilin Q v a) = 0 := by
    intro v
    have hrveq : r v = v + α v • a := by rw [← hα v, hf_apply]; module
    have hexp : Q (v + α v • a) = Q v + α v * (α v * Q a + polarBilin Q v a) := by
      rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polarBilin_apply_apply,
        polar_smul_right, smul_eq_mul]
      ring
    have hv := hisom v
    rw [hrveq, hexp] at hv
    have hv' : Q v + α v * (α v * Q a + polarBilin Q v a) = Q v + 0 := by simpa using hv
    exact add_left_cancel hv'
  have hQa : Q a ≠ 0 := by
    by_contra hQa0
    have hBa : ∀ v, polarBilin Q v a = 0 := by
      intro v
      have hsum : polarBilin Q (v + a) a = polarBilin Q v a := by
        rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_add_left, polar_self, hQa0,
          smul_zero, add_zero]
      by_cases hv : α v = 0
      · have hv' : α (v + a) ≠ 0 := by
          rw [map_add, hαa, hv, zero_add]
          exact neg_ne_zero.mpr h2
        have h2' := hrel (v + a)
        rw [hQa0, mul_zero, zero_add] at h2'
        have hB2 : polarBilin Q (v + a) a = 0 := by
          have := (mul_eq_zero.mp h2').resolve_left hv'
          simpa using this
        rwa [← hsum]
      · have h2' := hrel v
        rw [hQa0] at h2'
        simp only [mul_zero, add_zero] at h2'
        have hBv : polarBilin Q v a = 0 := by
          have := (mul_eq_zero.mp h2').resolve_left hv
          simpa using this
        exact hBv
    exact ha_ne (hQ.2 a hBa)
  have hαv : ∀ v, α v = -polarBilin Q v a / Q a := by
    intro v
    by_cases hv : α v = 0
    · have hBva : polarBilin Q v a = 0 := by
        have hαva : α (v + a) = -2 := by rw [map_add, hαa, hv, zero_add]
        have hsum : polarBilin Q (v + a) a = polarBilin Q v a + 2 * Q a := by
          rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_add_left, polar_self,
            two_smul]
          ring
        have h2' := hrel (v + a)
        rw [hαva] at h2'
        rcases mul_eq_zero.mp h2' with h | h
        · exact absurd h (neg_ne_zero.mpr h2)
        · rw [hsum] at h
          ring_nf at h
          exact h
      rw [hv, hBva]
      ring
    · have h2' := hrel v
      have h3 : α v * Q a + polarBilin Q v a = 0 := (mul_eq_zero.mp h2').resolve_left hv
      have h4 : α v * Q a = -polarBilin Q v a := by
        have := congrArg (fun t : K => t - polarBilin Q v a) h3
        simpa using this
      have h5 : α v * Q a / Q a = -polarBilin Q v a / Q a := by rw [h4]
      rwa [mul_div_cancel_right₀ _ hQa] at h5
  refine ⟨a, hQa, ?_⟩
  ext v
  rw [owCr_orthRefl_apply]
  have hrveq : r v = v + α v • a := by rw [← hα v, hf_apply]; module
  rw [hrveq, hαv v]
  module

theorem owCr_restrict_nondegenerate {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) [Module.Finite K U]
    (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0) (a : U) (ha : Q a ≠ 0) :
    (polarBilin (Q.comp (LinearMap.BilinForm.orthogonal (polarBilin Q) (K ∙ a)).subtype)).Nondegenerate := by
  have hBaa : polarBilin Q a a ≠ 0 := by
    rw [polarBilin_apply_apply, polar_self, two_smul]
    intro h
    exact (mul_ne_zero h2 ha) (by rw [two_mul]; exact h)
  have hrefl : (polarBilin Q).IsRefl := fun x y h => by
    rw [polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply]
    exact h
  have h := LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton (polarBilin Q) hQ hrefl hBaa
  convert h using 1
  rw [QuadraticMap.polarBilin_comp]
  rfl

theorem owCr_exists_isotropic_orth {K : Type*} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]
    (Q : QuadraticForm K U) (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Module.finrank K U) (a : U) (ha : Q a ≠ 0) :
    ∃ u : U, u ≠ 0 ∧ Q u = 0 ∧ polarBilin Q u a = 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  have h2 : (2 : K) ≠ 0 := CFSG.RankThree.Classical.two_ne_zero_of_card_odd hK'
  let V : Submodule K U := LinearMap.BilinForm.orthogonal (polarBilin Q) (K ∙ a)
  have hVker : V = LinearMap.ker ((polarBilin Q).flip a) := by
    ext x
    rw [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker, LinearMap.flip_apply]
    simp only [polarBilin_apply_apply]
    constructor
    · intro hx
      rw [polar_comm]
      exact hx a (Submodule.mem_span_singleton_self a)
    · intro hx n hn
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hn
      rw [polar_smul_left, polar_comm, hx, smul_zero]
  have hVdim : Module.finrank K V = Module.finrank K U - 1 := by
    rw [hVker]
    have hφa : ((polarBilin Q).flip a) a ≠ 0 := by
      rw [LinearMap.flip_apply, polarBilin_apply_apply, polar_self, two_smul]
      intro h
      exact (mul_ne_zero h2 ha) (by rw [two_mul]; exact h)
    have hφne : ((polarBilin Q).flip a) ≠ 0 := fun h => hφa (by rw [h]; rfl)
    have hrange : Module.finrank K (LinearMap.range ((polarBilin Q).flip a)) = 1 := by
      have hne : LinearMap.range ((polarBilin Q).flip a) ≠ ⊥ :=
        fun h => hφne (LinearMap.range_eq_bot.mp h)
      have h1 : 1 ≤ Module.finrank K (LinearMap.range ((polarBilin Q).flip a)) :=
        (Submodule.one_le_finrank_iff).mpr hne
      have hle : Module.finrank K (LinearMap.range ((polarBilin Q).flip a)) ≤ 1 := by
        calc Module.finrank K (LinearMap.range ((polarBilin Q).flip a))
            ≤ Module.finrank K K := Submodule.finrank_le _
          _ = 1 := Module.finrank_self K
      exact le_antisymm hle h1
    have h := LinearMap.finrank_range_add_finrank_ker ((polarBilin Q).flip a)
    omega
  have hV3 : 3 ≤ Module.finrank K V := by omega
  have hQrest := owCr_restrict_nondegenerate Q hQ h2 a ha
  obtain ⟨v, hvne, hvQ⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isotropic_of_finrank_ge_three hodd
      (Q.comp V.subtype) hQrest hV3
  refine ⟨v, ?_, ?_, ?_⟩
  · intro h
    exact hvne (Subtype.ext h)
  · simpa using hvQ
  · have hva : polarBilin Q a (v : U) = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp v.2) a (Submodule.mem_span_singleton_self a)
    simpa [polarBilin_apply_apply, polar_comm] using hva

end CFSG.StandardType.ZS

end
