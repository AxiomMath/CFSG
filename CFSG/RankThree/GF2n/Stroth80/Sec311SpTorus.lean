module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPoint

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]

@[expose] def hypTorusMap (F : LinearMap.BilinForm K V) (e f : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id + ((a - 1) • F.flip f).smulRight e + ((a⁻¹ - 1) • F.flip e).smulRight f

theorem hypTorusMap_apply (F : LinearMap.BilinForm K V) (e f : V) (a : K) (v : V) :
    hypTorusMap F e f a v = v + ((a - 1) * F v f) • e + ((a⁻¹ - 1) * F v e) • f := by
  simp [hypTorusMap, add_assoc]

theorem hypTorusMap_F_e (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (a : K) (y : V) : F (hypTorusMap F e f a y) e = a⁻¹ * F y e := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  simp only [hypTorusMap_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, form_self halt, hfe]
  ring

theorem hypTorusMap_F_f (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (a : K) (y : V) : F (hypTorusMap F e f a y) f = a * F y f := by
  simp only [hypTorusMap_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, form_self halt, hef]
  ring

theorem hypTorusMap_apply_e (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (a : K) : hypTorusMap F e f a e = a • e := by
  simp only [hypTorusMap_apply, hef, form_self halt, mul_one, mul_zero, zero_smul, add_zero]
  module

theorem hypTorusMap_apply_f (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (a : K) : hypTorusMap F e f a f = a⁻¹ • f := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  simp only [hypTorusMap_apply, hfe, form_self halt, mul_one, mul_zero, zero_smul, add_zero]
  module

theorem hypTorusMap_of_perp (F : LinearMap.BilinForm K V) (e f : V) (a : K) {v : V}
    (h1 : F v e = 0) (h2 : F v f = 0) : hypTorusMap F e f a v = v := by
  simp only [hypTorusMap_apply, h1, h2, mul_zero, zero_smul, add_zero]

theorem hypTorusMap_one (F : LinearMap.BilinForm K V) (e f v : V) :
    hypTorusMap F e f 1 v = v := by
  simp [hypTorusMap_apply]

theorem hypTorusMap_isIsom (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) {a : K} (ha : a * a⁻¹ = 1) (x y : V) :
    F (hypTorusMap F e f a x) (hypTorusMap F e f a y) = F x y := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  simp only [hypTorusMap_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, form_self halt, hef, hfe, form_comm halt e y, form_comm halt f y]
  linear_combination (F x e * F y f + F y e * F x f) * ha

theorem hypTorusMap_comp (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (a b : K) (v : V) :
    hypTorusMap F e f a (hypTorusMap F e f b v) = hypTorusMap F e f (a * b) v := by
  rw [hypTorusMap_apply F e f a (hypTorusMap F e f b v), hypTorusMap_F_f F halt hef b v,
    hypTorusMap_F_e F halt hef b v, hypTorusMap_apply F e f b v, hypTorusMap_apply F e f (a * b) v]
  module

theorem hypTorusMap_comp_inv (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) {a : K} (ha : a * a⁻¹ = 1) (v : V) :
    hypTorusMap F e f a (hypTorusMap F e f a⁻¹ v) = v := by
  rw [hypTorusMap_comp F halt hef, ha, hypTorusMap_one]

theorem hypTorusMap_inv_comp (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) {a : K} (ha : a⁻¹ * a = 1) (v : V) :
    hypTorusMap F e f a⁻¹ (hypTorusMap F e f a v) = v := by
  rw [hypTorusMap_comp F halt hef, ha, hypTorusMap_one]

@[expose] def hypTorusEquiv (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) {a : K} (ha : a ≠ 0) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinear (hypTorusMap F e f a) (hypTorusMap F e f a⁻¹)
    (LinearMap.ext fun v => hypTorusMap_comp_inv F halt hef (mul_inv_cancel₀ ha) v)
    (LinearMap.ext fun v => hypTorusMap_inv_comp F halt hef (inv_mul_cancel₀ ha) v)

theorem hypTorusEquiv_apply (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) {a : K} (ha : a ≠ 0) (v : V) :
    hypTorusEquiv F halt hef ha v = hypTorusMap F e f a v := rfl

@[expose] def hypSwapMap (F : LinearMap.BilinForm K V) (e f : V) : V →ₗ[K] V :=
  LinearMap.id + (F.flip e + F.flip f).smulRight (e + f)

theorem hypSwapMap_apply (F : LinearMap.BilinForm K V) (e f v : V) :
    hypSwapMap F e f v = v + (F v e + F v f) • (e + f) := by
  simp [hypSwapMap, add_assoc]

theorem hypSwapMap_F_e (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (v : V) : F (hypSwapMap F e f v) e = F v f := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  rw [hypSwapMap_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    form_self halt, hfe]
  linear_combination F v e * (two_eq_zero_K (K := K))

theorem hypSwapMap_F_f (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (v : V) : F (hypSwapMap F e f v) f = F v e := by
  rw [hypSwapMap_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    form_self halt, hef]
  linear_combination F v f * (two_eq_zero_K (K := K))

theorem hypSwapMap_invol (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (v : V) : hypSwapMap F e f (hypSwapMap F e f v) = v := by
  rw [hypSwapMap_apply F e f (hypSwapMap F e f v), hypSwapMap_F_e F halt hef v,
    hypSwapMap_F_f F halt hef v, hypSwapMap_apply F e f v]
  have h2 : (2 : K) • (e + f) = 0 := by rw [two_eq_zero_K (K := K), zero_smul]
  linear_combination (norm := module) (F v e + F v f) • h2

@[expose] def hypSwapEquiv (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) : V ≃ₗ[K] V :=
  LinearEquiv.ofInvolutive (hypSwapMap F e f) (hypSwapMap_invol F halt hef)

theorem hypSwapEquiv_apply (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (v : V) : hypSwapEquiv F halt hef v = hypSwapMap F e f v := rfl

theorem hyp_swap_torus_swap (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (b : K) (v : V) :
    hypSwapMap F e f (hypTorusMap F e f b (hypSwapMap F e f v)) = hypTorusMap F e f b⁻¹ v := by
  have hS1 := hypSwapMap_F_e F halt hef v
  have hS2 := hypSwapMap_F_f F halt hef v
  have hY1 : F (hypTorusMap F e f b (hypSwapMap F e f v)) e = b⁻¹ * F v f := by
    rw [hypTorusMap_F_e F halt hef, hS1]
  have hY2 : F (hypTorusMap F e f b (hypSwapMap F e f v)) f = b * F v e := by
    rw [hypTorusMap_F_f F halt hef, hS2]
  have h2e : (2 : K) • e = 0 := by rw [two_eq_zero_K (K := K), zero_smul]
  have h2f : (2 : K) • f = 0 := by rw [two_eq_zero_K (K := K), zero_smul]
  rw [hypSwapMap_apply F e f (hypTorusMap F e f b (hypSwapMap F e f v)), hY1, hY2,
    hypTorusMap_apply F e f b (hypSwapMap F e f v), hS1, hS2, hypSwapMap_apply F e f v,
    hypTorusMap_apply F e f b⁻¹ v, inv_inv]
  linear_combination (norm := module) (F v f + b * F v e) • h2e + (F v e + b⁻¹ * F v f) • h2f

theorem hyp_swap_torus_swap' (F : LinearMap.BilinForm K V) {e f : V} (halt : F.IsAlt)
    (hef : F e f = 1) (c : K) (v : V) :
    hypSwapMap F e f (hypTorusMap F e f c⁻¹ (hypSwapMap F e f v)) = hypTorusMap F e f c v := by
  rw [hyp_swap_torus_swap F halt hef c⁻¹ v, inv_inv]

theorem qfPolarAdd (Qf : QuadraticForm K V) (x y : V) :
    Qf (x + y) = Qf x + Qf y + Qf.polarBilin x y := by
  rw [QuadraticMap.polarBilin_apply_apply]
  exact QuadraticMap.map_add Qf x y

theorem qfSmulMul (Qf : QuadraticForm K V) (c : K) (x : V) :
    Qf (c • x) = c * c * Qf x := by
  rw [QuadraticMap.map_smul, smul_eq_mul]

theorem polarBilin_isAlt (Qf : QuadraticForm K V) :
    LinearMap.BilinForm.IsAlt Qf.polarBilin := by
  intro v
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
    charTwo_add_self]

theorem hypTorusMap_qf (Qf : QuadraticForm K V) {e f : V} (he : Qf e = 0) (hf : Qf f = 0)
    (hef : Qf.polarBilin e f = 1) {b : K} (hb : b * b⁻¹ = 1) (v : V) :
    Qf (hypTorusMap Qf.polarBilin e f b v) = Qf v := by
  simp only [hypTorusMap_apply, qfPolarAdd, qfSmulMul, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, he, hf, hef]
  linear_combination (Qf.polarBilin v e * Qf.polarBilin v f) * hb

theorem hypSwapMap_qf (Qf : QuadraticForm K V) {e f : V} (he : Qf e = 0) (hf : Qf f = 0)
    (hef : Qf.polarBilin e f = 1) (v : V) :
    Qf (hypSwapMap Qf.polarBilin e f v) = Qf v := by
  simp only [hypSwapMap_apply, qfPolarAdd, qfSmulMul, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, he, hf, hef]
  linear_combination ((Qf.polarBilin v e + Qf.polarBilin v f) *
    (Qf.polarBilin v e + Qf.polarBilin v f)) * (two_eq_zero_K (K := K))

theorem hypSwapEquiv_mem (Qf : QuadraticForm K V) {e f : V} (he : Qf e = 0) (hf : Qf f = 0)
    (hef : Qf.polarBilin e f = 1) :
    hypSwapEquiv Qf.polarBilin (polarBilin_isAlt Qf) hef ∈ orthSubgroup Qf := by
  intro v
  rw [hypSwapEquiv_apply]
  exact hypSwapMap_qf Qf he hf hef v

theorem hypTorusEquiv_mem (Qf : QuadraticForm K V) {e f : V} (he : Qf e = 0) (hf : Qf f = 0)
    (hef : Qf.polarBilin e f = 1) {b : K} (hb : b ≠ 0) :
    hypTorusEquiv Qf.polarBilin (polarBilin_isAlt Qf) hef hb ∈ orthSubgroup Qf := by
  intro v
  rw [hypTorusEquiv_apply]
  exact hypTorusMap_qf Qf he hf hef (mul_inv_cancel₀ hb) v

theorem exists_mul_self_eq_of_charTwo [Finite K] (a : K) : ∃ c : K, c * c = a := by
  have hinj : Function.Injective (fun x : K => x * x) := by
    intro x y hxy
    have hxy' : x * x = y * y := hxy
    have h0 : (x - y) * (x - y) = 0 := by
      linear_combination hxy' + (y * (y - x)) * (two_eq_zero_K (K := K))
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)
  exact Finite.surjective_of_injective hinj a

theorem commutator_of_relations {G : Type*} [Group G] (S B C A : G) (hSS : S * S = 1)
    (hBC : B * C = 1) (hSBS : S * B * S = C) (hCC : C * C = A) :
    @Bracket.bracket G G commutatorElement S B = A := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hSS,
    inv_eq_of_mul_eq_one_right hBC, hSBS, hCC]

theorem torus_fixed_free (F : LinearMap.BilinForm K V) (hnd : F.Nondegenerate)
    (halt : F.IsAlt) {e f : V} (hef : F e f = 1) {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    {g : V ≃ₗ[K] V} (hg : g ∈ pointRadSubgroup F e)
    (hc : hypTorusEquiv F halt hef ha0 * g = g * hypTorusEquiv F halt hef ha0) : g = 1 := by
  have he : e ≠ 0 := ne_zero_of_form_eq_one hef
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have hcomm : ∀ x, hypTorusMap F e f a (g x) = g (hypTorusMap F e f a x) := by
    intro x
    have h := congrArg (fun h : V ≃ₗ[K] V => h x) hc
    simpa only [LinearEquiv.mul_apply, hypTorusEquiv_apply] using h
  have hpt : ∀ y, F y e = 0 → g y = y + F (g f - f) y • e :=
    fun y hy => pointRad_apply_perp halt hef hg y hy
  have hgω : F (g f - f) e = 0 := pointRad_om_perp (f := f) hg
  have hA : ∀ v, F v e = 0 → F (g f - f) (hypTorusMap F e f a v) = a * F (g f - f) v := by
    intro v hv
    have hτv : F (hypTorusMap F e f a v) e = 0 := by
      rw [hypTorusMap_F_e F halt hef a v, hv, mul_zero]
    have h1 := hpt _ hτv
    have h2 := hpt v hv
    have h3 := hcomm v
    rw [h2, map_add, map_smul, hypTorusMap_apply_e F halt hef a, h1] at h3
    have h4 := add_left_cancel h3
    have h5 : (F (g f - f) v * a - F (g f - f) (hypTorusMap F e f a v)) • e = 0 := by
      rw [sub_smul, ← smul_smul, h4, sub_self]
    rcases smul_eq_zero.mp h5 with h6 | h6
    · rw [mul_comm]
      exact (sub_eq_zero.mp h6).symm
    · exact absurd h6 he
  have hB : ∀ w, F w e = 0 → F w f = 0 → F (g f - f) w = 0 := by
    intro w hwe hwf
    have h := hA w hwe
    rw [hypTorusMap_of_perp F e f a hwe hwf] at h
    have h2 : (a - 1) * F (g f - f) w = 0 := by linear_combination (-1 : K) * h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) ha1
    · exact h3
  have hC : ∀ v, F v e = 0 → F (g f - f) v = 0 := by
    intro v hv
    have hw_e : F (v - F v f • e) e = 0 := by
      simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hv, form_self halt]
    have hw_f : F (v - F v f • e) f = 0 := by
      simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hef]
    have hdec : v = F v f • e + (v - F v f • e) := by abel
    have key : F (g f - f) (F v f • e + (v - F v f • e)) = 0 := by
      rw [map_add, map_smul, smul_eq_mul, hgω, mul_zero, hB _ hw_e hw_f, add_zero]
    rwa [← hdec] at key
  obtain ⟨d, hd⟩ := perp_perp hnd halt e (g f - f) hC
  have hgf : g f = d • e + f := sub_eq_iff_eq_add.mp hd
  have hF : (d * a - a⁻¹ * d) • e = 0 := by
    have h := hcomm f
    rw [hgf, map_add, map_smul, hypTorusMap_apply_e F halt hef a, hypTorusMap_apply_f F halt hef a,
      map_smul, hgf, smul_add] at h
    linear_combination (norm := module) h
  have hd1 : d * a - a⁻¹ * d = 0 := (smul_eq_zero.mp hF).resolve_right he
  have hne : a - a⁻¹ ≠ 0 := by
    intro h0
    have h1 : (a - 1) * (a - 1) = 0 := by
      linear_combination a * h0 + mul_inv_cancel₀ ha0 + (1 - a) * (two_eq_zero_K (K := K))
    exact ha1 (sub_eq_zero.mp (mul_self_eq_zero.mp h1))
  have hd2 : d * (a - a⁻¹) = 0 := by linear_combination hd1
  have hd0 : d = 0 := (mul_eq_zero.mp hd2).resolve_right hne
  have hgf' : g f = f := by rw [hgf, hd0, zero_smul, zero_add]
  have hge : g e = e := (mem_pointRad_iff.mp hg).2.1
  have hgw : ∀ w, F w e = 0 → g w = w := by
    intro w hw
    rw [hpt w hw, hC w hw, zero_smul, add_zero]
  refine LinearEquiv.ext fun v => ?_
  show g v = v
  have hw : F (v - F v f • e - F v e • f) e = 0 := by
    simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, form_self halt, hfe]
  have hdec2 : v = F v f • e + F v e • f + (v - F v f • e - F v e • f) := by abel
  calc g v = g (F v f • e + F v e • f + (v - F v f • e - F v e • f)) := by rw [← hdec2]
    _ = F v f • e + F v e • f + (v - F v f • e - F v e • f) := by
        rw [map_add, map_add, map_smul, map_smul, hge, hgf', hgw _ hw]
    _ = v := by abel

theorem exists_torus_symp {F : LinearMap.BilinForm K V} (hnd : F.Nondegenerate)
    (halt : F.IsAlt) {e f : V} (hef : F e f = 1) {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ∃ τ : V ≃ₗ[K] V, IsIsom F τ ∧ τ e = a • e ∧
      ∀ g ∈ pointRadSubgroup F e, τ * g = g * τ → g = 1 := by
  refine ⟨hypTorusEquiv F halt hef ha0, fun x y => ?_, ?_, fun g hg hc =>
    torus_fixed_free F hnd halt hef ha0 ha1 hg hc⟩
  · rw [hypTorusEquiv_apply, hypTorusEquiv_apply]
    exact hypTorusMap_isIsom F halt hef (mul_inv_cancel₀ ha0) x y
  · rw [hypTorusEquiv_apply]
    exact hypTorusMap_apply_e F halt hef a

theorem exists_torus_orth [Finite K] {Qf : QuadraticForm K V} (hnd : Qf.polarBilin.Nondegenerate)
    {e f : V} (he : Qf e = 0) (hf : Qf f = 0) (hef : Qf.polarBilin e f = 1) {a : K}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ∃ τ : V ≃ₗ[K] V, τ ∈ ⁅orthSubgroup Qf, orthSubgroup Qf⁆ ∧ τ e = a • e ∧
      ∀ g ∈ pointRadSubgroup Qf.polarBilin e, τ * g = g * τ → g = 1 := by
  have halt : LinearMap.BilinForm.IsAlt Qf.polarBilin := polarBilin_isAlt Qf
  obtain ⟨c, hc⟩ := exists_mul_self_eq_of_charTwo a
  have hc0 : c ≠ 0 := by
    intro h
    apply ha0
    rw [← hc, h, zero_mul]
  have hb0 : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hSmem := hypSwapEquiv_mem Qf he hf hef
  have hBmem := hypTorusEquiv_mem Qf he hf hef hb0
  have hSS : hypSwapEquiv Qf.polarBilin halt hef * hypSwapEquiv Qf.polarBilin halt hef = 1 := by
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, hypSwapEquiv_apply]
    exact hypSwapMap_invol Qf.polarBilin halt hef v
  have hBC : hypTorusEquiv Qf.polarBilin halt hef hb0 * hypTorusEquiv Qf.polarBilin halt hef hc0 =
      1 := by
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, hypTorusEquiv_apply]
    exact hypTorusMap_inv_comp Qf.polarBilin halt hef (inv_mul_cancel₀ hc0) v
  have hSBS : hypSwapEquiv Qf.polarBilin halt hef * hypTorusEquiv Qf.polarBilin halt hef hb0 *
      hypSwapEquiv Qf.polarBilin halt hef = hypTorusEquiv Qf.polarBilin halt hef hc0 := by
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.mul_apply, hypSwapEquiv_apply, hypTorusEquiv_apply]
    exact hyp_swap_torus_swap' Qf.polarBilin halt hef c v
  have hCC : hypTorusEquiv Qf.polarBilin halt hef hc0 * hypTorusEquiv Qf.polarBilin halt hef hc0 =
      hypTorusEquiv Qf.polarBilin halt hef ha0 := by
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.mul_apply, hypTorusEquiv_apply]
    rw [hypTorusMap_comp Qf.polarBilin halt hef c c v, hc]
  have hSB := commutator_of_relations _ _ _ _ hSS hBC hSBS hCC
  refine ⟨hypTorusEquiv Qf.polarBilin halt hef ha0, ?_, ?_, fun g hg hgc =>
    torus_fixed_free Qf.polarBilin hnd halt hef ha0 ha1 hg hgc⟩
  · rw [← hSB]
    exact Subgroup.commutator_mem_commutator hSmem hBmem
  · rw [hypTorusEquiv_apply]
    exact hypTorusMap_apply_e Qf.polarBilin halt hef a

end CFSG.RankThree.GF2n.Stroth80.Classify
