module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClDefs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {F : LinearMap.BilinForm K V}

theorem charTwo_add_self (a : K) : a + a = 0 := by
  rw [← two_mul, CharTwo.two_eq_zero, zero_mul]

theorem charTwo_neg (a : K) : -a = a := CharTwo.neg_eq a

theorem vec_add_self (K : Type) [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    (v : V) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

theorem vec_neg_eq (K : Type) [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero]
  exact vec_add_self K v

theorem vec_sub_eq_add (K : Type) [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    (v w : V) : v - w = v + w := by
  rw [sub_eq_add_neg, vec_neg_eq K]

theorem form_comm (halt : F.IsAlt) (x y : V) : F x y = F y x := by
  have := halt.neg_eq x y
  rw [charTwo_neg] at this
  exact this

theorem form_self (halt : F.IsAlt) (x : V) : F x x = 0 := halt.self_eq_zero x

theorem two_eq_zero_K : (2 : K) = 0 := CharTwo.two_eq_zero

theorem mem_pointRad_iff {e : V} {g : V ≃ₗ[K] V} :
    g ∈ pointRadSubgroup F e ↔
      IsIsom F g ∧ g e = e ∧ ∀ v, F v e = 0 → ∃ c : K, g v = v + c • e := Iff.rfl

theorem pointRad_om_perp {e f : V} {g : V ≃ₗ[K] V} (hg : g ∈ pointRadSubgroup F e) :
    F (g f - f) e = 0 := by
  obtain ⟨h1, h2, -⟩ := hg
  have := h1 f e
  rw [h2] at this
  simp only [map_sub, LinearMap.sub_apply]
  rw [this, sub_self]

theorem pointRad_apply_perp (halt : F.IsAlt) {e f : V} (hef : F e f = 1) {g : V ≃ₗ[K] V}
    (hg : g ∈ pointRadSubgroup F e) (y : V) (hy : F y e = 0) :
    g y = y + F (g f - f) y • e := by
  obtain ⟨h1, h2, h3⟩ := hg
  obtain ⟨c, hc⟩ := h3 y hy
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have key : F (g f) (g y) = F f y := h1 f y
  have e1 : F (g f) e = 1 := by
    have := h1 f e
    rw [h2, hfe] at this
    exact this
  have e2 : F (g f) y + c = F f y := by
    have := key
    rw [hc, map_add, map_smul, e1, smul_eq_mul, mul_one] at this
    exact this
  have e3 : F (g f - f) y = c := by
    simp only [map_sub, LinearMap.sub_apply]
    linear_combination e2 - c * (two_eq_zero_K (K := K))
  rw [hc, e3]

theorem pointRad_ext (halt : F.IsAlt) {e f : V} (hef : F e f = 1) {g g' : V ≃ₗ[K] V}
    (hg : g ∈ pointRadSubgroup F e) (hg' : g' ∈ pointRadSubgroup F e) (h : g f = g' f) :
    g = g' := by
  ext v
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have hy : F (v - F v e • f) e = 0 := by
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hfe, smul_eq_mul,
      mul_one, sub_self]
  have hv : v = F v e • f + (v - F v e • f) := by abel
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  rw [map_add, map_add, map_smul, map_smul, h, pointRad_apply_perp halt hef hg _ hy,
    pointRad_apply_perp halt hef hg' _ hy, h]

theorem pointRad_om_mul (halt : F.IsAlt) {e f : V} (hef : F e f = 1) {g g' : V ≃ₗ[K] V}
    (hg : g ∈ pointRadSubgroup F e) (hg' : g' ∈ pointRadSubgroup F e) :
    (g * g') f - f = (g f - f) + (g' f - f) + F (g f - f) (g' f - f) • e := by
  have h1 := pointRad_apply_perp halt hef hg (g' f - f) (pointRad_om_perp hg')
  have h2 : g' f = f + (g' f - f) := by abel
  simp only [LinearEquiv.mul_apply]
  conv_lhs => rw [h2, map_add, h1]
  abel

theorem pointRad_mul_self (halt : F.IsAlt) {e f : V} (hef : F e f = 1) {g : V ≃ₗ[K] V}
    (hg : g ∈ pointRadSubgroup F e) : g * g = 1 := by
  apply pointRad_ext halt hef ((pointRadSubgroup F e).mul_mem hg hg) (pointRadSubgroup F e).one_mem
  have := pointRad_om_mul halt hef hg hg
  rw [form_self halt, zero_smul, add_zero, vec_add_self K] at this
  rw [sub_eq_zero] at this
  rw [this]
  rfl

@[expose] def elationMap (F : LinearMap.BilinForm K V) (e f ω : V) : V →ₗ[K] V :=
  LinearMap.id + (F.flip e).smulRight ω + (F.flip ω + (F f ω) • F.flip e).smulRight e

theorem elationMap_apply (F : LinearMap.BilinForm K V) (e f ω v : V) :
    elationMap F e f ω v = v + F v e • ω + (F v ω + F f ω * F v e) • e := by
  simp [elationMap, add_assoc]

theorem elationMap_involutive (halt : F.IsAlt) {e f ω : V} (hω : F ω e = 0) :
    Function.Involutive (elationMap F e f ω) := by
  intro v
  have hωe' : F e ω = 0 := by rw [form_comm halt]; exact hω
  have h1 : F (elationMap F e f ω v) e = F v e := by
    rw [elationMap_apply]
    simp [map_add, map_smul, hω, form_self halt]
  have h2 : F (elationMap F e f ω v) ω = F v ω := by
    rw [elationMap_apply]
    simp [map_add, map_smul, hωe', form_self halt]
  rw [elationMap_apply F e f ω (elationMap F e f ω v), h1, h2, elationMap_apply F e f ω v]
  have a1 : F v e • ω + F v e • ω = 0 := vec_add_self K _
  have a2 : (F v ω + F f ω * F v e) • e + (F v ω + F f ω * F v e) • e = 0 := vec_add_self K _
  calc _ = v + (F v e • ω + F v e • ω) +
        ((F v ω + F f ω * F v e) • e + (F v ω + F f ω * F v e) • e) := by abel
    _ = v := by rw [a1, a2, add_zero, add_zero]

@[expose] def elationEquiv (halt : F.IsAlt) (e f ω : V) (hω : F ω e = 0) : V ≃ₗ[K] V :=
  LinearEquiv.ofInvolutive (elationMap F e f ω) (elationMap_involutive halt hω)

theorem elationEquiv_apply (halt : F.IsAlt) (e f ω : V) (hω : F ω e = 0) (v : V) :
    elationEquiv halt e f ω hω v = v + F v e • ω + (F v ω + F f ω * F v e) • e :=
  elationMap_apply F e f ω v

theorem elationEquiv_f (halt : F.IsAlt) {e f ω : V} (hef : F e f = 1) (hω : F ω e = 0) :
    elationEquiv halt e f ω hω f = f + ω := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  rw [elationEquiv_apply, hfe, one_smul, mul_one, charTwo_add_self, zero_smul, add_zero]

theorem elationEquiv_mem (halt : F.IsAlt) {e f ω : V} (hef : F e f = 1) (hω : F ω e = 0) :
    elationEquiv halt e f ω hω ∈ pointRadSubgroup F e := by
  have hωe' : F e ω = 0 := by rw [form_comm halt]; exact hω
  refine ⟨fun x y => ?_, ?_, fun y hy => ⟨F y ω, ?_⟩⟩
  · rw [elationEquiv_apply, elationEquiv_apply]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      form_self halt, hω, hωe']
    rw [form_comm halt ω y, form_comm halt e y]
    linear_combination (F y e * F x ω + F x e * F y ω + F f ω * F x e * F y e) *
      (two_eq_zero_K (K := K))
  · rw [elationEquiv_apply]
    simp [form_self halt, hωe']
  · rw [elationEquiv_apply, hy]
    simp

theorem exists_smul_of_ker_le (φ ψ : V →ₗ[K] K) (h : ∀ v, φ v = 0 → ψ v = 0) :
    ∃ c : K, ∀ v, ψ v = c * φ v := by
  have h1 : ⨅ _i : Unit, LinearMap.ker φ ≤ LinearMap.ker ψ := by
    simp only [ciInf_const]
    intro v hv
    exact h v hv
  have h2 := mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => φ) (K := ψ) h1
  rw [Set.range_const, Submodule.mem_span_singleton] at h2
  obtain ⟨c, hc⟩ := h2
  exact ⟨c, fun v => by rw [← hc]; simp⟩

theorem perp_perp (hnd : F.Nondegenerate) (halt : F.IsAlt) (e u : V)
    (h : ∀ v, F v e = 0 → F u v = 0) : ∃ c : K, u = c • e := by
  obtain ⟨c, hc⟩ := exists_smul_of_ker_le (F.flip e) (F u) (fun v hv => h v hv)
  refine ⟨c, ?_⟩
  have : u - c • e = 0 := by
    apply hnd.1
    intro v
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h5 : (F.flip e) v = F v e := rfl
    rw [hc v, h5, form_comm halt e v]
    ring
  exact sub_eq_zero.mp this

theorem ne_zero_of_form_eq_one {e f : V} (hef : F e f = 1) : e ≠ 0 := by
  rintro rfl
  simp at hef

theorem ElationFull.om (hnd : F.Nondegenerate) (halt : F.IsAlt) {e f : V} (hef : F e f = 1)
    {D : Set (V ≃ₗ[K] V)} (hD : D ⊆ pointRad F e) (h : ElationFull F D e) {ω : V}
    (hω : F ω e = 0) : ∃ g ∈ D, ∃ c : K, g f - f = ω + c • e := by
  have he : e ≠ 0 := ne_zero_of_form_eq_one hef
  obtain ⟨g, hgD, hg⟩ := h (F ω) hω
  have hgp : g ∈ pointRadSubgroup F e := hD hgD
  have hperp : ∀ v, F v e = 0 → F (ω - (g f - f)) v = 0 := by
    intro v hv
    have h1 := hg v hv
    have h2 := pointRad_apply_perp halt hef hgp v hv
    rw [h2] at h1
    have h3 : (F ω v - F (g f - f) v) • e = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr (add_left_cancel h1).symm
    rcases smul_eq_zero.mp h3 with h4 | h4
    · rw [map_sub, LinearMap.sub_apply]
      exact h4
    · exact absurd h4 he
  obtain ⟨c, hc⟩ := perp_perp hnd halt e _ hperp
  refine ⟨g, hgD, -c, ?_⟩
  rw [neg_smul, ← sub_eq_add_neg, ← hc]
  abel

section Dim

variable [Finite K] [FiniteDimensional K V]

theorem exists_perp_not_mem_span (hdim : 3 ≤ Module.finrank K V) {e : V} (hne : e ≠ 0) :
    ∃ ω : V, F ω e = 0 ∧ ∀ c : K, ω ≠ c • e := by
  by_contra hcon
  push Not at hcon
  have hle : LinearMap.ker (F.flip e) ≤ Submodule.span K {e} := by
    intro ω hω
    obtain ⟨c, hc⟩ := hcon ω hω
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank K (Submodule.span K {e}) = 1 := finrank_span_singleton hne
  have h3 := LinearMap.finrank_range_add_finrank_ker (F.flip e)
  have h4 : Module.finrank K (LinearMap.range (F.flip e)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (F.flip e))
    simpa using this
  omega

theorem exists_perp_ne_zero (hdim : 3 ≤ Module.finrank K V) (e f : V) :
    ∃ w : V, w ≠ 0 ∧ F w e = 0 ∧ F w f = 0 := by
  let ψ : V →ₗ[K] K × K := (F.flip e).prod (F.flip f)
  have h3 := LinearMap.finrank_range_add_finrank_ker ψ
  have h4 : Module.finrank K (LinearMap.range ψ) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range ψ)
    rwa [Module.finrank_prod, Module.finrank_self] at this
  have h5 : 1 ≤ Module.finrank K (LinearMap.ker ψ) := by omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp h5)
  refine ⟨w, hw0, ?_, ?_⟩
  · exact congrArg Prod.fst hw
  · exact congrArg Prod.snd hw

end Dim

theorem eq_zero_of_perp_span (hnd : F.Nondegenerate) {P : Set V} (hspan : Submodule.span K P = ⊤)
    {u : V} (h : ∀ e ∈ P, F u e = 0) : u = 0 := by
  apply hnd.1
  intro y
  have hy : y ∈ Submodule.span K P := by rw [hspan]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

theorem exists_partner (hnd : F.Nondegenerate) (halt : F.IsAlt) {e f : V} (hef : F e f = 1)
    {w : V} (hwe : F w e = 0) (hwf : F w f = 0) (hw : w ≠ 0) :
    ∃ w' : V, F w' e = 0 ∧ F w' f = 0 ∧ F w w' = 1 := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have : ∃ z, F w z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (hnd.1 w hcon)
  obtain ⟨z, hz⟩ := this
  set u : V := z + F z f • e + F z e • f with hu
  have hue : F u e = 0 := by
    simp only [hu, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      form_self halt, hfe]
    linear_combination (F z e) * (two_eq_zero_K (K := K))
  have huf : F u f = 0 := by
    simp only [hu, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      form_self halt, hef]
    linear_combination (F z f) * (two_eq_zero_K (K := K))
  have hwu : F w u = F w z := by
    simp only [hu, map_add, map_smul, smul_eq_mul, hwe, hwf]
    ring
  refine ⟨(F w z)⁻¹ • u, ?_, ?_, ?_⟩
  · rw [map_smul, LinearMap.smul_apply, hue, smul_zero]
  · rw [map_smul, LinearMap.smul_apply, huf, smul_zero]
  · rw [map_smul, hwu, smul_eq_mul, inv_mul_cancel₀ hz]

theorem mem_pointRad_iff' {e : V} {g : V ≃ₗ[K] V} :
    g ∈ pointRad F e ↔ g ∈ pointRadSubgroup F e := Iff.rfl

theorem pointRadSubgroup_le_symp (e : V) : pointRadSubgroup F e ≤ sympSubgroup F :=
  fun _ hg => hg.1

theorem conj_mem_pointRad {e : V} {g h : V ≃ₗ[K] V} (hg : g ∈ sympSubgroup F)
    (hh : h ∈ pointRadSubgroup F e) : g * h * g⁻¹ ∈ pointRadSubgroup F (g e) := by
  have hh' := hh
  obtain ⟨h1, h2, h3⟩ := hh'
  have hg' : IsIsom F g := hg
  refine ⟨?_, ?_, ?_⟩
  · exact (sympSubgroup F).mul_mem ((sympSubgroup F).mul_mem hg (pointRadSubgroup_le_symp e hh))
      ((sympSubgroup F).inv_mem hg)
  · simp [LinearEquiv.mul_apply, h2]
  · intro v hv
    have hv' : F (g⁻¹ v) e = 0 := by
      have := hg' (g⁻¹ v) e
      rw [show g (g⁻¹ v) = v by simp] at this
      rw [← this]
      exact hv
    obtain ⟨c, hc⟩ := h3 (g⁻¹ v) hv'
    refine ⟨c, ?_⟩
    simp only [LinearEquiv.mul_apply]
    rw [hc, map_add, map_smul]
    simp

theorem elationFull_conj {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ sympSubgroup F) {e : V}
    (hfull : ElationFull F ((H : Set _) ∩ pointRad F e) e) {g : V ≃ₗ[K] V} (hg : g ∈ H) :
    ElationFull F ((H : Set _) ∩ pointRad F (g e)) (g e) := by
  intro φ hφ
  obtain ⟨h, ⟨hhH, hhP⟩, hh⟩ := hfull (φ.comp (g : V →ₗ[K] V)) (by simpa using hφ)
  refine ⟨g * h * g⁻¹, ⟨H.mul_mem (H.mul_mem hg hhH) (H.inv_mem hg),
    conj_mem_pointRad (hH hg) hhP⟩, ?_⟩
  intro w hw
  have hg' : IsIsom F g := hH hg
  have hw' : F (g⁻¹ w) e = 0 := by
    have := hg' (g⁻¹ w) e
    rw [show g (g⁻¹ w) = w by simp] at this
    rw [← this]
    exact hw
  have := hh (g⁻¹ w) hw'
  simp only [LinearEquiv.mul_apply]
  rw [this, map_add, map_smul]
  simp

end CFSG.RankThree.GF2n.Stroth80.Classify
