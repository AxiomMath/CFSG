module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.ClassicalGroups.Orthogonal.Represents
import CFSG.LieType.Universal.SpinOmega.Reflections
import CFSG.LocalAnalysis.StandardType.ZS.Basic
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma smul_of_ker_le {φ ψ : Module.Dual (ZMod p) U}
    (h : LinearMap.ker φ ≤ LinearMap.ker ψ) {a : U} (hφa : φ a ≠ 0) :
    ψ = (ψ a / φ a) • φ := by
  ext v
  have hmem : v - (φ v / φ a) • a ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ (φ v) hφa, sub_self]
  have hv : ψ (v - (φ v / φ a) • a) = 0 := LinearMap.mem_ker.mp (h hmem)
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hv
  rw [LinearMap.smul_apply, smul_eq_mul, hv, div_eq_mul_inv, div_eq_mul_inv]
  ring

private lemma reflect_smul_of_ne_zero {Q : QuadraticForm (ZMod p) U} {μ : ZMod p} (hμ : μ ≠ 0)
    (a : U) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q (μ • a) =
      CFSG.ClassicalGroups.Orthogonal.reflect Q a :=
  CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero hμ a

private lemma zs_ker_le_polar_of_isRefl {Q : QuadraticForm (ZMod p) U} (hp : p ≠ 2)
    {t : U ≃ₗ[ZMod p] U} (htiso : IsIsom p Q t) {a : U} {φ : Module.Dual (ZMod p) U}
    (hφ : φ a = 2) (ht : t = Module.reflection hφ) :
    LinearMap.ker φ ≤ LinearMap.ker (QuadraticMap.polarBilin Q a) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr htiso
  have hta : t a = -a := by rw [ht, Module.reflection_apply_self hφ]
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have hRv : t v = v := by rw [ht, Module.reflection_apply, hv, zero_smul, sub_zero]
  have hpolar := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem htO a v
  rw [hta, hRv, QuadraticMap.polar_neg_left] at hpolar
  have h2p : (2 : ZMod p) * QuadraticMap.polar Q a v = 0 := by
    rw [two_mul]
    exact (neg_eq_iff_add_eq_zero).mp hpolar
  exact (mul_eq_zero.mp h2p).resolve_left h2

private lemma zs_exists_eq_reflect_of_isRefl [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {t : U ≃ₗ[ZMod p] U} (htrefl : IsRefl p t) (htiso : IsIsom p Q t) :
    ∃ (a : U) (φ : Module.Dual (ZMod p) U) (hφ : φ a = 2),
      Q a ≠ 0 ∧ t = Module.reflection hφ ∧
        t = CFSG.ClassicalGroups.Orthogonal.reflect Q a := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨a, φ, hφ, ht⟩ := (isRefl_iff hp t).mp htrefl
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at hφ
    exact h2 hφ.symm
  have hker := zs_ker_le_polar_of_isRefl hp htiso hφ ht
  have hφne : φ a ≠ 0 := by rw [hφ]; exact h2
  have hψne : QuadraticMap.polarBilin Q a ≠ 0 := by
    intro h0
    exact ha0 (hQ.1 a fun y => by rw [h0]; simp)
  set lam : ZMod p := QuadraticMap.polarBilin Q a a / φ a with hlam
  have hψeq : QuadraticMap.polarBilin Q a = lam • φ := by
    rw [hlam]
    exact smul_of_ker_le hker hφne
  have hlamQ : lam = Q a := by
    rw [hlam, QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hφ,
      mul_div_cancel_left₀ (Q a) h2]
  have hQa_ne : Q a ≠ 0 := by
    intro h0
    exact hψne (by rw [hψeq, hlamQ, h0, zero_smul])
  have hψx : ∀ x, QuadraticMap.polar Q a x = Q a * φ x := by
    intro x
    rw [← QuadraticMap.polarBilin_apply_apply, hψeq, hlamQ, LinearMap.smul_apply, smul_eq_mul]
  have ht_eq : t = CFSG.ClassicalGroups.Orthogonal.reflect Q a := by
    ext x
    rw [ht, Module.reflection_apply, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa_ne,
      hψx x, mul_div_cancel_left₀ (φ x) hQa_ne]
  exact ⟨a, φ, hφ, hQa_ne, ht, ht_eq⟩

private lemma zs_classRefl_of_eq_reflect [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p} (hc : c ≠ 0) {a : U} (hQa_eq : Q a = c) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a ∈ ClassRefl p Q c := by
  have hQa : Q a ≠ 0 := by rw [hQa_eq]; exact hc
  refine ⟨?_, ?_, a, hQa_eq, ?_⟩
  · rw [isRefl_iff hp]
    refine ⟨a, (Q a)⁻¹ • QuadraticMap.polarBilin Q a, ?_, ?_⟩
    · rw [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply,
        CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, smul_eq_mul,
        ← mul_assoc, mul_comm ((Q a)⁻¹) 2, mul_assoc, inv_mul_cancel₀ hQa, mul_one]
    · ext x
      rw [Module.reflection_apply, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa,
        LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, smul_eq_mul,
        div_eq_mul_inv, mul_comm]
  · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q a)
  · rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
      mul_div_cancel_right₀ (2 : ZMod p) hQa, two_smul]
    abel

theorem mem_classRefl_iff [Module.Finite (ZMod p) U] (hp : p ≠ 2) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    (t : U ≃ₗ[ZMod p] U) :
    t ∈ ClassRefl p Q c ↔ ∃ a : U, Q a = c ∧ t = CFSG.ClassicalGroups.Orthogonal.reflect Q a := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  constructor
  · rintro ⟨htrefl, htiso, a₀, hQa₀, hta₀⟩
    obtain ⟨a, φ, hφ, -, ht, ht_eq⟩ := zs_exists_eq_reflect_of_isRefl hp hQ htrefl htiso
    have hspan : a₀ ∈ Submodule.span (ZMod p) {a} := by
      rw [Submodule.mem_span_singleton]
      have htwo : (2 : ZMod p) • a₀ = φ a₀ • a := by
        have h := hta₀
        rw [ht, Module.reflection_apply] at h
        rw [two_smul]
        nth_rewrite 1 [sub_eq_iff_eq_add.mp h]
        abel
      refine ⟨(2 : ZMod p)⁻¹ * φ a₀, ?_⟩
      calc ((2 : ZMod p)⁻¹ * φ a₀) • a = (2 : ZMod p)⁻¹ • (φ a₀ • a) := by rw [smul_smul]
        _ = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • a₀) := by rw [← htwo]
        _ = a₀ := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hspan
    have ha₀_ne : a₀ ≠ 0 := fun h => hc (by rw [← hQa₀, h, QuadraticMap.map_zero])
    have hμ0 : μ ≠ 0 := fun h => ha₀_ne (by rw [h, zero_smul] at hμ; exact hμ.symm)
    exact ⟨a₀, hQa₀, by rw [ht_eq, ← reflect_smul_of_ne_zero hμ0 a, hμ]⟩
  · rintro ⟨a, hQa_eq, rfl⟩
    exact zs_classRefl_of_eq_reflect hp hc hQa_eq

theorem conj_mem_classRefl {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    {g t : U ≃ₗ[ZMod p] U} (hg : IsIsom p Q g) (ht : t ∈ ClassRefl p Q c) :
    g * t * g⁻¹ ∈ ClassRefl p Q c := by
  obtain ⟨htrefl, htiso, a, hQa, hta⟩ := ht
  refine ⟨⟨?_, ?_⟩, ?_, g a, ?_, ?_⟩
  · rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, htrefl.1]
    simp
  · have hsub : (((g * t * g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id)
        = (g : U →ₗ[ZMod p] U) ∘ₗ (((t : U →ₗ[ZMod p] U) - LinearMap.id)) ∘ₗ
            (g.symm : U →ₗ[ZMod p] U) := by
      ext v
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
        LinearEquiv.coe_coe, LinearEquiv.mul_apply, LinearEquiv.coe_inv, map_sub,
        LinearEquiv.apply_symm_apply]
    have hrange : LinearMap.range
        (((g * t * g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id)
        = Submodule.map (g : U →ₗ[ZMod p] U)
            (LinearMap.range (((t : U →ₗ[ZMod p] U) - LinearMap.id))) := by
      rw [hsub, LinearMap.range_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr (g.symm.surjective), Submodule.map_top]
    rw [hrange, LinearEquiv.finrank_map_eq g
      (LinearMap.range (((t : U →ₗ[ZMod p] U) - LinearMap.id)))]
    exact htrefl.2
  · intro v
    show Q ((g * t * g⁻¹) v) = Q v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg (t (g⁻¹ v)), htiso (g⁻¹ v)]
    have h2 : Q (g⁻¹ v) = Q v := by
      have h := hg (g⁻¹ v)
      rw [show g (g⁻¹ v) = v by simp] at h
      exact h.symm
    exact h2
  · rw [hg a, hQa]
  · show (g * t * g⁻¹) (g a) = -(g a)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, show g⁻¹ (g a) = a by simp, hta, map_neg]

theorem isIsom_of_mem_closure_classRefl {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ Subgroup.closure (ClassRefl p Q c)) : IsIsom p Q g := by
  let I : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {g | IsIsom p Q g}
      one_mem' := by intro v; simp
      mul_mem' := by
        intro a b ha hb v
        rw [LinearEquiv.mul_apply, ha (b v), hb v]
      inv_mem' := by
        intro a ha v
        have h := ha (a⁻¹ v)
        rw [show a (a⁻¹ v) = v by simp] at h
        exact h.symm }
  exact (Subgroup.closure_le I).mpr (fun t ht => ht.2.1) hg

theorem conj_mem_closure_classRefl {Q : QuadraticForm (ZMod p) U} {c : ZMod p}
    {g x : U ≃ₗ[ZMod p] U} (hg : IsIsom p Q g) (hx : x ∈ Subgroup.closure (ClassRefl p Q c)) :
    g * x * g⁻¹ ∈ Subgroup.closure (ClassRefl p Q c) := by
  induction hx using Subgroup.closure_induction with
  | mem t ht => exact Subgroup.subset_closure (conj_mem_classRefl hg ht)
  | one => simp
  | mul a b ha hb iha ihb =>
    rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
    exact mul_mem iha ihb
  | inv a ha iha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact inv_mem iha

private lemma zs_reflect_mul_apply {Q : QuadraticForm (ZMod p) U} {u w v : U}
    (hu : Q u ≠ 0) (hw : Q w ≠ 0) (huw : QuadraticMap.polar Q u w = 0) :
    (CFSG.ClassicalGroups.Orthogonal.reflect Q u *
      CFSG.ClassicalGroups.Orthogonal.reflect Q w) v =
      v - (QuadraticMap.polar Q u v / Q u) • u -
        (QuadraticMap.polar Q w v / Q w) • w := by
  rw [LinearEquiv.mul_apply, CFSG.ClassicalGroups.Orthogonal.reflect_apply hw,
    CFSG.ClassicalGroups.Orthogonal.reflect_apply hu, QuadraticMap.polar_sub_right,
    CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, huw, mul_zero, sub_zero]
  abel

private lemma zs_plane_norm {Q : QuadraticForm (ZMod p) U} {a z : U} {c d : ZMod p}
    (hz : QuadraticMap.polar Q a z = 0) (ha : Q a = d) (hzQ : Q z = d) (hd : d ≠ 0)
    {s t : ZMod p} (hst : s ^ 2 + t ^ 2 = c / d) :
    Q (s • a + t • z) = c ∧ Q (-t • a + s • z) = c := by
  have hnorm : ∀ u v : ZMod p, Q (u • a + v • z) = (u ^ 2 + v ^ 2) * d := by
    intro u v
    rw [QuadraticMap.map_add Q, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
      CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hz, ha, hzQ]
    ring
  exact ⟨by rw [hnorm, hst, div_mul_cancel₀ c hd],
    by rw [hnorm, show (-t) ^ 2 + s ^ 2 = c / d by rw [neg_sq, add_comm]; exact hst,
      div_mul_cancel₀ c hd]⟩

private lemma zs_plane_mul {Q : QuadraticForm (ZMod p) U} {a z : U} {c d : ZMod p}
    (hz : QuadraticMap.polar Q a z = 0) (ha : Q a = d) (hzQ : Q z = d) (hd : d ≠ 0)
    (hc : c ≠ 0) {s t : ZMod p} (hst : s ^ 2 + t ^ 2 = c / d)
    (hx : Q (s • a + t • z) = c) (hy : Q (-t • a + s • z) = c) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a * CFSG.ClassicalGroups.Orthogonal.reflect Q z =
      CFSG.ClassicalGroups.Orthogonal.reflect Q (s • a + t • z) *
        CFSG.ClassicalGroups.Orthogonal.reflect Q (-t • a + s • z) := by
  have ha_ne : Q a ≠ 0 := by rw [ha]; exact hd
  have hz_ne : Q z ≠ 0 := by rw [hzQ]; exact hd
  have hstd : (s ^ 2 + t ^ 2) * d = c := by rw [hst, div_mul_cancel₀ c hd]
  have hx_ne : Q (s • a + t • z) ≠ 0 := by rw [hx]; exact hc
  have hy_ne : Q (-t • a + s • z) ≠ 0 := by rw [hy]; exact hc
  have hxy : QuadraticMap.polar Q (s • a + t • z) (-t • a + s • z) = 0 := by
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq]
    rw [show QuadraticMap.polar Q z a = 0 by rw [QuadraticMap.polar_comm]; exact hz, hz,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, ha, hzQ]
    ring
  ext v
  rw [zs_reflect_mul_apply ha_ne hz_ne hz, zs_reflect_mul_apply hx_ne hy_ne hxy]
  have hpx : QuadraticMap.polar Q (s • a + t • z) v =
      s * QuadraticMap.polar Q a v + t * QuadraticMap.polar Q z v := by
    rw [QuadraticMap.polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq]
  have hpy : QuadraticMap.polar Q (-t • a + s • z) v =
      -t * QuadraticMap.polar Q a v + s * QuadraticMap.polar Q z v := by
    rw [QuadraticMap.polar_add_left, CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq]
  rw [hpx, hpy, hx, hy, ha, hzQ, sub_sub, sub_sub, sub_right_inj]
  match_scalars <;> field_simp <;> rw [← hstd] <;> ring

private lemma zs_plane {Q : QuadraticForm (ZMod p) U} {a z : U} {c d : ZMod p}
    (hz : QuadraticMap.polar Q a z = 0) (ha : Q a = d) (hzQ : Q z = d) (hd : d ≠ 0)
    (hc : c ≠ 0) {s t : ZMod p} (hst : s ^ 2 + t ^ 2 = c / d) :
    Q (s • a + t • z) = c ∧ Q (-t • a + s • z) = c ∧
      (CFSG.ClassicalGroups.Orthogonal.reflect Q a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q z =
        CFSG.ClassicalGroups.Orthogonal.reflect Q (s • a + t • z) *
          CFSG.ClassicalGroups.Orthogonal.reflect Q (-t • a + s • z)) := by
  obtain ⟨hx, hy⟩ := zs_plane_norm hz ha hzQ hd hst
  exact ⟨hx, hy, zs_plane_mul hz ha hzQ hd hc hst hx hy⟩

private lemma zs_perp_radical_le_one [Module.Finite (ZMod p) U] [DecidableEq U]
    {Q : QuadraticForm (ZMod p) U} {a b : U}
    {P W : Submodule (ZMod p) U} (hp : p ≠ 2) (ha : Q a ≠ 0)
    (hP : P = Submodule.span (ZMod p) (({a, b} : Finset U) : Set U))
    (hPle2 : Module.finrank (ZMod p) P ≤ 2)
    (hWorth : LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W = P) :
    Module.finrank (ZMod p)
      ((LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W).comap W.subtype) ≤ 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hne : W ⊓ P ≠ P := by
    intro hEq
    have haP : a ∈ P := by rw [hP]; exact Submodule.subset_span (by simp)
    have haW : a ∈ W := (hEq.symm ▸ haP : a ∈ W ⊓ P).1
    have hBaa : QuadraticMap.polarBilin Q a a = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp (hWorth ▸ haP)) a haW
    rw [QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul] at hBaa
    exact ha ((mul_eq_zero.mp hBaa).resolve_left h2)
  have hlt : Module.finrank (ZMod p) (W ⊓ P : Submodule (ZMod p) U) <
      Module.finrank (ZMod p) P :=
    Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne (inf_le_right : (W ⊓ P : Submodule (ZMod p) U) ≤ P) hne)
  have hmap : ((LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W).comap
      W.subtype).map W.subtype = W ⊓ P := by
    rw [← hWorth]
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, Submodule.mem_comap.mp hw⟩
    · rintro ⟨hxW, hxP⟩
      exact ⟨⟨x, hxW⟩, Submodule.mem_comap.mpr hxP, rfl⟩
  have hradfin : Module.finrank (ZMod p)
      ((LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W).comap W.subtype) =
      Module.finrank (ZMod p) (W ⊓ P : Submodule (ZMod p) U) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective W.subtype W.subtype_injective _).finrank_eq
  omega

private lemma zs_perp_T_nondeg {Q : QuadraticForm (ZMod p) U} {W : Submodule (ZMod p) U}
    {radW T' : Submodule (ZMod p) W} (hBsymm : (QuadraticMap.polarBilin Q).IsRefl)
    (hradW : radW = (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W).comap
      W.subtype) (hsup : radW ⊔ T' = ⊤) (hdisj : radW ⊓ T' = ⊥) :
    CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q (T'.map W.subtype) := by
  intro x hxT hall
  obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hxT
  have hx'rad : x' ∈ radW := by
    rw [hradW, Submodule.mem_comap, LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨r, hr, t, ht, hrt⟩ := Submodule.mem_sup.mp
      (hsup ▸ Submodule.mem_top : (⟨n, hn⟩ : W) ∈ radW ⊔ T')
    have hcoe : (r : U) + (t : U) = n := by simpa using congrArg (Subtype.val) hrt
    rw [hradW] at hr
    have hr0 : QuadraticMap.polarBilin Q (r : U) (x' : U) = 0 := (hBsymm.eq_iff).mpr
      ((LinearMap.BilinForm.mem_orthogonal_iff.mp (Submodule.mem_comap.mp hr)) (x' : U) x'.2)
    have ht0 : QuadraticMap.polarBilin Q (t : U) (x' : U) = 0 := by
      have htT : (t : U) ∈ T'.map W.subtype := Submodule.mem_map_of_mem (f := W.subtype) ht
      have h := hall (t : U) htT
      have h' : QuadraticMap.polarBilin Q (x' : U) (t : U) = 0 := by
        simpa only [QuadraticMap.polarBilin_apply_apply, Submodule.subtype_apply] using h
      rwa [hBsymm.eq_iff]
    rw [← hcoe, map_add, LinearMap.add_apply]
    change QuadraticMap.polarBilin Q (r : U) (x' : U) +
      QuadraticMap.polarBilin Q (t : U) (x' : U) = 0
    rw [hr0, ht0, add_zero]
  have hxinf : x' ∈ radW ⊓ T' := ⟨hx'rad, hx'⟩
  rw [hdisj, Submodule.mem_bot] at hxinf
  exact Subtype.ext_iff.mp hxinf

private theorem zs_perp_has_nondeg [Module.Finite (ZMod p) U] [DecidableEq U] (hp : p ≠ 2)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {a b : U} (ha : Q a ≠ 0) :
    ∃ (W T : Submodule (ZMod p) U), T ≤ W ∧
      W = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
        (Submodule.span (ZMod p) (({a, b} : Finset U) : Set U)) ∧
      CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q T ∧
      2 ≤ Module.finrank (ZMod p) T := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  let B := QuadraticMap.polarBilin Q
  let s : Finset U := {a, b}
  let P : Submodule (ZMod p) U := Submodule.span (ZMod p) (s : Set U)
  let W : Submodule (ZMod p) U := LinearMap.BilinForm.orthogonal B P
  have hBsymm : B.IsRefl := (QuadraticMap.isSymm_polarBilin Q).isRefl
  have hWorth : LinearMap.BilinForm.orthogonal B W = P := by
    rw [LinearMap.BilinForm.orthogonal_orthogonal hQ hBsymm]
  have hPle2 : Module.finrank (ZMod p) P ≤ 2 := by
    have h := finrank_span_finset_le_card (R := ZMod p) s
    have hcard : s.card ≤ 2 := by
      change ({a, b} : Finset U).card ≤ 2
      exact (Finset.card_insert_le a {b}).trans (by simp)
    exact h.trans hcard
  have hWfin : 3 ≤ Module.finrank (ZMod p) W := by
    have h := LinearMap.BilinForm.finrank_orthogonal hQ P
    change Module.finrank (ZMod p) W =
      Module.finrank (ZMod p) U - Module.finrank (ZMod p) P at h
    omega
  let radW : Submodule (ZMod p) W := (LinearMap.BilinForm.orthogonal B W).comap W.subtype
  obtain ⟨T', hT'⟩ := Submodule.exists_isCompl radW
  have hTnd := zs_perp_T_nondeg (Q := Q) hBsymm rfl hT'.sup_eq_top hT'.disjoint.eq_bot
  have hradle : Module.finrank (ZMod p) radW ≤ 1 := zs_perp_radical_le_one hp ha rfl hPle2 hWorth
  have hT'le : Module.finrank (ZMod p) (T'.map W.subtype) = Module.finrank (ZMod p) T' :=
    (Submodule.equivMapOfInjective W.subtype W.subtype_injective T').finrank_eq.symm
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq radW T'
  rw [hT'.sup_eq_top, hT'.disjoint.eq_bot, finrank_bot, finrank_top, add_zero] at hsum
  refine ⟨W, T'.map W.subtype, ?_, ?_, hTnd, ?_⟩
  · exact Submodule.map_le_iff_le_comap.mpr fun x _ => (x : W).2
  · change LinearMap.BilinForm.orthogonal B P = LinearMap.BilinForm.orthogonal B
      (Submodule.span (ZMod p) (({a, b} : Finset U) : Set U))
    rfl
  · omega

private theorem zs_exists_orth_norm [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {a b : U} (ha : Q a ≠ 0)
    {d : ZMod p} :
    ∃ z : U, QuadraticMap.polar Q a z = 0 ∧ QuadraticMap.polar Q b z = 0 ∧ Q z = d := by
  classical
  obtain ⟨W, T, hTW, hW, hTnd, hTfin⟩ := zs_perp_has_nondeg (b := b) hp h5 hQ ha
  obtain ⟨z, hzT, hzQ⟩ :=
    hTnd.exists_map_eq (ZMod.prime_ne_zero p 2 hp) hTfin d
  have hzW : z ∈ W := hTW hzT
  rw [hW] at hzW
  refine ⟨z, ?_, ?_, hzQ⟩
  · have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hzW) a
      (Submodule.subset_span (by simp))
    rwa [QuadraticMap.polarBilin_apply_apply] at h
  · have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hzW) b
      (Submodule.subset_span (by simp))
    rwa [QuadraticMap.polarBilin_apply_apply] at h

private lemma zs_mul_mem_closure_of_norm_c [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0) {u v : U} (hu : Q u = c) (hv : Q v = c) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q u *
      CFSG.ClassicalGroups.Orthogonal.reflect Q v ∈
      Subgroup.closure (ClassRefl p Q c) := by
  refine Subgroup.mul_mem _
    (Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).mpr ⟨u, hu, rfl⟩))
    (Subgroup.subset_closure ((mem_classRefl_iff hp hQ hc _).mpr ⟨v, hv, rfl⟩))

private theorem zs_refl_mul_mem_of_ne_zero [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) {a b : U}
    (hab : Q a = Q b) (ha : Q a ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a * CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈
      Subgroup.closure (ClassRefl p Q c) := by
  obtain ⟨z, haz, hbz, hzQ⟩ := zs_exists_orth_norm (d := Q a) hp h5 hQ ha
  obtain ⟨s, t, hst⟩ : ∃ s t : ZMod p, s ^ 2 + t ^ 2 = c / Q a := by
    obtain ⟨m, n, hmn⟩ := CharP.sq_add_sq (ZMod p) p ((c / Q a).val : ℤ)
    exact ⟨(m : ZMod p), (n : ZMod p), by
      rw [hmn, Int.cast_natCast, ZMod.natCast_zmod_val]⟩
  obtain ⟨hx, hy, heq⟩ := zs_plane haz rfl hzQ ha hc hst
  obtain ⟨hx', hy', heq'⟩ := zs_plane hbz hab.symm hzQ ha hc hst
  have h1 : CFSG.ClassicalGroups.Orthogonal.reflect Q a *
      CFSG.ClassicalGroups.Orthogonal.reflect Q z ∈
      Subgroup.closure (ClassRefl p Q c) := by
    rw [heq]
    exact zs_mul_mem_closure_of_norm_c hp hQ hc hx hy
  have h2 : CFSG.ClassicalGroups.Orthogonal.reflect Q b *
      CFSG.ClassicalGroups.Orthogonal.reflect Q z ∈
      Subgroup.closure (ClassRefl p Q c) := by
    rw [heq']
    exact zs_mul_mem_closure_of_norm_c hp hQ hc hx' hy'
  have hsplit : CFSG.ClassicalGroups.Orthogonal.reflect Q a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q b =
      (CFSG.ClassicalGroups.Orthogonal.reflect Q a *
        CFSG.ClassicalGroups.Orthogonal.reflect Q z) *
      (CFSG.ClassicalGroups.Orthogonal.reflect Q b *
        CFSG.ClassicalGroups.Orthogonal.reflect Q z)⁻¹ := by
    rw [mul_inv_rev, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
      CFSG.ClassicalGroups.Orthogonal.reflect_inv]
    rw [show (CFSG.ClassicalGroups.Orthogonal.reflect Q a *
          CFSG.ClassicalGroups.Orthogonal.reflect Q z) *
          (CFSG.ClassicalGroups.Orthogonal.reflect Q z *
            CFSG.ClassicalGroups.Orthogonal.reflect Q b) =
          CFSG.ClassicalGroups.Orthogonal.reflect Q a *
            (CFSG.ClassicalGroups.Orthogonal.reflect Q z *
              CFSG.ClassicalGroups.Orthogonal.reflect Q z) *
            CFSG.ClassicalGroups.Orthogonal.reflect Q b by group,
      CFSG.ClassicalGroups.Orthogonal.reflect_mul_self, mul_one]
  rw [hsplit]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

theorem reflect_mul_reflect_mem_closure_classRefl [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) {a b : U}
    (hab : Q a = Q b) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a * CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈
      Subgroup.closure (ClassRefl p Q c) := by
  by_cases ha0 : Q a = 0
  · have hb0 : Q b = 0 := by rw [← hab]; exact ha0
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero ha0,
      CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hb0, one_mul]
    exact Subgroup.one_mem _
  · exact zs_refl_mul_mem_of_ne_zero hp h5 hQ hc hab ha0

open scoped commutatorElement in
private lemma zs_commutator_refl_mem [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) {u v : U} :
    ⁅CFSG.ClassicalGroups.Orthogonal.reflect Q u,
      CFSG.ClassicalGroups.Orthogonal.reflect Q v⁆ ∈
      Subgroup.closure (ClassRefl p Q c) := by
  rw [commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
    CFSG.ClassicalGroups.Orthogonal.reflect_inv]
  have hconj : CFSG.ClassicalGroups.Orthogonal.reflect Q u *
      CFSG.ClassicalGroups.Orthogonal.reflect Q v * CFSG.ClassicalGroups.Orthogonal.reflect Q u =
      CFSG.ClassicalGroups.Orthogonal.reflect Q
        (CFSG.ClassicalGroups.Orthogonal.reflect Q u v) := by
    calc CFSG.ClassicalGroups.Orthogonal.reflect Q u *
          CFSG.ClassicalGroups.Orthogonal.reflect Q v *
          CFSG.ClassicalGroups.Orthogonal.reflect Q u
        = CFSG.ClassicalGroups.Orthogonal.reflect Q u *
          CFSG.ClassicalGroups.Orthogonal.reflect Q v *
          (CFSG.ClassicalGroups.Orthogonal.reflect Q u)⁻¹ := by
          rw [CFSG.ClassicalGroups.Orthogonal.reflect_inv]
      _ = CFSG.ClassicalGroups.Orthogonal.reflect Q
            (CFSG.ClassicalGroups.Orthogonal.reflect Q u v) :=
          CFSG.ClassicalGroups.Orthogonal.reflect_conj
            (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q u) v
  rw [hconj]
  refine reflect_mul_reflect_mem_closure_classRefl hp h5 hQ hc ?_
  exact CFSG.ClassicalGroups.Orthogonal.map_of_mem
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q u) v

open scoped commutatorElement in
private theorem zs_commutator_le_classRefl_closure [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      Subgroup.closure (ClassRefl p Q c) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hN : ∀ x ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ y ∈ Subgroup.closure (ClassRefl p Q c),
      x * y * x⁻¹ ∈ Subgroup.closure (ClassRefl p Q c) := fun x hx y hy =>
    conj_mem_closure_classRefl (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx) hy
  have hNO : Subgroup.closure (ClassRefl p Q c) ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun x hx =>
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (isIsom_of_mem_closure_classRefl hx)
  have hSO : Set.range (CFSG.ClassicalGroups.Orthogonal.reflect Q) ⊆
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro x ⟨v, hv⟩
    subst hv
    exact CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q v
  have hO : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (Set.range (CFSG.ClassicalGroups.Orthogonal.reflect Q) ∪
        Subgroup.closure (ClassRefl p Q c)) := fun x hx =>
    Subgroup.closure_mono Set.subset_union_left
      (CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_le_closure_reflect h2 hQ hx)
  have hS : ∀ s ∈ Set.range (CFSG.ClassicalGroups.Orthogonal.reflect Q),
      ∀ t ∈ Set.range (CFSG.ClassicalGroups.Orthogonal.reflect Q),
      ⁅s, t⁆ ∈ Subgroup.closure (ClassRefl p Q c) := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact zs_commutator_refl_mem hp h5 hQ hc
  exact CFSG.ClassicalGroups.Orthogonal.commutator_le_of_le_closure hN hNO hSO hO hS

theorem commutator_mem_closure_classRefl [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {g h : U ≃ₗ[ZMod p] U} (hg : IsIsom p Q g) (hh : IsIsom p Q h) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.closure (ClassRefl p Q c) := by
  exact zs_commutator_le_classRefl_closure hp h5 hQ hc
    (Subgroup.commutator_mem_commutator
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg)
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hh))

end CFSG.StandardType.ZS

end
