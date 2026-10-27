module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineHomology
import CFSG.LocalAnalysis.StandardType.ZS.ThroughRefl
import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction

public section

namespace CFSG.StandardType.ZS

private theorem commute_of_finrank_eq_one {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (h : Module.finrank K V = 1)
    (f g : V ≃ₗ[K] V) : f * g = g * f := by
  obtain ⟨a, ha, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h (f : V →ₗ[K] V)
  obtain ⟨b, hb, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h (g : V →ₗ[K] V)
  ext v
  simp only [LinearEquiv.mul_apply]
  have hfa : f v = a • v := by
    have h := congrArg (fun (h : V →ₗ[K] V) => h v) ha
    simpa using h
  have hgb : g v = b • v := by
    have h := congrArg (fun (h : V →ₗ[K] V) => h v) hb
    simpa using h
  calc
    (f * g) v = f (g v) := by rw [LinearEquiv.mul_apply]
    _ = f (b • v) := by rw [hgb]
    _ = b • f v := by rw [map_smul]
    _ = b • (a • v) := by rw [hfa]
    _ = (b * a) • v := by rw [smul_smul]
    _ = (a * b) • v := by rw [mul_comm]
    _ = a • (b • v) := by rw [smul_smul]
    _ = a • g v := by rw [hgb]
    _ = g (a • v) := by rw [map_smul]
    _ = g (f v) := by rw [hfa]
    _ = (g * f) v := by rw [LinearEquiv.mul_apply]

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem pow_apply_of_scalar_on_submodule
    {V : Submodule (ZMod p) U} {z : U ≃ₗ[ZMod p] U} {ζ : ZMod p}
    (hzV : ∀ v ∈ V, z v = ζ • v) :
    ∀ n : ℕ, ∀ v ∈ V, (z ^ n) v = ζ ^ n • v := by
  intro n
  induction n with
  | zero => intro v _; simp
  | succ n ih =>
      intro v hv
      rw [pow_succ', LinearEquiv.mul_apply, ih v hv]
      rw [hzV _ (Submodule.smul_mem V (ζ ^ n) hv), smul_smul, ← pow_succ']

private theorem pow_apply_of_fixed_on_submodule
    {C : Submodule (ZMod p) U} {z : U ≃ₗ[ZMod p] U}
    (hzC : ∀ c ∈ C, z c = c) :
    ∀ n : ℕ, ∀ c ∈ C, (z ^ n) c = c := by
  intro n
  induction n with
  | zero => intro c _; simp
  | succ n ih =>
      intro c hc
      rw [pow_succ', LinearEquiv.mul_apply, ih c hc, hzC c hc]

private theorem orderOf_eq_of_scalar_on_compl [Module.Finite (ZMod p) U]
    {V C : Submodule (ZMod p) U} (hV : V ⊔ C = ⊤) (hVne : V ≠ ⊥)
    {z : U ≃ₗ[ZMod p] U} {ζ : ZMod p}
    (hzV : ∀ v ∈ V, z v = ζ • v) (hzC : ∀ c ∈ C, z c = c) :
    orderOf z = orderOf ζ := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro hzn
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
    have h1 : (z ^ n) v = v := by rw [hzn]; rfl
    have h2 : (z ^ n) v = ζ ^ n • v := pow_apply_of_scalar_on_submodule hzV n v hv
    rw [h2] at h1
    have h3 : (ζ ^ n - 1) • v = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    have h4 : ζ ^ n - 1 = 0 := (smul_eq_zero.mp h3).resolve_right hv0
    exact sub_eq_zero.mp h4
  · intro hζn
    ext u
    have hu : u ∈ V ⊔ C := by rw [hV]; exact Submodule.mem_top
    obtain ⟨v, hv, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add, pow_apply_of_scalar_on_submodule hzV n v hv,
        pow_apply_of_fixed_on_submodule hzC n c hc, hζn, one_smul]
    rfl

private theorem exists_scalar_of_mem_center [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : ReflGen p X)
    (hs : SplitSupport X (Module.finrank (ZMod p) U - 1)) {z : U ≃ₗ[ZMod p] U} (hz : z ∈ X)
    (hzc : ∀ x ∈ X, z * x = x * z) (hVne : HardMathSupport.Kantor79.commutatorSpace X ≠ ⊥) :
    ∃ ζ : ZMod p, ζ ≠ 0 ∧
      ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace X, z v = ζ • v := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let hVinv : ∀ h ∈ X, ∀ v ∈ V, h v ∈ V := fun _ hh _ hv => apply_mem_commutatorSpace hh hv
  let ρ := restrictHom X V hVinv
  have hA : AbsIrred p (movedGroup X) :=
    absIrred_of_reflGen (reflGen_movedGroup hX) (irred_movedGroup_of_splitSupport hs)
  let T : Module.End (ZMod p) V := ((ρ ⟨z, hz⟩ : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V)
  have hTcomm : ∀ a ∈ movedGroup X,
      T ∘ₗ (a : V →ₗ[ZMod p] V) = (a : V →ₗ[ZMod p] V) ∘ₗ T := by
    rintro a ⟨x, rfl⟩
    have hc : ρ ⟨z, hz⟩ * ρ x = ρ x * ρ ⟨z, hz⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hzc x x.2)
    simpa only [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp] using
      congrArg (fun e : V ≃ₗ[ZMod p] V => (e : V →ₗ[ZMod p] V)) hc
  obtain ⟨ζ, hζ⟩ := hA.2 T hTcomm
  have hzV : ∀ v ∈ V, z v = ζ • v := by
    intro v hv
    have h := congrArg (fun e : V →ₗ[ZMod p] V => ((e ⟨v, hv⟩ : V) : U)) hζ
    simpa [T, ρ, restrictHom_apply] using h
  have hζ0 : ζ ≠ 0 := by
    intro hζzero
    have hzero : T = 0 := by
      rw [hζ, hζzero, zero_smul]
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
    have h1 : ((T ⟨v, hv⟩ : V) : U) = 0 := by
      have h : T ⟨v, hv⟩ = 0 := by rw [hzero]; rfl
      exact congrArg (fun e : V => (e : U)) h
    have h2 : ((T ⟨v, hv⟩ : V) : U) = z v := by simp [T, ρ, restrictHom_apply]
    rw [h2] at h1
    have h3 : v = 0 := z.injective (by rw [h1, map_zero])
    exact hv0 h3
  exact ⟨ζ, hζ0, hzV⟩

private theorem exists_compl_line [Module.Finite (ZMod p) U] {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport X (Module.finrank (ZMod p) U - 1))
    (hn : 1 ≤ Module.finrank (ZMod p) U) :
    ∃ y : U, y ≠ 0 ∧ centralizerSpace X = Submodule.span (ZMod p) {y} := by
  have hCdim : Module.finrank (ZMod p) (centralizerSpace X) = 1 := by
    have h := Submodule.finrank_add_eq_of_isCompl hs.1
    rw [hs.2.1] at h
    omega
  have hCne : centralizerSpace X ≠ ⊥ := by
    intro hbot
    have hfin : Module.finrank (ZMod p) (centralizerSpace X) = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCne
  exact ⟨y, hy0, eq_span_singleton_of_mem_of_finrank_eq_one hCdim hy hy0⟩

private theorem exists_isHomologyWith_of_rank_le_one [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport X (Module.finrank (ZMod p) U - 1))
    (hn : Module.finrank (ZMod p) U ≤ 1) {z : U ≃ₗ[ZMod p] U} (hz : z ∈ X) :
    ∃ (τ : ZMod p) (g : U ≃ₗ[ZMod p] U) (c : U) (φ : Module.Dual (ZMod p) U),
      g ∈ scalarHull X ∧ IsHomologyWith τ g c φ ∧ orderOf z = orderOf τ := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  have h0 : Module.finrank (ZMod p) U - 1 = 0 := by omega
  have hVbot : V = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    have h := hs.2.1
    rw [h0] at h
    exact h
  have hCtop : centralizerSpace X = ⊤ := by
    have h := hs.1.sup_eq_top
    simpa [V, hVbot] using h
  have hz1 : z = 1 := by
    ext v
    have hv : v ∈ centralizerSpace X := by rw [hCtop]; exact Submodule.mem_top
    have hfix : z v = v := mem_centralizerSpace.mp hv z hz
    simpa using hfix
  refine ⟨1, 1, 0, 0, ?_, ?_, ?_⟩
  · simp [scalarHull]
  · constructor <;> simp
  · rw [hz1, orderOf_one]
    simp

private theorem exists_homology_of_scalar [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport X (Module.finrank (ZMod p) U - 1))
    {z : U ≃ₗ[ZMod p] U} (hz : z ∈ X) {ζ : ZMod p} (hζ0 : ζ ≠ 0)
    (hzV : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace X, z v = ζ • v)
    {y : U} (hy0 : y ≠ 0) (hCspan : centralizerSpace X = Submodule.span (ZMod p) {y})
    (hzy : z y = y) :
    ∃ (g : U ≃ₗ[ZMod p] U) (φ : Module.Dual (ZMod p) U),
      g ∈ scalarHull X ∧ IsHomologyWith ζ⁻¹ g y φ := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let u := Units.mk0 ζ hζ0
  let g := LinearEquiv.smulOfUnit u⁻¹ * z
  have hg : g ∈ scalarHull X := by
    rw [scalarHull]
    exact Subgroup.mul_mem _ (smulOfUnit_mem_scalarHull X u⁻¹) (le_scalarHull X hz)
  have hgV : ∀ v ∈ V, g v = v := by
    intro v hv
    simp only [g, LinearEquiv.mul_apply, LinearEquiv.smulOfUnit, hzV v hv]
    rw [DistribMulAction.toLinearEquiv_apply]
    rw [Units.smul_def]
    rw [smul_smul]
    rw [show ζ = (↑u : ZMod p) from rfl]
    rw [Units.inv_mul, one_smul]
  have hgy : g y = ζ⁻¹ • y := by
    simp only [g, LinearEquiv.mul_apply, LinearEquiv.smulOfUnit, hzy]
    rfl
  have hcompl : IsCompl V (Submodule.span (ZMod p) {y}) := by
    rw [← hCspan]
    exact hs.1
  obtain ⟨φ, hφ, _⟩ := exists_isHomologyWith_of_isCompl (g := g) (τ := ζ⁻¹) (W := V) (y := y)
    hy0 hcompl hgV hgy
  exact ⟨g, φ, hg, hφ⟩

theorem exists_isHomologyWith_of_mem_center [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : ReflGen p X)
    (hs : SplitSupport X (Module.finrank (ZMod p) U - 1)) {z : U ≃ₗ[ZMod p] U} (hz : z ∈ X)
    (hzc : ∀ x ∈ X, z * x = x * z) :
    ∃ (τ : ZMod p) (g : U ≃ₗ[ZMod p] U) (c : U) (φ : Module.Dual (ZMod p) U),
      g ∈ scalarHull X ∧ IsHomologyWith τ g c φ ∧ orderOf z = orderOf τ := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let n := Module.finrank (ZMod p) U
  have hs' : SplitSupport X (n - 1) := hs
  by_cases hn : n ≤ 1
  · exact exists_isHomologyWith_of_rank_le_one hs' hn hz
  · have hn2 : 2 ≤ n := by omega
    have hVne : V ≠ ⊥ := by
      intro hbot
      have hfin : Module.finrank (ZMod p) V = 0 := by rw [hbot, finrank_bot]
      have h : n - 1 = 0 := by rw [← hs'.2.1, hfin]
      omega
    obtain ⟨ζ, hζ0, hzV⟩ := exists_scalar_of_mem_center hX hs' hz hzc hVne
    obtain ⟨y, hy0, hCspan⟩ := exists_compl_line hs' (by omega)
    have hy : y ∈ centralizerSpace X := by
      rw [hCspan]; exact Submodule.mem_span_singleton_self y
    have hzy : z y = y := mem_centralizerSpace.mp hy z hz
    have hzC : ∀ c ∈ centralizerSpace X, z c = c := fun c hc => mem_centralizerSpace.mp hc z hz
    obtain ⟨g, φ, hg, hφ⟩ := exists_homology_of_scalar hs' hz hζ0 hzV hy0 hCspan hzy
    refine ⟨ζ⁻¹, g, y, φ, hg, hφ, ?_⟩
    have hcompl : IsCompl V (Submodule.span (ZMod p) {y}) := by
      rw [← hCspan]; exact hs'.1
    have hzC' : ∀ c ∈ Submodule.span (ZMod p) {y}, z c = c := by
      intro c hc
      rw [← hCspan] at hc
      exact hzC c hc
    rw [orderOf_eq_of_scalar_on_compl hcompl.sup_eq_top hVne hzV hzC']
    rw [orderOf_eq_orderOf_iff]
    intro k
    constructor
    · intro hk
      rw [inv_pow, hk, inv_one]
    · intro hk
      have h : (ζ ^ k)⁻¹ = 1 := by
        rw [← inv_pow]
        exact hk
      exact inv_eq_one.mp h

theorem mul_self_eq_one_of_splitSupport_one {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : ReflGen p X)
    (hs : SplitSupport X 1) {x : U ≃ₗ[ZMod p] U} (hx : x ∈ X) : x * x = 1 := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  have hVdim : Module.finrank (ZMod p) V = 1 := hs.2.1
  have hVinv : ∀ h ∈ X, ∀ v ∈ V, h v ∈ V := fun h hh v hv => apply_mem_commutatorSpace hh hv
  let ρ := restrictHom X V hVinv
  have hρ : Function.Injective ρ := restrictHom_injective_of_splitSupport hs
  have hcomm : ∀ a b : X, a * b = b * a := by
    intro a b
    apply hρ
    rw [map_mul, map_mul]
    exact commute_of_finrank_eq_one hVdim (ρ a) (ρ b)
  have hgen : X = Subgroup.closure {t | t ∈ X ∧ IsRefl p t} := hX
  rw [hgen] at hx
  refine Subgroup.closure_induction (p := fun x _ => x * x = 1) ?mem ?one ?mul ?inv hx
  · rintro t ⟨htX, htv⟩
    exact htv.1
  · simp
  · intro a b ha hb ha2 hb2
    have haX : a ∈ X := by rw [hgen]; exact ha
    have hbX : b ∈ X := by rw [hgen]; exact hb
    have hcomm_ab : a * b = b * a := by
      have h := congrArg (fun z : X => (z : U ≃ₗ[ZMod p] U)) (hcomm ⟨a, haX⟩ ⟨b, hbX⟩)
      simpa [Subgroup.coe_mul] using h
    calc
      (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm_ab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  · intro a ha ha2
    calc
      a⁻¹ * a⁻¹ = (a * a)⁻¹ := by rw [mul_inv_rev]
      _ = 1 := by rw [ha2, inv_one]

theorem eq_one_of_splitSupport_zero [Module.Finite (ZMod p) U] {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport X 0) {x : U ≃ₗ[ZMod p] U} (hx : x ∈ X) : x = 1 := by
  have hV : HardMathSupport.Kantor79.commutatorSpace X = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    exact hs.2.1
  have hC : centralizerSpace X = ⊤ := by
    have h := hs.1.sup_eq_top
    rw [hV, bot_sup_eq] at h
    exact h
  ext v
  have hv : v ∈ centralizerSpace X := by rw [hC]; exact Submodule.mem_top
  have hfix : x v = v := mem_centralizerSpace.mp hv x hx
  simpa using hfix

end CFSG.StandardType.ZS

end
