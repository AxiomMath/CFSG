module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.StandardType.ZS

private theorem tv_pow_apply {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    {g : V ≃ₗ[K] V} {u : V} {ψ : Module.Dual K V}
    (hg : ∀ v, g v = v + ψ v • u) (hψu : ψ u = 0) (k : ℕ) (v : V) :
    (g ^ k) v = v + ((k : K) * ψ v) • u := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : (k : K) * ψ v + ψ v = ((k + 1 : ℕ) : K) * ψ v := by
        push_cast; ring
      rw [pow_succ', LinearEquiv.mul_apply, ih, hg, map_add, map_smul, hψu, smul_zero,
        add_zero, add_assoc, ← add_smul, ← hk]

private theorem isTransvectionLin_pow {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {g : V ≃ₗ[ZMod p] V}
    (hg : QTwoLin.IsTransvectionLin g) :
    QTwoLin.IsTransvectionLin (g ^ (p - 1)) := by
  obtain ⟨u, ψ, hu0, hψ0, hψu, hgform⟩ := hg
  have hp1 : ((p - 1 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hp_dvd_p : p ∣ p := dvd_rfl
    have hsub := Nat.dvd_sub hp_dvd_p h
    rw [Nat.sub_sub_self (Fact.out : p.Prime).one_le] at hsub
    exact (Fact.out : p.Prime).not_dvd_one hsub
  let ψ' : Module.Dual (ZMod p) V :=
    { toFun := fun v => ((p - 1 : ℕ) : ZMod p) * ψ v
      map_add' := by intro a b; rw [map_add, mul_add]
      map_smul' := by
        intro a b
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply]
        ring }
  have hψ'u : ψ' u = 0 := by
    change ((p - 1 : ℕ) : ZMod p) * ψ u = 0
    rw [hψu, mul_zero]
  have hψ'0 : ψ' ≠ 0 := by
    intro h0
    apply hψ0
    ext v
    have h := congrArg (fun l : Module.Dual (ZMod p) V => l v) h0
    have h' : ((p - 1 : ℕ) : ZMod p) * ψ v = 0 := by simpa [ψ'] using h
    exact (mul_eq_zero.mp h').resolve_left hp1
  refine ⟨u, ψ', hu0, hψ'0, hψ'u, fun v => ?_⟩
  rw [tv_pow_apply hgform hψu (p - 1) v]
  rfl

section Field

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

private theorem smulOfUnit_mul (a b : Kˣ) :
    (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U) * LinearEquiv.smulOfUnit b =
      LinearEquiv.smulOfUnit (a * b) := by
  ext v
  simp [LinearEquiv.smulOfUnit, mul_smul]

private theorem smulOfUnit_one : (LinearEquiv.smulOfUnit (1 : Kˣ) : U ≃ₗ[K] U) = 1 := by
  ext v
  simp [LinearEquiv.smulOfUnit]

private theorem smulOfUnit_inv (a : Kˣ) :
    (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U)⁻¹ = LinearEquiv.smulOfUnit a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [smulOfUnit_mul, mul_inv_cancel, smulOfUnit_one]

private theorem smulOfUnit_pow (a : Kˣ) (n : ℕ) :
    (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U) ^ n = LinearEquiv.smulOfUnit (a ^ n) := by
  induction n with
  | zero => simpa using smulOfUnit_one.symm
  | succ n ih => rw [pow_succ, ih, smulOfUnit_mul, ← pow_succ]

private theorem smulOfUnit_commute (a : Kˣ) (g : U ≃ₗ[K] U) :
    Commute (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U) g := by
  show (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U) * g = g * LinearEquiv.smulOfUnit a
  ext v
  change (a : K) • g v = g ((a : K) • v)
  rw [map_smul]

private theorem exists_smulOfUnit_of_mem_closure {z : U ≃ₗ[K] U}
    (hz : z ∈ Subgroup.closure (Set.range fun a : Kˣ => (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U))) :
    ∃ a : Kˣ, (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U) = z := by
  refine Subgroup.closure_induction (p := fun z _ => ∃ a : Kˣ,
    (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U) = z) ?_ ?_ ?_ ?_ hz
  · rintro x hx
    exact hx
  · exact ⟨1, smulOfUnit_one⟩
  · rintro x y hx hy ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by rw [← ha, ← hb]; exact (smulOfUnit_mul a b).symm⟩
  · rintro x hx ⟨a, ha⟩
    exact ⟨a⁻¹, by rw [← ha]; exact (smulOfUnit_inv a).symm⟩

@[expose] def IsHomologyWith (τ : K) (g : U ≃ₗ[K] U) (c : U) (φ : Module.Dual K U) : Prop :=
  φ c = τ - 1 ∧ ∀ v, g v = v + φ v • c

namespace IsHomologyWith

variable {τ : K} {g : U ≃ₗ[K] U} {c : U} {φ : Module.Dual K U}

theorem centre_ne_zero (h : IsHomologyWith τ g c φ) (hτ : τ ≠ 1) : c ≠ 0 := by
  intro hc
  apply hτ
  have h1 := h.1
  rw [hc, map_zero] at h1
  exact sub_eq_zero.mp h1.symm

theorem apply_centre (h : IsHomologyWith τ g c φ) : g c = τ • c := by
  rw [h.2 c, h.1]
  module

theorem apply_of_apply_eq_zero (h : IsHomologyWith τ g c φ) {v : U} (hv : φ v = 0) : g v = v := by
  rw [h.2 v, hv, zero_smul, add_zero]

theorem mem_span_of_apply_eq_smul (h : IsHomologyWith τ g c φ) (hτ : τ ≠ 1) {v : U}
    (hv : g v = τ • v) : v ∈ Submodule.span K {c} := by
  have h1 : τ • v = v + φ v • c := by rw [← hv, h.2 v]
  have h2 : (τ - 1) • v = φ v • c := by
    rw [sub_smul, one_smul, h1]
    module
  have h4 : v = (τ - 1)⁻¹ • ((τ - 1) • v) := by
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hτ), one_smul]
  have h3 : v = ((τ - 1)⁻¹ * φ v) • c := by
    calc v = (τ - 1)⁻¹ • ((τ - 1) • v) := h4
      _ = (τ - 1)⁻¹ • (φ v • c) := by rw [h2]
      _ = ((τ - 1)⁻¹ * φ v) • c := by rw [smul_smul]
  rw [h3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton c))

theorem conj (h : IsHomologyWith τ g c φ) (k : U ≃ₗ[K] U) :
    IsHomologyWith τ (k * g * k⁻¹) (k c) (φ ∘ₗ (k.symm : U →ₗ[K] U)) := by
  refine ⟨?_, fun v => ?_⟩
  · simpa [LinearMap.comp_apply] using h.1
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h.2, map_add, map_smul]
    simp [LinearMap.comp_apply]

theorem type_ne_zero (h : IsHomologyWith τ g c φ) : τ ≠ 0 := by
  intro hτ
  have hc : c = 0 := by
    apply g.injective
    rw [apply_centre h, hτ, zero_smul, map_zero]
  have h2 : (-1 : K) = 0 := by
    have h1 := h.1
    rw [hc, map_zero, hτ] at h1
    rw [zero_sub] at h1
    exact h1.symm
  exact one_ne_zero (neg_eq_zero.mp h2)

theorem inv (h : IsHomologyWith τ g c φ) : IsHomologyWith τ⁻¹ g⁻¹ c (-τ⁻¹ • φ) := by
  have hτ : τ ≠ 0 := type_ne_zero h
  have hτ' : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ
  refine ⟨?_, fun v => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, h.1]
    linear_combination (-1) * hτ'
  · change g.symm v = v + (-τ⁻¹ • φ) v • c
    apply g.injective
    rw [LinearEquiv.apply_symm_apply, h.2]
    simp only [map_add, map_smul, h.1, LinearMap.smul_apply, smul_eq_mul]
    rw [add_assoc, ← add_smul]
    have hcoef : (-τ⁻¹) * φ v + (φ v + (-τ⁻¹) * φ v * (τ - 1)) = 0 := by
      linear_combination (-(φ v)) * hτ'
    rw [hcoef, zero_smul, add_zero]

end IsHomologyWith

theorem exists_isHomologyWith_of_isCompl {g : U ≃ₗ[K] U} {τ : K} {W : Submodule K U} {y : U}
    (hy0 : y ≠ 0) (hc : IsCompl W (Submodule.span K {y})) (hW : ∀ w ∈ W, g w = w)
    (hy : g y = τ • y) :
    ∃ φ : Module.Dual K U, IsHomologyWith τ g y φ ∧ ∀ w ∈ W, φ w = 0 := by
  let i : K →ₗ[K] U := LinearMap.toSpanSingleton K U y
  have hi : Function.Injective i := by
    intro a b hab
    have h' : a • y = b • y := by simpa [i] using hab
    have h : (a - b) • y = 0 := by rw [sub_smul, h', sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hy0)
  have hcompl : IsCompl (LinearMap.range i) W := by
    rw [LinearMap.range_toSpanSingleton]
    exact hc.symm
  let π : U →ₗ[K] K := LinearMap.linearProjOfIsCompl W i hi hcompl
  let φ : Module.Dual K U := (τ - 1) • π
  have hπy : π y = 1 := by
    have h := LinearMap.linearProjOfIsCompl_apply_left (q := W) (i := i) (hi := hi)
      (h := hcompl) 1
    simpa [i] using h
  have hφy : φ y = τ - 1 := by
    simp only [φ, LinearMap.smul_apply, hπy, smul_eq_mul, mul_one]
  have hφw : ∀ w ∈ W, φ w = 0 := by
    intro w hw
    simp only [φ, LinearMap.smul_apply]
    rw [LinearMap.linearProjOfIsCompl_apply_right' (q := W) (i := i) (hi := hi)
      (h := hcompl) w hw]
    simp
  have hform : ∀ v, g v = v + φ v • y := by
    intro v
    have hπv : π (v - π v • y) = 0 := by
      simp only [map_sub, map_smul, hπy, smul_eq_mul, mul_one, sub_self]
    have hw : v - π v • y ∈ W := by
      rw [← LinearMap.ker_linearProjOfIsCompl (q := W) (i := i) (hi := hi) (h := hcompl),
        LinearMap.mem_ker]
      exact hπv
    have hv : v = (v - π v • y) + π v • y := (sub_add_cancel v (π v • y)).symm
    calc g v = g ((v - π v • y) + π v • y) := congrArg g hv
      _ = g (v - π v • y) + π v • g y := by rw [map_add, map_smul]
      _ = (v - π v • y) + π v • (τ • y) := by rw [hW _ hw, hy]
      _ = v + φ v • y := by
          simp only [φ, LinearMap.smul_apply, smul_eq_mul]
          module
  exact ⟨φ, ⟨hφy, hform⟩, hφw⟩

private theorem comp_ne_zero_of_mem_range {g : U ≃ₗ[K] U} {i : K →ₗ[K] U} {π : U →ₗ[K] K}
    {f : U →ₗ[K] U} (hg : g ≠ 1) (hπ : ∀ a, π (i a) = a)
    (hfv : ∀ v, f v ∈ LinearMap.range i) (hf : ∀ v, f v = g v - v) : π ∘ₗ f ≠ 0 := by
  intro hψ
  apply hg
  ext v
  obtain ⟨a, ha⟩ := hfv v
  have hπ0 : π (f v) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun l : U →ₗ[K] K => l v) hψ
  have ha0 : a = 0 := by
    have h := hπ a
    rw [ha] at h
    rw [h] at hπ0
    exact hπ0
  have hgv : g v - v = 0 := by
    have hf0 : f v = 0 := by rw [← ha, ha0, map_zero]
    rw [← hf v]; exact hf0
  simpa using sub_eq_zero.mp hgv

theorem isTransvectionLin_of_sub_mem_span {g : U ≃ₗ[K] U} {u : U} (hg : g ≠ 1)
    (hsub : ∀ v, g v - v ∈ Submodule.span K {u}) (hu : g u = u) :
    QTwoLin.IsTransvectionLin g := by
  have hu0 : u ≠ 0 := by
    intro h0
    apply hg
    ext v
    have hv := hsub v
    rw [h0] at hv
    have hv0 : g v - v = 0 := by simpa using hv
    exact sub_eq_zero.mp hv0
  let i : K →ₗ[K] U := LinearMap.toSpanSingleton K U u
  have hi : Function.Injective i := by
    intro a b hab
    have h' : a • u = b • u := by simpa [i] using hab
    have h : (a - b) • u = 0 := by rw [sub_smul, h', sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hu0)
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range i)
  let π : U →ₗ[K] K := LinearMap.linearProjOfIsCompl W i hi hW
  let f : U →ₗ[K] U := (g : U →ₗ[K] U) - 1
  have hfu : f u = 0 := by
    change g u - u = 0
    rw [hu, sub_self]
  have hfv_mem : ∀ v, f v ∈ LinearMap.range i := by
    intro v
    rw [LinearMap.range_toSpanSingleton]
    simpa [f, i] using hsub v
  refine ⟨u, π ∘ₗ f, hu0, ?_, ?_, fun v => ?_⟩
  · exact comp_ne_zero_of_mem_range hg
      (fun a => LinearMap.linearProjOfIsCompl_apply_left (q := W) (i := i) (hi := hi)
        (h := hW) a) hfv_mem (fun v => by simp [f])
  · simp only [LinearMap.comp_apply]
    rw [hfu, map_zero]
  · obtain ⟨a, ha⟩ := hfv_mem v
    have hπ : (π ∘ₗ f) v = a := by
      have h := LinearMap.linearProjOfIsCompl_apply_left (q := W) (i := i) (hi := hi)
        (h := hW) a
      rw [ha] at h
      simpa [LinearMap.comp_apply] using h
    have hf : f v = a • u := by
      rw [← ha]
      simp only [i, LinearMap.toSpanSingleton_apply]
    have h1 : g v - v = a • u := by simpa [f] using hf
    have hgv : g v = v + a • u := by rw [← h1]; module
    rw [hgv, hπ]

@[expose] def scalarHull (G : Subgroup (U ≃ₗ[K] U)) : Subgroup (U ≃ₗ[K] U) :=
  G ⊔ Subgroup.closure (Set.range fun a : Kˣ => (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U))

theorem le_scalarHull (G : Subgroup (U ≃ₗ[K] U)) : G ≤ scalarHull G := le_sup_left

theorem scalarHull_mono {G G' : Subgroup (U ≃ₗ[K] U)} (h : G ≤ G') :
    scalarHull G ≤ scalarHull G' := sup_le (h.trans le_sup_left) le_sup_right

theorem smulOfUnit_mem_scalarHull (G : Subgroup (U ≃ₗ[K] U)) (a : Kˣ) :
    (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U) ∈ scalarHull G :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_range_self a))

theorem mem_scalarHull_iff {G : Subgroup (U ≃ₗ[K] U)} {g : U ≃ₗ[K] U} :
    g ∈ scalarHull G ↔ ∃ h ∈ G, ∃ a : Kˣ, ∀ v, g v = (a : K) • h v := by
  let Z : Subgroup (U ≃ₗ[K] U) :=
    Subgroup.closure (Set.range fun a : Kˣ => (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U))
  have hZ : Z.Normal := ⟨fun n hn k => by
    obtain ⟨a, rfl⟩ := exists_smulOfUnit_of_mem_closure hn
    rw [← (smulOfUnit_commute a k).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.subset_closure ⟨a, rfl⟩⟩
  have hmem : g ∈ G ⊔ Z ↔ ∃ h ∈ G, ∃ z ∈ Z, h * z = g := by
    rw [← SetLike.mem_coe, Subgroup.mul_normal (H := G) (N := Z) (hN := hZ)]
    exact Set.mem_mul
  constructor
  · intro hg
    rw [scalarHull] at hg
    obtain ⟨h, hhG, z, hzZ, hzg⟩ := hmem.mp hg
    obtain ⟨a, haz⟩ := exists_smulOfUnit_of_mem_closure hzZ
    refine ⟨h, hhG, a, fun v => ?_⟩
    rw [← hzg, ← haz, LinearEquiv.mul_apply]
    change h ((a : K) • v) = (a : K) • h v
    rw [map_smul]
  · rintro ⟨h, hhG, a, ha⟩
    have hg : g = (LinearEquiv.smulOfUnit a : U ≃ₗ[K] U) * h := by
      ext v
      rw [LinearEquiv.mul_apply]
      change g v = (a : K) • h v
      exact ha v
    rw [hg, scalarHull]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, rfl⟩))
      (Subgroup.mem_sup_left hhG)

theorem irreducible_scalarHull {G : Subgroup (U ≃ₗ[K] U)}
    (hirr : ∀ W : Submodule K U, (∀ h ∈ G, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule K U) (hW : ∀ h ∈ scalarHull G, ∀ w ∈ W, h w ∈ W) : W = ⊥ ∨ W = ⊤ :=
  hirr W fun h hh w hw => hW h (le_scalarHull G hh) w hw

end Field

section Primitive

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U]

theorem not_isImprimitiveOnV_scalarHull {G : Subgroup (U ≃ₗ[K] U)}
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) :
    ¬ Quasithin.SimsG4.IsImprimitiveOnV (scalarHull G) := by
  rintro ⟨r, W, hr, hne, hind, htop, hperm⟩
  exact hprim ⟨r, W, hr, hne, hind, htop, fun g hg i => hperm g (le_scalarHull G hg) i⟩

end Primitive

section PrimeField

variable {p : ℕ} [Fact p.Prime] {U : Type*} [AddCommGroup U] [Module (ZMod p) U]

theorem transvectionFree_scalarHull {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : QTwoLin.TransvectionFree G) : QTwoLin.TransvectionFree (scalarHull G) := by
  intro g hg hgtrans
  rw [mem_scalarHull_iff] at hg
  obtain ⟨h, hhG, a, ha⟩ := hg
  have hg_eq : g = (LinearEquiv.smulOfUnit a : U ≃ₗ[ZMod p] U) * h := by
    ext v
    rw [LinearEquiv.mul_apply]
    change g v = (a : ZMod p) • h v
    exact ha v
  have hh_eq : h = (LinearEquiv.smulOfUnit a : U ≃ₗ[ZMod p] U)⁻¹ * g := by
    rw [hg_eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hpow : h ^ (p - 1) = g ^ (p - 1) := by
    rw [hh_eq, smulOfUnit_inv, (smulOfUnit_commute a⁻¹ g).mul_pow (p - 1), smulOfUnit_pow,
      ZMod.units_pow_card_sub_one_eq_one p a⁻¹, smulOfUnit_one, one_mul]
  have htrans : QTwoLin.IsTransvectionLin (h ^ (p - 1)) := by
    rw [hpow]
    exact isTransvectionLin_pow hgtrans
  exact hG (h ^ (p - 1)) (pow_mem hhG (p - 1)) htrans

end PrimeField

end CFSG.StandardType.ZS

end
