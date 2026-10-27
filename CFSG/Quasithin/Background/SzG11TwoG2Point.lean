module

public import CFSG.Quasithin.Background.SzG11TwoG2Model
public import CFSG.Quasithin.Background.SzG11NCG2
public import CFSG.Quasithin.Background.JonesParshallG2Gen
public import CFSG.Quasithin.Background.SzG11NCSchur

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open CFSG.Quasithin.SzG11NC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_pointed_model {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K]
    {H : Subgroup (GLV V)} {φ₀ : ↥H ≃* ↥(cayleyGroup K)} {π₀ : quasithinZorn K →ₗ[ZMod 2] V}
    (hM : IsG2Model H (cayleyGroup K) φ₀ π₀) {v : V} (hv : v ≠ 0) :
    ∃ (φ : ↥H ≃* ↥(cayleyGroup K)) (π : quasithinZorn K →ₗ[ZMod 2] V),
      IsG2Model H (cayleyGroup K) φ π ∧ π (zU0 K) = v := by
  have hchar : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have h2F : (2 : K) = 0 := CharTwo.two_eq_zero
  have hker1 : ∀ c : K, π₀ ((c, 0, 0, c) : quasithinZorn K) = 0 := fun c =>
    (hM.ker _ (CharTwo.add_self_eq_zero c)).2 ⟨c, rfl⟩
  have hone : ∀ d : K, ((d, 0, 0, d) : quasithinZorn K) = d • cayleyOne K := fun d => by
    simp [cayleyOne, Prod.smul_def]
  have hfix : ∀ (a : ↥(cayleyGroup K)) (d : K),
      cgE a ((d, 0, 0, d) : quasithinZorn K) = (d, 0, 0, d) := fun a d => by
    rw [hone, map_smul, cg_one]
  have hgg : ∀ (a : ↥(cayleyGroup K)) (y : quasithinZorn K), cgE a (cgE a⁻¹ y) = y :=
    fun a y => by
      rw [← cg_mul_apply, mul_inv_cancel]
      rfl
  have htr : ∀ (a : ↥(cayleyGroup K)) (y : quasithinZorn K), y.1 + y.2.2.2 = 0 →
      (cgE a y).1 + (cgE a y).2.2.2 = 0 := fun a y hy => by
    have h := cg_tr a y
    simp only [cayleyTr] at h
    rw [h]
    exact hy
  obtain ⟨x, hxt, hxv⟩ := hM.surj v
  obtain ⟨c, hc⟩ := isSquare_of_charTwo' (cayleyNorm x)
  have hyt : cayleyTr (x + (c, 0, 0, c)) = 0 := by
    simp only [cayleyTr, Prod.fst_add, Prod.snd_add] at hxt ⊢
    linear_combination hxt + c * h2F
  have hyN : cayleyNorm (x + (c, 0, 0, c)) = 0 := by
    simp only [cayleyNorm, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply,
      add_zero] at hc ⊢
    linear_combination hc + c * hxt + c * c * h2F
  have hy0 : x + (c, 0, 0, c) ≠ 0 := by
    intro h
    have h' := congrArg π₀ h
    rw [map_add, hxv, hker1, add_zero, map_zero] at h'
    exact hv h'
  obtain ⟨g₀, hg₀, hg₀y⟩ := exists_closure_apply_zU0 hy0 hyt hyN
  rw [← cayleyGroup_eq_closure] at hg₀
  let g : ↥(cayleyGroup K) := ⟨g₀, hg₀⟩
  refine ⟨φ₀.trans (MulAut.conj g⁻¹),
    π₀ ∘ₗ ((cgE g).toLinearMap.restrictScalars (ZMod 2)), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro w
    obtain ⟨y, hyt', hyv⟩ := hM.surj w
    refine ⟨cgE g⁻¹ y, htr g⁻¹ y hyt', ?_⟩
    show π₀ (cgE g (cgE g⁻¹ y)) = w
    rw [hgg, hyv]
  · intro y hy
    show π₀ (cgE g y) = 0 ↔ _
    rw [hM.ker _ (htr g y hy)]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, ?_⟩
      have h' := congrArg (cgE g⁻¹) hd
      rw [cg_inv_apply, hfix] at h'
      exact h'
    · rintro ⟨d, rfl⟩
      exact ⟨d, hfix g d⟩
  · intro h y hy
    have hφ : (((φ₀.trans (MulAut.conj g⁻¹)) h : ↥(cayleyGroup K)) :
        quasithinZorn K ≃ₗ[K] quasithinZorn K) y = cgE g⁻¹ (cgE (φ₀ h) (cgE g y)) := by
      rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
      rfl
    show π₀ (cgE g _) = _
    rw [hφ, hgg]
    exact hM.equiv h _ (htr g y hy)
  · show π₀ (cgE g (zU0 K)) = v
    rw [show cgE g (zU0 K) = x + (c, 0, 0, c) from hg₀y, map_add, hxv, hker1, add_zero]

theorem exists_scalars_of_model (K : Type) [Field K] [Algebra (ZMod 2) K]
    {H : Subgroup (GLV V)} {G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)}
    (hG₀ : G₀ ≤ quasithinG2 K) {φ : ↥H ≃* ↥G₀} {π : quasithinZorn K →ₗ[ZMod 2] V}
    (hM : IsG2Model H G₀ φ π) :
    ∃ sc : K →+* Module.End (ZMod 2) V,
      (∀ κ, ∀ h ∈ H, ∀ v, sc κ (h v) = h (sc κ v)) ∧
      ∀ (κ : K) (x : quasithinZorn K), x.1 + x.2.2.2 = 0 → sc κ (π x) = π (κ • x) := by
  classical
  have hchar : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hsurj := hM.surj
  have hker := hM.ker
  have hequiv := hM.equiv
  choose pre pre_tz pre_spec using hsurj
  have smul_tz : ∀ (κ : K) (x : quasithinZorn K), x.1 + x.2.2.2 = 0 →
      (κ • x).1 + (κ • x).2.2.2 = 0 := by
    intro κ x hx
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [← mul_add, hx, mul_zero]
  have congr_smul : ∀ (κ : K) (x x' : quasithinZorn K), x.1 + x.2.2.2 = 0 →
      x'.1 + x'.2.2.2 = 0 → π x = π x' → π (κ • x) = π (κ • x') := by
    intro κ x x' hx hx' hxx
    have hd0 : (x - x').1 + (x - x').2.2.2 = 0 := by
      simp only [Prod.fst_sub, Prod.snd_sub]
      linear_combination hx - hx'
    have hπ : π (x - x') = 0 := by rw [map_sub, hxx, sub_self]
    obtain ⟨c, hc⟩ := (hker _ hd0).1 hπ
    have h2 : κ • (x - x') = (κ * c, 0, 0, κ * c) := by
      rw [hc]
      simp [Prod.smul_def]
    have h3 : π (κ • (x - x')) = 0 := by
      rw [hker _ (smul_tz κ _ hd0)]
      exact ⟨κ * c, h2⟩
    rw [smul_sub, map_sub, sub_eq_zero] at h3
    exact h3
  let scAdd : K → V →+ V := fun κ =>
    { toFun := fun v => π (κ • pre v)
      map_zero' := by
        have := congr_smul κ (pre 0) 0 (pre_tz 0) (by simp) (by rw [pre_spec, map_zero])
        simpa using this
      map_add' := fun v w => by
        have := congr_smul κ (pre (v + w)) (pre v + pre w) (pre_tz _)
          (by simp only [Prod.fst_add, Prod.snd_add]; linear_combination pre_tz v + pre_tz w)
          (by rw [pre_spec, map_add, pre_spec, pre_spec])
        rw [this, smul_add, map_add] }
  have scAdd_apply : ∀ κ v, scAdd κ v = π (κ • pre v) := fun κ v => rfl
  let sc : K →+* Module.End (ZMod 2) V :=
    { toFun := fun κ => (scAdd κ).toZModLinearMap 2
      map_one' := by
        apply LinearMap.ext
        intro v
        simp [scAdd_apply, pre_spec]
      map_mul' := fun κ κ' => by
        apply LinearMap.ext
        intro v
        show scAdd (κ * κ') v = scAdd κ (scAdd κ' v)
        rw [scAdd_apply, scAdd_apply, scAdd_apply]
        have := congr_smul κ (pre (π (κ' • pre v))) (κ' • pre v) (pre_tz _)
          (smul_tz κ' _ (pre_tz v)) (by rw [pre_spec])
        rw [this, mul_smul]
      map_zero' := by
        apply LinearMap.ext
        intro v
        simp [scAdd_apply]
      map_add' := fun κ κ' => by
        apply LinearMap.ext
        intro v
        show scAdd (κ + κ') v = scAdd κ v + scAdd κ' v
        rw [scAdd_apply, scAdd_apply, scAdd_apply, add_smul, map_add] }
  have sc_apply : ∀ κ v, sc κ v = π (κ • pre v) := fun κ v => rfl
  refine ⟨sc, fun κ h hh v => ?_, fun κ x hx => ?_⟩
  ·
    set g : quasithinZorn K ≃ₗ[K] quasithinZorn K :=
      ((φ ⟨h, hh⟩ : ↥G₀) : quasithinZorn K ≃ₗ[K] quasithinZorn K) with hgdef
    have hZ := isAlgAut_of_mem_quasithinG2 (hG₀ (φ ⟨h, hh⟩).2)
    have htr : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 → (g x).1 + (g x).2.2.2 = 0 :=
      fun x hx => hZ.trace_zero hx
    have hge : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 → π (g x) = h (π x) :=
      fun x hx => hequiv ⟨h, hh⟩ x hx
    rw [sc_apply, sc_apply]
    have e1 := congr_smul κ (pre (h v)) (g (pre v)) (pre_tz _) (htr _ (pre_tz v))
      (by rw [pre_spec, hge _ (pre_tz v), pre_spec])
    rw [e1, ← map_smul g, hge _ (smul_tz κ _ (pre_tz v))]
  ·
    rw [sc_apply]
    exact congr_smul κ (pre (π x)) x (pre_tz _) hx (pre_spec _)

end CFSG.Quasithin.G11.SzG11S.Two
