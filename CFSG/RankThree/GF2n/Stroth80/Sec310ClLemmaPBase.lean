module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClScalar

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

section Transvections

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

@[expose] def HasTransv (F : LinearMap.BilinForm K V) (J : Subgroup (V ≃ₗ[K] V)) (e : V)
    (c : K) : Prop :=
  ∃ g ∈ J, ∀ v, g v = v + (c * F v e) • e

@[expose] def NoTransv (F : LinearMap.BilinForm K V) (J : Subgroup (V ≃ₗ[K] V)) (e : V) :
    Prop :=
  ∀ c : K, HasTransv F J e c → c = 0

end Transvections

section Base

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

private theorem two_smul_zero' (v : V) : (2 : K) • v = 0 := by
  rw [two_eq_zero_K, zero_smul]

private theorem two_mul_smul_zero (x : K) (v : V) : (2 * x) • v = 0 := by
  rw [two_eq_zero_K, zero_mul, zero_smul]

private theorem exists_ne_zero_one (hq : 4 ≤ Nat.card K) : ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have key : ∀ z : K, z ≠ 1 → z = 0 := fun z hz => by
    by_contra h0
    exact hz (hcon z h0)
  have hinj : Function.Injective (fun x : K => decide (x = 1)) := by
    intro x y hxy
    by_cases hx : x = 1
    · by_cases hy : y = 1
      · rw [hx, hy]
      · simp [hx, hy] at hxy
    · by_cases hy : y = 1
      · simp [hx, hy] at hxy
      · rw [key x hx, key y hy]
  have hle := Nat.card_le_card_of_injective _ hinj
  have hB : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  omega

private theorem exists_dual_pair {p c : V} (hli : LinearIndependent K ![p, c]) (κ : K) :
    ∃ φ : Module.Dual K V, φ p = 0 ∧ φ c = κ := by
  have hcn : c ∉ Submodule.span K {p} := by
    intro hc
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hc
    have h := (LinearIndependent.pair_iff.mp hli) a (-1)
      (by rw [ha, neg_one_smul, add_neg_cancel])
    exact neg_ne_zero.mpr one_ne_zero h.2
  obtain ⟨φ₀, hφ₀c, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hcn inferInstance
  have hφ₀p : φ₀ p = 0 := by
    have hmem : φ₀ p ∈ (Submodule.span K {p}).map φ₀ :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self p)
    rw [hmap] at hmem
    exact (Submodule.mem_bot K).mp hmem
  refine ⟨(κ * (φ₀ c)⁻¹) • φ₀, ?_, ?_⟩
  · simp [hφ₀p]
  · rw [LinearMap.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hφ₀c, mul_one]

private theorem exists_transv_e (halt : F.IsAlt) {e f : V} (hef : F e f = 1) (c : K) :
    ∃ t : V ≃ₗ[K] V, t ∈ pointRadSubgroup F e ∧ t f = f + c • e ∧
      ∀ v, t v = v + (c * F v e) • e := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have hω : F (c • e) e = 0 := by
    rw [map_smul, LinearMap.smul_apply, form_self halt, smul_zero]
  refine ⟨elationEquiv halt e f (c • e) hω, elationEquiv_mem halt hef hω,
    elationEquiv_f halt hef hω, fun v => ?_⟩
  have hb : F v (c • e) + F f (c • e) * F v e = 0 := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hfe, mul_one]
    linear_combination (c * F v e) * (two_eq_zero_K (K := K))
  rw [elationEquiv_apply, hb, zero_smul, add_zero, smul_smul, mul_comm (F v e) c]

theorem conj_pointRad_om (halt : F.IsAlt) {e f : V} (hef : F e f = 1) {h g : V ≃ₗ[K] V}
    (hh : h ∈ sympSubgroup F) {s : K} (hhe : h e = s • e) (hg : g ∈ pointRadSubgroup F e)
    {w : V} {a μ ν : K} (hw : g f - f = w + a • e) (hwf : F w f = 0)
    (hhw : h w = μ • w + ν • e) :
    h * g * h⁻¹ ∈ pointRadSubgroup F e ∧ (h * g * h⁻¹) f - f = (s * μ) • w + (s ^ 2 * a) • e := by
  have hhI : IsIsom F h := hh
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have hs : s ≠ 0 := by
    rintro rfl
    apply ne_zero_of_form_eq_one hef
    exact (LinearEquiv.map_eq_zero_iff h).mp (by rw [hhe, zero_smul])
  have hmem : h * g * h⁻¹ ∈ pointRadSubgroup F e := by
    have := conj_mem_pointRad hh hg
    rwa [hhe, pointRad_smul hs] at this
  refine ⟨hmem, ?_⟩
  obtain ⟨u, hu⟩ : ∃ u, u = h⁻¹ f := ⟨_, rfl⟩
  have hu1 : h u = f := by rw [hu]; simp
  have hFue : F u e = s := by
    have := hhI u e
    rw [hu1, hhe, map_smul, hfe, smul_eq_mul, mul_one] at this
    exact this.symm
  obtain ⟨z, hz⟩ : ∃ z, z = u - s • f := ⟨_, rfl⟩
  have hz0 : F z e = 0 := by
    rw [hz]
    simp [map_sub, map_smul, hFue, hfe]
  have hFwu : F w u = ν := by
    have := hhI w u
    rw [hhw, hu1] at this
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hwf,
      hef, mul_zero, mul_one, zero_add] at this
    exact this.symm
  have hFwz : F w z = ν := by
    rw [hz, map_sub, map_smul, hFwu, hwf, smul_zero, sub_zero]
  have hFez : F e z = 0 := by rw [form_comm halt]; exact hz0
  have hgz : g z = z + F (g f - f) z • e := pointRad_apply_perp halt hef hg z hz0
  have hFgz : F (g f - f) z = ν := by
    rw [hw]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hFwz,
      hFez, mul_zero, add_zero]
  have hgf : g f = f + (w + a • e) := by rw [← hw]; abel
  have hsplit : u = z + s • f := by rw [hz]; abel
  have hgu : g u = z + ν • e + s • (f + (w + a • e)) := by
    rw [hsplit, map_add, map_smul, hgz, hFgz, hgf]
  have hhz : h z = f - s • h f := by rw [hz, map_sub, map_smul, hu1]
  have hkf : (h * g * h⁻¹) f = h (g u) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hu]
  rw [hkf, hgu]
  simp only [map_add, map_smul, hhz, hhe, hhw]
  linear_combination (norm := module) two_mul_smul_zero (ν * s) e

theorem coord_unique (halt : F.IsAlt) {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)}
    (hT : NoTransv F J e) {g g' : V ≃ₗ[K] V} (hg : g ∈ J ⊓ pointRadSubgroup F e)
    (hg' : g' ∈ J ⊓ pointRadSubgroup F e) {w : V} {a a' : K} (h1 : g f - f = w + a • e)
    (h2 : g' f - f = w + a' • e) : a = a' := by
  have hgJ : g ∈ J := (Subgroup.mem_inf.mp hg).1
  have hgQ : g ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg).2
  have hgJ' : g' ∈ J := (Subgroup.mem_inf.mp hg').1
  have hgQ' : g' ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg').2
  obtain ⟨-, hge, -⟩ := id hgQ
  have hwe : F w e = 0 := by
    have h := pointRad_om_perp (f := f) hgQ
    rw [h1] at h
    simpa [form_self halt] using h
  have hgw : g w = w := by
    rw [pointRad_apply_perp halt hef hgQ w hwe, h1]
    simp [map_add, map_smul, form_self halt, form_comm halt e w, hwe]
  have hgf : g f = f + (w + a • e) := by rw [← h1]; abel
  have hg'f : g' f = f + (w + a' • e) := by rw [← h2]; abel
  obtain ⟨t, htQ, htf, htv⟩ := exists_transv_e halt hef (a + a')
  have hk : g * g' = t := by
    refine pointRad_ext halt hef ((pointRadSubgroup F e).mul_mem hgQ hgQ') htQ ?_
    rw [LinearEquiv.mul_apply, hg'f, map_add, map_add, map_smul, hgw, hge, hgf, htf]
    linear_combination (norm := module) two_smul_zero' (K := K) w
  have hTr : HasTransv F J e (a + a') :=
    ⟨g * g', J.mul_mem hgJ hgJ', fun v => by rw [hk, htv]⟩
  have h0 := hT (a + a') hTr
  linear_combination h0 + (-a') * (two_eq_zero_K (K := K))

theorem exists_diag_of_perp (halt : F.IsAlt) {J : Subgroup (V ≃ₗ[K] V)}
    {p c : V} (hcp : F c p = 0) (hli : LinearIndependent K ![p, c])
    (hp : ElationFull F ((J : Set _) ∩ pointRad F p) p)
    (hc : ElationFull F ((J : Set _) ∩ pointRad F c) c) {s : K} (hs : s ≠ 0) :
    ∃ h ∈ J, h p = s • p ∧ h c = s⁻¹ • c := by
  have hpp : F p p = 0 := form_self halt p
  have hpc : F p c = 0 := by rw [form_comm halt]; exact hcp
  have hcc : F c c = 0 := form_self halt c
  have hli' : LinearIndependent K ![c, p] := LinearIndependent.pair_symm_iff.mp hli
  have hX : ∀ κ : K, ∃ g ∈ J, g p = p ∧ g c = c + κ • p := by
    intro κ
    obtain ⟨φ, hφp, hφc⟩ := exists_dual_pair hli κ
    obtain ⟨g, hg, hgv⟩ := hp φ hφp
    refine ⟨g, hg.1, ?_, ?_⟩
    · rw [hgv p hpp, hφp, zero_smul, add_zero]
    · rw [hgv c hcp, hφc]
  have hY : ∀ κ : K, ∃ g ∈ J, g c = c ∧ g p = p + κ • c := by
    intro κ
    obtain ⟨φ, hφc, hφp⟩ := exists_dual_pair hli' κ
    obtain ⟨g, hg, hgv⟩ := hc φ hφc
    refine ⟨g, hg.1, ?_, ?_⟩
    · rw [hgv c hcc, hφc, zero_smul, add_zero]
    · rw [hgv p hpc, hφp]
  choose X hXJ hXp hXc using hX
  choose Y hYJ hYc hYp using hY
  have hNc : ∀ a : K, a ≠ 0 → (X a * Y a⁻¹ * X a) c = a • p := by
    intro a ha
    have haa : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
    have hai : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
    simp only [LinearEquiv.mul_apply, map_add, map_smul, hXc, hXp, hYc, hYp, smul_add,
      smul_smul, haa, hai, mul_one, one_smul]
    linear_combination (norm := module) two_smul_zero' (K := K) c + two_smul_zero' (K := K) (a • p)
  have hNp : ∀ a : K, a ≠ 0 → (X a * Y a⁻¹ * X a) p = a⁻¹ • c := by
    intro a ha
    have hai : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
    simp only [LinearEquiv.mul_apply, map_add, map_smul, hXc, hXp, hYc, hYp, smul_add,
      smul_smul, hai, one_smul]
    linear_combination (norm := module) two_smul_zero' (K := K) p
  have hN1p : (X 1 * Y 1⁻¹ * X 1) p = c := by rw [hNp 1 one_ne_zero, inv_one, one_smul]
  have hN1c : (X 1 * Y 1⁻¹ * X 1) c = p := by rw [hNc 1 one_ne_zero, one_smul]
  refine ⟨(X s * Y s⁻¹ * X s) * (X 1 * Y 1⁻¹ * X 1), ?_, ?_, ?_⟩
  · exact J.mul_mem (J.mul_mem (J.mul_mem (hXJ s) (hYJ _)) (hXJ s))
      (J.mul_mem (J.mul_mem (hXJ 1) (hYJ _)) (hXJ 1))
  · rw [LinearEquiv.mul_apply, hN1p, hNc s hs]
  · rw [LinearEquiv.mul_apply, hN1c, hNp s hs]

theorem zero_of_perp_point (hnd : F.Nondegenerate) (halt : F.IsAlt) (hq : 4 ≤ Nat.card K)
    {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)} (hJ : J ≤ sympSubgroup F)
    (hfull : ElationFull F ((J : Set _) ∩ pointRad F e) e) (hT : NoTransv F J e) {c : V}
    (hce : F c e = 0) (hcne : ∀ t : K, c ≠ t • e)
    (hc : ElationFull F ((J : Set _) ∩ pointRad F c) c) {g₀ : V ≃ₗ[K] V}
    (hg₀ : g₀ ∈ J ⊓ pointRadSubgroup F e) {a : K}
    (hω : g₀ f - f = (c - F c f • e) + a • e) : a = 0 := by
  have he0 : e ≠ 0 := ne_zero_of_form_eq_one hef
  have hli : LinearIndependent K ![e, c] :=
    (LinearIndependent.pair_iff' he0).mpr (fun t ht => hcne t ht.symm)
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_one hq
  obtain ⟨h, hhJ, hhe, hhc⟩ := exists_diag_of_perp halt hce hli hfull hc hl0
  have hwf : F (c - F c f • e) f = 0 := by
    simp [map_sub, map_smul, hef]
  have hhw : h (c - F c f • e) = l⁻¹ • (c - F c f • e) + ((l⁻¹ + l) * F c f) • e := by
    rw [map_sub, map_smul, hhc, hhe]
    linear_combination (norm := module) (-1 : K) • two_mul_smul_zero (F c f * l) e
  obtain ⟨hmemQ, hom⟩ :=
    conj_pointRad_om halt hef (hJ hhJ) hhe (Subgroup.mem_inf.mp hg₀).2 hω hwf hhw
  have hmemJ : h * g₀ * h⁻¹ ∈ J ⊓ pointRadSubgroup F e :=
    Subgroup.mem_inf.mpr ⟨J.mul_mem (J.mul_mem hhJ (Subgroup.mem_inf.mp hg₀).1)
      (J.inv_mem hhJ), hmemQ⟩
  have h1 : (h * g₀ * h⁻¹) f - f = (c - F c f • e) + (l ^ 2 * a) • e := by
    rw [hom, mul_inv_cancel₀ hl0, one_smul]
  have hcoord : l ^ 2 * a = a := coord_unique halt hef hT hmemJ hg₀ h1 hω
  have hfac : (l + 1) ^ 2 * a = 0 := by
    linear_combination hcoord + (l * a + a) * (two_eq_zero_K (K := K))
  have hl1' : l + 1 ≠ 0 := fun h0 => hl1 (by linear_combination h0 - (two_eq_zero_K (K := K)))
  exact (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hl1')

theorem zero_of_perp_point_smul (hnd : F.Nondegenerate) (halt : F.IsAlt) (hq : 4 ≤ Nat.card K)
    {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)} (hJ : J ≤ sympSubgroup F)
    (hfull : ElationFull F ((J : Set _) ∩ pointRad F e) e) (hT : NoTransv F J e) {c : V}
    (hce : F c e = 0) (hcne : ∀ t : K, c ≠ t • e)
    (hc : ElationFull F ((J : Set _) ∩ pointRad F c) c) (θ : K) {g₀ : V ≃ₗ[K] V}
    (hg₀ : g₀ ∈ J ⊓ pointRadSubgroup F e) {a : K}
    (hω : g₀ f - f = θ • (c - F c f • e) + a • e) : a = 0 := by
  by_cases hθ : θ = 0
  · subst hθ
    obtain ⟨t, htQ, htf, htv⟩ := exists_transv_e halt hef a
    have hω0 : g₀ f = f + a • e := by
      have h1 : g₀ f - f = a • e := by rw [hω, zero_smul, zero_add]
      rw [← h1]
      abel
    have hgt : g₀ = t :=
      pointRad_ext halt hef (Subgroup.mem_inf.mp hg₀).2 htQ (by rw [hω0, htf])
    exact hT a ⟨g₀, (Subgroup.mem_inf.mp hg₀).1, fun v => by rw [hgt, htv]⟩
  · have hce' : F (θ • c) e = 0 := by
      rw [map_smul, LinearMap.smul_apply, hce, smul_zero]
    have hcne' : ∀ t : K, θ • c ≠ t • e := fun t ht =>
      hcne (θ⁻¹ * t) (by
        calc c = θ⁻¹ • (θ • c) := (inv_smul_smul₀ hθ c).symm
          _ = θ⁻¹ • (t • e) := by rw [ht]
          _ = (θ⁻¹ * t) • e := smul_smul θ⁻¹ t e)
    have hset : pointRad F (θ • c) = pointRad F c := by
      unfold pointRad
      rw [pointRad_smul hθ]
    have hc' : ElationFull F ((J : Set _) ∩ pointRad F (θ • c)) (θ • c) := by
      rw [hset]
      exact (elationFull_smul hθ).mpr hc
    have hsub : θ • c - F (θ • c) f • e = θ • (c - F c f • e) := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_sub, smul_smul]
    have hω' : g₀ f - f = (θ • c - F (θ • c) f • e) + a • e := by
      rw [hsub, hω]
    exact zero_of_perp_point hnd halt hq hef hJ hfull hT hce' hcne' hc' hg₀ hω'

end Base

section Dichotomy

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

private theorem lin_one_apply (x : V) : (1 : V ≃ₗ[K] V) x = x := rfl

theorem dichotomy_b1 (hnd : F.Nondegenerate) (halt : F.IsAlt) (hdim : Module.finrank K V = 4)
    {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)} (hJ : J ≤ sympSubgroup F)
    (hff : ElationFull F ((J : Set _) ∩ pointRad F f) f)
    (hb : ∀ g ∈ J, F (g e) e = 0 → ∃ t : K, g e = t • e) :
    NoTransv F J f ∧ ∀ g ∈ J ⊓ pointRadSubgroup F f, F (g e - e) e = 0 → g = 1 := by
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  have hconj : ∀ g ∈ J ⊓ pointRadSubgroup F f, F (g e - e) e = 0 → g = 1 := by
    intro g hg hgz
    have hgJ : g ∈ J := (Subgroup.mem_inf.mp hg).1
    have hgQ : g ∈ pointRadSubgroup F f := (Subgroup.mem_inf.mp hg).2
    have h2 : F (g e - e) e = F (g e) e := by
      rw [map_sub, LinearMap.sub_apply, form_self halt, sub_zero]
    have hFe : F (g e) e = 0 := by rw [← h2]; exact hgz
    obtain ⟨t, ht⟩ := hb g hgJ hFe
    have hgf : F (g e - e) f = 0 := pointRad_om_perp (e := f) (f := e) hgQ
    rw [ht] at hgf
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hef,
      mul_one] at hgf
    have ht1 : t = 1 := sub_eq_zero.mp hgf
    rw [ht1, one_smul] at ht
    exact pointRad_ext halt hef' hgQ (pointRadSubgroup F f).one_mem
      (by rw [lin_one_apply]; exact ht)
  obtain ⟨w, hw0, hwe, hwf⟩ := exists_perp_ne_zero (F := F) (by omega) e f
  have hkex : ∀ s : K, ∃ k ∈ J ⊓ pointRadSubgroup F f, ∃ d : K,
      k e - e = s • w + d • f := by
    intro s
    have hω : F (s • w) f = 0 := by simp [hwf]
    obtain ⟨k, hk, d, hkd⟩ := ElationFull.om hnd halt hef' Set.inter_subset_right hff hω
    exact ⟨k, Subgroup.mem_inf.mpr ⟨hk.1, hk.2⟩, d, hkd⟩
  choose kk hkmem dd hkd using hkex
  refine ⟨fun c₀ hτ => ?_, hconj⟩
  obtain ⟨τ, hτJ, hτv⟩ := hτ
  by_contra hc₀
  have hτQ : τ ∈ pointRadSubgroup F f := by
    refine ⟨hJ hτJ, ?_, fun v _ => ⟨c₀ * F v f, hτv v⟩⟩
    rw [hτv f, form_self halt, mul_zero, zero_smul, add_zero]
  have hτe : τ e - e = c₀ • f := by
    rw [hτv e, hef, mul_one, add_sub_cancel_left]
  have hmulQ : ∀ x y : V ≃ₗ[K] V, x ∈ pointRadSubgroup F f → y ∈ pointRadSubgroup F f →
      ∀ s t d d' : K, x e - e = s • w + d • f → y e - e = t • w + d' • f →
        (x * y) e - e = (s + t) • w + (d + d') • f := by
    intro x y hx hy s t d d' hxe hye
    have hfw : F f w = 0 := by rw [form_comm halt]; exact hwf
    have hFz : F (s • w + d • f) (t • w + d' • f) = 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        form_self halt, hwf, hfw, mul_zero, zero_mul, add_zero, zero_add]
    rw [pointRad_om_mul halt hef' hx hy, hxe, hye, hFz, zero_smul, add_zero]
    module
  obtain ⟨T, hT⟩ : ∃ T : Bool → V ≃ₗ[K] V, ∀ b, T b = cond b τ 1 :=
    ⟨fun b => cond b τ 1, fun b => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Bool → K, ∀ b, β b = cond b c₀ 0 :=
    ⟨fun b => cond b c₀ 0, fun b => rfl⟩
  have hTmem : ∀ b, T b ∈ J ⊓ pointRadSubgroup F f := by
    intro b
    cases b
    · rw [hT]; exact Subgroup.mem_inf.mpr ⟨J.one_mem, (pointRadSubgroup F f).one_mem⟩
    · rw [hT]; exact Subgroup.mem_inf.mpr ⟨hτJ, hτQ⟩
  have hTω : ∀ b, T b e - e = (0 : K) • w + (β b) • f := by
    intro b
    rw [zero_smul, zero_add]
    cases b
    · rw [hT, hβ]; simp
    · rw [hT, hβ]; exact hτe
  have hpsi : ∀ s b, (kk s * T b) e - e = (s + 0) • w + (dd s + β b) • f := fun s b =>
    hmulQ _ _ (Subgroup.mem_inf.mp (hkmem s)).2 (Subgroup.mem_inf.mp (hTmem b)).2 s 0 (dd s)
      (β b) (hkd s) (hTω b)
  have hQ : ∀ s b, kk s * T b ∈ pointRadSubgroup F f := fun s b =>
    (pointRadSubgroup F f).mul_mem (Subgroup.mem_inf.mp (hkmem s)).2
      (Subgroup.mem_inf.mp (hTmem b)).2
  have hJQ : ∀ s b, kk s * T b ∈ J ⊓ pointRadSubgroup F f := fun s b =>
    (J ⊓ pointRadSubgroup F f).mul_mem (hkmem s) (hTmem b)
  have hinj : Function.Injective (fun p : K × Bool => dd p.1 + β p.2) := by
    rintro ⟨s, b⟩ ⟨s', b'⟩ hEq
    simp only at hEq
    have hψ := hmulQ _ _ (hQ s b) (hQ s' b') (s + 0) (s' + 0) (dd s + β b) (dd s' + β b')
      (hpsi s b) (hpsi s' b')
    have hcoef : (dd s + β b) + (dd s' + β b') = 0 := by
      linear_combination hEq + (dd s' + β b') * (two_eq_zero_K (K := K))
    rw [hcoef] at hψ
    have hψmem : (kk s * T b) * (kk s' * T b') ∈ J ⊓ pointRadSubgroup F f :=
      (J ⊓ pointRadSubgroup F f).mul_mem (hJQ s b) (hJQ s' b')
    have hψe : ((kk s * T b) * (kk s' * T b')) e - e = (s + s') • w := by
      rw [hψ]
      simp only [add_zero, zero_smul]
    have hF0 : F (((kk s * T b) * (kk s' * T b')) e - e) e = 0 := by
      rw [hψe]
      simp [hwe]
    have hψ1 := hconj _ hψmem hF0
    rw [hψ1, lin_one_apply, sub_self] at hψe
    have hs0 : s + s' = 0 := (smul_eq_zero.mp hψe.symm).resolve_right hw0
    have hss : s = s' := by linear_combination hs0 + (-s') * (two_eq_zero_K (K := K))
    subst hss
    have hβb : β b = β b' := add_left_cancel hEq
    rw [hβ, hβ] at hβb
    have hc₀' : (0 : K) ≠ c₀ := fun h => hc₀ h.symm
    have hbb : b = b' := by
      revert hβb
      cases b <;> cases b' <;> simp [hc₀, hc₀']
    subst hbb
    rfl
  have hcard := Nat.card_le_card_of_injective _ hinj
  have hB : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, hB] at hcard
  have hpos : 0 < Nat.card K := Nat.card_pos
  omega

theorem dichotomy_b2 (hnd : F.Nondegenerate) (halt : F.IsAlt) (hq : 4 ≤ Nat.card K)
    (hdim : Module.finrank K V = 4) {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : J ≤ sympSubgroup F) (hff : ElationFull F ((J : Set _) ∩ pointRad F f) f)
    (hb : ∀ g ∈ J, F (g e) e = 0 → ∃ t : K, g e = t • e) :
    ∀ g ∈ J, F (g f) f = 0 → ∃ t : K, g f = t • f := by
  intro g hg hgf
  by_contra hno
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  obtain ⟨hT, hconj⟩ := dichotomy_b1 hnd halt hdim hef hJ hff hb
  have hcne : ∀ t : K, g f ≠ t • f := fun t ht => hno ⟨t, ht⟩
  have hc : ElationFull F ((J : Set _) ∩ pointRad F (g f)) (g f) :=
    elationFull_conj hJ hff hg
  have hω : F (g f - F (g f) e • f) f = 0 := by
    simp [map_sub, map_smul, form_self halt, hgf]
  obtain ⟨g₀, hg₀, a, ha⟩ := ElationFull.om hnd halt hef' Set.inter_subset_right hff hω
  have hg₀Q : g₀ ∈ J ⊓ pointRadSubgroup F f := Subgroup.mem_inf.mpr hg₀
  have ha0 : a = 0 := zero_of_perp_point hnd halt hq hef' hJ hff hT hgf hcne hc hg₀Q ha
  have hg₀1 : g₀ = 1 := by
    apply hconj g₀ hg₀Q
    rw [ha, ha0, zero_smul, add_zero]
    simp [map_sub, map_smul, hef']
  have hWeq : g f - F (g f) e • f = 0 := by
    have h1 := ha
    rw [ha0, zero_smul, add_zero, hg₀1, lin_one_apply, sub_self] at h1
    exact h1.symm
  exact hcne (F (g f) e) (sub_eq_zero.mp hWeq)

theorem dichotomy_b3 (hnd : F.Nondegenerate) (halt : F.IsAlt) (hdim : Module.finrank K V = 4)
    {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)} (hJ : J ≤ sympSubgroup F)
    (hfe : ElationFull F ((J : Set _) ∩ pointRad F e) e)
    (hb2 : ∀ g ∈ J, F (g f) f = 0 → ∃ t : K, g f = t • f) :
    NoTransv F J e ∧ ∀ g ∈ J ⊓ pointRadSubgroup F e, F (g f - f) f = 0 → g = 1 := by
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  exact dichotomy_b1 hnd halt hdim hef' hJ hfe hb2

end Dichotomy

end CFSG.RankThree.GF2n.Stroth80.Classify
