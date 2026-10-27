module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClLemmaPBase
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClMain

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

private theorem two_smul_zero_K (v : V) : (2 : K) • v = 0 := by
  rw [two_eq_zero_K, zero_smul]

private theorem perp_smul {e f w : V} (hwe : F w e = 0) (hwf : F w f = 0) (c : K) :
    F (c • w) e = 0 ∧ F (c • w) f = 0 := by
  refine ⟨?_, ?_⟩
  · rw [map_smul, LinearMap.smul_apply, hwe, smul_zero]
  · rw [map_smul, LinearMap.smul_apply, hwf, smul_zero]

private theorem coeff_zero_of_disp (halt : F.IsAlt) {e f : V} (hef : F e f = 1)
    {J : Subgroup (V ≃ₗ[K] V)} (hT : NoTransv F J e) {g : V ≃ₗ[K] V}
    (hg : g ∈ J ⊓ pointRadSubgroup F e) {c : K} (hc : g f - f = c • e) : c = 0 := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have hQ : g ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg).2
  have hgf : g f = f + c • e := by rw [← hc]; abel
  refine hT c ⟨g, (Subgroup.mem_inf.mp hg).1, fun v => ?_⟩
  have hu : F (v - F v e • f) e = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hfe,
      mul_one, sub_self]
  have heu : F e (v - F v e • f) = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hef,
      mul_one]
    rw [form_comm halt e v, sub_self]
  have hgu := pointRad_apply_perp halt hef hQ (v - F v e • f) hu
  simp only [hc, map_smul, LinearMap.smul_apply, smul_eq_mul, heu, smul_zero, zero_smul,
    add_zero] at hgu
  have hsplit : v = F v e • f + (v - F v e • f) := by abel
  calc g v = g (F v e • f + (v - F v e • f)) := by rw [← hsplit]
    _ = F v e • g f + g (v - F v e • f) := by rw [map_add, map_smul]
    _ = v + (c * F v e) • e := by rw [hgu, hgf]; module

private theorem coord_data (hnd : F.Nondegenerate) (halt : F.IsAlt) {e f : V} (hef : F e f = 1)
    {J : Subgroup (V ≃ₗ[K] V)} (hT : NoTransv F J e)
    (hfe : ElationFull F ((J : Set _) ∩ pointRad F e) e) :
    ∃ a : V → K,
      (∀ w, F w e = 0 → F w f = 0 → ∃ g ∈ J ⊓ pointRadSubgroup F e, g f - f = w + a w • e) ∧
      (∀ g ∈ J ⊓ pointRadSubgroup F e, ∀ (w : V) (c : K), F w e = 0 → F w f = 0 →
        g f - f = w + c • e → c = a w) ∧
      (∀ w w' : V, F w e = 0 → F w f = 0 → F w' e = 0 → F w' f = 0 →
        a (w + w') = a w + a w' + F w w') := by
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  have hD : ((J : Set (V ≃ₗ[K] V)) ∩ pointRad F e) ⊆ pointRad F e := Set.inter_subset_right
  have hex : ∀ w : V, ∃ g : V ≃ₗ[K] V, F w e = 0 → F w f = 0 →
      g ∈ J ⊓ pointRadSubgroup F e ∧ ∃ c : K, g f - f = w + c • e := by
    intro w
    by_cases hw : F w e = 0
    · obtain ⟨g, hgD, c, hc⟩ := ElationFull.om hnd halt hef hD hfe hw
      exact ⟨g, fun _ _ => ⟨Subgroup.mem_inf.mpr ⟨hgD.1, hgD.2⟩, c, hc⟩⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose gsel hgsel using hex
  obtain ⟨a, ha⟩ : ∃ a : V → K, ∀ w, a w = F f (gsel w f - f) :=
    ⟨fun w => F f (gsel w f - f), fun _ => rfl⟩
  have hi : ∀ w, F w e = 0 → F w f = 0 → gsel w f - f = w + a w • e := by
    intro w hwe hwf
    obtain ⟨_, c, hc⟩ := hgsel w hwe hwf
    have hac : a w = c := by
      rw [ha w, hc]
      simp only [map_add, map_smul, smul_eq_mul]
      rw [form_comm halt f w, hwf, hef', zero_add, mul_one]
    rw [hac]
    exact hc
  have hK : ∀ g ∈ J ⊓ pointRadSubgroup F e, ∀ c : K, g f - f = c • e → c = 0 :=
    fun g hg c hc => coeff_zero_of_disp halt hef hT hg hc
  refine ⟨a, fun w hwe hwf => ⟨gsel w, (hgsel w hwe hwf).1, hi w hwe hwf⟩, ?_, ?_⟩
  · intro g hg w c hwe hwf hc
    exact coord_unique halt hef hT hg (hgsel w hwe hwf).1 hc (hi w hwe hwf)
  · intro w w' hwe hwf hwe' hwf'
    have hwwe : F (w + w') e = 0 := by
      rw [map_add, LinearMap.add_apply, hwe, hwe', zero_add]
    have hwwf : F (w + w') f = 0 := by
      rw [map_add, LinearMap.add_apply, hwf, hwf', zero_add]
    have hF2 : F e (w + w') = 0 := by rw [form_comm halt, hwwe]
    have hg1 := hgsel w hwe hwf
    have hg2 := hgsel w' hwe' hwf'
    have hg3 := hgsel (w + w') hwwe hwwf
    have hd1 := hi w hwe hwf
    have hd2 := hi w' hwe' hwf'
    have hd3 := hi (w + w') hwwe hwwf
    have hQ1 : gsel w ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg1.1).2
    have hQ2 : gsel w' ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg2.1).2
    have hQ3 : gsel (w + w') ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg3.1).2
    have hQ12 : gsel w * gsel w' ∈ pointRadSubgroup F e :=
      (pointRadSubgroup F e).mul_mem hQ1 hQ2
    have hmem : gsel w * gsel w' * gsel (w + w') ∈ J ⊓ pointRadSubgroup F e :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg1.1 hg2.1) hg3.1
    have h12 : (gsel w * gsel w') f - f = (w + w') + (a w + a w' + F w w') • e := by
      rw [pointRad_om_mul halt hef hQ1 hQ2, hd1, hd2, form_add_smul_e halt e w w' (a w) (a w'),
        hwe, form_comm halt e w', hwe']
      simp only [mul_zero, add_zero]
      module
    have hF0 : F ((w + w') + (a w + a w' + F w w') • e) ((w + w') + a (w + w') • e) = 0 := by
      rw [form_add_smul_e halt e (w + w') (w + w') (a w + a w' + F w w') (a (w + w')),
        form_self halt, hwwe, hF2]
      ring
    have hsplit : (w + w') + (a w + a w' + F w w') • e + ((w + w') + a (w + w') • e) =
        ((w + w') + (w + w')) + (a w + a w' + F w w' + a (w + w')) • e := by
      module
    have h123 : (gsel w * gsel w' * gsel (w + w')) f - f =
        (a w + a w' + F w w' + a (w + w')) • e := by
      rw [pointRad_om_mul halt hef hQ12 hQ3, h12, hd3, hF0, zero_smul, add_zero, hsplit,
        vec_add_self K (w + w'), zero_add]
    have hcomp := hK _ hmem (a w + a w' + F w w' + a (w + w')) h123
    linear_combination hcomp - (a w + a w' + F w w') * two_eq_zero_K (K := K)

private theorem span_four (halt : F.IsAlt) (hdim : Module.finrank K V = 4) {e f w₁ w₂ : V}
    (hef : F e f = 1) (hw₁e : F w₁ e = 0) (hw₁f : F w₁ f = 0) (hw₂e : F w₂ e = 0)
    (hw₂f : F w₂ f = 0) (h12 : F w₁ w₂ = 1) :
    Submodule.span K (Set.range ![e, f, w₁, w₂]) = ⊤ := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have h21 : F w₂ w₁ = 1 := by rw [form_comm halt]; exact h12
  have hee : F e e = 0 := form_self halt e
  have hff : F f f = 0 := form_self halt f
  have hew₂ : F e w₂ = 0 := by rw [form_comm halt]; exact hw₂e
  have hfw₂ : F f w₂ = 0 := by rw [form_comm halt]; exact hw₂f
  have hew₁ : F e w₁ = 0 := by rw [form_comm halt]; exact hw₁e
  have hfw₁ : F f w₁ = 0 := by rw [form_comm halt]; exact hw₁f
  have hli : LinearIndependent K ![e, f, w₁, w₂] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : g 0 • e + g 1 • f + g 2 • w₁ + g 3 • w₂ = 0 := by
      simpa [Fin.sum_univ_four] using hg
    have k0 : g 0 = 0 := by
      have h := congrArg (fun v => F v f) hsum
      simpa [map_add, map_smul, hef, hff, hw₁f, hw₂f] using h
    have k1 : g 1 = 0 := by
      have h := congrArg (fun v => F v e) hsum
      simpa [map_add, map_smul, hfe, hee, hw₁e, hw₂e] using h
    have k2 : g 2 = 0 := by
      have h := congrArg (fun v => F v w₂) hsum
      simpa [map_add, map_smul, hew₂, hfw₂, h12, form_self halt w₂] using h
    have k3 : g 3 = 0 := by
      have h := congrArg (fun v => F v w₁) hsum
      simpa [map_add, map_smul, hew₁, hfw₁, h21, form_self halt w₁] using h
    intro i
    fin_cases i <;> simp [k0, k1, k2, k3]
  have hcard : Fintype.card (Fin 4) = Module.finrank K V := by rw [Fintype.card_fin, hdim]
  exact hli.span_eq_top_of_card_eq_finrank' hcard

private theorem decomp_W (hnd : F.Nondegenerate) (halt : F.IsAlt) (hdim : Module.finrank K V = 4)
    {e f w₁ w₂ : V} (hef : F e f = 1) (hw₁e : F w₁ e = 0) (hw₁f : F w₁ f = 0)
    (hw₂e : F w₂ e = 0) (hw₂f : F w₂ f = 0) (h12 : F w₁ w₂ = 1) {x : V}
    (hxe : F x e = 0) (hxf : F x f = 0) :
    x = F x w₂ • w₁ + F x w₁ • w₂ := by
  have h21 : F w₂ w₁ = 1 := by rw [form_comm halt]; exact h12
  have hspan := span_four halt hdim hef hw₁e hw₁f hw₂e hw₂f h12
  have hy : x - (F x w₂ • w₁ + F x w₁ • w₂) = 0 := by
    apply eq_zero_of_perp_span hnd hspan
    rintro p ⟨i, rfl⟩
    fin_cases i
    · simp [hxe, hw₁e, hw₂e]
    · simp [hxf, hw₁f, hw₂f]
    · simp [form_self halt w₁, h21]
    · simp [h12, form_self halt w₂]
  exact sub_eq_zero.mp hy

private theorem cone_zero (hnd : F.Nondegenerate) (halt : F.IsAlt) (hq : 4 ≤ Nat.card K)
    {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)} (hJ : J ≤ sympSubgroup F)
    (hfe : ElationFull F ((J : Set _) ∩ pointRad F e) e)
    (hff : ElationFull F ((J : Set _) ∩ pointRad F f) f)
    (hTe : NoTransv F J e) (hTf : NoTransv F J f) {a a' : V → K}
    (ha1 : ∀ w, F w e = 0 → F w f = 0 → ∃ g ∈ J ⊓ pointRadSubgroup F e, g f - f = w + a w • e)
    (hb1 : ∀ w, F w e = 0 → F w f = 0 → ∃ g ∈ J ⊓ pointRadSubgroup F f, g e - e = w + a' w • f)
    {w : V} (hwe : F w e = 0) (hwf : F w f = 0) (hw : w ≠ 0) (hz : a w = 0) :
    (∀ θ : K, a (θ • w) = 0) ∧ (∀ θ : K, a' (θ • w) = 0) := by
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  have hfwe : F (f + w) e = 1 := by
    rw [map_add, LinearMap.add_apply, hef', hwe, add_zero]
  have hfwf : F (f + w) f = 0 := by
    rw [map_add, LinearMap.add_apply, form_self halt, hwf, zero_add]
  obtain ⟨g₀, hg₀, hω₀⟩ := ha1 w hwe hwf
  rw [hz, zero_smul, add_zero] at hω₀
  have hgf : g₀ f = f + w := by rw [← hω₀]; abel
  have hc1 : ElationFull F ((J : Set _) ∩ pointRad F (f + w)) (f + w) := by
    rw [← hgf]
    exact elationFull_conj hJ hff (Subgroup.mem_inf.mp hg₀).1
  have hfw_ne : ∀ t : K, f + w ≠ t • f := by
    intro t ht
    apply hw
    have h1 := congrArg (fun v => F v e) ht
    simp only [hfwe, map_smul, LinearMap.smul_apply, smul_eq_mul, hef', mul_one] at h1
    have ht1 : t = 1 := by first | exact h1.symm | exact h1
    rw [ht1, one_smul] at ht
    simpa using ht
  have hcw : (f + w) - F (f + w) e • f = w := by
    rw [hfwe, one_smul]
    abel
  have hpart1 : ∀ θ : K, a' (θ • w) = 0 := by
    intro θ
    obtain ⟨g', hg', hω'⟩ := hb1 (θ • w) (perp_smul hwe hwf θ).1 (perp_smul hwe hwf θ).2
    refine zero_of_perp_point_smul hnd halt hq hef' hJ hff hTf hfwf hfw_ne hc1 θ hg' ?_
    rw [hcw]
    exact hω'
  refine ⟨fun θ => ?_, hpart1⟩
  have ha'w : a' w = 0 := by simpa using hpart1 1
  obtain ⟨g', hg', hω'⟩ := hb1 w hwe hwf
  rw [ha'w, zero_smul, add_zero] at hω'
  have hgw : g' e = e + w := by rw [← hω']; abel
  have hc2 : ElationFull F ((J : Set _) ∩ pointRad F (e + w)) (e + w) := by
    rw [← hgw]
    exact elationFull_conj hJ hfe (Subgroup.mem_inf.mp hg').1
  have hew : F (e + w) e = 0 := by
    rw [map_add, LinearMap.add_apply, form_self halt, hwe, zero_add]
  have hefw : F (e + w) f = 1 := by
    rw [map_add, LinearMap.add_apply, hef, hwf, add_zero]
  have hne2 : ∀ t : K, e + w ≠ t • e := by
    intro t ht
    apply hw
    have h1 := congrArg (fun v => F v f) ht
    simp only [hefw, map_smul, LinearMap.smul_apply, smul_eq_mul, hef, mul_one] at h1
    have ht1 : t = 1 := by first | exact h1.symm | exact h1
    rw [ht1, one_smul] at ht
    simpa using ht
  have hcw2 : (e + w) - F (e + w) f • e = w := by
    rw [hefw, one_smul]
    abel
  obtain ⟨g₁, hg₁, hω₁⟩ := ha1 (θ • w) (perp_smul hwe hwf θ).1 (perp_smul hwe hwf θ).2
  refine zero_of_perp_point_smul hnd halt hq hef hJ hfe hTe hew hne2 hc2 θ hg₁ ?_
  rw [hcw2]
  exact hω₁

private theorem exists_coeff_of_line (halt : F.IsAlt) {e f : V} {a : V → K} {w₀ : V}
    (hwe : F w₀ e = 0) (hwf : F w₀ f = 0) (hw₀ : w₀ ≠ 0)
    (hadd : ∀ w w' : V, F w e = 0 → F w f = 0 → F w' e = 0 → F w' f = 0 →
      a (w + w') = a w + a w' + F w w')
    (hz : ∀ w : V, F w e = 0 → F w f = 0 → w ≠ 0 → a w ≠ 0) (κ : K) :
    ∃ t : K, a (t • w₀) = κ := by
  have hinj : Function.Injective (fun t : K => a (t • w₀)) := by
    intro t t' h
    by_contra hne
    have hsub : F ((t - t') • w₀) (t' • w₀) = 0 := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_self halt, mul_zero,
        smul_zero]
    have hsum : (t - t') • w₀ + t' • w₀ = t • w₀ := by
      rw [← add_smul, sub_add_cancel]
    have h1 := hadd ((t - t') • w₀) (t' • w₀) (perp_smul hwe hwf _).1 (perp_smul hwe hwf _).2
      (perp_smul hwe hwf _).1 (perp_smul hwe hwf _).2
    rw [hsum, hsub, add_zero] at h1
    have h0 : a ((t - t') • w₀) = 0 := by
      simp only at h
      linear_combination h - h1
    exact hz _ (perp_smul hwe hwf _).1 (perp_smul hwe hwf _).2
      (smul_ne_zero (sub_ne_zero.mpr hne) hw₀) h0
  exact Finite.surjective_of_injective hinj κ

private theorem hyp_case (hnd : F.Nondegenerate) (halt : F.IsAlt) (hq : 4 ≤ Nat.card K)
    (hdim : Module.finrank K V = 4) {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : J ≤ sympSubgroup F) (hfe : ElationFull F ((J : Set _) ∩ pointRad F e) e)
    (hff : ElationFull F ((J : Set _) ∩ pointRad F f) f)
    (hTe : NoTransv F J e) (hTf : NoTransv F J f) {a a' : V → K}
    (ha1 : ∀ w, F w e = 0 → F w f = 0 → ∃ g ∈ J ⊓ pointRadSubgroup F e, g f - f = w + a w • e)
    (ha3 : ∀ w w' : V, F w e = 0 → F w f = 0 → F w' e = 0 → F w' f = 0 →
      a (w + w') = a w + a w' + F w w')
    (hb1 : ∀ w, F w e = 0 → F w f = 0 → ∃ g ∈ J ⊓ pointRadSubgroup F f, g e - e = w + a' w • f)
    (hb3 : ∀ w w' : V, F w e = 0 → F w f = 0 → F w' e = 0 → F w' f = 0 →
      a' (w + w') = a' w + a' w' + F w w')
    {w₁ : V} (hw₁e : F w₁ e = 0) (hw₁f : F w₁ f = 0) (hw₁ : w₁ ≠ 0) (hz : a w₁ = 0) :
    (∀ (c : K) (w : V), F w e = 0 → F w f = 0 → a (c • w) = c ^ 2 * a w) ∧
      ∀ w : V, F w e = 0 → F w f = 0 → a' w = a w := by
  obtain ⟨hc1a, hc1b⟩ := cone_zero hnd halt hq hef hJ hfe hff hTe hTf ha1 hb1 hw₁e hw₁f hw₁ hz
  obtain ⟨w', hw'e, hw'f, hw'1⟩ := exists_partner hnd halt hef hw₁e hw₁f hw₁
  have hF1 : F w' (a w' • w₁) = a w' := by
    rw [map_smul, form_comm halt w' w₁, hw'1, smul_eq_mul, mul_one]
  have hF12 : F w₁ (w' + a w' • w₁) = 1 := by
    rw [map_add, hw'1, map_smul, form_self halt, smul_zero, add_zero]
  obtain ⟨w₂, hw₂e, hw₂f, h12, hw₂0, hz₂⟩ : ∃ w₂ : V, F w₂ e = 0 ∧ F w₂ f = 0 ∧
      F w₁ w₂ = 1 ∧ w₂ ≠ 0 ∧ a w₂ = 0 := by
    refine ⟨w' + a w' • w₁, ?_, ?_, hF12, ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply, hw'e, (perp_smul hw₁e hw₁f (a w')).1, add_zero]
    · rw [map_add, LinearMap.add_apply, hw'f, (perp_smul hw₁e hw₁f (a w')).2, add_zero]
    · intro h0
      rw [h0, map_zero] at hF12
      exact zero_ne_one hF12
    · rw [ha3 w' (a w' • w₁) hw'e hw'f (perp_smul hw₁e hw₁f (a w')).1
        (perp_smul hw₁e hw₁f (a w')).2, hc1a (a w'), hF1]
      linear_combination (a w') * two_eq_zero_K (K := K)
  obtain ⟨hc2a, hc2b⟩ := cone_zero hnd halt hq hef hJ hfe hff hTe hTf ha1 hb1 hw₂e hw₂f hw₂0 hz₂
  have hlin_a : ∀ s t : K, a (s • w₁ + t • w₂) = s * t := by
    intro s t
    rw [ha3 _ _ (perp_smul hw₁e hw₁f s).1 (perp_smul hw₁e hw₁f s).2
      (perp_smul hw₂e hw₂f t).1 (perp_smul hw₂e hw₂f t).2, hc1a s, hc2a t]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, h12, zero_add, mul_one]
    ring
  have hlin_b : ∀ s t : K, a' (s • w₁ + t • w₂) = s * t := by
    intro s t
    rw [hb3 _ _ (perp_smul hw₁e hw₁f s).1 (perp_smul hw₁e hw₁f s).2
      (perp_smul hw₂e hw₂f t).1 (perp_smul hw₂e hw₂f t).2, hc1b s, hc2b t]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, h12, zero_add, mul_one]
    ring
  have hform_a : ∀ x : V, F x e = 0 → F x f = 0 → a x = F x w₂ * F x w₁ := by
    intro x hxe hxf
    have h := hlin_a (F x w₂) (F x w₁)
    rw [← decomp_W hnd halt hdim hef hw₁e hw₁f hw₂e hw₂f h12 hxe hxf] at h
    exact h
  have hform_b : ∀ x : V, F x e = 0 → F x f = 0 → a' x = F x w₂ * F x w₁ := by
    intro x hxe hxf
    have h := hlin_b (F x w₂) (F x w₁)
    rw [← decomp_W hnd halt hdim hef hw₁e hw₁f hw₂e hw₂f h12 hxe hxf] at h
    exact h
  refine ⟨fun c w hwe hwf => ?_, fun w hwe hwf => ?_⟩
  · rw [hform_a (c • w) (perp_smul hwe hwf c).1 (perp_smul hwe hwf c).2, hform_a w hwe hwf]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · rw [hform_b w hwe hwf, hform_a w hwe hwf]

private theorem ell_case (hnd : F.Nondegenerate) (halt : F.IsAlt) (hq : 4 ≤ Nat.card K)
    (hdim : Module.finrank K V = 4) {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : J ≤ sympSubgroup F) (hfe : ElationFull F ((J : Set _) ∩ pointRad F e) e)
    (hff : ElationFull F ((J : Set _) ∩ pointRad F f) f)
    (hTe : NoTransv F J e) {a a' : V → K}
    (ha1 : ∀ w, F w e = 0 → F w f = 0 → ∃ g ∈ J ⊓ pointRadSubgroup F e, g f - f = w + a w • e)
    (ha4 : ∀ g ∈ J ⊓ pointRadSubgroup F e, ∀ (w : V) (c : K), F w e = 0 → F w f = 0 →
      g f - f = w + c • e → c = a w)
    (ha3 : ∀ w w' : V, F w e = 0 → F w f = 0 → F w' e = 0 → F w' f = 0 →
      a (w + w') = a w + a w' + F w w')
    (hb1 : ∀ w, F w e = 0 → F w f = 0 → ∃ g ∈ J ⊓ pointRadSubgroup F f, g e - e = w + a' w • f)
    (hb4 : ∀ g ∈ J ⊓ pointRadSubgroup F f, ∀ (w : V) (c : K), F w e = 0 → F w f = 0 →
      g e - e = w + c • f → c = a' w)
    (hb3 : ∀ w w' : V, F w e = 0 → F w f = 0 → F w' e = 0 → F w' f = 0 →
      a' (w + w') = a' w + a' w' + F w w')
    (hzf : ∀ w : V, F w e = 0 → F w f = 0 → w ≠ 0 → a w ≠ 0) :
    (∀ (c : K) (w : V), F w e = 0 → F w f = 0 → a (c • w) = c ^ 2 * a w) ∧
      ∀ w : V, F w e = 0 → F w f = 0 → a' w = a w := by
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  have hee : F e e = 0 := form_self halt e
  have ha0 : a 0 = 0 := by
    have h := ha4 1 (J ⊓ pointRadSubgroup F e).one_mem 0 0 (by simp) (by simp) (by simp)
    exact h.symm
  have hb0 : a' 0 = 0 := by
    have h := hb4 1 (J ⊓ pointRadSubgroup F f).one_mem 0 0 (by simp) (by simp) (by simp)
    exact h.symm
  have hbe : ∀ g ∈ J, F (g e) e = 0 → ∃ t : K, g e = t • e := by
    intro g hg hz
    by_contra hno
    have hcne : ∀ t : K, g e ≠ t • e := fun t ht => hno ⟨t, ht⟩
    have hc : ElationFull F ((J : Set _) ∩ pointRad F (g e)) (g e) :=
      elationFull_conj hJ hfe hg
    have hcf : F (g e - F (g e) f • e) e = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hee,
        smul_zero, sub_zero, mul_zero, hz]
    have hwf : F (g e - F (g e) f • e) f = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hef,
        mul_one, sub_self]
    have hwne : g e - F (g e) f • e ≠ 0 := by
      intro h0
      exact hcne (F (g e) f) (sub_eq_zero.mp h0)
    obtain ⟨g₀, hg₀, hω₀⟩ := ha1 _ hcf hwf
    have h0 := zero_of_perp_point_smul hnd halt hq hef hJ hfe hTe hz hcne hc 1 hg₀
      (by rw [one_smul]; exact hω₀)
    exact hzf _ hcf hwf hwne h0
  obtain ⟨-, hconj⟩ := dichotomy_b1 hnd halt hdim hef hJ hff hbe
  have hzf' : ∀ w : V, F w e = 0 → F w f = 0 → w ≠ 0 → a' w ≠ 0 := by
    intro w hwe hwf hw h0
    obtain ⟨g, hg, hω⟩ := hb1 w hwe hwf
    rw [h0, zero_smul, add_zero] at hω
    have hg1 : g = 1 := hconj g hg (by rw [hω]; exact hwe)
    apply hw
    rw [← hω, hg1]
    simp
  have hhom_line : ∀ w₀ : V, F w₀ e = 0 → F w₀ f = 0 → w₀ ≠ 0 → ∀ lam : K, lam ≠ 0 →
      a (lam • w₀) = lam ^ 2 * a w₀ := by
    intro w₀ hwe hwf hw₀ lam hlam
    have hew₀ : F e w₀ = 0 := by rw [form_comm halt]; exact hwe
    have hfw₀ : F f w₀ = 0 := by rw [form_comm halt]; exact hwf
    choose tt htt using (fun κ : K => exists_coeff_of_line halt hwe hwf hw₀ ha3 hzf κ)
    choose ss hss using (fun κ : K => exists_coeff_of_line halt hwe hwf hw₀ hb3 hzf' κ)
    choose X hXJ hXf using (fun κ : K =>
      ha1 (tt κ • w₀) (perp_smul hwe hwf (tt κ)).1 (perp_smul hwe hwf (tt κ)).2)
    choose Y hYJ hYe using (fun κ : K =>
      hb1 (ss κ • w₀) (perp_smul hwe hwf (ss κ)).1 (perp_smul hwe hwf (ss κ)).2)
    simp only [htt] at hXf
    simp only [hss] at hYe
    have hXQ : ∀ κ, X κ ∈ pointRadSubgroup F e := fun κ => (Subgroup.mem_inf.mp (hXJ κ)).2
    have hYQ : ∀ κ, Y κ ∈ pointRadSubgroup F f := fun κ => (Subgroup.mem_inf.mp (hYJ κ)).2
    have hXJ' : ∀ κ, X κ ∈ J := fun κ => (Subgroup.mem_inf.mp (hXJ κ)).1
    have hYJ' : ∀ κ, Y κ ∈ J := fun κ => (Subgroup.mem_inf.mp (hYJ κ)).1
    have hXe : ∀ κ, X κ e = e := fun κ => (hXQ κ).2.1
    have hYf : ∀ κ, Y κ f = f := fun κ => (hYQ κ).2.1
    have hXw : ∀ κ, X κ w₀ = w₀ := by
      intro κ
      rw [pointRad_apply_perp halt hef (hXQ κ) w₀ hwe, hXf κ]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        form_self halt, hew₀, mul_zero, zero_smul, add_zero, smul_zero]
    have hYw : ∀ κ, Y κ w₀ = w₀ := by
      intro κ
      rw [pointRad_apply_perp halt hef' (hYQ κ) w₀ hwf, hYe κ]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        form_self halt, hfw₀, mul_zero, zero_smul, add_zero, smul_zero]
    have hYe' : ∀ κ, Y κ e = e + (ss κ • w₀ + κ • f) := fun κ => by
      rw [← hYe κ]
      abel
    have hXf' : ∀ κ, X κ f = f + (tt κ • w₀ + κ • e) := fun κ => by
      rw [← hXf κ]
      abel
    have hnw : ∀ κ : K, (X κ * Y κ⁻¹ * X κ) w₀ = w₀ := by
      intro κ
      simp only [LinearEquiv.mul_apply, hXw, hYw]
    have hn_e : ∀ κ : K, κ ≠ 0 →
        (X κ * Y κ⁻¹ * X κ) e = κ⁻¹ • f + (ss κ⁻¹ + κ⁻¹ * tt κ) • w₀ := by
      intro κ hκ
      have hk : (κ⁻¹ * κ) • e = e := by rw [inv_mul_cancel₀ hκ, one_smul]
      simp only [LinearEquiv.mul_apply, hXe, hYe', map_add, map_smul, hXw, hXf']
      linear_combination (norm := module) hk + two_smul_zero_K (K := K) e
    have hn_f : ∀ κ : K, κ ≠ 0 →
        (X κ * Y κ⁻¹ * X κ) f = κ • e + (tt κ + κ * ss κ⁻¹) • w₀ := by
      intro κ hκ
      have hk : (κ * κ⁻¹) • (f + (tt κ • w₀ + κ • e)) = f + (tt κ • w₀ + κ • e) := by
        rw [mul_inv_cancel₀ hκ, one_smul]
      simp only [LinearEquiv.mul_apply, hXf', map_add, map_smul, hYf, hYw, hYe', hXe, hXw]
      linear_combination (norm := module) hk + two_smul_zero_K (K := K) f
        + tt κ • two_smul_zero_K (K := K) w₀ + κ • two_smul_zero_K (K := K) e
    obtain ⟨h, hh⟩ : ∃ h : V ≃ₗ[K] V,
        h = (X lam * Y lam⁻¹ * X lam) * (X 1 * Y 1⁻¹ * X 1) := ⟨_, rfl⟩
    have hhJ : h ∈ J := by
      rw [hh]
      exact J.mul_mem (J.mul_mem (J.mul_mem (hXJ' lam) (hYJ' lam⁻¹)) (hXJ' lam))
        (J.mul_mem (J.mul_mem (hXJ' 1) (hYJ' 1⁻¹)) (hXJ' 1))
    have hhw : h w₀ = w₀ := by
      rw [hh, LinearEquiv.mul_apply, hnw, hnw]
    have he_eq : h e = lam • e + ((tt lam + lam * ss lam⁻¹) + (ss 1⁻¹ + 1⁻¹ * tt 1)) • w₀ := by
      rw [hh, LinearEquiv.mul_apply, hn_e 1 one_ne_zero, map_add, map_smul, map_smul,
        hn_f lam hlam, hnw]
      simp only [inv_one, one_smul]
      module
    have hFh : F (h e) e = 0 := by
      rw [he_eq]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hee,
        hwe, mul_zero, add_zero, smul_zero, zero_add]
    obtain ⟨τ, hτ⟩ := hbe h hhJ hFh
    have hτl : τ = lam := by
      have h1 : lam • e + ((tt lam + lam * ss lam⁻¹) + (ss 1⁻¹ + 1⁻¹ * tt 1)) • w₀ = τ • e := by
        rw [← he_eq, hτ]
      have h2 := congrArg (fun v => F v f) h1
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hef,
        hwf, mul_one, mul_zero, add_zero] at h2
      first | exact h2.symm | exact h2
    have hhe : h e = lam • e := by rw [hτ, hτl]
    obtain ⟨g, hgJQ, hgω⟩ := ha1 w₀ hwe hwf
    have hcon := conj_pointRad_om halt hef (hJ hhJ) hhe (Subgroup.mem_inf.mp hgJQ).2 hgω hwf
      (show h w₀ = (1 : K) • w₀ + (0 : K) • e by rw [hhw, one_smul, zero_smul, add_zero])
    have hmemJ : h * g * h⁻¹ ∈ J ⊓ pointRadSubgroup F e :=
      Subgroup.mem_inf.mpr ⟨J.mul_mem (J.mul_mem hhJ (Subgroup.mem_inf.mp hgJQ).1) (J.inv_mem hhJ),
        hcon.1⟩
    have h4 := ha4 _ hmemJ (lam • w₀) (lam ^ 2 * a w₀) (perp_smul hwe hwf lam).1
      (perp_smul hwe hwf lam).2 (by rw [hcon.2, mul_one])
    exact h4.symm
  have hhom : ∀ (c : K) (w : V), F w e = 0 → F w f = 0 → a (c • w) = c ^ 2 * a w := by
    intro c w hwe hwf
    by_cases hw0 : w = 0
    · subst hw0
      simp [ha0]
    · by_cases hc0 : c = 0
      · subst hc0
        simp [ha0]
      · exact hhom_line w hwe hwf hw0 c hc0
  refine ⟨hhom, fun w hwe hwf => ?_⟩
  by_cases hw0 : w = 0
  · subst hw0
    rw [ha0, hb0]
  have hb : a' w ≠ 0 := hzf' w hwe hwf hw0
  obtain ⟨y, hyJ, hyω⟩ := hb1 w hwe hwf
  have hew : F e w = 0 := by rw [form_comm halt]; exact hwe
  have hfw : F f w = 0 := by rw [form_comm halt]; exact hwf
  have hbinv : a' w * (a' w)⁻¹ = 1 := mul_inv_cancel₀ hb
  have hbu : a' w • (a' w)⁻¹ • w = w := by rw [smul_smul, hbinv, one_smul]
  obtain ⟨ι, hιdef⟩ : ∃ ι : K, ι = (a' w)⁻¹ + a ((a' w)⁻¹ • w) := ⟨_, rfl⟩
  have hι : ι = 0 := by
    by_contra hι0
    obtain ⟨t, ht⟩ := exists_coeff_of_line halt hwe hwf hw0 ha3 hzf ι
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hι0
      rw [zero_smul, ha0] at ht
      exact ht.symm
    have htw : t • w ≠ 0 := smul_ne_zero ht0 hw0
    obtain ⟨x₁, hx₁J, hx₁ω⟩ := ha1 (t • w) (perp_smul hwe hwf t).1 (perp_smul hwe hwf t).2
    rw [ht] at hx₁ω
    obtain ⟨w₂, hw₂e, hw₂f, hw₂1⟩ := exists_partner hnd halt hef (perp_smul hwe hwf t).1
      (perp_smul hwe hwf t).2 htw
    obtain ⟨y₁, hy₁J, hy₁ω⟩ := hb1 w₂ hw₂e hw₂f
    obtain ⟨x, hxJ, hxω⟩ := ha1 ((a' w)⁻¹ • w) (perp_smul hwe hwf _).1 (perp_smul hwe hwf _).2
    have hxQ := (Subgroup.mem_inf.mp hxJ).2
    have hx₁Q := (Subgroup.mem_inf.mp hx₁J).2
    have hy₁Q := (Subgroup.mem_inf.mp hy₁J).2
    have hyQ := (Subgroup.mem_inf.mp hyJ).2
    have hyJ' := (Subgroup.mem_inf.mp hyJ).1
    have hxJ' := (Subgroup.mem_inf.mp hxJ).1
    have hx₁J' := (Subgroup.mem_inf.mp hx₁J).1
    have hy₁J' := (Subgroup.mem_inf.mp hy₁J).1
    have hye : y e = e + (w + a' w • f) := by rw [← hyω]; abel
    have hxw : x w = w := by
      rw [pointRad_apply_perp halt hef hxQ w hwe, hxω]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        form_self halt, hew, mul_zero, zero_smul, add_zero, smul_zero]
    have hxe : x e = e := hxQ.2.1
    have hxf : x f = f + ((a' w)⁻¹ • w + a ((a' w)⁻¹ • w) • e) := by
      rw [← hxω]
      abel
    have hx₁f : x₁ f = f + (t • w + ι • e) := by
      rw [← hx₁ω]
      abel
    have hx₁chain : x₁ (f + ι • e) = f + t • w := by
      rw [map_add, map_smul, hx₁Q.2.1, hx₁f]
      linear_combination (norm := module) ι • two_smul_zero_K (K := K) e
    have hxye : x (y e) = a' w • (f + ι • e) := by
      rw [hye, map_add, map_add, map_smul, hxe, hxw, hxf, hιdef]
      have hbinv_e : (a' w * (a' w)⁻¹) • e = e := by rw [hbinv, one_smul]
      linear_combination (norm := module) hbu + two_smul_zero_K (K := K) w - hbinv_e
    have hvf : F (f + t • w) f = 0 := by
      rw [map_add, LinearMap.add_apply, form_self halt, (perp_smul hwe hwf t).2, zero_add]
    have hF9 : t * F w₂ w = 1 := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, form_comm halt w w₂] at hw₂1
      exact hw₂1
    have hF8 : F (w₂ + a' w₂ • f) (f + t • w) = 1 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hw₂f, form_self halt, hfw, mul_zero, zero_add, add_zero]
      linear_combination hF9
    have hy₁f : y₁ (f + t • w) = t • w := by
      rw [pointRad_apply_perp halt hef' hy₁Q (f + t • w) hvf, hy₁ω, hF8, one_smul,
        add_right_comm, vec_add_self K f, zero_add]
    have hge : (y₁ * x₁ * x * y) e = a' w • (t • w) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxye, map_smul,
        hx₁chain, map_smul, hy₁f]
    have hgJ : y₁ * x₁ * x * y ∈ J := J.mul_mem (J.mul_mem (J.mul_mem hy₁J' hx₁J') hxJ') hyJ'
    have hFg : F ((y₁ * x₁ * x * y) e) e = 0 := by
      rw [hge]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hwe, mul_zero, smul_zero]
    obtain ⟨τ', hτ'⟩ := hbe _ hgJ hFg
    rw [hge] at hτ'
    have hτ0 : τ' = 0 := by
      have h1 := congrArg (fun v => F v f) hτ'
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hwf, hef, mul_one, mul_zero,
        smul_zero] at h1
      first | exact h1.symm | exact h1
    rw [hτ0, zero_smul] at hτ'
    rcases smul_eq_zero.mp hτ' with h | h
    · exact hb h
    · rcases smul_eq_zero.mp h with h' | h'
      · exact ht0 h'
      · exact hw0 h'
  have hι2 : (a' w)⁻¹ + a ((a' w)⁻¹ • w) = 0 := by
    rw [← hιdef]
    exact hι
  have hu := hhom (a' w)⁻¹ w hwe hwf
  rw [hu] at hι2
  have key : a' w + a w = 0 := by
    linear_combination (a' w) ^ 2 * hι2 - (a' w + a w * ((a' w)⁻¹ * a' w + 1)) * hbinv
  linear_combination key + (-(a w)) * two_eq_zero_K (K := K)

private theorem elationFull_of_le {A J : Subgroup (V ≃ₗ[K] V)} {e : V} (hAJ : A ≤ J)
    (hA : (A : Set (V ≃ₗ[K] V)) ⊆ pointRad F e) (hfull : ElationFull F A e) :
    ElationFull F ((J : Set _) ∩ pointRad F e) e := by
  intro φ hφ
  obtain ⟨g, hgA, hg⟩ := hfull φ hφ
  exact ⟨g, ⟨hAJ hgA, hA hgA⟩, hg⟩

theorem aData_of_noTransv (hnd : F.Nondegenerate) (halt : F.IsAlt) (hq : 4 ≤ Nat.card K)
    (hdim : Module.finrank K V = 4) {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : J ≤ sympSubgroup F) (hfe : ElationFull F ((J : Set _) ∩ pointRad F e) e)
    (hff : ElationFull F ((J : Set _) ∩ pointRad F f) f) (hTe : NoTransv F J e)
    (hTf : NoTransv F J f) : ∃ a : V → K, AData F J e f a := by
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  obtain ⟨a, ha1, ha4, ha3⟩ := coord_data hnd halt hef hTe hfe
  obtain ⟨a', hb1', hb4', hb3'⟩ := coord_data hnd halt hef' hTf hff
  have hb1 : ∀ w, F w e = 0 → F w f = 0 →
      ∃ g ∈ J ⊓ pointRadSubgroup F f, g e - e = w + a' w • f :=
    fun w hwe hwf => hb1' w hwf hwe
  have hb4 : ∀ g ∈ J ⊓ pointRadSubgroup F f, ∀ (w : V) (c : K), F w e = 0 → F w f = 0 →
      g e - e = w + c • f → c = a' w :=
    fun g hg w c hwe hwf h => hb4' g hg w c hwf hwe h
  have hb3 : ∀ w w' : V, F w e = 0 → F w f = 0 → F w' e = 0 → F w' f = 0 →
      a' (w + w') = a' w + a' w' + F w w' :=
    fun w w' hwe hwf hwe' hwf' => hb3' w w' hwf hwe hwf' hwe'
  by_cases hz : ∃ w₁ : V, F w₁ e = 0 ∧ F w₁ f = 0 ∧ w₁ ≠ 0 ∧ a w₁ = 0
  · obtain ⟨w₁, h1, h2, h3, h4⟩ := hz
    obtain ⟨hhom, heq⟩ :=
      hyp_case hnd halt hq hdim hef hJ hfe hff hTe hTf ha1 ha3 hb1 hb3 h1 h2 h3 h4
    exact ⟨a, ha1, hhom, ha3, ha4, fun g hg w c hwe hwf hc =>
      (hb4 g hg w c hwe hwf hc).trans (heq w hwe hwf)⟩
  · push Not at hz
    obtain ⟨hhom, heq⟩ := ell_case hnd halt hq hdim hef hJ hfe hff hTe ha1 ha4 ha3 hb1 hb4 hb3 hz
    exact ⟨a, ha1, hhom, ha3, ha4, fun g hg w c hwe hwf hc =>
      (hb4 g hg w c hwe hwf hc).trans (heq w hwe hwf)⟩

private theorem hasTransv_conj (halt : F.IsAlt) {e : V} {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : J ≤ sympSubgroup F) {k : V ≃ₗ[K] V} (hk : k ∈ J) {lam : K}
    (hke : k e = lam • e) {c : K} (hc : HasTransv F J e c) : HasTransv F J e (lam ^ 2 * c) := by
  obtain ⟨g₀, hg₀J, hg₀⟩ := hc
  refine ⟨k * g₀ * k⁻¹, J.mul_mem (J.mul_mem hk hg₀J) (J.inv_mem hk), fun v => ?_⟩
  have hk' : IsIsom F k := hJ hk
  have h1 := hk' (k⁻¹ v) e
  rw [show k (k⁻¹ v) = v by simp, hke] at h1
  simp only [map_smul, smul_eq_mul] at h1
  simp only [LinearEquiv.mul_apply]
  rw [hg₀ (k⁻¹ v), map_add, map_smul, hke, show k (k⁻¹ v) = v by simp, ← h1]
  congr 1
  rw [smul_smul]
  congr 1
  ring

theorem transv_full (hnd : F.Nondegenerate) (halt : F.IsAlt) (hq : 4 ≤ Nat.card K)
    (hdim : Module.finrank K V = 4) {e f : V} (hef : F e f = 1) {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : J ≤ sympSubgroup F) (hfe : ElationFull F ((J : Set _) ∩ pointRad F e) e)
    (hff : ElationFull F ((J : Set _) ∩ pointRad F f) f) {c₀ : K} (hc₀ : c₀ ≠ 0)
    (h : HasTransv F J e c₀) : ∀ c : K, HasTransv F J e c := by
  have hA : ∃ g ∈ J, F (g e) e = 0 ∧ ∀ t : K, g e ≠ t • e := by
    by_contra hA
    have hb : ∀ g ∈ J, F (g e) e = 0 → ∃ t : K, g e = t • e := fun g hg hz => by
      by_contra hno
      exact hA ⟨g, hg, hz, fun t ht => hno ⟨t, ht⟩⟩
    have hb2 := dichotomy_b2 hnd halt hq hdim hef hJ hff hb
    exact hc₀ ((dichotomy_b3 hnd halt hdim hef hJ hfe hb2).1 c₀ h)
  obtain ⟨g, hgJ, hgz, hgn⟩ := hA
  have he0 : e ≠ 0 := ne_zero_of_form_eq_one hef
  have hli : LinearIndependent K ![e, g e] :=
    (LinearIndependent.pair_iff' he0).mpr (fun t ht => hgn t ht.symm)
  have hc_full : ElationFull F ((J : Set _) ∩ pointRad F (g e)) (g e) :=
    elationFull_conj hJ hfe hgJ
  have hdiag : ∀ s : K, s ≠ 0 → ∃ k ∈ J, k e = s • e := fun s hs => by
    obtain ⟨k, hk, hke, -⟩ := exists_diag_of_perp halt hgz hli hfe hc_full hs
    exact ⟨k, hk, hke⟩
  intro c
  by_cases hc : c = 0
  · subst hc
    exact ⟨1, J.one_mem, fun v => by simp⟩
  · obtain ⟨lam, hlam⟩ := sq_surj_K (c * c₀⁻¹)
    have hlam0 : lam ≠ 0 := by
      intro h0
      apply hc
      have h1 : c * c₀⁻¹ = 0 := by rw [← hlam, h0, zero_pow two_ne_zero]
      exact (mul_eq_zero.mp h1).resolve_right (inv_ne_zero hc₀)
    obtain ⟨k, hk, hke⟩ := hdiag lam hlam0
    have hcc := hasTransv_conj halt hJ hk hke h
    have hc' : lam ^ 2 * c₀ = c := by
      rw [hlam]
      field_simp
    rw [hc'] at hcc
    exact hcc

theorem lemmaP_sharp (hnd : F.Nondegenerate) (halt : F.IsAlt) (hq : 4 ≤ Nat.card K)
    (hdim : Module.finrank K V = 4) {e f : V} (hef : F e f = 1) (A A' : Subgroup (V ≃ₗ[K] V))
    (hA : (A : Set _) ⊆ pointRad F e) (hA' : (A' : Set _) ⊆ pointRad F f)
    (hfull : ElationFull F A e) (hfull' : ElationFull F A' f) :
    (∀ c : K, HasTransv F (A ⊔ A') e c) ∨ (∀ c : K, HasTransv F (A ⊔ A') f c) ∨
      ∃ Qf : QuadraticForm K V, Qf.polarBilin = F ∧ Qf e = 0 ∧ Qf f = 0 ∧
        A ≤ orthSubgroup Qf ∧ A' ≤ orthSubgroup Qf := by
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  have hAs : A ≤ sympSubgroup F := fun g hg => pointRadSubgroup_le_symp e (hA hg)
  have hA's : A' ≤ sympSubgroup F := fun g hg => pointRadSubgroup_le_symp f (hA' hg)
  have hJ : A ⊔ A' ≤ sympSubgroup F := sup_le hAs hA's
  have hfeJ := elationFull_of_le (J := A ⊔ A') le_sup_left hA hfull
  have hffJ := elationFull_of_le (J := A ⊔ A') le_sup_right hA' hfull'
  by_cases h1 : NoTransv F (A ⊔ A') e
  · by_cases h2 : NoTransv F (A ⊔ A') f
    · right
      right
      obtain ⟨a, ha⟩ := aData_of_noTransv hnd halt hq hdim hef hJ hfeJ hffJ h1 h2
      obtain ⟨Q, hQ, hQe, hQf, hQA, hQA'⟩ := exists_quadForm_of_aData halt hef ha
      exact ⟨Q, hQ, hQe, hQf,
        fun g hg => hQA (Subgroup.mem_inf.mpr ⟨(le_sup_left : A ≤ A ⊔ A') hg, hA hg⟩),
        fun g hg => hQA' (Subgroup.mem_inf.mpr ⟨(le_sup_right : A' ≤ A ⊔ A') hg, hA' hg⟩)⟩
    · right
      left
      unfold NoTransv at h2
      push Not at h2
      obtain ⟨c, hc, hc0⟩ := h2
      exact transv_full hnd halt hq hdim hef' hJ hffJ hfeJ hc0 hc
  · left
    unfold NoTransv at h1
    push Not at h1
    obtain ⟨c, hc, hc0⟩ := h1
    exact transv_full hnd halt hq hdim hef hJ hfeJ hffJ hc0 hc

private theorem span_elPts (hnd : F.Nondegenerate) (halt : F.IsAlt) {e f : V} (hef : F e f = 1)
    {J : Subgroup (V ≃ₗ[K] V)} (hJ : J ≤ sympSubgroup F)
    (hfeJ : ElationFull F ((J : Set _) ∩ pointRad F e) e)
    (hffJ : ElationFull F ((J : Set _) ∩ pointRad F f) f) :
    Submodule.span K (ElPts F J) = ⊤ := by
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  have he : e ∈ ElPts F J := ⟨ne_zero_of_form_eq_one hef, hfeJ⟩
  have hf : f ∈ ElPts F J := ⟨ne_zero_of_form_eq_one hef', hffJ⟩
  have hSe : e ∈ Submodule.span K (ElPts F J) := Submodule.subset_span he
  have hSf : f ∈ Submodule.span K (ElPts F J) := Submodule.subset_span hf
  have hperp : ∀ w : V, F w e = 0 → w ∈ Submodule.span K (ElPts F J) := by
    intro w hw
    obtain ⟨g, hgD, c, hc⟩ := ElationFull.om hnd halt hef Set.inter_subset_right hfeJ hw
    have hgJ : g ∈ J := hgD.1
    have hgf : g f ∈ Submodule.span K (ElPts F J) :=
      Submodule.subset_span (ElPts_invariant hJ hgJ hf)
    have hce : c • e ∈ Submodule.span K (ElPts F J) := Submodule.smul_mem _ c hSe
    have hw' : w = (g f - f) - c • e := by
      rw [hc]
      abel
    rw [hw']
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hgf hSf) hce
  rw [eq_top_iff]
  intro v _
  have hw : F (v - F v e • f) e = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hef',
      mul_one, sub_self]
  have key := Submodule.add_mem _ (Submodule.smul_mem _ (F v e) hSf) (hperp _ hw)
  simpa using key

theorem lemmaP_of_mcLaughlin (hMcL : McLaughlinStatement) : LemmaPStatement := by
  intro K V _ _ _ _ _ _ F hq hnd halt hdim e f hef A A' hA hA' hfull hfull'
  have hdim' : 4 ≤ Module.finrank K V := hdim.ge
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  have hAs : A ≤ sympSubgroup F := fun g hg => pointRadSubgroup_le_symp e (hA hg)
  have hA's : A' ≤ sympSubgroup F := fun g hg => pointRadSubgroup_le_symp f (hA' hg)
  have hJ : A ⊔ A' ≤ sympSubgroup F := sup_le hAs hA's
  have hfeJ := elationFull_of_le (J := A ⊔ A') (le_sup_left : A ≤ A ⊔ A') hA hfull
  have hffJ := elationFull_of_le (J := A ⊔ A') (le_sup_right : A' ≤ A ⊔ A') hA' hfull'
  have hP0 : ∀ g ∈ ElPts F (A ⊔ A'), g ≠ 0 := fun g hg => hg.1
  rcases lemmaP_sharp hnd halt hq hdim hef A A' hA hA' hfull hfull' with hT | hT | hQ
  · left
    exact eq_symp_of_transvection_point
      (fun hnd halt hq hdim X hX Y hY0 htr hgen hirr =>
        eq_symp_of_transvections hMcL hnd halt hq hdim X hX Y hY0 htr hgen hirr)
      hnd halt hq hdim' hJ (P := ElPts F (A ⊔ A')) hP0 (fun g hg => hg.2)
      (span_elPts hnd halt hef hJ hfeJ hffJ) (⟨ne_zero_of_form_eq_one hef, hfeJ⟩ :
        e ∈ ElPts F (A ⊔ A')) hT
  · left
    exact eq_symp_of_transvection_point
      (fun hnd halt hq hdim X hX Y hY0 htr hgen hirr =>
        eq_symp_of_transvections hMcL hnd halt hq hdim X hX Y hY0 htr hgen hirr)
      hnd halt hq hdim' hJ (P := ElPts F (A ⊔ A')) hP0 (fun g hg => hg.2)
      (span_elPts hnd halt hef' hJ hffJ hfeJ) (⟨ne_zero_of_form_eq_one hef', hffJ⟩ :
        f ∈ ElPts F (A ⊔ A')) hT
  · right
    exact hQ

end CFSG.RankThree.GF2n.Stroth80.Classify

namespace CFSG.RankThree.GF2n.Stroth80

theorem stroth310Classify_of_mcLaughlin (h34 : Stroth34Statement)
    (hMcL : McLaughlinStatement) (hSiegel : Classify.SiegelGenStatement) :
    Stroth310ClassifyStatement :=
  stroth310Classify_of_inputs h34 hMcL (Classify.lemmaP_of_mcLaughlin hMcL) hSiegel

end CFSG.RankThree.GF2n.Stroth80
