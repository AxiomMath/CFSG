module

public import CFSG.RankThree.PartOne.LIT.McSpMixed

public section

namespace CFSG.RankThree.PartOne.LIT

open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {H : Subgroup (V ≃ₗ[ZMod p] V)} {U L : Submodule (ZMod p) V}
  {ωU ωL : LinearMap.BilinForm (ZMod p) V}

private theorem exists_mem_notMem_span_pair_of_finrank_two
    (hU : Module.finrank (ZMod p) U = 2) {a b : V} (ha : a ∈ U) (hb : b ∈ U) (ha0 : a ≠ 0) :
    ∃ c ∈ U, c ∉ Submodule.span (ZMod p) {a} ∧ c ∉ Submodule.span (ZMod p) {b} := by
  obtain ⟨w, hwU, hw⟩ : ∃ w ∈ U, w ∉ Submodule.span (ZMod p) {a} := by
    by_contra hno
    push Not at hno
    have h1 := Submodule.finrank_mono (show U ≤ Submodule.span (ZMod p) {a} from hno)
    rw [finrank_span_singleton ha0, hU] at h1
    omega
  by_cases hba : b ∈ Submodule.span (ZMod p) {a}
  · refine ⟨w, hwU, hw, fun hwb => hw ?_⟩
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hwb
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hba
    exact Submodule.mem_span_singleton.mpr ⟨s * t, by rw [mul_smul, ht, hs]⟩
  · refine ⟨a + b, U.add_mem ha hb, fun h => hba ?_, fun h => hba ?_⟩
    · have : b = (a + b) - a := by abel
      rw [this]
      exact Submodule.sub_mem _ h (Submodule.mem_span_singleton_self a)
    · obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp h
      have has : a = (s - 1) • b := by rw [sub_smul, hs, one_smul]; abel
      by_cases hs1 : s - 1 = 0
      · rw [hs1, zero_smul] at has
        exact absurd has ha0
      · refine Submodule.mem_span_singleton.mpr ⟨(s - 1)⁻¹, ?_⟩
        rw [has, smul_smul, inv_mul_cancel₀ hs1, one_smul]

private structure FormMixed {H : Subgroup (V ≃ₗ[ZMod p] V)} {U L : Submodule (ZMod p) V}
    (hF : IsFrame H U L) (ωU ωL : LinearMap.BilinForm (ZMod p) V) (x : V)
    (h : Module.Dual (ZMod p) V) (lam mu : ZMod p) : Prop where
  trIn : TrIn H x h
  ne_zero : h ≠ 0
  projU_ne : hF.projU x ≠ 0
  projL_ne : hF.projL x ≠ 0
  shape : ∀ w, h w = lam * ωU x w + mu * ωL x w
  lam_ne : lam ≠ 0
  mu_ne : mu ≠ 0

private theorem PlaneForms.exists_form_mixed_data (hP : PlaneForms ωU ωL U L)
    (hua : HasUniqueAxes H) (hF : IsFrame H U L) {x : V} {h : Module.Dual (ZMod p) V}
    (hxh : TrIn H x h) (hh : h ≠ 0) (hxU : hF.projU x ≠ 0) (hxL : hF.projL x ≠ 0) :
    ∃ lam mu, FormMixed hF ωU ωL x h lam mu := by
  have hx0 : x ≠ 0 := fun h0 => hxU (by rw [h0, map_zero])
  obtain ⟨lam, mu, hshape, hlam, hmu⟩ := hua.shape_of_planeForms hF hP hx0 hh hxh
  exact ⟨lam, mu, ⟨hxh, hh, hxU, hxL, hshape, hlam hxU, hmu hxL⟩⟩

private theorem PlaneForms.exists_form_center (hP : PlaneForms ωU ωL U L) (hF : IsFrame H U L)
    {x y : V} (hxU : hF.projU x ≠ 0) (hyU : hF.projU y ≠ 0) :
    ∃ c ∈ U, ωU c y ≠ 0 ∧ ωU x c ≠ 0 := by
  obtain ⟨c, hcU, hcx, hcy⟩ :=
    exists_mem_notMem_span_pair_of_finrank_two hF.2.1 (hF.projU_mem x) (hF.projU_mem y) hxU
  refine ⟨c, hcU, fun h0 => hcy ?_, fun h0 => hcx ?_⟩
  · refine hP.kerU _ (hF.projU_mem y) hyU c hcU ?_
    have h1 : ωU c y = ωU c (hF.projU y) := hP.right_projU hF c y
    have h2 : -ωU c (hF.projU y) = ωU (hF.projU y) c := hP.altU.neg_eq c _
    rw [← h2, ← h1, h0, neg_zero]
  · refine hP.kerU _ (hF.projU_mem x) hxU c hcU ?_
    rw [← hP.left_projU hF x c]
    exact h0

private theorem PlaneForms.exists_form_conj (hP : PlaneForms ωU ωL U L) (hF : IsFrame H U L)
    {c : V} (hc : c ∈ U) (s : ZMod p) :
    ∃ τ ∈ H, (∀ z, τ z = z + (s * ωU c z) • c) ∧ ∀ z, τ.symm z = z - (s * ωU c z) • c := by
  have hfc : (s • ωU c) c = 0 := by simp [hP.altU.self_eq_zero c]
  obtain ⟨-, τ, hτ, hτx⟩ := (hP.trIn_axisU hF hc).smul s
  refine ⟨τ, hτ, fun z => ?_, fun z => ?_⟩
  · rw [hτx z, LinearMap.smul_apply, smul_eq_mul]
  · have := TrIn.inv_apply hfc hτx z
    rw [LinearMap.smul_apply, smul_eq_mul] at this
    exact this

private theorem PlaneForms.form_mu_mul_lam_eq (hP : PlaneForms ωU ωL U L) (hua : HasUniqueAxes H)
    (hF : IsFrame H U L) {x y : V} {h₁ h₂ : Module.Dual (ZMod p) V}
    {lam₁ mu₁ lam₂ mu₂ : ZMod p} (N₁ : FormMixed hF ωU ωL x h₁ lam₁ mu₁)
    (N₂ : FormMixed hF ωU ωL y h₂ lam₂ mu₂) (hC : ωL x y ≠ 0) : mu₁ * lam₂ = mu₂ * lam₁ := by
  have hx0 : x ≠ 0 := fun h => N₁.projU_ne (by rw [h, map_zero])
  have hy0 : y ≠ 0 := fun h => N₂.projU_ne (by rw [h, map_zero])
  obtain ⟨c, hcU, hcy, hxc⟩ := hP.exists_form_center hF N₁.projU_ne N₂.projU_ne
  have hD : ωU c y * ωU x c ≠ 0 := mul_ne_zero hcy hxc
  obtain ⟨s, hs⟩ : ∃ s : ZMod p,
      lam₁ * (ωU x y + s * (ωU c y * ωU x c)) + mu₁ * ωL x y = 0 :=
    ⟨(-(mu₁ * ωL x y) / lam₁ - ωU x y) / (ωU c y * ωU x c), by
      have := N₁.lam_ne
      field_simp
      ring⟩
  obtain ⟨τ, hτ, hτx, hτinv⟩ := hP.exists_form_conj hF hcU s
  have hconj : TrIn H (τ y) (h₂ ∘ₗ τ.symm.toLinearMap) := N₂.trIn.conj hτ
  have hτy0 : τ y ≠ 0 := fun h => hy0 (τ.injective (by rw [h, map_zero]))
  have hf0 : h₂ ∘ₗ τ.symm.toLinearMap ≠ 0 := by
    intro h0
    apply N₂.ne_zero
    ext w
    simpa using LinearMap.congr_fun h0 (τ w)
  have e1 : h₁ (τ y) = 0 := by
    rw [N₁.shape, hτx y]
    simp only [map_add, map_smul, smul_eq_mul, hP.vanishL_right x c hcU]
    linear_combination hs
  have e2 := (hua.reciprocal hx0 hτy0 N₁.ne_zero hf0 N₁.trIn hconj).mp e1
  have e3 : (h₂ ∘ₗ τ.symm.toLinearMap) x
      = -(lam₂ * (ωU x y + s * (ωU c y * ωU x c)) + mu₂ * ωL x y) := by
    have n1 : ωU y x = -ωU x y := (hP.altU.neg_eq x y).symm
    have n2 : ωL y x = -ωL x y := (hP.altL.neg_eq x y).symm
    have n3 : ωU c x = -ωU x c := (hP.altU.neg_eq x c).symm
    have n4 : ωU y c = -ωU c y := (hP.altU.neg_eq c y).symm
    have n5 : ωL y c = 0 := hP.vanishL_right y c hcU
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hτinv x, map_sub, map_smul, N₂.shape x, N₂.shape c, n1, n2, n3, n4, n5, smul_eq_mul]
    ring
  rw [e3, neg_eq_zero] at e2
  have e4 : ωL x y * (mu₁ * lam₂ - mu₂ * lam₁) = 0 := by
    linear_combination lam₂ * hs - lam₁ * e2
  exact sub_eq_zero.mp ((mul_eq_zero.mp e4).resolve_left hC)

private theorem PlaneForms.form_omegaL_eq_zero_iff (hP : PlaneForms ωU ωL U L)
    (hF : IsFrame H U L) {x y : V} (hx : hF.projL x ≠ 0) :
    ωL x y = 0 ↔ hF.projL y ∈ Submodule.span (ZMod p) {hF.projL x} := by
  have key : ωL x y = ωL (hF.projL x) (hF.projL y) := by
    rw [hP.left_projL hF x y, hP.right_projL hF (hF.projL x) y]
  rw [key]
  constructor
  · exact hP.kerL _ (hF.projL_mem x) hx _ (hF.projL_mem y)
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    rw [← ha, map_smul, hP.altL.self_eq_zero, smul_zero]

private theorem PlaneForms.exists_form_kappa (hP : PlaneForms ωU ωL U L)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hua : HasUniqueAxes H) (hF : IsFrame H U L) :
    ∃ κ : ZMod p, κ ≠ 0 ∧ ∀ {x h lam mu}, FormMixed hF ωU ωL x h lam mu → mu = κ * lam := by
  obtain ⟨x₀, h₀, hxh₀, hh₀, hxU₀, hxL₀⟩ := HasUniqueAxes.exists_mixed H hirr hgen hua hF
  obtain ⟨lam₀, mu₀, N₀⟩ := hP.exists_form_mixed_data hua hF hxh₀ hh₀ hxU₀ hxL₀
  refine ⟨mu₀ / lam₀, div_ne_zero N₀.mu_ne N₀.lam_ne, fun {x h lam mu} N => ?_⟩
  have key : mu * lam₀ = mu₀ * lam := by
    by_cases hC : ωL x x₀ = 0
    · have hmem := (hP.form_omegaL_eq_zero_iff hF N.projL_ne).mp hC
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
      obtain ⟨x₁, h₁, hxh₁, hh₁, hxU₁, hxL₁, hnot⟩ :=
        HasUniqueAxes.exists_mixed_projL_notMem_span H hirr hgen hua hF (hF.projL_mem x)
      obtain ⟨lam₁, mu₁, N₁⟩ := hP.exists_form_mixed_data hua hF hxh₁ hh₁ hxU₁ hxL₁
      have hC1 : ωL x x₁ ≠ 0 := fun h0 => hnot ((hP.form_omegaL_eq_zero_iff hF N.projL_ne).mp h0)
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ha
        exact N₀.projL_ne ha.symm
      have hC2 : ωL x₀ x₁ ≠ 0 := by
        rw [hP.left_projL hF x₀ x₁, ← ha, map_smul, LinearMap.smul_apply, smul_eq_mul,
          ← hP.left_projL hF x x₁]
        exact mul_ne_zero ha0 hC1
      have k1 := hP.form_mu_mul_lam_eq hua hF N N₁ hC1
      have k2 := hP.form_mu_mul_lam_eq hua hF N₀ N₁ hC2
      have k3 : lam₁ * (mu * lam₀ - mu₀ * lam) = 0 := by
        linear_combination lam₀ * k1 - lam * k2
      exact sub_eq_zero.mp ((mul_eq_zero.mp k3).resolve_left N₁.lam_ne)
    · exact hP.form_mu_mul_lam_eq hua hF N N₀ hC
  rw [div_mul_eq_mul_div, eq_div_iff N₀.lam_ne]
  exact key

private theorem PlaneForms.form_separatingLeft (hP : PlaneForms ωU ωL U L) (hF : IsFrame H U L)
    {κ : ZMod p} (hκ : κ ≠ 0) (y : V) (hy : ∀ z, ωU y z + κ * ωL y z = 0) : y = 0 := by
  have hU0 : hF.projU y = 0 := by
    by_contra hne
    obtain ⟨z, hz, hzne⟩ := hP.nondegU _ (hF.projU_mem y) hne
    apply hzne
    rw [← hP.left_projU hF y z]
    have := hy z
    rwa [hP.vanishL_right y z hz, mul_zero, add_zero] at this
  have hL0 : hF.projL y = 0 := by
    by_contra hne
    obtain ⟨z, hz, hzne⟩ := hP.nondegL _ (hF.projL_mem y) hne
    apply hzne
    rw [← hP.left_projL hF y z]
    have := hy z
    rw [hP.vanishU_right y z hz, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_left hκ
  rw [← hF.projU_add_projL y, hU0, hL0, add_zero]

private theorem PlaneForms.form_axis_eq (hP : PlaneForms ωU ωL U L) (hua : HasUniqueAxes H)
    (hF : IsFrame H U L) {κ : ZMod p} (hκ : κ ≠ 0)
    (hmix : ∀ {x h lam mu}, FormMixed hF ωU ωL x h lam mu → mu = κ * lam)
    {x : V} {f : Module.Dual (ZMod p) V} (hxf : TrIn H x f) (hx0 : x ≠ 0) (hf0 : f ≠ 0) :
    ∃ t : ZMod p, ∀ y, f y = t * (ωU y x + κ * ωL y x) := by
  obtain ⟨lam, mu, hshape, hlam, hmu⟩ := hua.shape_of_planeForms hF hP hx0 hf0 hxf
  have hBx : ∀ y, ωU y x + κ * ωL y x = -(ωU x y + κ * ωL x y) := fun y => by
    rw [← hP.altU.neg_eq x y, ← hP.altL.neg_eq x y]
    ring
  by_cases hU : hF.projU x = 0
  · have hωU0 : ∀ y, ωU x y = 0 := fun y => by
      rw [hP.left_projU hF, hU, map_zero, LinearMap.zero_apply]
    refine ⟨-(mu / κ), fun y => ?_⟩
    rw [hshape y, hBx y, hωU0 y]
    field_simp
    ring
  · by_cases hL : hF.projL x = 0
    · have hωL0 : ∀ y, ωL x y = 0 := fun y => by
        rw [hP.left_projL hF, hL, map_zero, LinearMap.zero_apply]
      refine ⟨-lam, fun y => ?_⟩
      rw [hshape y, hBx y, hωL0 y]
      ring
    · have hμ : mu = κ * lam := hmix ⟨hxf, hf0, hU, hL, hshape, hlam hU, hmu hL⟩
      refine ⟨-lam, fun y => ?_⟩
      rw [hshape y, hBx y, hμ]
      ring

variable (H)

theorem HasUniqueAxes.exists_form [Module.Finite (ZMod p) V]
    (_hdim : Module.finrank (ZMod p) V = 4)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hua : HasUniqueAxes H) {U L : Submodule (ZMod p) V} (hF : IsFrame H U L) :
    ∃ B : LinearMap.BilinForm (ZMod p) V, B.IsAlt ∧ B.Nondegenerate ∧
      ∀ (x : V) (f : Module.Dual (ZMod p) V), TrIn H x f → x ≠ 0 → f ≠ 0 →
        ∃ t : ZMod p, ∀ y, f y = t * B y x := by
  obtain ⟨ωU, ωL, hP⟩ := exists_planeForms H hF
  obtain ⟨κ, hκ, hmix⟩ := hP.exists_form_kappa hirr hgen hua hF
  have hB : ∀ y z, (ωU + κ • ωL) y z = ωU y z + κ * ωL y z := fun y z => by simp
  have hleft : ∀ y, (∀ z, (ωU + κ • ωL) y z = 0) → y = 0 := fun y hy =>
    hP.form_separatingLeft hF hκ y fun z => by rw [← hB]; exact hy z
  refine ⟨ωU + κ • ωL, hP.altU.add (hP.altL.smul κ), ⟨hleft, fun z hz => hleft z fun y => ?_⟩,
    fun x f hxf hx0 hf0 => ?_⟩
  · rw [← (hP.altU.add (hP.altL.smul κ)).neg_eq y z, hz y, neg_zero]
  · obtain ⟨t, ht⟩ := hP.form_axis_eq hua hF hκ hmix hxf hx0 hf0
    exact ⟨t, fun y => by rw [ht y, hB]⟩

end CFSG.RankThree.PartOne.LIT
