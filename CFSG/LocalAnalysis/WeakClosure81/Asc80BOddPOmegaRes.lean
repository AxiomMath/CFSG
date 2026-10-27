module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaDih
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.WeakClosure81.OSeitz

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh QuadraticMap CFSG.ClassicalGroups.Orthogonal

section CentralAniso

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

omit [Finite P] in
theorem exists_singular_of_central (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    (hdim : 7 ≤ Module.finrank K V) {E : Subgroup P} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {t g : elementaryGroup Q} (ht : π t ∈ E) (hg : π g ∈ E)
    (ht1 : π t ≠ 1) (hg1 : π g ≠ 1) (htg : π t ≠ π g)
    (htt : ∀ v, (t : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) v) = v)
    (hgg : ∀ v, (g : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v) = -v)
    (hcomm : ∀ v, (t : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v) = (g : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) v)) :
    ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧
      ∀ h : elementaryGroup Q, π h ∈ E → ∀ w ∈ W, (h : V ≃ₗ[K] V) w ∈ W := by
  classical
  set T : V ≃ₗ[K] V := (t : V ≃ₗ[K] V) with hT
  set G : V ≃ₗ[K] V := (g : V ≃ₗ[K] V) with hG
  have hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q g.2
  have key : ∀ ε : K, 3 ≤ Module.finrank K (LinearMap.ker ((T : V →ₗ[K] V) - ε • LinearMap.id)) →
      ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧
        ∀ h : elementaryGroup Q, π h ∈ E → ∀ w ∈ W, (h : V ≃ₗ[K] V) w ∈ W := by
    intro ε h3
    obtain ⟨x, hxU, hx0, hxQ⟩ := OrthBlk.exists_singular_of_three_le_any (Q := Q) h3
    have hTx : T x = ε • x := by
      have := LinearMap.mem_ker.1 hxU
      simpa [sub_eq_zero] using this
    have hGxQ : Q (G x) = 0 := by rw [map_of_mem hGO, hxQ]
    have hxGx : polar Q x (G x) = 0 := by
      have h := polar_map_of_mem hGO x (G x)
      rw [hgg, polar_neg_right, polar_comm] at h
      have : (2 : K) * polar Q x (G x) = 0 := by linear_combination -h
      exact (mul_eq_zero.1 this).resolve_left h2K
    have h1 : x ∈ Submodule.span K {x, G x} := Submodule.subset_span (by simp)
    have h2 : G x ∈ Submodule.span K {x, G x} := Submodule.subset_span (by simp)
    have hT1 : (T : V →ₗ[K] V) x ∈ Submodule.span K {x, G x} := by
      rw [LinearEquiv.coe_coe, hTx]
      exact Submodule.smul_mem _ _ h1
    have hT2 : (T : V →ₗ[K] V) (G x) ∈ Submodule.span K {x, G x} := by
      rw [LinearEquiv.coe_coe, hcomm, hTx, map_smul]
      exact Submodule.smul_mem _ _ h2
    have hG1 : (G : V →ₗ[K] V) x ∈ Submodule.span K {x, G x} := h2
    have hG2 : (G : V →ₗ[K] V) (G x) ∈ Submodule.span K {x, G x} := by
      rw [LinearEquiv.coe_coe, hgg]
      exact Submodule.neg_mem _ h1
    refine ⟨Submodule.span K {x, G x}, fun h => hx0 ?_, fun z hz => ?_,
      stab_of_ab hc hE h4 ht hg ht1 hg1 htg (span_pair_stable (T : V →ₗ[K] V) hT1 hT2)
        (span_pair_stable (G : V →ₗ[K] V) hG1 hG2)⟩
    · rw [h] at h1
      exact (Submodule.mem_bot K).1 h1
    · obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hz
      have h0 : polar Q (α • x) (β • G x) = 0 := by
        rw [polar_smul_left_eq, polar_smul_right_eq, hxGx, mul_zero, mul_zero]
      have h : polar Q (α • x) (β • G x) = Q (α • x + β • G x) - Q (α • x) - Q (β • G x) := rfl
      rw [QuadraticMap.map_smul, QuadraticMap.map_smul, hxQ, hGxQ, h0] at h
      linear_combination -h
  set U := LinearMap.ker ((T : V →ₗ[K] V) - (1 : K) • LinearMap.id) with hU
  set U' := LinearMap.ker ((T : V →ₗ[K] V) - (-1 : K) • LinearMap.id) with hU'
  have htop : U ⊔ U' = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    have hv : v = (2 : K)⁻¹ • (v + T v) + (2 : K)⁻¹ • (v - T v) := by
      have : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2K
      linear_combination (norm := module) (-1 : K) • this • v
    rw [hv]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [hU, LinearMap.mem_ker]
      simp [htt, add_comm]
    · rw [hU', LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, map_smul, map_sub, htt,
        LinearMap.smul_apply, LinearMap.id_apply]
      module
  have h1 := Submodule.finrank_add_le_finrank_add_finrank U U'
  rw [htop, finrank_top] at h1
  by_cases hle : 3 ≤ Module.finrank K U
  · exact key 1 hle
  · exact key (-1) (by change 3 ≤ Module.finrank K U'; omega)

end CentralAniso

section Aniso

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem eichler_gadget {p v f : V} (hpv : polar Q p v = 0)
    (hpf : polar Q p f = 0) (hvf : polar Q v f = 0) (hQv : Q v = -Q p) :
    Q (p + v) = 0 ∧ polar Q (p + v) f = 0 ∧
      eichler Q (p + v) f p = (1 - polar Q p p * Q f) • p + polar Q p p • (f - Q f • v) := by
  have he : Q (p + v) = 0 := by
    have h : polar Q p v = Q (p + v) - Q p - Q v := rfl
    rw [hpv, hQv] at h
    linear_combination -h
  have hef : polar Q (p + v) f = 0 := by rw [polar_add_left, hpf, hvf, add_zero]
  refine ⟨he, hef, ?_⟩
  rw [eichler_apply he hef, polar_add_right, hpv, add_zero, hpf]
  module

theorem isRootCenter_of_aniso {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (h2K : (2 : K) ≠ 0)
    (W : Fin 4 → Submodule K V)
    (hort : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j, polar Q x y = 0)
    (hani : ∀ i, ∀ x ∈ W i, Q x = 0 → x = 0)
    (hspan : ∀ v, ∃ v₀ ∈ W 0, ∃ v₁ ∈ W 1, ∃ v₂ ∈ W 2, ∃ v₃ ∈ W 3, v = v₀ + v₁ + v₂ + v₃)
    (hU : ∀ i, i ≠ 3 → ∀ c : K, c ≠ 0 → ∃ v ∈ W i, Q v = c)
    (hP : ∀ i, i ≠ 3 → ∀ v ∈ W i, ∃ w ∈ W i, w ≠ 0 ∧ polar Q v w = 0)
    (hY4 : 4 ≤ Module.finrank K ↥(W 1 ⊔ W 2))
    (hE03 : ∀ e ∈ W 0 ⊔ W 3, ∀ w ∈ W 0 ⊔ W 3, eichler Q e w ∈ H)
    (hE01 : ∀ e ∈ W 0 ⊔ W 1, ∀ w ∈ W 0 ⊔ W 1, eichler Q e w ∈ H)
    (hE12 : ∀ e ∈ W 1 ⊔ W 2, ∀ w ∈ W 1 ⊔ W 2, eichler Q e w ∈ H)
    {s₀ s₃ : V} (hs₀ : s₀ ∈ W 0) (hs₃ : s₃ ∈ W 3) (hs₃0 : s₃ ≠ 0) (hQs : Q s₀ + Q s₃ = 0) :
    IsRootCenter Q H (s₀ + s₃) := by
  have hpolself : ∀ x : V, polar Q x x = 2 * Q x := fun x => by
    rw [polar_self, two_smul, two_mul]
  have hQne : ∀ i, ∀ x ∈ W i, x ≠ 0 → Q x ≠ 0 := fun i x hx hx0 hQ => hx0 (hani i x hx hQ)
  have h03 := hort 0 3 (by decide)
  have h01 := hort 0 1 (by decide)
  have h02 := hort 0 2 (by decide)
  have h12 := hort 1 2 (by decide)
  have h31 := hort 3 1 (by decide)
  have h32 := hort 3 2 (by decide)
  have hsQ : Q (s₀ + s₃) = 0 := by
    have h : polar Q s₀ s₃ = Q (s₀ + s₃) - Q s₀ - Q s₃ := rfl
    rw [h03 _ hs₀ _ hs₃] at h
    linear_combination -h + hQs
  have hs0 : s₀ + s₃ ≠ 0 := by
    intro h
    have h1 : polar Q (s₀ + s₃) s₃ = 2 * Q s₃ := by
      rw [polar_add_left, h03 _ hs₀ _ hs₃, zero_add, hpolself]
    rw [h, polar_zero_left] at h1
    exact hQne 3 s₃ hs₃ hs₃0 ((mul_eq_zero.1 h1.symm).resolve_left h2K)
  set Y := W 1 ⊔ W 2 with hYdef
  have hsY : ∀ y ∈ Y, polar Q (s₀ + s₃) y = 0 := by
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    rw [polar_add_right, polar_add_left, polar_add_left, h01 _ hs₀ _ hy₁, h02 _ hs₀ _ hy₂,
      h31 _ hs₃ _ hy₁, h32 _ hs₃ _ hy₂]
    ring
  have hYnd : PolarNondegOn Q Y := by
    intro x hx hxY
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    have e1 := hxY x₁ (Submodule.mem_sup_left hx₁)
    have e2 := hxY x₂ (Submodule.mem_sup_right hx₂)
    rw [polar_add_left, hort 2 1 (by decide) _ hx₂ _ hx₁, add_zero, hpolself] at e1
    rw [polar_add_left, h12 _ hx₁ _ hx₂, zero_add, hpolself] at e2
    rw [hani 1 x₁ hx₁ ((mul_eq_zero.1 e1).resolve_left h2K),
      hani 2 x₂ hx₂ ((mul_eq_zero.1 e2).resolve_left h2K), add_zero]
  have hYH : ∀ e ∈ Y, ∀ w ∈ Y, eichler Q e w ∈ H := hE12
  have hne_g : ∀ i, i ≠ 3 → ∀ {v f : V}, v ∈ W i → f ∈ W i → Q v ≠ 0 → f ≠ 0 →
      polar Q v f = 0 → f - Q f • v ≠ 0 := by
    intro i hi v f hv hf hQv hf0 hvf h
    have hfv : f = Q f • v := sub_eq_zero.1 h
    have := hvf
    rw [hfv, polar_smul_right_eq, hpolself] at this
    have hQf : Q f ≠ 0 := hQne i f hf hf0
    exact mul_ne_zero hQf (mul_ne_zero h2K hQv) this
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero, zero_add] at hQs
    exact hQne 3 s₃ hs₃ hs₃0 hQs
  obtain ⟨p, hp, hp0, hs₀p⟩ := hP 0 (by decide) s₀ hs₀
  have hQp := hQne 0 p hp hp0
  obtain ⟨v, hv, hQv⟩ := hU 1 (by decide) (-Q p) (neg_ne_zero.2 hQp)
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hQv
    exact hQp (neg_eq_zero.1 hQv.symm)
  obtain ⟨f, hf, hf0, hvf⟩ := hP 1 (by decide) v hv
  obtain ⟨heQ, hef, hgp⟩ := eichler_gadget (Q := Q) (h01 _ hp _ hv) (h01 _ hp _ hf) hvf hQv
  have hgH : eichler Q (p + v) f ∈ H := hE01 _ (Submodule.add_mem_sup hp hv) _
    (Submodule.mem_sup_right hf)
  have hgs : eichler Q (p + v) f (s₀ + s₃) = s₀ + s₃ := by
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_add_left, polar_add_right, polar_add_right, hs₀p, h01 _ hs₀ _ hv,
        hort 3 0 (by decide) _ hs₃ _ hp, h31 _ hs₃ _ hv]
      ring
    · rw [polar_add_left, h01 _ hs₀ _ hf, h31 _ hs₃ _ hf, add_zero]
  have hpR : p ∈ rootSet Q H (s₀ + s₃) := by
    refine ⟨?_, hE03 _ (Submodule.add_mem_sup hs₀ hs₃) _ (Submodule.mem_sup_left hp)⟩
    rw [polar_add_left, hs₀p, hort 3 0 (by decide) _ hs₃ _ hp, add_zero]
  have hmixR := rootSet_map hH hgH hpR
  rw [hgs, hgp] at hmixR
  set κ := polar Q p p with hκ
  have hκ0 : κ ≠ 0 := by rw [hκ, hpolself]; exact mul_ne_zero h2K hQp
  set y := κ • (f - Q f • v) with hydef
  have hyW : y ∈ W 1 := Submodule.smul_mem _ _ (Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hv))
  have hy0 : y ≠ 0 := smul_ne_zero hκ0 (hne_g 1 (by decide) hv hf (hQne 1 v hv hv0) hf0 hvf)
  have hQy := hQne 1 y hyW hy0
  obtain ⟨v₃, hv₃, hQv₃⟩ := hU 2 (by decide) (-Q y) (neg_ne_zero.2 hQy)
  have hv₃0 : v₃ ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hQv₃
    exact hQy (neg_eq_zero.1 hQv₃.symm)
  obtain ⟨f₃, hf₃, hf₃0, hv₃f₃⟩ := hP 2 (by decide) v₃ hv₃
  obtain ⟨-, -, hg₃⟩ := eichler_gadget (Q := Q) (h12 _ hyW _ hv₃) (h12 _ hyW _ hf₃) hv₃f₃
    hQv₃
  have hmove : eichler Q (y + v₃) f₃ y ≠ y := by
    rw [hg₃]
    intro h
    have h' : polar Q y y • (f₃ - Q f₃ • v₃) = (polar Q y y * Q f₃) • y := by
      linear_combination (norm := module) h
    have hl : polar Q y y • (f₃ - Q f₃ • v₃) ∈ W 2 :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ hf₃ (Submodule.smul_mem _ _ hv₃))
    have hr : (polar Q y y * Q f₃) • y ∈ W 1 := Submodule.smul_mem _ _ hyW
    have h0 : polar Q y y • (f₃ - Q f₃ • v₃) = 0 := by
      have hz := hort 1 2 (by decide) _ (h' ▸ hr) _ hl
      rw [h'] at hz ⊢
      rw [h'] at hl
      exact hani 2 _ hl (by
        have := hpolself ((polar Q y y * Q f₃) • y)
        rw [hz] at this
        exact ((mul_eq_zero.1 this.symm).resolve_left h2K))
    rcases smul_eq_zero.1 h0 with h1 | h1
    · rw [hpolself] at h1
      exact mul_ne_zero h2K hQy h1
    · exact hne_g 2 (by decide) hv₃ hf₃ (hQne 2 v₃ hv₃ hv₃0) hf₃0 hv₃f₃ h1
  have hpivot := subset_rootSet_of_mixed hH hYnd hY4 hYH hsY
    ⟨_, hmixR, y, Submodule.mem_sup_left hyW, (1 - κ * Q f) • p, by abel,
      fun z hz => by
        obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hz
        rw [polar_add_left, polar_smul_right_eq, polar_smul_right_eq, hort 1 0 (by decide) _ hz₁ _ hp,
          hort 2 0 (by decide) _ hz₂ _ hp]
        ring,
      y + v₃, Submodule.add_mem_sup hyW hv₃, f₃, Submodule.mem_sup_right hf₃, hmove⟩
  refine ⟨hs0, hsQ, fun w hw => ?_⟩
  obtain ⟨w₀, hw₀, w₁, hw₁, w₂, hw₂, w₃, hw₃, rfl⟩ := hspan w
  have hb : w₁ + w₂ ∈ rootSet Q H (s₀ + s₃) := hpivot _ (Submodule.add_mem_sup hw₁ hw₂)
  have ha : w₀ + w₃ ∈ rootSet Q H (s₀ + s₃) := by
    refine ⟨?_, hE03 _ (Submodule.add_mem_sup hs₀ hs₃) _ (Submodule.add_mem_sup hw₀ hw₃)⟩
    have h1 := hb.1
    have h2 : polar Q (s₀ + s₃) (w₀ + w₁ + w₂ + w₃) =
        polar Q (s₀ + s₃) (w₀ + w₃) + polar Q (s₀ + s₃) (w₁ + w₂) := by
      rw [← polar_add_right]
      congr 1
      abel
    rw [h2, h1, add_zero] at hw
    exact hw
  have := (rootSet Q H (s₀ + s₃)).add_mem ha hb
  have e : w₀ + w₃ + (w₁ + w₂) = w₀ + w₁ + w₂ + w₃ := by abel
  rw [e] at this
  exact this.2

end Aniso

section Assembly

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

omit [Finite K] [FiniteDimensional K V] in
theorem eichler_neg_neg (u w : V) : eichler Q (-u) (-w) = eichler Q u w := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have h' : Q (-u) = 0 ∧ polar Q (-u) (-w) = 0 := by
      rw [QuadraticMap.map_neg, polar_neg_left, polar_neg_right, neg_neg]
      exact h
    refine LinearEquiv.ext fun x => ?_
    rw [eichler_apply h'.1 h'.2, eichler_apply h.1 h.2, polar_neg_right, polar_neg_right,
      QuadraticMap.map_neg]
    module
  · have h' : ¬(Q (-u) = 0 ∧ polar Q (-u) (-w) = 0) := by
      rw [QuadraticMap.map_neg, polar_neg_left, polar_neg_right, neg_neg]
      exact h
    rw [eichler_of_not h, eichler_of_not h']

omit [Finite P] [Finite K] [FiniteDimensional K V] in
theorem eichler_mem_cGenV_of_eig {E : Subgroup P} {h : elementaryGroup Q} (hh : π h ∈ E)
    (hh1 : π h ≠ 1) {ε : K} (hε : ε = 1 ∨ ε = -1) {e w : V}
    (he : (h : V ≃ₗ[K] V) e = ε • e) (hw : (h : V ≃ₗ[K] V) w = ε • w) :
    eichler Q e w ∈ cGenV π E := by
  have hO : (h : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q h.2
  have hconj := eichler_conj hO e w
  have hfix : eichler Q ((h : V ≃ₗ[K] V) e) ((h : V ≃ₗ[K] V) w) = eichler Q e w := by
    rw [he, hw]
    rcases hε with rfl | rfl
    · rw [one_smul, one_smul]
    · rw [neg_one_smul, neg_one_smul, eichler_neg_neg]
  rw [hfix] at hconj
  set x : elementaryGroup Q := ⟨eichler Q e w, eichler_mem_elementaryGroup Q e w⟩ with hx
  have hxh : x * h = h * x := by
    refine Subtype.ext ?_
    change eichler Q e w * (h : V ≃ₗ[K] V) = (h : V ≃ₗ[K] V) * eichler Q e w
    calc eichler Q e w * (h : V ≃ₗ[K] V)
        = ((h : V ≃ₗ[K] V) * eichler Q e w * (h : V ≃ₗ[K] V)⁻¹) * (h : V ≃ₗ[K] V) := by
          rw [hconj]
      _ = (h : V ≃ₗ[K] V) * eichler Q e w := by group
  refine ⟨x, ?_, rfl⟩
  have hsub : (⊤ : Subgroup P) ⊓ Subgroup.centralizer {π h} ≤
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} :=
    le_iSup₂_of_le (π h) hh (le_iSup_of_le hh1 le_rfl)
  refine hsub ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  rw [← map_mul, ← map_mul, hxh]

omit [Finite K] in
theorem exists_orth_of_finrank_two {U : Submodule K V} (hU : Module.finrank K U = 2) {v : V} :
    ∃ w ∈ U, w ≠ 0 ∧ polar Q v w = 0 := by
  set f : U →ₗ[K] K := (polarBilin Q v).domRestrict U with hf
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hr : Module.finrank K (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at this
  have hk : LinearMap.ker f ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨w, w.2, fun h => hw0 (Subtype.ext h), ?_⟩
  have := LinearMap.mem_ker.1 hw
  simpa [hf] using this

theorem exists_eq_of_finrank_two (h2K : (2 : K) ≠ 0) {U : Submodule K V}
    (hU : Module.finrank K U = 2) (hani : ∀ x ∈ U, Q x = 0 → x = 0) {c : K} (_hc : c ≠ 0) :
    ∃ v ∈ U, Q v = c := by
  have hne : U ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hU
    omega
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨p', hp', hp'0, hpp'⟩ := exists_orth_of_finrank_two (Q := Q) hU (v := p)
  have hQp : Q p ≠ 0 := fun h => hp0 (hani p hp h)
  have hQp' : Q p' ≠ 0 := fun h => hp'0 (hani p' hp' h)
  obtain ⟨x, y, hxy⟩ := SpSeitz.exists_sq_add_sq h2K hQp hQp' (-c)
  refine ⟨x • p + y • p', U.add_mem (U.smul_mem _ hp) (U.smul_mem _ hp'), ?_⟩
  have h : polar Q (x • p) (y • p') = Q (x • p + y • p') - Q (x • p) - Q (y • p') := rfl
  rw [polar_smul_left_eq, polar_smul_right_eq, hpp', QuadraticMap.map_smul,
    QuadraticMap.map_smul] at h
  simp only [smul_eq_mul] at h
  linear_combination -h + hxy

omit [Finite P] in
theorem top_le_of_four (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0) {E : Subgroup P}
    (W : Fin 4 → Submodule K V)
    (hort : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j, polar Q x y = 0)
    (hani : ∀ i, ∀ x ∈ W i, Q x = 0 → x = 0)
    (hspan : ∀ v, ∃ v₀ ∈ W 0, ∃ v₁ ∈ W 1, ∃ v₂ ∈ W 2, ∃ v₃ ∈ W 3, v = v₀ + v₁ + v₂ + v₃)
    (h2 : ∀ i, i ≠ 3 → Module.finrank K (W i) = 2) (hW3 : W 3 ≠ ⊥)
    (hE : ∀ i j, i ≠ j → ∀ e ∈ W i ⊔ W j, ∀ w ∈ W i ⊔ W j, eichler Q e w ∈ cGenV π E) :
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  have hU : ∀ i, i ≠ 3 → ∀ c : K, c ≠ 0 → ∃ v ∈ W i, Q v = c := fun i hi c hc =>
    exists_eq_of_finrank_two h2K (h2 i hi) (hani i) hc
  have hP : ∀ i, i ≠ 3 → ∀ v ∈ W i, ∃ w ∈ W i, w ≠ 0 ∧ polar Q v w = 0 := fun i hi v _ =>
    exists_orth_of_finrank_two (h2 i hi)
  have hY4 : 4 ≤ Module.finrank K ↥(W 1 ⊔ W 2) := by
    have hinf : W 1 ⊓ W 2 = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      rw [Submodule.mem_bot]
      refine hani 1 x hx.1 ?_
      have h := hort 1 2 (by decide) x hx.1 x hx.2
      rw [polar_self, two_smul, ← two_mul] at h
      exact (mul_eq_zero.1 h).resolve_left h2K
    have h := Submodule.finrank_sup_add_finrank_inf_eq (W 1) (W 2)
    rw [hinf, finrank_bot, add_zero, h2 1 (by decide), h2 2 (by decide)] at h
    omega
  obtain ⟨s₃, hs₃, hs₃0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW3
  have hQs₃ : Q s₃ ≠ 0 := fun h => hs₃0 (hani 3 s₃ hs₃ h)
  obtain ⟨s₀, hs₀, hQs₀⟩ := hU 0 (by decide) (-Q s₃) (neg_ne_zero.2 hQs₃)
  have hH := cGenV_le_orthogonalGroup (Q := Q) (π := π) E
  have hrc := isRootCenter_of_aniso hH h2K W hort hani hspan hU hP hY4 (hE 0 3 (by decide))
    (hE 0 1 (by decide)) (hE 1 2 (by decide)) hs₀ hs₃ hs₃0 (by rw [hQs₀]; ring)
  have hrc' := isRootCenter_of_aniso hH h2K W hort hani hspan hU hP hY4 (hE 0 3 (by decide))
    (hE 0 1 (by decide)) (hE 1 2 (by decide)) hs₀ ((W 3).neg_mem hs₃) (neg_ne_zero.2 hs₃0)
    (by rw [hQs₀, QuadraticMap.map_neg]; ring)
  have hpol : polar Q (s₀ + s₃) (s₀ + -s₃) = 4 * Q s₀ := by
    rw [polar_add_left, polar_add_right, polar_add_right, polar_neg_right, polar_neg_right,
      hort 0 3 (by decide) _ hs₀ _ hs₃, hort 3 0 (by decide) _ hs₃ _ hs₀, polar_self, polar_self,
      hQs₀]
    simp only [two_smul]
    ring
  have h4 : polar Q (s₀ + s₃) (s₀ + -s₃) ≠ 0 := by
    rw [hpol, hQs₀]
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero h2K h2K) (neg_ne_zero.2 hQs₃)
  set c := polar Q (s₀ + s₃) (s₀ + -s₃) with hcdef
  exact top_le_of_elementaryGroup_le hc (elementaryGroup_le_of_hypPair hc.nondegenerate hH
    ⟨s₀ + s₃, c⁻¹ • (s₀ + -s₃), hrc.2.1, by rw [QuadraticMap.map_smul, hrc'.2.1, smul_zero],
      by rw [polar_smul_right_eq, inv_mul_cancel₀ h4]⟩ hrc (hrc'.smul (inv_ne_zero h4)))

end Assembly

section Perm

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

omit [Finite P] in
theorem top_le_of_four' (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0) {E : Subgroup P}
    (W : Fin 4 → Submodule K V)
    (hort : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j, polar Q x y = 0)
    (hani : ∀ i, ∀ x ∈ W i, Q x = 0 → x = 0)
    (hspan : ∀ v, ∃ f : Fin 4 → V, (∀ i, f i ∈ W i) ∧ v = ∑ i, f i) (k : Fin 4)
    (h2 : ∀ i, i ≠ k → Module.finrank K (W i) = 2) (hWk : W k ≠ ⊥)
    (hE : ∀ i j, i ≠ j → ∀ e ∈ W i ⊔ W j, ∀ w ∈ W i ⊔ W j, eichler Q e w ∈ cGenV π E) :
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  set σ : Equiv.Perm (Fin 4) := Equiv.swap k 3 with hσ
  have hσ3 : σ 3 = k := by rw [hσ, Equiv.swap_apply_right]
  have hσk : ∀ i, σ i = k → i = 3 := fun i h => by
    rw [← hσ3] at h
    exact σ.injective h
  refine top_le_of_four hc h2K (fun i => W (σ i)) (fun i j hij => hort _ _ (σ.injective.ne hij))
    (fun i => hani (σ i)) (fun v => ?_) (fun i hi => h2 (σ i) fun h => hi (hσk i h))
    (by simpa [hσ3] using hWk) (fun i j hij => hE _ _ (σ.injective.ne hij))
  obtain ⟨f, hf, rfl⟩ := hspan v
  refine ⟨f (σ 0), hf _, f (σ 1), hf _, f (σ 2), hf _, f (σ 3), hf _, ?_⟩
  rw [← Equiv.sum_comp σ f, Fin.sum_univ_four]

end Perm

section Comm

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

def sgn₁ (K : Type) [Field K] (i : Fin 4) : K := if i.val < 2 then 1 else -1

def sgn₂ (K : Type) [Field K] (i : Fin 4) : K := if i.val % 2 = 0 then 1 else -1

omit [Finite K] in
theorem sgn₁_mul_self (i : Fin 4) : sgn₁ K i * sgn₁ K i = 1 := by
  unfold sgn₁; split_ifs <;> simp

omit [Finite K] in
theorem sgn₂_mul_self (i : Fin 4) : sgn₂ K i * sgn₂ K i = 1 := by
  unfold sgn₂; split_ifs <;> simp

omit [Finite K] in
theorem sgn_or (i : Fin 4) : (sgn₁ K i = 1 ∨ sgn₁ K i = -1) ∧ (sgn₂ K i = 1 ∨ sgn₂ K i = -1) := by
  unfold sgn₁ sgn₂; split_ifs <;> simp

omit [Finite K] in
theorem sgn_ne (i j : Fin 4) (hij : i ≠ j) :
    sgn₁ K i * sgn₁ K j = -1 ∨ sgn₂ K i * sgn₂ K j = -1 := by
  unfold sgn₁ sgn₂
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

omit [Finite K] in
theorem sgn_eq (i j : Fin 4) (hij : i ≠ j) :
    sgn₁ K i = sgn₁ K j ∨ sgn₂ K i = sgn₂ K j ∨ sgn₁ K i * sgn₂ K i = sgn₁ K j * sgn₂ K j := by
  unfold sgn₁ sgn₂
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

omit [Finite K] [FiniteDimensional K V] in
theorem eig_sup (h : V →ₗ[K] V) {ε : K} {U U' : Submodule K V} (hU : ∀ x ∈ U, h x = ε • x)
    (hU' : ∀ x ∈ U', h x = ε • x) : ∀ x ∈ U ⊔ U', h x = ε • x := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, hU y hy, hU' z hz, smul_add]

omit [Finite P] in
theorem top_le_of_comm (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    (hdim : 7 ≤ Module.finrank K V) {E : Subgroup P} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {g₁ g₂ : elementaryGroup Q} (h₁ : π g₁ ∈ E) (h₂ : π g₂ ∈ E)
    (h₁1 : π g₁ ≠ 1) (h₂1 : π g₂ ≠ 1) (h₁₂ : π g₁ ≠ π g₂)
    (hg₁ : ∀ v, (g₁ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v) = v)
    (hg₂ : ∀ v, (g₂ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) = v)
    (hcomm : ∀ v, (g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) = (g₂ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v))
    (hA : ∀ W : Submodule K V, (∀ x ∈ W, Q x = 0) →
      (∀ g : elementaryGroup Q, π g ∈ E → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W) → W = ⊥) :
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  classical
  set A : V ≃ₗ[K] V := (g₁ : V ≃ₗ[K] V) with hAdef
  set B : V ≃ₗ[K] V := (g₂ : V ≃ₗ[K] V) with hBdef
  have hAO : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q g₁.2
  have hBO : B ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q g₂.2
  set W : Fin 4 → Submodule K V := fun i =>
    LinearMap.ker ((A : V →ₗ[K] V) - sgn₁ K i • LinearMap.id) ⊓
      LinearMap.ker ((B : V →ₗ[K] V) - sgn₂ K i • LinearMap.id) with hWdef
  have hmem : ∀ i x, x ∈ W i ↔ A x = sgn₁ K i • x ∧ B x = sgn₂ K i • x := by
    intro i x
    simp [hWdef, sub_eq_zero]
  have hort : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j, polar Q x y = 0 := by
    intro i j hij x hx y hy
    rw [hmem] at hx hy
    have k : ∀ (s t : K), s * t = -1 → polar Q (s • x) (t • y) = polar Q x y →
        polar Q x y = 0 := by
      intro s t hst h
      rw [polar_smul_left_eq, polar_smul_right_eq, ← mul_assoc, hst] at h
      have : (2 : K) * polar Q x y = 0 := by linear_combination -h
      exact (mul_eq_zero.1 this).resolve_left h2K
    rcases sgn_ne (K := K) i j hij with h | h
    · exact k _ _ h (by rw [← hx.1, ← hy.1, polar_map_of_mem hAO])
    · exact k _ _ h (by rw [← hx.2, ← hy.2, polar_map_of_mem hBO])
  have hani : ∀ i, ∀ x ∈ W i, Q x = 0 → x = 0 := by
    intro i x hx hQ
    rw [hmem] at hx
    have hstab := stab_of_ab hc hE h4 h₁ h₂ h₁1 h₂1 h₁₂ (X := K ∙ x)
      (fun w hw => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
        change A (c • x) ∈ _
        rw [map_smul, hx.1, smul_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
      (fun w hw => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
        change B (c • x) ∈ _
        rw [map_smul, hx.2, smul_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
    have h0 := hA (K ∙ x) (fun y hy => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [QuadraticMap.map_smul, hQ, smul_zero]) hstab
    exact Submodule.span_singleton_eq_bot.1 h0
  have h4K : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2K h2K
  have hspan : ∀ v, ∃ f : Fin 4 → V, (∀ i, f i ∈ W i) ∧ v = ∑ i, f i := by
    intro v
    refine ⟨fun i => (4 : K)⁻¹ • (v + sgn₁ K i • A v + sgn₂ K i • B v + (sgn₁ K i * sgn₂ K i) • A (B v)),
      fun i => ?_, ?_⟩
    · rw [hmem]
      have s1 := sgn₁_mul_self (K := K) i
      have s2 := sgn₂_mul_self (K := K) i
      constructor
      · simp only [map_smul, map_add, hg₁]
        linear_combination (norm := module) (-(4 : K)⁻¹) • s1 • (A v + sgn₂ K i • A (B v))
      · simp only [map_smul, map_add, ← hcomm, hg₂]
        linear_combination (norm := module) (-(4 : K)⁻¹) • s2 • (B v + sgn₁ K i • A (B v))
    · have h4 : (4 : K)⁻¹ * 4 = 1 := inv_mul_cancel₀ h4K
      simp only [Fin.sum_univ_four, sgn₁, sgn₂]
      norm_num
      linear_combination (norm := module) (-1 : K) • h4 • v
  have hle2 : ∀ i, Module.finrank K (W i) ≤ 2 := by
    intro i
    by_contra h
    obtain ⟨x, hx, hx0, hxQ⟩ :=
      OrthBlk.exists_singular_of_three_le_any (Q := Q) (S := W i) (by omega)
    exact hx0 (hani i x hx hxQ)
  have htop : W 0 ⊔ W 1 ⊔ W 2 ⊔ W 3 = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨f, hf, rfl⟩ := hspan v
    rw [Fin.sum_univ_four]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup (Submodule.add_mem_sup (hf 0) (hf 1))
      (hf 2)) (hf 3)
  have hsum : 7 ≤ Module.finrank K (W 0) + Module.finrank K (W 1) + Module.finrank K (W 2) +
      Module.finrank K (W 3) := by
    have e1 := Submodule.finrank_add_le_finrank_add_finrank (W 0 ⊔ W 1 ⊔ W 2) (W 3)
    have e2 := Submodule.finrank_add_le_finrank_add_finrank (W 0 ⊔ W 1) (W 2)
    have e3 := Submodule.finrank_add_le_finrank_add_finrank (W 0) (W 1)
    rw [htop, finrank_top] at e1
    omega
  have hk : ∃ k : Fin 4, (∀ i, i ≠ k → Module.finrank K (W i) = 2) ∧
      Module.finrank K (W k) ≠ 0 := by
    have h0 := hle2 0
    have h1 := hle2 1
    have h2 := hle2 2
    have h3 := hle2 3
    by_cases e0 : Module.finrank K (W 0) = 2
    · by_cases e1 : Module.finrank K (W 1) = 2
      · by_cases e2 : Module.finrank K (W 2) = 2
        · refine ⟨3, fun i hi => ?_, by omega⟩
          fin_cases i
          · exact e0
          · exact e1
          · exact e2
          · exact absurd rfl hi
        · refine ⟨2, fun i hi => ?_, by omega⟩
          fin_cases i
          · exact e0
          · exact e1
          · exact absurd rfl hi
          · change Module.finrank K (W 3) = 2; omega
      · refine ⟨1, fun i hi => ?_, by omega⟩
        fin_cases i
        · exact e0
        · exact absurd rfl hi
        · change Module.finrank K (W 2) = 2; omega
        · change Module.finrank K (W 3) = 2; omega
    · refine ⟨0, fun i hi => ?_, by omega⟩
      fin_cases i
      · exact absurd rfl hi
      · change Module.finrank K (W 1) = 2; omega
      · change Module.finrank K (W 2) = 2; omega
      · change Module.finrank K (W 3) = 2; omega
  obtain ⟨k, hk2, hk0⟩ := hk
  have hWk : W k ≠ ⊥ := fun h => hk0 (by rw [h, finrank_bot])
  have h12E : π (g₁ * g₂) ∈ E := by rw [map_mul]; exact E.mul_mem h₁ h₂
  have h121 : π (g₁ * g₂) ≠ 1 := by rw [map_mul]; exact mul_ne_one_of_ne hE h₂ h₁₂
  have hE' : ∀ i j, i ≠ j → ∀ e ∈ W i ⊔ W j, ∀ w ∈ W i ⊔ W j, eichler Q e w ∈ cGenV π E := by
    intro i j hij e he w hw
    have hs := sgn_or (K := K) i
    rcases sgn_eq (K := K) i j hij with h | h | h
    · have hh := eig_sup (A : V →ₗ[K] V) (ε := sgn₁ K i) (U := W i) (U' := W j)
        (fun x hx => ((hmem i x).1 hx).1) (fun x hx => by rw [h]; exact ((hmem j x).1 hx).1)
      exact eichler_mem_cGenV_of_eig h₁ h₁1 hs.1 (hh e he) (hh w hw)
    · have hh := eig_sup (B : V →ₗ[K] V) (ε := sgn₂ K i) (U := W i) (U' := W j)
        (fun x hx => ((hmem i x).1 hx).2) (fun x hx => by rw [h]; exact ((hmem j x).1 hx).2)
      exact eichler_mem_cGenV_of_eig h₂ h₂1 hs.2 (hh e he) (hh w hw)
    · have hAB : ∀ l, ∀ x ∈ W l, ((g₁ * g₂ : elementaryGroup Q) : V ≃ₗ[K] V) x =
          (sgn₁ K l * sgn₂ K l) • x := by
        intro l x hx
        rw [hmem] at hx
        change A (B x) = _
        rw [hx.2, map_smul, hx.1, smul_smul, mul_comm]
      have hh := eig_sup (((g₁ * g₂ : elementaryGroup Q) : V ≃ₗ[K] V) : V →ₗ[K] V)
        (ε := sgn₁ K i * sgn₂ K i) (U := W i) (U' := W j) (hAB i) (fun x hx => by
          rw [h]; exact hAB j x hx)
      have hε : sgn₁ K i * sgn₂ K i = 1 ∨ sgn₁ K i * sgn₂ K i = -1 := by
        rcases hs.1 with h1 | h1 <;> rcases hs.2 with h2 | h2 <;> simp [h1, h2]
      exact eichler_mem_cGenV_of_eig h12E h121 hε (hh e he) (hh w hw)
  exact top_le_of_four' hc h2K W hort hani hspan k hk2 hWk hE'

end Comm

section Res

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P] {π : elementaryGroup Q →* P}

theorem top_le_of_res (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    (hdim : 7 ≤ Module.finrank K V) {E : Subgroup P} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4)
    (hR : (∀ W : Submodule K V, (∀ x ∈ W, Q x = 0) →
          (∀ g : elementaryGroup Q, π g ∈ E → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W) → W = ⊥) ∨
        (¬ HasElemLift π E ∧ ¬ HasCentralInvLift π E)) :
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨g₁, g₂, h₁, h₂, h₁1, h₂1, h₁₂, ε₁, ε₂, δ, hε₁, hε₂, hδ, hg₁, hg₂, hgg⟩ :=
    exists_lifts hc hE h4
  rcases hδ with rfl | rfl
  swap
  · exact top_le_of_anti hc h2K hdim hE h4 h₁ h₂ h₁1 h₂1 h₁₂ hε₁ hε₂ hg₁ hg₂
      (fun v => by rw [hgg, neg_one_smul])
  have hcomm : ∀ v, (g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) =
      (g₂ : V ≃ₗ[K] V) ((g₁ : V ≃ₗ[K] V) v) := fun v => by rw [hgg, one_smul]
  rcases hR with hA | ⟨-, hn⟩
  swap
  · exact absurd (hasCentralInvLift_of_comm hc hE h4 h₁ h₂ h₁1 h₂1 h₁₂ hε₁ hε₂ hg₁ hg₂ hcomm) hn
  have hvac : ∀ {t g : elementaryGroup Q}, π t ∈ E → π g ∈ E → π t ≠ 1 → π g ≠ 1 →
      π t ≠ π g → (∀ v, (t : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) v) = v) →
      (∀ v, (g : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v) = -v) →
      (∀ v, (t : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v) = (g : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) v)) → False := by
    intro t g ht hg ht1 hg1 htg htt hgg' htc
    obtain ⟨W, hW0, hWQ, hWs⟩ :=
      exists_singular_of_central hc h2K hdim hE h4 ht hg ht1 hg1 htg htt hgg' htc
    exact hW0 (hA W hWQ hWs)
  have hmul : ∀ v, ((g₁ * g₂ : elementaryGroup Q) : V ≃ₗ[K] V) v =
      (g₁ : V ≃ₗ[K] V) ((g₂ : V ≃ₗ[K] V) v) := fun v => rfl
  rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl
  · exact top_le_of_comm hc h2K hdim hE h4 h₁ h₂ h₁1 h₂1 h₁₂ (by simpa using hg₁)
      (by simpa using hg₂) hcomm hA
  · exact (hvac h₁ h₂ h₁1 h₂1 h₁₂ (by simpa using hg₁) (by simpa using hg₂) hcomm).elim
  · exact (hvac h₂ h₁ h₂1 h₁1 (Ne.symm h₁₂) (by simpa using hg₂) (by simpa using hg₁)
      (fun v => (hcomm v).symm)).elim
  · refine (hvac (t := g₁ * g₂) (g := g₁) (by rw [map_mul]; exact E.mul_mem h₁ h₂) h₁
      (by rw [map_mul]; exact mul_ne_one_of_ne hE h₂ h₁₂) h₁1 ?_ (fun v => ?_)
      (by simpa using hg₁) (fun v => ?_)).elim
    · rw [map_mul]
      intro h
      exact h₂1 (by simpa using h)
    · rw [hmul, hmul, ← hcomm ((g₂ : V ≃ₗ[K] V) v), hg₂]
      simp [hg₁]
    · rw [hmul, hmul, hcomm, hg₁, hg₁, map_smul]

end Res

theorem exists_orthCover7_of_isOddOrthogonal {X : Type} [Group X] (h : IsOddOrthogonal X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (2 : K) ≠ 0 ∧
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
        (Q : QuadraticForm K V) (π : elementaryGroup Q →* X),
          7 ≤ Module.finrank K V ∧ IsOrthogonalCover Q π := by
  obtain ⟨n, p, f, hp2, hm⟩ := h
  have h2 : ∀ {K : Type} [Field K] [Finite K], p.Prime → 1 ≤ f → Nat.card K = p ^ f →
      (2 : K) ≠ 0 := by
    intro K _ _ hp hf hK h0
    have : CharP K p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
    have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  rcases hm with hm | hm | hm
  · have hn : 3 ≤ n := hm.1.2.2.1
    obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eS⟩⟩ := hm.statedClassicalModel_of_ne_zero (by omega)
    have h2K := h2 hp hf hK
    obtain ⟨π, hπ⟩ := exists_orthCover (CFSG.LieType.Universal.Spin.coe_quadOdd n K)
      (commutator_orthogonalGroup_quadOdd h2K hn) (regular_quadOdd (K := K) h2K hn).1 eS
    refine ⟨K, inferInstance, inferInstance, h2K, _, inferInstance, inferInstance, inferInstance,
      _, π, ?_, hπ⟩
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  · have hn : 4 ≤ n := hm.1.2.2
    obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eS⟩⟩ := hm.statedClassicalModel_of_ne_zero (by omega)
    obtain ⟨π, hπ⟩ := exists_orthCover (CFSG.LieType.Universal.Spin.coe_quadPlus n K)
      (commutator_orthogonalGroup_quadPlus (by omega)) (regular_quadPlus (K := K) (n := n)
        (by omega)).1 eS
    refine ⟨K, inferInstance, inferInstance, h2 hp hf hK, _, inferInstance, inferInstance,
      inferInstance, _, π, ?_, hπ⟩
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · have hn : 4 ≤ n := hm.1.2.2
    obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, b, c, hirr, ⟨eS⟩⟩ :=
      hm.statedClassicalModel_of_ne_zero (by omega)
    obtain ⟨π, hπ⟩ := exists_orthCover (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)
      (commutator_orthogonalGroup_quadMinus hn hirr) (regular_quadMinus (K := K) (n := n) hn
        hirr).1 eS
    refine ⟨K, inferInstance, inferInstance, h2 hp hf hK, _, inferInstance, inferInstance,
      inferInstance, _, π, ?_, hπ⟩
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega

theorem seitzFourORes7_holds :
    ∀ (X : Type) [Group X] [Finite X], IsOddOrthogonal X →
      ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
        (Q : QuadraticForm K V) (π : elementaryGroup Q →* X), IsOrthogonalCover Q π →
        7 ≤ Module.finrank K V → (2 : K) ≠ 0 → ∀ E : Subgroup X, IsElemAbelian 2 E →
        Nat.card E = 4 →
        ((∀ W : Submodule K V, (∀ x ∈ W, Q x = 0) →
            (∀ g : elementaryGroup Q, π g ∈ E → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W) → W = ⊥) ∨
          (¬ HasElemLift π E ∧ ¬ HasCentralInvLift π E)) →
        (⊤ : Subgroup X) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup X) ⊓ Subgroup.centralizer {a} := by
  intro X _ _ _ K V _ _ _ _ _ Q π hc hdim h2K E hE h4 hR
  exact top_le_of_res hc h2K hdim hE h4 hR

theorem seitzFourInner_orthogonal_of_res7 :
    SeitzFourInner fun X _ => IsOddOrthogonal X := by
  have hR := seitzFourORes7_holds
  intro G _ _ L E hLn hLs hnab hfam hC hE h4 hEL _
  classical
  obtain ⟨K, _, _, h2K, V, _, _, _, Q, π, hdim, hc⟩ := exists_orthCover7_of_isOddOrthogonal hfam
  have : Finite ↥L := inferInstance
  set E' : Subgroup ↥L := E.subgroupOf L with hE'
  have hE' : IsElemAbelian 2 E' := hE.subgroupOf L
  have h4' : Nat.card E' = 4 := by
    rw [← h4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  apply iSup_centralizer_eq_of_subgroupOf
  by_cases hW : ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧
      ∀ g : elementaryGroup Q, π g ∈ E' → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W
  · obtain ⟨W, hW0, hWQ, hWs⟩ := hW
    by_cases hl : HasElemLift π E'
    · exact top_le_iSup_centralizer_of_singular hc h2K hE' h4' hW0 hWQ hWs hl
    by_cases ht : HasCentralInvLift π E'
    · obtain ⟨t, ht, ht1, htt, htc⟩ := ht
      exact top_le_iSup_centralizer_of_singular_central hc h2K hE' h4' hW0 hWQ hWs ht ht1 htt htc
    · exact hR ↥L hfam K V Q π hc hdim h2K E' hE' h4' (Or.inr ⟨hl, ht⟩)
  · refine hR ↥L hfam K V Q π hc hdim h2K E' hE' h4' (Or.inl fun W hWQ hWs => ?_)
    by_contra hne
    exact hW ⟨W, hne, hWQ, hWs⟩

theorem seitzFourInner_orthogonal : SeitzFourInner fun X _ => IsOddOrthogonal X :=
  seitzFourInner_orthogonal_of_res7

end CFSG.LocalAnalysis.WeakClosure81.OSeitz
