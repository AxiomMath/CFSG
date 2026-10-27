module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddPlane

public section

namespace CFSG.StandardType

namespace OrthBstarOdd

open Module CFSG.RankThree.PartOne.LIT OrthRestOdd

variable {K : Type} [Field K]

structure FrameData {V : Type} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (E : Subgroup (V ≃ₗ[K] V)) (W W' : Submodule K V) (s : V ≃ₗ[K] V) (τ : K) : Prop where
  finrank_left : finrank K W = 2
  finrank_right : finrank K W' = 2
  orth : ∀ w ∈ W, ∀ w' ∈ W', QuadraticMap.polar Q w w' = 0
  fpf_left : ∀ v ∈ W, v ≠ 0 → s v ≠ v
  fpf_right : ∀ v ∈ W', v ≠ 0 → s v ≠ v
  sq : ∀ v ∈ W ⊔ W', s (s v) = τ • s v + v
  act : ∀ e ∈ E, ∃ α β : K, ∀ v ∈ W ⊔ W', e v = α • v + β • s v
  aniso_left : ∀ v ∈ W, v ≠ 0 → Q v ≠ 0
  aniso_right : ∀ v ∈ W', v ≠ 0 → Q v ≠ 0
  tau_ne : τ ≠ 0
  sing : ∃ y ∈ W ⊔ W', y ≠ 0 ∧ Q y = 0

section General

variable {V : Type} [AddCommGroup V] [Module K V]

theorem isoGroup_of [CharP K 2] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} {T : Subgroup (V ≃ₗ[K] V)}
    (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g) (hpow : ∀ g ∈ T, g ^ p = 1)
    (hQT : ∀ g ∈ T, ∀ v, Q (g v) = Q v) : IsoGroup (QuadraticMap.polarBilin Q) p T where
  sep := hQ.1
  alt v := by rw [QuadraticMap.polarBilin_apply_apply]; exact polar_self_eq_zero Q v
  comm := hcomm
  pow := hpow
  pres g hg u w := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    exact polar_map (hQT g hg) u w

theorem polar_comp_subtype {Q : QuadraticForm K V} {U : Submodule K V} (u u' : U) :
    QuadraticMap.polar (Q.comp U.subtype) u u' = QuadraticMap.polar Q u u' := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add, Submodule.subtype_apply]

theorem nondeg_comp {Q : QuadraticForm K V} {U : Submodule K V}
    (h : ∀ u ∈ U, (∀ u' ∈ U, QuadraticMap.polar Q u u' = 0) → u = 0) :
    (QuadraticMap.polarBilin (Q.comp U.subtype)).Nondegenerate := by
  refine ⟨fun u hu => Subtype.ext (h u u.2 fun u' hu' => ?_),
    fun u hu => Subtype.ext (h u u.2 fun u' hu' => ?_)⟩
  · have := hu ⟨u', hu'⟩
    rwa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype] at this
  · have := hu ⟨u', hu'⟩
    rwa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype, QuadraticMap.polar_comm] at this

theorem commSpace_eq_map {E : Subgroup (V ≃ₗ[K] V)} {U W : Submodule K V} (hc : IsCompl U W)
    (hU : ∀ g ∈ E, ∀ s ∈ U, g s ∈ U) (hW : ∀ g ∈ E, ∀ s ∈ W, g s ∈ W) {g : E}
    (h1 : resHom E W hW g = 1) :
    commSpace (g : V ≃ₗ[K] V) = (commSpace (resHom E U hU g)).map U.subtype := by
  have hfixW : ∀ w ∈ W, (g : V ≃ₗ[K] V) w = w := fun w hw =>
    congrArg Subtype.val (LinearEquiv.congr_fun h1 ⟨w, hw⟩)
  ext y
  constructor
  · intro hy
    obtain ⟨z, rfl⟩ := mem_commSpace.mp hy
    have hz : z ∈ U ⊔ W := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    refine ⟨⟨(g : V ≃ₗ[K] V) u - u, Submodule.sub_mem _ (hU g g.2 u hu) hu⟩,
      mem_commSpace.mpr ⟨⟨u, hu⟩, Subtype.ext ?_⟩, ?_⟩
    · rw [Submodule.coe_sub, resHom_apply]
    · simp only [Submodule.subtype_apply]
      rw [map_add, hfixW w hw]
      abel
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hw'
    refine mem_commSpace.mpr ⟨(w : V), ?_⟩
    rw [Submodule.subtype_apply, Submodule.coe_sub, resHom_apply]

theorem FrameData.map {Q : QuadraticForm K V} {E : Subgroup (V ≃ₗ[K] V)} {U : Submodule K V}
    (hU : ∀ e ∈ E, ∀ u ∈ U, e u ∈ U) {W₀ W₀' : Submodule K U} {s : V ≃ₗ[K] V} (hs : s ∈ E)
    {τ : K}
    (h : FrameData (Q.comp U.subtype) (resHom E U hU).range W₀ W₀' (resHom E U hU ⟨s, hs⟩) τ) :
    FrameData Q E (W₀.map U.subtype) (W₀'.map U.subtype) s τ where
  finrank_left := by rw [Submodule.finrank_map_subtype_eq]; exact h.finrank_left
  finrank_right := by rw [Submodule.finrank_map_subtype_eq]; exact h.finrank_right
  orth := by
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    have := h.orth w hw w' hw'
    rwa [polar_comp_subtype] at this
  fpf_left := by
    rintro _ ⟨v, hv, rfl⟩ hv0 heq
    exact h.fpf_left v hv (fun h0 => hv0 (by rw [h0]; rfl)) (Subtype.ext heq)
  fpf_right := by
    rintro _ ⟨v, hv, rfl⟩ hv0 heq
    exact h.fpf_right v hv (fun h0 => hv0 (by rw [h0]; rfl)) (Subtype.ext heq)
  sq := by
    intro v hv
    rw [← Submodule.map_sup] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    exact congrArg Subtype.val (h.sq v₀ hv₀)
  act := by
    intro e he
    obtain ⟨α, β, hαβ⟩ := h.act _ ⟨⟨e, he⟩, rfl⟩
    refine ⟨α, β, fun v hv => ?_⟩
    rw [← Submodule.map_sup] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    exact congrArg Subtype.val (hαβ v₀ hv₀)
  aniso_left := by
    rintro _ ⟨v, hv, rfl⟩ hv0
    exact h.aniso_left v hv (fun h0 => hv0 (by rw [h0]; rfl))
  aniso_right := by
    rintro _ ⟨v, hv, rfl⟩ hv0
    exact h.aniso_right v hv (fun h0 => hv0 (by rw [h0]; rfl))
  tau_ne := h.tau_ne
  sing := by
    obtain ⟨y, hy, hy0, hQy⟩ := h.sing
    refine ⟨y, ?_, fun h0 => hy0 (Subtype.ext h0), hQy⟩
    rw [← Submodule.map_sup]
    exact ⟨y, hy, rfl⟩

theorem fix_all_of_fix [FiniteDimensional K V] {p : ℕ} (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    {r s : V ≃ₗ[K] V} (hrp : r ^ p = 1) (hrs : s * r = r * s) {W : Submodule K V}
    (hW : finrank K W = 2) (hrW : ∀ v ∈ W, r v ∈ W) (hfpf : ∀ v ∈ W, v ≠ 0 → r v ≠ v) {v : V}
    (hvW : v ∈ W) (hv0 : v ≠ 0) (hsv : s v = v) : ∀ u ∈ W, s u = u := by
  have hspan := mem_span_of_finrank_two hW hvW (hrW v hvW) (indep_of_ne hrp hK1 (hfpf v hvW hv0))
  have hsr : s (r v) = r v := by
    have := LinearEquiv.congr_fun hrs v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsv] at this
    exact this
  intro u hu
  obtain ⟨a, b, rfl⟩ := hspan u hu
  rw [map_add, map_smul, map_smul, hsv, hsr]

theorem act_of_pow {s : V ≃ₗ[K] V} {τ : K} {S : Submodule K V}
    (hsq : ∀ v ∈ S, s (s v) = τ • s v + v) :
    ∀ k : ℕ, ∃ α β : K, ∀ v ∈ S, (s ^ k) v = α • v + β • s v := by
  intro k
  induction k with
  | zero => exact ⟨1, 0, fun v _ => by simp⟩
  | succ k ih =>
    obtain ⟨α, β, h⟩ := ih
    refine ⟨β, α + β * τ, fun v hv => ?_⟩
    rw [pow_succ', LinearEquiv.mul_apply, h v hv, map_add, map_smul, map_smul, hsq v hv]
    module

end General

section Small

variable [CharP K 2] {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]

theorem false_of_dim_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) (hX : finrank K X = 2) {Q : QuadraticForm K X}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {t : X ≃ₗ[K] X} (htQ : ∀ v, Q (t v) = Q v)
    (htp : t ^ p = 1) (ht1 : t ≠ 1) {y : X} (hy : y ≠ 0) (hQy : Q y = 0) : False := by
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  have hev := even_finrank_of_regular (Q.comp (commSpace t).subtype)
    (nondeg_comp (commSpace_nondeg hQ hpK htQ htp))
  have h0 : finrank K (commSpace t) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero]
    exact commSpace_ne_bot ht1
  have hle : finrank K (commSpace t) ≤ 2 := hX ▸ Submodule.finrank_le _
  obtain ⟨k, hk⟩ := hev
  have htop : commSpace t = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  obtain ⟨-, -, -, hanis⟩ := plane_facts hp hp2 hK1 htQ htp (W := ⊤) (by rw [finrank_top, hX])
    (fun w _ hw => hQ.1 w fun v => hw v Submodule.mem_top) (fun _ _ => Submodule.mem_top)
    (fun v _ hv0 => fpf_commSpace hpK htp v (htop ▸ Submodule.mem_top) hv0)
  exact hanis y Submodule.mem_top hy hQy

end Small

end OrthBstarOdd

end CFSG.StandardType
