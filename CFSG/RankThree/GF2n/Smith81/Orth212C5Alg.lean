module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthC5

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {q : QuadraticForm K V}

theorem polar_self_zero (q : QuadraticForm K V) (v : V) : polar q v v = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

theorem eichler_sub_self {a s w : V} (ha : q a = 0) (hw : polar q a w = 0)
    (hsa : polar q s a = 1) (hsw : polar q s w = 0) :
    eichler q a w s - s = w - q w • a := by
  rw [eichler_apply ha hw, hsa, hsw, one_smul, zero_add, mul_one]
  abel

theorem polar_smul_mem_of_eichler_stable {S : AddSubgroup V} {a s w w' : V}
    (ha : q a = 0) (hs : s ∈ S) (hsa : polar q s a = 1)
    (hw : polar q a w = 0 ∧ polar q s w = 0) (hw' : polar q a w' = 0 ∧ polar q s w' = 0)
    (hstab : ∀ u, polar q a u = 0 → polar q s u = 0 → u ∈ ({w, w', w + w'} : Set V) →
      eichler q a u s ∈ S) :
    polar q w w' • a ∈ S := by
  have h1 := S.sub_mem (hstab w hw.1 hw.2 (by simp)) hs
  have h2 := S.sub_mem (hstab w' hw'.1 hw'.2 (by simp)) hs
  have hww : polar q a (w + w') = 0 ∧ polar q s (w + w') = 0 := by
    simp [polar_add_right, hw.1, hw.2, hw'.1, hw'.2]
  have h3 := S.sub_mem (hstab (w + w') hww.1 hww.2 (by simp)) hs
  rw [eichler_sub_self ha hw.1 hsa hw.2] at h1
  rw [eichler_sub_self ha hw'.1 hsa hw'.2] at h2
  rw [eichler_sub_self ha hww.1 hsa hww.2] at h3
  have := S.sub_mem (S.add_mem h1 h2) h3
  convert this using 1
  rw [polar]
  simp only [sub_smul]
  abel

theorem exists_partner (hnd : ∀ u, (∀ v, polar q u v = 0) → u = 0) {s : V} (hs : q s = 0)
    (hs0 : s ≠ 0) : ∃ a, q a = 0 ∧ polar q s a = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, polar q s y ≠ 0 := by
    by_contra h
    push Not at h
    exact hs0 (hnd s h)
  obtain ⟨y', h1⟩ : ∃ y', polar q s y' = 1 :=
    ⟨(polar q s y)⁻¹ • y, by rw [polar_smul_right_eq, inv_mul_cancel₀ hy]⟩
  have h1' : polar q y' s = 1 := by rw [polar_comm, h1]
  have h2 : polar q s s = 0 := polar_self_zero q s
  refine ⟨y' + q y' • s, ?_, ?_⟩
  · rw [QuadraticMap.map_add q y' (q y' • s), QuadraticMap.map_smul, polar_smul_right_eq, h1', hs]
    have : (2 : K) = 0 := CharTwo.two_eq_zero
    simp only [smul_eq_mul]
    linear_combination (q y') * this
  · rw [polar_add_right, polar_smul_right_eq, h1, h2]
    ring

theorem polar_proj {s a : V} (hsa : polar q s a = 1) (y : V) :
    polar q s (y - (polar q y s • a + polar q y a • s)) = 0 ∧
      polar q a (y - (polar q y s • a + polar q y a • s)) = 0 := by
  have h2 : polar q s s = 0 := polar_self_zero q s
  have h3 : polar q a a = 0 := polar_self_zero q a
  have h4 : polar q a s = 1 := by rw [polar_comm, hsa]
  constructor
  · rw [polar_sub_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hsa, h2,
      polar_comm q s y]
    ring
  · rw [polar_sub_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, h3, h4,
      polar_comm q a y]
    ring

section Dim

variable [FiniteDimensional K V]

theorem exists_perp_pair (hnd : ∀ u, (∀ v, polar q u v = 0) → u = 0)
    (hdim : 4 ≤ Module.finrank K V) {s a : V} (hsa : polar q s a = 1) :
    ∃ w w' : V, (polar q s w = 0 ∧ polar q a w = 0) ∧ (polar q s w' = 0 ∧ polar q a w' = 0) ∧
      polar q w w' = 1 := by
  let Φ : V →ₗ[K] K × K := (q.polarBilin s).prod (q.polarBilin a)
  have hker : ∀ v, v ∈ LinearMap.ker Φ ↔ polar q s v = 0 ∧ polar q a v = 0 := by
    intro v
    simp [Φ, LinearMap.mem_ker, Prod.ext_iff]
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  have h2 : Module.finrank K (LinearMap.range Φ) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    simpa [Module.finrank_prod] using this
  have h3 : 0 < Module.finrank K (LinearMap.ker Φ) := by omega
  obtain ⟨⟨w, hw⟩, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h3
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨hws, hwa⟩ := (hker w).mp hw
  obtain ⟨y, hy⟩ : ∃ y, polar q w y ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0' (hnd w h)
  obtain ⟨hp1, hp2⟩ := polar_proj hsa y
  set y₁ : V := y - (polar q y s • a + polar q y a • s) with hy₁
  have hws' : polar q w s = 0 := by rw [polar_comm, hws]
  have hwa' : polar q w a = 0 := by rw [polar_comm, hwa]
  have h4 : polar q w y₁ = polar q w y := by
    rw [hy₁, polar_sub_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hws',
      hwa']
    ring
  have h5 : polar q w y₁ ≠ 0 := by rw [h4]; exact hy
  refine ⟨w, (polar q w y₁)⁻¹ • y₁, ⟨hws, hwa⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [polar_smul_right_eq, hp1, mul_zero]
  · rw [polar_smul_right_eq, hp2, mul_zero]
  · rw [polar_smul_right_eq, inv_mul_cancel₀ h5]

theorem smul_mem_of_stable (hnd : ∀ u, (∀ v, polar q u v = 0) → u = 0)
    (hdim : 4 ≤ Module.finrank K V) {S : AddSubgroup V}
    (hS : ∀ a w, q a = 0 → polar q a w = 0 → ∀ v ∈ S, eichler q a w v ∈ S)
    {s a : V} (hs : s ∈ S) (ha : q a = 0) (hsa : polar q s a = 1) (c : K) : c • a ∈ S := by
  obtain ⟨w, w', ⟨hws, hwa⟩, ⟨hws', hwa'⟩, hww⟩ := exists_perp_pair hnd hdim hsa
  have hcw : polar q a (c • w') = 0 ∧ polar q s (c • w') = 0 := by
    simp only [polar_smul_right_eq, hwa', hws', mul_zero, and_self]
  have := polar_smul_mem_of_eichler_stable (S := S) (q := q) ha hs hsa ⟨hwa, hws⟩ hcw
    (fun u hu _ _ => hS a u ha hu s hs)
  rwa [polar_smul_right_eq, hww, mul_one] at this

theorem eq_top_of_stable (hnd : ∀ u, (∀ v, polar q u v = 0) → u = 0)
    (hdim : 4 ≤ Module.finrank K V) {S : AddSubgroup V}
    (hS : ∀ a w, q a = 0 → polar q a w = 0 → ∀ v ∈ S, eichler q a w v ∈ S)
    {s : V} (hs : s ∈ S) (hsq : q s = 0) (hs0 : s ≠ 0) : S = ⊤ := by
  obtain ⟨a₀, ha₀, hsa₀⟩ := exists_partner hnd hsq hs0
  have hsa₀' : polar q a₀ s = 1 := by rw [polar_comm, hsa₀]
  have hKa : ∀ c : K, c • a₀ ∈ S := smul_mem_of_stable hnd hdim hS hs ha₀ hsa₀
  have ha₀S : a₀ ∈ S := by simpa using hKa 1
  have hKs : ∀ c : K, c • s ∈ S := smul_mem_of_stable hnd hdim hS ha₀S hsq hsa₀'
  have hN : ∀ z, polar q s z = 0 → polar q a₀ z = 0 → z ∈ S := by
    intro z hzs hza
    have hzs' : polar q z s = 0 := by rw [polar_comm, hzs]
    have hza' : polar q z a₀ = 0 := by rw [polar_comm, hza]
    have hb : q (a₀ + z + q z • s) = 0 := by
      rw [QuadraticMap.map_add q (a₀ + z) (q z • s), QuadraticMap.map_add q a₀ z,
        QuadraticMap.map_smul, polar_add_left, polar_smul_right_eq, polar_smul_right_eq, ha₀, hsq,
        hza, hzs', hsa₀']
      have : (2 : K) = 0 := CharTwo.two_eq_zero
      simp only [smul_eq_mul]
      linear_combination (q z) * this
    have hsb : polar q s (a₀ + z + q z • s) = 1 := by
      rw [polar_add_right, polar_add_right, polar_smul_right_eq, hsa₀, hzs,
        polar_self_zero q s]
      ring
    have hbS : a₀ + z + q z • s ∈ S := by
      simpa using smul_mem_of_stable hnd hdim hS hs hb hsb 1
    have : z = (a₀ + z + q z • s) - a₀ - q z • s := by abel
    rw [this]
    exact S.sub_mem (S.sub_mem hbS ha₀S) (hKs _)
  rw [eq_top_iff]
  intro y _
  obtain ⟨h1, h2⟩ := polar_proj hsa₀ y
  have hy : y = (y - (polar q y s • a₀ + polar q y a₀ • s)) +
      (polar q y s • a₀ + polar q y a₀ • s) := by abel
  rw [hy]
  exact S.add_mem (hN _ h1 h2) (S.add_mem (hKa _) (hKs _))

end Dim

theorem exists_dual (hnd : ∀ u, (∀ v, polar q u v = 0) → u = 0) {u w : V}
    (hind : LinearIndependent K ![u, w]) :
    ∃ f₁ f₂ : V, polar q u f₁ = 1 ∧ polar q w f₁ = 0 ∧ polar q u f₂ = 0 ∧ polar q w f₂ = 1 := by
  let Ψ : V →ₗ[K] K × K := (q.polarBilin u).prod (q.polarBilin w)
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.dualMap_injective_iff]
    rw [← LinearMap.ker_eq_bot (f := Ψ.dualMap)]
    refine LinearMap.ker_eq_bot'.mpr fun ξ hξ => ?_
    have h1 : ∀ v, ξ (1, 0) * polar q u v + ξ (0, 1) * polar q w v = 0 := by
      intro v
      have := LinearMap.congr_fun hξ v
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
      have e : Ψ v = (polar q u v) • ((1 : K), (0 : K)) + (polar q w v) • ((0 : K), (1 : K)) := by
        ext <;> simp [Ψ]
      rw [e, map_add, map_smul, map_smul] at this
      simpa [mul_comm] using this
    have h2 : ξ (1, 0) • u + ξ (0, 1) • w = 0 := by
      apply hnd
      intro v
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h1]
    obtain ⟨e1, e2⟩ := LinearIndependent.pair_iff.mp hind _ _ h2
    refine LinearMap.ext fun ab => ?_
    have e : ab = ab.1 • ((1 : K), (0 : K)) + ab.2 • ((0 : K), (1 : K)) := by
      ext <;> simp
    rw [e, map_add, map_smul, map_smul, e1, e2]
    simp
  obtain ⟨f₁, hf₁⟩ := hsurj (1, 0)
  obtain ⟨f₂, hf₂⟩ := hsurj (0, 1)
  have hΨ : ∀ f, Ψ f = (polar q u f, polar q w f) := fun f => by simp [Ψ]
  rw [hΨ] at hf₁ hf₂
  simp only [Prod.mk.injEq] at hf₁ hf₂
  exact ⟨f₁, f₂, hf₁.1, hf₁.2, hf₂.1, hf₂.2⟩

theorem eichler_swap {u w : V} (hu : q u = 0) (hw : q w = 0) (huw : polar q u w = 0) :
    eichler q u w = eichler q w u := by
  have hwu : polar q w u = 0 := by rw [polar_comm, huw]
  have h2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huw, eichler_apply hw hwu, hu, hw]
  linear_combination (norm := module) h2 (polar q x u • w) - h2 (polar q x w • u)

theorem eichler_comm_left {a b c : V} (hb : polar q a b = 0) (hc : polar q a c = 0) :
    eichler q a b * eichler q a c = eichler q a c * eichler q a b := by
  rw [eichler_mul hb hc, eichler_mul hc hb, add_comm]

theorem eichler_apply_perp {a b x : V} (ha : q a = 0) (hb : polar q a b = 0)
    (hx : polar q x a = 0) : eichler q a b x = x - polar q x b • a := by
  rw [eichler_apply ha hb, hx]
  simp

theorem prod_subset_of_stable (hnd : ∀ u, (∀ v, polar q u v = 0) → u = 0) {u w : V}
    (hu : q u = 0) (hw : q w = 0) (huw : polar q u w = 0)
    (hind : LinearIndependent K ![u, w]) {D : AddSubgroup (V × V)}
    (hD1 : ∀ p ∈ D, p.1 ∈ Submodule.span K {u, w} ∧ p.2 ∈ Submodule.span K {u, w})
    (hD0 : ∃ p ∈ D, p ≠ 0)
    (ht : ∀ p ∈ D, (p.1 + p.2, p.2) ∈ D) (ht' : ∀ p ∈ D, (p.1, p.1 + p.2) ∈ D)
    (hE : ∀ a b, q a = 0 → polar q a b = 0 →
      eichler q a b * eichler q u w = eichler q u w * eichler q a b →
      ∀ p ∈ D, (eichler q a b p.1, eichler q a b p.2) ∈ D) :
    ∀ a ∈ Submodule.span K {u, w}, ∀ b ∈ Submodule.span K {u, w}, (a, b) ∈ D := by
  obtain ⟨f₁, f₂, h11, h12, h21, h22⟩ := exists_dual hnd hind
  have hwu : polar q w u = 0 := by rw [polar_comm, huw]
  have hE₁ : ∀ c : K, polar q u (c • f₂) = 0 := fun c => by
    rw [polar_smul_right_eq, h21, mul_zero]
  have hE₂ : ∀ c : K, polar q w (c • f₁) = 0 := fun c => by
    rw [polar_smul_right_eq, h12, mul_zero]
  have hc₁ : ∀ c : K, eichler q u (c • f₂) * eichler q u w =
      eichler q u w * eichler q u (c • f₂) := fun c => eichler_comm_left (hE₁ c) huw
  have hc₂ : ∀ c : K, eichler q w (c • f₁) * eichler q u w =
      eichler q u w * eichler q w (c • f₁) := fun c => by
    rw [eichler_swap hu hw huw]
    exact eichler_comm_left (hE₂ c) hwu
  let S : AddSubgroup V :=
    { carrier := {a | (a, 0) ∈ D}
      add_mem' := fun {a b} ha hb => by simpa using D.add_mem ha hb
      zero_mem' := D.zero_mem
      neg_mem' := fun {a} ha => by simpa using D.neg_mem ha }
  have hmemS : ∀ a, a ∈ S ↔ (a, 0) ∈ D := fun a => Iff.rfl
  have hS₁ : ∀ a ∈ S, a ∈ Submodule.span K {u, w} := fun a ha => (hD1 _ ha).1
  have key₁ : ∀ (c α β : K), eichler q u (c • f₂) (α • u + β • w) =
      (α • u + β • w) - (c * β) • u := by
    intro c α β
    have hp : polar q (α • u + β • w) u = 0 := by
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_self_zero, hwu]; ring
    rw [eichler_apply_perp hu (hE₁ c) hp, polar_smul_right_eq, polar_add_left,
      polar_smul_left_eq, polar_smul_left_eq, h21, h22]
    simp
  have key₂ : ∀ (c α β : K), eichler q w (c • f₁) (α • u + β • w) =
      (α • u + β • w) - (c * α) • w := by
    intro c α β
    have hp : polar q (α • u + β • w) w = 0 := by
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_self_zero, huw]; ring
    rw [eichler_apply_perp hw (hE₂ c) hp, polar_smul_right_eq, polar_add_left,
      polar_smul_left_eq, polar_smul_left_eq, h11, h12]
    simp
  have hl₁ : ∀ a ∈ S, ∀ c : K, eichler q u (c • f₂) a ∈ S := fun a ha c => by
    have := hE u (c • f₂) hu (hE₁ c) (hc₁ c) _ ha
    exact (hmemS _).mpr (by simpa using this)
  have hl₂ : ∀ a ∈ S, ∀ c : K, eichler q w (c • f₁) a ∈ S := fun a ha c => by
    have := hE w (c • f₁) hw (hE₂ c) (hc₂ c) _ ha
    exact (hmemS _).mpr (by simpa using this)
  obtain ⟨s₀, hs₀, hs₀0⟩ : ∃ s₀ ∈ S, s₀ ≠ 0 := by
    obtain ⟨⟨a, b⟩, hp, hp0⟩ := hD0
    by_cases hb : b = 0
    · refine ⟨a, ?_, fun ha => hp0 ?_⟩
      · rw [hmemS]; simpa [hb] using hp
      · simp [ha, hb]
    · refine ⟨b, ?_, hb⟩
      rw [hmemS]
      have := D.sub_mem (ht _ hp) hp
      simpa using this
  have hβ : ∀ p ∈ S, ∀ α β : K, α • u + β • w = p → ∀ c : K, (c * β) • u ∈ S := by
    intro p hp α β hαβ c
    have h1 := S.sub_mem hp (hl₁ p hp c)
    rw [← hαβ, key₁] at h1
    simpa using h1
  have hα : ∀ p ∈ S, ∀ α β : K, α • u + β • w = p → ∀ c : K, (c * α) • w ∈ S := by
    intro p hp α β hαβ c
    have h1 := S.sub_mem hp (hl₂ p hp c)
    rw [← hαβ, key₂] at h1
    simpa using h1
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp (hS₁ s₀ hs₀)
  have hline : (∀ c : K, c • u ∈ S) ∧ ∀ c : K, c • w ∈ S := by
    by_cases hb : β = 0
    · have ha : α ≠ 0 := by
        rintro rfl
        apply hs₀0
        rw [← hαβ, hb]
        simp
      have hw' : ∀ c : K, c • w ∈ S := fun c => by
        have := hα s₀ hs₀ α β hαβ (c * α⁻¹)
        rwa [mul_assoc, inv_mul_cancel₀ ha, mul_one] at this
      refine ⟨fun c => ?_, hw'⟩
      have h1 := hβ (1 • w) (by simpa using hw' 1) 0 1 (by simp) c
      simpa using h1
    · have hu' : ∀ c : K, c • u ∈ S := fun c => by
        have := hβ s₀ hs₀ α β hαβ (c * β⁻¹)
        rwa [mul_assoc, inv_mul_cancel₀ hb, mul_one] at this
      refine ⟨hu', fun c => ?_⟩
      have h1 := hα (1 • u) (by simpa using hu' 1) 1 0 (by simp) c
      simpa using h1
  have hP : ∀ a ∈ Submodule.span K {u, w}, (a, 0) ∈ D := by
    intro a ha
    obtain ⟨α', β', rfl⟩ := Submodule.mem_span_pair.mp ha
    exact S.add_mem (hline.1 α') (hline.2 β')
  intro a ha b hb
  have h0b : ((0 : V), b) ∈ D := by
    have := D.sub_mem (ht' _ (hP b hb)) (hP b hb)
    simpa using this
  have := D.add_mem (hP a ha) h0b
  simpa using this

end CFSG.RankThree.GF2n.Smith81.OrthC5
