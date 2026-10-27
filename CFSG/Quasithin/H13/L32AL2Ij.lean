module

public import CFSG.Quasithin.H13.L32AL2Ie

public section

namespace CFSG.Quasithin.H13.L32A.L2

variable {Ω : Type*} [Group Ω]

structure S3Like (H : Subgroup Ω) : Prop where
  orders : ∀ g ∈ H, g = 1 ∨ g ^ 2 = 1 ∨ g ^ 3 = 1
  three : ∀ a ∈ H, ∀ a' ∈ H, a ^ 3 = 1 → a ≠ 1 → a' ^ 3 = 1 → a' ≠ 1 → a' = a ∨ a' = a⁻¹
  inv : ∀ a ∈ H, ∀ s ∈ H, a ^ 3 = 1 → s ^ 2 = 1 → s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a⁻¹
  cent : ∀ g ∈ H, ∀ a ∈ H, g ^ 2 = 1 → a ^ 3 = 1 → a ≠ 1 → g * a = a * g → g = 1
  invol : ∃ s ∈ H, s ^ 2 = 1 ∧ s ≠ 1
  elt : ∃ a ∈ H, a ^ 3 = 1 ∧ a ≠ 1

theorem S3Like.of_mulEquiv {H : Subgroup Ω} (e : ↥H ≃* Equiv.Perm (Fin 3)) : S3Like H := by
  have he : ∀ {g : Ω} (hg : g ∈ H), g = 1 ↔ e ⟨g, hg⟩ = 1 := fun {g} hg => by
    rw [map_eq_one_iff e e.injective]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hpow : ∀ {g : Ω} (hg : g ∈ H) (n : ℕ), g ^ n = 1 ↔ e ⟨g, hg⟩ ^ n = 1 := fun {g} hg n => by
    rw [← map_pow, map_eq_one_iff e e.injective]
    exact ⟨fun h => Subtype.ext (by simpa using h), fun h => by simpa using congrArg Subtype.val h⟩
  refine ⟨fun g hg => ?_, fun a ha a' ha' h3 h1 h3' h1' => ?_, fun a ha s hs h3 h2 => ?_,
    fun g hg a ha h2 h3 h1 hc => ?_, ?_, ?_⟩
  · rw [he hg, hpow hg, hpow hg]
    generalize e ⟨g, hg⟩ = p
    revert p
    decide
  · rw [hpow ha] at h3
    rw [hpow ha'] at h3'
    rw [Ne, he ha] at h1
    rw [Ne, he ha'] at h1'
    have key : ∀ p q : Equiv.Perm (Fin 3), p ^ 3 = 1 → p ≠ 1 → q ^ 3 = 1 → q ≠ 1 →
        q = p ∨ q = p⁻¹ := by decide
    rcases key _ _ h3 h1 h3' h1' with h | h
    · left
      have := congrArg Subtype.val (e.injective h)
      exact this
    · right
      have h' : e ⟨a', ha'⟩ = e (⟨a, ha⟩⁻¹) := by rw [h, map_inv]
      exact congrArg Subtype.val (e.injective h')
  · rw [hpow ha] at h3
    rw [hpow hs] at h2
    have key : ∀ p q : Equiv.Perm (Fin 3), p ^ 3 = 1 → q ^ 2 = 1 →
        q * p * q⁻¹ = p ∨ q * p * q⁻¹ = p⁻¹ := by decide
    rcases key _ _ h3 h2 with h | h
    · left
      have h' : e (⟨s, hs⟩ * ⟨a, ha⟩ * ⟨s, hs⟩⁻¹) = e ⟨a, ha⟩ := by
        rw [map_mul, map_mul, map_inv, h]
      exact congrArg Subtype.val (e.injective h')
    · right
      have h' : e (⟨s, hs⟩ * ⟨a, ha⟩ * ⟨s, hs⟩⁻¹) = e (⟨a, ha⟩⁻¹) := by
        rw [map_mul, map_mul, map_inv, map_inv, h]
      exact congrArg Subtype.val (e.injective h')
  · rw [hpow hg] at h2
    rw [hpow ha] at h3
    rw [Ne, he ha] at h1
    rw [he hg]
    have hc' : e ⟨g, hg⟩ * e ⟨a, ha⟩ = e ⟨a, ha⟩ * e ⟨g, hg⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hc
    have key : ∀ p q : Equiv.Perm (Fin 3), p ^ 2 = 1 ∧ q ^ 3 = 1 ∧ q ≠ 1 ∧ p * q = q * p →
        p = 1 := by decide
    exact key _ _ ⟨h2, h3, h1, hc'⟩
  · refine ⟨(e.symm (Equiv.swap 0 1) : Ω), (e.symm (Equiv.swap 0 1)).2, ?_, ?_⟩
    · rw [hpow (e.symm (Equiv.swap 0 1)).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
      decide
    · rw [Ne, he (e.symm (Equiv.swap 0 1)).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
      decide
  · refine ⟨(e.symm (finRotate 3) : Ω), (e.symm (finRotate 3)).2, ?_, ?_⟩
    · rw [hpow (e.symm (finRotate 3)).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
      decide
    · rw [Ne, he (e.symm (finRotate 3)).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
      decide

section Prod

variable {G₁ G₂ : Subgroup Ω} (hinf : G₁ ⊓ G₂ = ⊥) (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
  (h₁ : S3Like G₁) (h₂ : S3Like G₂)
include hinf hc h₁ h₂

omit h₂ in
theorem mem_or_mem_of_conj {k : Ω} (hk : k ∈ G₁ ⊔ G₂) (hk3 : k ^ 3 = 1)
    (hP : ∀ j ∈ G₁ ⊔ G₂, j * k * j⁻¹ = k ∨ j * k * j⁻¹ = k⁻¹) : k ∈ G₁ ∨ k ∈ G₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_comm hc hk
  obtain ⟨ha3, hb3⟩ := pow_eq_one_and_of_mul hinf hc ha hb hk3
  by_cases ha1 : a = 1
  · right
    rw [ha1, one_mul]
    exact hb
  by_cases hb1 : b = 1
  · left
    rw [hb1, mul_one]
    exact ha
  exfalso
  obtain ⟨s, hs, hs2, hs1⟩ := h₁.invol
  have hsb : s * b = b * s := hc s hs b hb
  have hsa : s * a * s⁻¹ = a⁻¹ := by
    rcases h₁.inv a ha s hs ha3 hs2 with h | h
    · exfalso
      exact hs1 (h₁.cent s hs a ha hs2 ha3 ha1 (by
        calc s * a = s * a * s⁻¹ * s := by group
          _ = a * s := by rw [h]))
    · exact h
  have e : s * (a * b) * s⁻¹ = a⁻¹ * b := by
    calc s * (a * b) * s⁻¹ = s * a * s⁻¹ * (s * b * s⁻¹) := by group
      _ = a⁻¹ * b := by rw [hsa, hsb, mul_inv_cancel_right]
  have hab : Commute a b := hc a ha b hb
  rcases hP s (Subgroup.mem_sup_left hs) with h | h <;> rw [e] at h
  ·
    have h' : a⁻¹ = a := mul_right_cancel h
    apply ha1
    calc a = a ^ 3 * (a * a)⁻¹ := by rw [pow_three]; group
      _ = 1 := by rw [ha3]; nth_rewrite 1 [← h']; group
  ·
    rw [hab.mul_inv] at h
    have h' : b = b⁻¹ := mul_left_cancel h
    apply hb1
    calc b = b ^ 3 * (b * b)⁻¹ := by rw [pow_three]; group
      _ = 1 := by rw [hb3]; nth_rewrite 2 [h']; group

omit hinf h₂ in
theorem conj_cases_of_mem {r : Ω} (hr : r ∈ G₁) (hr3 : r ^ 3 = 1) :
    ∀ j ∈ G₁ ⊔ G₂, j * r * j⁻¹ = r ∨ j * r * j⁻¹ = r⁻¹ := by
  intro j hj
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_comm hc hj
  have e : a * b * r * (a * b)⁻¹ = a * r * a⁻¹ := by
    rw [mul_inv_rev, mul_assoc a b r, ← hc r hr b hb]
    group
  rw [e]
  rcases h₁.orders a ha with rfl | h2 | h3
  · left
    group
  · exact h₁.inv r hr a ha hr3 h2
  · by_cases hr1 : r = 1
    · left
      rw [hr1]
      group
    have hc3 : (a * r * a⁻¹) ^ 3 = 1 := by
      rw [show (a * r * a⁻¹) ^ 3 = a * r ^ 3 * a⁻¹ by rw [pow_three, pow_three]; group, hr3]
      group
    have hc1 : a * r * a⁻¹ ≠ 1 := fun h => hr1 (by
      calc r = a⁻¹ * (a * r * a⁻¹) * a := by group
        _ = 1 := by rw [h]; group)
    exact h₁.three r hr _ (mul_mem (mul_mem ha hr) (inv_mem ha)) hr3 hr1 hc3 hc1

omit hc h₁ h₂ in
theorem eq_one_of_mem_mem {a : Ω} (h1 : a ∈ G₁) (h2 : a ∈ G₂) : a = 1 :=
  eq_one_of_mem_of_inf_eq_bot hinf h1 h2

theorem conj_mem_of_pow_three {u : Ω}
    (huN : u ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup Ω) : Set Ω)) (hu3 : u ^ 3 = 1) {r : Ω}
    (hr : r ∈ G₁) (hr3 : r ^ 3 = 1) : u * r * u⁻¹ ∈ G₁ := by
  have hJ : ∀ {k : Ω}, k ∈ G₁ ⊔ G₂ → u * k * u⁻¹ ∈ G₁ ⊔ G₂ := fun hk =>
    (Subgroup.mem_normalizer_iff.mp huN _).mp hk
  have hJ' : ∀ {j : Ω}, j ∈ G₁ ⊔ G₂ → u⁻¹ * j * u ∈ G₁ ⊔ G₂ := fun {j} hj => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem huN) j).mp hj
    rwa [inv_inv] at this
  have hPu : ∀ {k : Ω}, (∀ j ∈ G₁ ⊔ G₂, j * k * j⁻¹ = k ∨ j * k * j⁻¹ = k⁻¹) →
      ∀ j ∈ G₁ ⊔ G₂, j * (u * k * u⁻¹) * j⁻¹ = u * k * u⁻¹ ∨
        j * (u * k * u⁻¹) * j⁻¹ = (u * k * u⁻¹)⁻¹ := by
    intro k hk j hj
    have e : j * (u * k * u⁻¹) * j⁻¹ = u * ((u⁻¹ * j * u) * k * (u⁻¹ * j * u)⁻¹) * u⁻¹ := by
      group
    rw [e]
    rcases hk _ (hJ' hj) with h | h
    · left
      rw [h]
    · right
      rw [h]
      group
  have hpow3 : ∀ {k : Ω}, k ^ 3 = 1 → (u * k * u⁻¹) ^ 3 = 1 := fun {k} hk => by
    rw [show (u * k * u⁻¹) ^ 3 = u * k ^ 3 * u⁻¹ by rw [pow_three, pow_three]; group, hk]
    group
  by_cases hr1 : r = 1
  · rw [hr1, mul_one, mul_inv_cancel]
    exact one_mem _
  have hrJ : r ∈ G₁ ⊔ G₂ := Subgroup.mem_sup_left hr
  set r₁ := u * r * u⁻¹ with hr₁
  set r₂ := u * r₁ * u⁻¹ with hr₂
  have hr₃ : u * r₂ * u⁻¹ = r := by
    rw [hr₂, hr₁]
    calc u * (u * (u * r * u⁻¹) * u⁻¹) * u⁻¹ = u ^ 3 * r * (u ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = r := by rw [hu3]; group
  have hP : ∀ j ∈ G₁ ⊔ G₂, j * r * j⁻¹ = r ∨ j * r * j⁻¹ = r⁻¹ :=
    conj_cases_of_mem hc h₁ hr hr3
  have hP₁ := hPu hP
  have hP₂ := hPu hP₁
  have h13 : r₁ ^ 3 = 1 := hpow3 hr3
  have h23 : r₂ ^ 3 = 1 := hpow3 h13
  have hr₁1 : r₁ ≠ 1 := fun h => hr1 (by
    calc r = u⁻¹ * r₁ * u := by rw [hr₁]; group
      _ = 1 := by rw [h]; group)
  have hr₂1 : r₂ ≠ 1 := fun h => hr₁1 (by
    calc r₁ = u⁻¹ * r₂ * u := by rw [hr₂]; group
      _ = 1 := by rw [h]; group)
  rcases mem_or_mem_of_conj hinf hc h₁ (hJ hrJ) h13 hP₁ with hm | hm
  · exact hm
  exfalso
  rcases mem_or_mem_of_conj hinf hc h₁ (hJ (hJ hrJ)) h23 hP₂ with hm2 | hm2
  ·
    rcases h₁.three r hr r₂ hm2 hr3 hr1 h23 hr₂1 with h | h
    · rw [h] at hr₃
      exact hr1 (eq_one_of_mem_mem hinf hr (hr₃ ▸ hm))
    · have h' : u * r₂ * u⁻¹ = r₁⁻¹ := by rw [h, hr₁]; group
      rw [hr₃] at h'
      exact hr1 (eq_one_of_mem_mem hinf hr (h' ▸ inv_mem hm))
  ·
    rcases h₂.three r₁ hm r₂ hm2 h13 hr₁1 h23 hr₂1 with h | h
    · have h0 : u * r₁ * u⁻¹ = u * r * u⁻¹ := by rw [← hr₂, h, hr₁]
      have h' : r₁ = r := mul_left_cancel (mul_right_cancel h0)
      exact hr1 (eq_one_of_mem_mem hinf hr (h' ▸ hm))
    · have h0 : u * r₁ * u⁻¹ = u * r⁻¹ * u⁻¹ := by rw [← hr₂, h, hr₁]; group
      have h' : r₁ = r⁻¹ := mul_left_cancel (mul_right_cancel h0)
      exact hr1 (inv_eq_one.mp (eq_one_of_mem_mem hinf (inv_mem hr) (h' ▸ hm)))

end Prod

section Main

variable [Finite Ω] {G₁ G₂ : Subgroup Ω}

theorem mem_normalizer_of_s3s3 (hinf : G₁ ⊓ G₂ = ⊥) (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (h₁ : S3Like G₁) (h₂ : S3Like G₂) {u : Ω}
    (huN : u ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup Ω) : Set Ω)) (hu3 : u ^ 3 = 1) :
    u ∈ Subgroup.normalizer (G₁ : Set Ω) := by
  have hinf' : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have huN' : u ∈ Subgroup.normalizer ((G₂ ⊔ G₁ : Subgroup Ω) : Set Ω) := by
    rw [sup_comm]; exact huN
  have hu2N : u⁻¹ ∈ Subgroup.normalizer ((G₂ ⊔ G₁ : Subgroup Ω) : Set Ω) := inv_mem huN'
  have hu2_3 : u⁻¹ ^ 3 = 1 := by rw [inv_pow, hu3, inv_one]
  refine mem_normalizer_of_forall_conj_mem fun g hg => ?_
  rcases h₁.orders g hg with rfl | hg2 | hg3
  · rw [mul_one, mul_inv_cancel]
    exact one_mem _
  ·
    have hJ : u * g * u⁻¹ ∈ G₁ ⊔ G₂ :=
      (Subgroup.mem_normalizer_iff.mp huN _).mp (Subgroup.mem_sup_left hg)
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_comm hc hJ
    obtain ⟨a3, ha3, ha33, ha31⟩ := h₂.elt
    have hpre : u⁻¹ * a3 * u⁻¹⁻¹ ∈ G₂ :=
      conj_mem_of_pow_three hinf' hc' h₂ h₁ hu2N hu2_3 ha3 ha33
    have hgc : g * (u⁻¹ * a3 * u⁻¹⁻¹) = (u⁻¹ * a3 * u⁻¹⁻¹) * g := hc g hg _ hpre
    have hcomm : (u * g * u⁻¹) * a3 = a3 * (u * g * u⁻¹) := by
      have e1 : a3 = u * (u⁻¹ * a3 * u⁻¹⁻¹) * u⁻¹ := by group
      calc u * g * u⁻¹ * a3 = u * (g * (u⁻¹ * a3 * u⁻¹⁻¹)) * u⁻¹ := by
            nth_rewrite 1 [e1]; group
        _ = u * ((u⁻¹ * a3 * u⁻¹⁻¹) * g) * u⁻¹ := by rw [hgc]
        _ = a3 * (u * g * u⁻¹) := by group
    rw [hab] at hcomm
    have h1 : (a * b) * (1 * a3) = (1 * a3) * (a * b) := by simpa using hcomm
    obtain ⟨-, hb3⟩ := commute_and_of_mul hinf hc ha (one_mem G₁) hb ha3 h1
    have hsq : (a * b) ^ 2 = 1 := by
      rw [← hab, show (u * g * u⁻¹) ^ 2 = u * g ^ 2 * u⁻¹ by rw [pow_two, pow_two]; group, hg2]
      group
    obtain ⟨-, hb2⟩ := pow_eq_one_and_of_mul hinf hc ha hb hsq
    have hb1 : b = 1 := h₂.cent b hb a3 ha3 hb2 ha33 ha31 hb3
    rw [hab, hb1, mul_one]
    exact ha
  · exact conj_mem_of_pow_three hinf hc h₁ h₂ huN hu3 hg hg3

end Main

end CFSG.Quasithin.H13.L32A.L2
