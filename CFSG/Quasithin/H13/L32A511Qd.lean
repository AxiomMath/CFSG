module

public import CFSG.Quasithin.H13.L32A511Qc

public section

namespace CFSG.Quasithin.H13.Q511

variable {G : Type*} [Group G]

@[expose] def conjRes (D : Subgroup G) (g : G) (h : ∀ d ∈ D, g * d * g⁻¹ ∈ D) : ↥D →* ↥D where
  toFun d := ⟨g * d * g⁻¹, h d d.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp only [Subgroup.coe_mul]; group

theorem coe_conjRes (D : Subgroup G) (g : G) (h : ∀ d ∈ D, g * d * g⁻¹ ∈ D) (d : ↥D) :
    ((conjRes D g h d : ↥D) : G) = g * d * g⁻¹ := rfl

theorem pow_conj (g d : G) (n : ℕ) : g * d ^ n * g⁻¹ = (g * d * g⁻¹) ^ n := by
  rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]

theorem exists_good_elt [Finite G] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {D₁ Z₁ : Subgroup G}
    (hZD : Z₁ ≤ D₁) (hZc : ∀ z ∈ Z₁, ∀ d ∈ D₁, z * d = d * z)
    (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₁, a * b * a⁻¹ * b⁻¹ ∈ Z₁) (hexp : ∀ d ∈ D₁, d ^ p = 1)
    {x s c : G} (hx3 : x ^ 3 = 1) (hs2 : s ^ 2 = 1) (hc2 : c ^ 2 = 1)
    (hsx : s * x * s⁻¹ = x⁻¹) (hcx : c * x = x * c) (hcs : c * s = s * c)
    (hxD : ∀ d ∈ D₁, x * d * x⁻¹ ∈ D₁) (hsD : ∀ d ∈ D₁, s * d * s⁻¹ ∈ D₁)
    (hcD : ∀ d ∈ D₁, c * d * c⁻¹ ∈ D₁) (hxZ : ∀ z ∈ Z₁, x * z * x⁻¹ ∈ Z₁)
    (hsZ : ∀ z ∈ Z₁, s * z * s⁻¹ ∈ Z₁) (hcZ : ∀ z ∈ Z₁, c * z * c⁻¹ ∈ Z₁)
    {d₀ : G} (hd₀ : d₀ ∈ D₁) (hnt : x * d₀ * x⁻¹ * d₀⁻¹ ∉ Z₁) :
    ∃ r ∈ D₁, s * r * s⁻¹ = r⁻¹ ∧ (c * r * c⁻¹ = r ∨ c * r * c⁻¹ = r⁻¹) ∧
      r * (x * r * x⁻¹) * (x * (x * r * x⁻¹) * x⁻¹) ∈ Z₁ ∧
      ∀ k : ℕ, (x * r * x⁻¹) * (r ^ k)⁻¹ ∉ Z₁ := by
  classical
  set N : Subgroup ↥D₁ := Z₁.subgroupOf D₁ with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (n : G) * g = g * n := hZc _ hn _ g.2
    have : ((g * n * g⁻¹ : ↥D₁) : G) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h1]
      group
    rw [this]
    exact hn
  have hmk : ∀ a b : ↥D₁, (a : ↥D₁ ⧸ N) = (b : ↥D₁ ⧸ N) ↔ (a : G) * (b : G)⁻¹ ∈ Z₁ := by
    intro a b
    rw [QuotientGroup.eq_iff_div_mem, hN, Subgroup.mem_subgroupOf]
    simp [div_eq_mul_inv]
  have hQc : ∀ a b : ↥D₁ ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    have := hcomm a a.2 b b.2
    simpa [mul_assoc] using this
  have hleN : ∀ (g : G) (hD : ∀ d ∈ D₁, g * d * g⁻¹ ∈ D₁), (∀ z ∈ Z₁, g * z * g⁻¹ ∈ Z₁) →
      N ≤ N.comap (conjRes D₁ g hD) := by
    intro g hD hZ n hn
    rw [Subgroup.mem_comap, hN, Subgroup.mem_subgroupOf, coe_conjRes]
    exact hZ _ hn
  let Xb := QuotientGroup.map N N (conjRes D₁ x hxD) (hleN x hxD hxZ)
  let Sb := QuotientGroup.map N N (conjRes D₁ s hsD) (hleN s hsD hsZ)
  let Cb := QuotientGroup.map N N (conjRes D₁ c hcD) (hleN c hcD hcZ)
  have hXmk : ∀ d : ↥D₁, Xb d = ((conjRes D₁ x hxD d : ↥D₁) : ↥D₁ ⧸ N) := fun d =>
    QuotientGroup.map_mk _ _ _ _ d
  have hSmk : ∀ d : ↥D₁, Sb d = ((conjRes D₁ s hsD d : ↥D₁) : ↥D₁ ⧸ N) := fun d =>
    QuotientGroup.map_mk _ _ _ _ d
  have hCmk : ∀ d : ↥D₁, Cb d = ((conjRes D₁ c hcD d : ↥D₁) : ↥D₁ ⧸ N) := fun d =>
    QuotientGroup.map_mk _ _ _ _ d
  have hx1 : x⁻¹ = x ^ 2 := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, hx3]
  have hs1 : s⁻¹ = s := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_two, hs2]
  have hc1 : c⁻¹ = c := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_two, hc2]
  let _ : CommGroup (↥D₁ ⧸ N) := { (inferInstance : Group (↥D₁ ⧸ N)) with mul_comm := hQc }
  have hX3 : ∀ q, Xb (Xb (Xb q)) = q := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hXmk, hXmk, hXmk]
    congr 1
    ext
    simp only [coe_conjRes]
    calc x * (x * (x * (d : G) * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * d * (x ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = d := by rw [hx3]; group
  have hS2 : ∀ q, Sb (Sb q) = q := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hSmk, hSmk]
    congr 1
    ext
    simp only [coe_conjRes]
    calc s * (s * (d : G) * s⁻¹) * s⁻¹ = s ^ 2 * d * (s ^ 2)⁻¹ := by
          rw [pow_two]; group
      _ = d := by rw [hs2]; group
  have hC2 : ∀ q, Cb (Cb q) = q := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hCmk, hCmk]
    congr 1
    ext
    simp only [coe_conjRes]
    calc c * (c * (d : G) * c⁻¹) * c⁻¹ = c ^ 2 * d * (c ^ 2)⁻¹ := by
          rw [pow_two]; group
      _ = d := by rw [hc2]; group
  have hSX : ∀ q, Sb (Xb q) = Xb (Xb (Sb q)) := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hXmk, hSmk, hSmk, hXmk, hXmk]
    congr 1
    ext
    simp only [coe_conjRes]
    calc s * (x * (d : G) * x⁻¹) * s⁻¹ =
          (s * x * s⁻¹) * (s * d * s⁻¹) * (s * x * s⁻¹)⁻¹ := by group
      _ = x ^ 2 * (s * d * s⁻¹) * (x ^ 2)⁻¹ := by
          rw [hsx, inv_inv, hx1, show (x ^ 2)⁻¹ = x by rw [← hx1, inv_inv]]
      _ = x * (x * (s * d * s⁻¹) * x⁻¹) * x⁻¹ := by rw [pow_two]; group
  have hCX : ∀ q, Cb (Xb q) = Xb (Cb q) := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hXmk, hCmk, hCmk, hXmk]
    congr 1
    ext
    simp only [coe_conjRes]
    calc c * (x * (d : G) * x⁻¹) * c⁻¹ = (c * x) * d * (c * x)⁻¹ := by group
      _ = (x * c) * d * (x * c)⁻¹ := by rw [hcx]
      _ = x * (c * d * c⁻¹) * x⁻¹ := by group
  have hCS : ∀ q, Cb (Sb q) = Sb (Cb q) := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hSmk, hCmk, hCmk, hSmk]
    congr 1
    ext
    simp only [coe_conjRes]
    calc c * (s * (d : G) * s⁻¹) * c⁻¹ = (c * s) * d * (c * s)⁻¹ := by group
      _ = (s * c) * d * (s * c)⁻¹ := by rw [hcs]
      _ = s * (c * d * c⁻¹) * s⁻¹ := by group
  have hexpQ : ∀ q : ↥D₁ ⧸ N, q ^ p = 1 := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow]
    have : d ^ p = 1 := Subtype.ext (by simpa using hexp d d.2)
    rw [this, QuotientGroup.mk_one]
  have hq₀ : Xb ((⟨d₀, hd₀⟩ : ↥D₁) : ↥D₁ ⧸ N) ≠ ((⟨d₀, hd₀⟩ : ↥D₁) : ↥D₁ ⧸ N) := by
    rw [hXmk, Ne, hmk, coe_conjRes]
    exact hnt
  obtain ⟨m, hm0, hSm, hCm, hNm, hind⟩ := exists_vec (M := Additive (↥D₁ ⧸ N)) hp hp5
    (fun q => by
      apply Additive.toMul.injective
      simp [hexpQ])
    (MonoidHom.toAdditive Xb) (MonoidHom.toAdditive Sb) (MonoidHom.toAdditive Cb)
    (fun q => by simp [hX3])
    (fun q => by simp [hS2])
    (fun q => by simp [hC2])
    (fun q => by simp [hSX])
    (fun q => by simp [hCX])
    (fun q => by simp [hCS])
    (q₀ := Additive.ofMul ((⟨d₀, hd₀⟩ : ↥D₁) : ↥D₁ ⧸ N))
    (by
      intro h
      apply hq₀
      have := congrArg Additive.toMul h
      simpa [MonoidHom.coe_toAdditive] using this)
  set m' : ↥D₁ ⧸ N := Additive.toMul m with hm'
  have hSm' : Sb m' = m'⁻¹ := by
    have := congrArg Additive.toMul hSm
    simpa [MonoidHom.coe_toAdditive] using this
  have hCm' : Cb m' = m' ∨ Cb m' = m'⁻¹ := by
    rcases hCm with h | h
    · left
      have := congrArg Additive.toMul h
      simpa [MonoidHom.coe_toAdditive] using this
    · right
      have := congrArg Additive.toMul h
      simpa [MonoidHom.coe_toAdditive] using this
  have hNm' : m' * Xb m' * Xb (Xb m') = 1 := by
    have := congrArg Additive.toMul hNm
    simpa [MonoidHom.coe_toAdditive] using this
  have hind' : ∀ k : ℕ, Xb m' ≠ m' ^ k := by
    intro k h
    apply hind k
    apply Additive.toMul.injective
    simpa [MonoidHom.coe_toAdditive] using h
  obtain ⟨d₃, hd₃⟩ := QuotientGroup.mk_surjective m'
  have hmkeq : ∀ a b : ↥D₁, (a : ↥D₁ ⧸ N) = b → (a : G) * (b : G)⁻¹ ∈ Z₁ :=
    fun a b h => (hmk a b).mp h
  obtain ⟨b₀, hb₀D, hb₀Z, hb₀2, hb₀s, hb₀fix, hcb₀⟩ : ∃ b₀ : G,
      (∀ d ∈ D₁, b₀ * d * b₀⁻¹ ∈ D₁) ∧ (∀ z ∈ Z₁, b₀ * z * b₀⁻¹ ∈ Z₁) ∧ b₀⁻¹ = b₀ ∧
      b₀ * s = s * b₀ ∧ b₀ * d₃ * b₀⁻¹ * (d₃ : G)⁻¹ ∈ Z₁ ∧
      (∀ r : G, b₀ * r * b₀⁻¹ = r → s * r * s⁻¹ = r⁻¹ →
        (c * r * c⁻¹ = r ∨ c * r * c⁻¹ = r⁻¹)) := by
    rcases hCm' with h | h
    · refine ⟨c, hcD, hcZ, hc1, hcs, ?_, fun r hr _ => Or.inl hr⟩
      have := hmkeq (conjRes D₁ c hcD d₃) d₃ (by rw [← hCmk, hd₃, h])
      simpa [coe_conjRes] using this
    · refine ⟨s * c, fun d hd => ?_, fun z hz => ?_, ?_, ?_, ?_, fun r hr hrs => Or.inr ?_⟩
      · have := hsD _ (hcD d hd)
        simpa [mul_assoc] using this
      · have := hsZ _ (hcZ z hz)
        simpa [mul_assoc] using this
      · rw [mul_inv_rev, hs1, hc1, hcs]
      · rw [mul_assoc, ← hcs, ← mul_assoc]
      · have h1 : Sb (Cb (d₃ : ↥D₁ ⧸ N)) = (d₃ : ↥D₁ ⧸ N) := by
          rw [hd₃, h, map_inv, hSm', inv_inv]
        rw [hCmk, hSmk] at h1
        have := hmkeq _ d₃ h1
        simp only [coe_conjRes] at this
        simpa [mul_assoc] using this
      · have e : c = s * (s * c) := by rw [← mul_assoc, ← pow_two, hs2, one_mul]
        rw [e, show s * (s * c) * r * (s * (s * c))⁻¹ = s * ((s * c) * r * (s * c)⁻¹) * s⁻¹ by
          group, hr, hrs]
  have hbb : b₀ * b₀ = 1 := by
    nth_rewrite 2 [← hb₀2]
    exact mul_inv_cancel b₀
  obtain ⟨ζ, hζ⟩ : ∃ ζ : G, ζ = b₀ * d₃ * b₀⁻¹ * (d₃ : G)⁻¹ := ⟨_, rfl⟩
  have hζZ : ζ ∈ Z₁ := hζ ▸ hb₀fix
  have hζD : ζ ∈ D₁ := hZD hζZ
  have hζb : b₀ * ζ * b₀⁻¹ = ζ⁻¹ := by
    calc b₀ * ζ * b₀⁻¹ = (b₀ * b₀) * (d₃ * b₀⁻¹ * (d₃ : G)⁻¹ * b₀⁻¹) := by rw [hζ]; group
      _ = d₃ * b₀⁻¹ * (d₃ : G)⁻¹ * b₀⁻¹ := by rw [hbb, one_mul]
      _ = d₃ * b₀ * (d₃ : G)⁻¹ * b₀⁻¹ := by nth_rewrite 1 [hb₀2]; rfl
      _ = ζ⁻¹ := by rw [hζ]; group
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, 2 * k₁ = p + 1 := by
    obtain ⟨t, ht⟩ := hpodd
    exact ⟨t + 1, by omega⟩
  have hζp : ζ ^ p = 1 := hexp ζ hζD
  have h2 : ζ ^ k₁ * ζ ^ k₁ = ζ := by
    rw [← pow_add, ← two_mul, hk₁, pow_succ, hζp, one_mul]
  have hζk : (ζ⁻¹) ^ k₁ * ζ = ζ ^ k₁ := by
    calc (ζ⁻¹) ^ k₁ * ζ = (ζ ^ k₁)⁻¹ * (ζ ^ k₁ * ζ ^ k₁) := by rw [h2, inv_pow]
      _ = ζ ^ k₁ := by group
  obtain ⟨d₄, hd₄⟩ : ∃ d₄ : G, d₄ = ζ ^ k₁ * d₃ := ⟨_, rfl⟩
  have hd₄D : d₄ ∈ D₁ := hd₄ ▸ D₁.mul_mem (D₁.pow_mem hζD k₁) d₃.2
  have hd₄b : b₀ * d₄ * b₀⁻¹ = d₄ := by
    have e1 : b₀ * d₃ * b₀⁻¹ = ζ * d₃ := by rw [hζ]; group
    calc b₀ * d₄ * b₀⁻¹ = (b₀ * ζ ^ k₁ * b₀⁻¹) * (b₀ * d₃ * b₀⁻¹) := by rw [hd₄]; group
      _ = (b₀ * ζ * b₀⁻¹) ^ k₁ * (ζ * d₃) := by rw [pow_conj, e1]
      _ = (ζ⁻¹) ^ k₁ * ζ * d₃ := by rw [hζb, mul_assoc]
      _ = d₄ := by rw [hζk, hd₄]
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : G, r₀ = d₄ * (s * d₄ * s⁻¹)⁻¹ := ⟨_, rfl⟩
  have hr₀D : r₀ ∈ D₁ := hr₀ ▸ D₁.mul_mem hd₄D (D₁.inv_mem (hsD _ hd₄D))
  have hss : s * s = 1 := by rw [← pow_two, hs2]
  have hr₀s : s * r₀ * s⁻¹ = r₀⁻¹ := by
    calc s * r₀ * s⁻¹ = s * d₄ * s⁻¹ * ((s * s) * d₄ * (s * s)⁻¹)⁻¹ := by rw [hr₀]; group
      _ = r₀⁻¹ := by rw [hss, hr₀]; group
  have hr₀b : b₀ * r₀ * b₀⁻¹ = r₀ := by
    calc b₀ * r₀ * b₀⁻¹ = (b₀ * d₄ * b₀⁻¹) * ((b₀ * s) * d₄ * (b₀ * s)⁻¹)⁻¹ := by
          rw [hr₀]; group
      _ = (b₀ * d₄ * b₀⁻¹) * ((s * b₀) * d₄ * (s * b₀)⁻¹)⁻¹ := by rw [hb₀s]
      _ = (b₀ * d₄ * b₀⁻¹) * (s * (b₀ * d₄ * b₀⁻¹) * s⁻¹)⁻¹ := by group
      _ = r₀ := by rw [hd₄b, hr₀]
  obtain ⟨r, hr⟩ : ∃ r : G, r = r₀ ^ k₁ := ⟨_, rfl⟩
  have hrD : r ∈ D₁ := hr ▸ D₁.pow_mem hr₀D k₁
  have hrs : s * r * s⁻¹ = r⁻¹ := by rw [hr, pow_conj, hr₀s, inv_pow]
  have hrb : b₀ * r * b₀⁻¹ = r := by rw [hr, pow_conj, hr₀b]
  have himg : ((⟨r, hrD⟩ : ↥D₁) : ↥D₁ ⧸ N) = m' := by
    have h4 : ((⟨d₄, hd₄D⟩ : ↥D₁) : ↥D₁ ⧸ N) = m' := by
      rw [← hd₃, hmk]
      have : d₄ * (d₃ : G)⁻¹ = ζ ^ k₁ := by rw [hd₄]; group
      rw [this]
      exact Z₁.pow_mem hζZ k₁
    have hs4 : ((⟨s * d₄ * s⁻¹, hsD _ hd₄D⟩ : ↥D₁) : ↥D₁ ⧸ N) = m'⁻¹ := by
      rw [← hSm', ← h4, hSmk]
      rfl
    have h0 : ((⟨r₀, hr₀D⟩ : ↥D₁) : ↥D₁ ⧸ N) = m' * m' := by
      have : (⟨r₀, hr₀D⟩ : ↥D₁) = ⟨d₄, hd₄D⟩ * (⟨s * d₄ * s⁻¹, hsD _ hd₄D⟩ : ↥D₁)⁻¹ :=
        Subtype.ext hr₀
      rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h4, hs4, inv_inv]
    have : (⟨r, hrD⟩ : ↥D₁) = (⟨r₀, hr₀D⟩ : ↥D₁) ^ k₁ := Subtype.ext (by simp [hr])
    rw [this, QuotientGroup.mk_pow, h0, ← pow_two, ← pow_mul, hk₁, pow_succ, hexpQ, one_mul]
  refine ⟨r, hrD, hrs, hcb₀ r hrb hrs, ?_, fun k hk => ?_⟩
  ·
    have h1 : (((⟨r, hrD⟩ : ↥D₁) * conjRes D₁ x hxD ⟨r, hrD⟩ *
        conjRes D₁ x hxD (conjRes D₁ x hxD ⟨r, hrD⟩) : ↥D₁) : ↥D₁ ⧸ N) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, ← hXmk, ← hXmk, ← hXmk, himg, hNm']
    rw [QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at h1
    simpa [coe_conjRes] using h1
  ·
    apply hind' k
    rw [← himg, hXmk, ← QuotientGroup.mk_pow, hmk]
    simpa [coe_conjRes] using hk

end CFSG.Quasithin.H13.Q511
