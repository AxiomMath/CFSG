module

public import CFSG.Walter.W67.Section5.P56AbStab
public import CFSG.Walter.W67.Section5.P56AbZsig

public section

namespace CFSG.Walter.W67

open P56Ab

namespace P56AbData

variable {G : Type} [Group G] [Finite G] (d : P56AbData G)

theorem exists_zsigmondy : ∃ v : ℕ, v.Prime ∧ orderOf (3 : ZMod v) = d.n :=
  exists_orderOf_three_eq (by have := d.three_le_n; omega) d.odd_n

theorem B_comm {a b : G} (ha : a ∈ d.B) (hb : b ∈ d.B) : a * b = b * a := by
  have := d.B_cyclic
  let _ : CommGroup d.B := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : d.B) ⟨b, hb⟩)

section zsig

variable {v : ℕ}

theorem v_dvd_iff (hvn : orderOf (3 : ZMod v) = d.n) (k : ℕ) : v ∣ 3 ^ k - 1 ↔ d.n ∣ k :=
  dvd_three_pow_sub_one_iff_of_orderOf hvn k

theorem v_ne_two [hv : Fact v.Prime] (hvn : orderOf (3 : ZMod v) = d.n) : v ≠ 2 := by
  rintro rfl
  have h31 : (3 : ZMod 2) = 1 := rfl
  rw [h31, orderOf_one] at hvn
  have := d.three_le_n
  omega

theorem v_dvd_card_B [hv : Fact v.Prime] (hvn : orderOf (3 : ZMod v) = d.n) : v ∣ Nat.card d.B := by
  have h1 : v ∣ 3 ^ d.n - 1 := (d.v_dvd_iff hvn d.n).mpr dvd_rfl
  rw [← d.card_B] at h1
  rcases (Nat.Prime.dvd_mul hv.out).mp h1 with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hv.out Nat.prime_two).mp h) (d.v_ne_two hvn)
  · exact h

@[expose] def U (v : ℕ) : Subgroup G where
  carrier := {b | b ∈ d.B ∧ b ^ (v ^ (Nat.card d.B).factorization v) = 1}
  one_mem' := ⟨d.B.one_mem, one_pow _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨d.B.mul_mem ha hb, by rw [(Commute.mul_pow (d.B_comm ha hb) _), ha', hb', one_mul]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨d.B.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩

theorem mem_U {b : G} :
    b ∈ d.U v ↔ b ∈ d.B ∧ b ^ (v ^ (Nat.card d.B).factorization v) = 1 := Iff.rfl

theorem U_le_B : d.U v ≤ d.B := fun _ hb => hb.1

theorem U_isPGroup : IsPGroup v (d.U v) :=
  fun x => ⟨_, Subtype.ext (by simpa using x.2.2)⟩

theorem exists_mem_U_orderOf [hv : Fact v.Prime] (hvn : orderOf (3 : ZMod v) = d.n) :
    ∃ u ∈ d.U v, orderOf u = v := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' v (d.v_dvd_card_B hvn)
  refine ⟨u, ⟨u.2, ?_⟩, by rw [← Subgroup.orderOf_coe] at hu; exact hu⟩
  have h1 : (Nat.card d.B).factorization v ≠ 0 := by
    have := (Nat.Prime.dvd_iff_one_le_factorization hv.out Nat.card_pos.ne').mp
      (d.v_dvd_card_B hvn)
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h1
  rw [hk, pow_succ, pow_mul']
  have : (u : G) ^ v = 1 := by
    rw [← Subgroup.orderOf_coe] at hu
    rw [← hu, pow_orderOf_eq_one]
  rw [this, one_pow]

theorem U_ne_bot [hv : Fact v.Prime] (hvn : orderOf (3 : ZMod v) = d.n) : d.U v ≠ ⊥ := by
  obtain ⟨u, hu, hou⟩ := d.exists_mem_U_orderOf hvn
  intro h
  rw [h, Subgroup.mem_bot] at hu
  rw [hu, orderOf_one] at hou
  exact hv.out.one_lt.ne hou

theorem H_le_normalizer_U : d.H ≤ Subgroup.normalizer (d.U v : Set G) := by
  intro h hh
  apply Sec53.mem_normalizer_of_conj_le
  rintro b ⟨hb, hb'⟩
  refine ⟨(Subgroup.mem_normalizer_iff.mp (d.H_le_normalizer_B hh) b).mp hb, ?_⟩
  rw [conj_pow, hb', mul_one, mul_inv_cancel]

theorem U_le_centralizer_J : d.U v ≤ Subgroup.centralizer ({d.J} : Set G) :=
  d.U_le_B.trans d.B_le

theorem U_le_NV : d.U v ≤ d.NV := d.U_le_B.trans d.B_le_NV

theorem P₀_faithful_U [hv : Fact v.Prime] (hvn : orderOf (3 : ZMod v) = d.n) :
    ∀ y ∈ d.P₀, (∀ u ∈ d.U v, y * u = u * y) → y = 1 := by
  intro y hy hyU
  by_contra hy1
  apply d.U_ne_bot hvn
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have h1 : u ^ (3 ^ (d.n / 3) - 1) = 1 := d.centralizer_B y hy hy1 u (d.U_le_B hu) (hyU u hu)
  have h2 : u ^ (v ^ (Nat.card d.B).factorization v) = 1 := hu.2
  have hcop : Nat.Coprime (3 ^ (d.n / 3) - 1) (v ^ (Nat.card d.B).factorization v) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hv.out, d.v_dvd_iff hvn]
    intro h
    have h3 := d.three_dvd_n
    have h9 := d.three_le_n
    have hpos : 0 < d.n / 3 := Nat.div_pos (by omega) (by norm_num)
    have := Nat.le_of_dvd hpos h
    omega
  have := Nat.Coprime.gcd_eq_one hcop
  have h3 : orderOf u ∣ Nat.gcd (3 ^ (d.n / 3) - 1) (v ^ (Nat.card d.B).factorization v) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [this] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem eq_bot_or_eq_of_U_le_normalizer [hv : Fact v.Prime] (hvn : orderOf (3 : ZMod v) = d.n)
    {P : Subgroup G} (hP : P = d.P₁ ∨ P = d.P₂) {R : Subgroup G} (hRP : R ≤ P)
    (hUR : d.U v ≤ Subgroup.normalizer (R : Set G)) : R = ⊥ ∨ R = P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPcard : Nat.card P = 3 ^ d.n := by rcases hP with rfl | rfl <;> simp [d.card_P₁, d.card_P₂]
  have hfpf : ∀ b ∈ d.B, b ≠ 1 → ∀ y ∈ P, b * y = y * b → y = 1 := by
    rcases hP with rfl | rfl
    · exact d.fixedPointFree₁
    · exact d.fixedPointFree₂
  obtain ⟨u, hu, hou⟩ := d.exists_mem_U_orderOf hvn
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hou
    exact hv.out.one_lt.ne hou
  set Z := Subgroup.zpowers u
  have hZR : Z ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr (hUR hu)
  have hZp : IsPGroup v Z := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hou, pow_one]
  let _ : MulDistribMulAction Z R := Subgroup.conjMulDistribMulActionOfLeNormalizer Z R hZR
  have hmod := hZp.card_modEq_card_fixedPoints R
  have hfix : Nat.card (MulAction.fixedPoints Z R) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, fun z => smul_one z⟩⟩⟩
    have key : ∀ r : MulAction.fixedPoints Z R, r = ⟨1, fun z => smul_one z⟩ := by
      intro r
      apply Subtype.ext
      apply Subtype.ext
      have hr := r.2 ⟨u, Subgroup.mem_zpowers u⟩
      have hr' : u * ((r : R) : G) * u⁻¹ = (r : R) := congrArg Subtype.val hr
      have hcomm : u * ((r : R) : G) = ((r : R) : G) * u := by
        calc u * ((r : R) : G) = u * ((r : R) : G) * u⁻¹ * u := by group
          _ = ((r : R) : G) * u := by rw [hr']
      exact hfpf u (d.U_le_B hu) hu1 _ (hRP (r : R).2) hcomm
    rw [key a, key b]
  rw [hfix] at hmod
  have hRp : IsPGroup 3 R := by
    have hPp : IsPGroup 3 P := by
      rcases hP with rfl | rfl
      · exact fun x => ⟨1, Subtype.ext (by simpa using d.P₁_pow x.2)⟩
      · exact fun x => ⟨1, Subtype.ext (by simpa using d.P₂_pow x.2)⟩
    exact hPp.to_le hRP
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hRp
  have hmn : m ≤ d.n := by
    have := Subgroup.card_dvd_of_le hRP
    rw [hm, hPcard] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hdvd : v ∣ 3 ^ m - 1 := by
    rw [hm] at hmod
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hmod.symm
  rw [d.v_dvd_iff hvn] at hdvd
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · left
    rw [h0, pow_zero] at hm
    exact Subgroup.eq_bot_of_card_eq R hm
  · right
    have hmn' : m = d.n := le_antisymm hmn (Nat.le_of_dvd h0 hdvd)
    apply Subgroup.eq_of_le_of_card_ge hRP
    rw [hm, hPcard, hmn']

end zsig

omit [Finite G] in
theorem conj_eq_inv_of_fpf {A : Type*} [Group A] {X : Subgroup A} [Finite X] {ι : A}
    (hι : ι * ι = 1) (hιX : ι ∈ Subgroup.normalizer (X : Set A))
    (hC : ∀ x ∈ X, ι * x = x * ι → x = 1) : ∀ z ∈ X, ι * z * ι⁻¹ = z⁻¹ := by
  have hιinv : ι⁻¹ = ι := by rw [inv_eq_iff_mul_eq_one, hι]
  let f : X → X := fun x =>
    ⟨(x : A)⁻¹ * (ι * x * ι⁻¹), X.mul_mem (X.inv_mem x.2)
      ((Subgroup.mem_normalizer_iff.mp hιX x).mp x.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h : (x : A)⁻¹ * (ι * x * ι⁻¹) = (y : A)⁻¹ * (ι * y * ι⁻¹) := congrArg Subtype.val hxy
    have hyx : (y : A) * (x : A)⁻¹ ∈ X := X.mul_mem y.2 (X.inv_mem x.2)
    have hcomm : ι * ((y : A) * (x : A)⁻¹) = ((y : A) * (x : A)⁻¹) * ι := by
      have h' : ι * (y : A) * ι⁻¹ * (ι * x * ι⁻¹)⁻¹ = (y : A) * (x : A)⁻¹ := by
        calc ι * (y : A) * ι⁻¹ * (ι * x * ι⁻¹)⁻¹
            = (y : A) * ((y : A)⁻¹ * (ι * y * ι⁻¹)) * ((x : A)⁻¹ * (ι * x * ι⁻¹))⁻¹ *
              (x : A)⁻¹ := by group
          _ = (y : A) * (x : A)⁻¹ := by rw [← h]; group
      calc ι * ((y : A) * (x : A)⁻¹) = (ι * (y : A) * ι⁻¹ * (ι * x * ι⁻¹)⁻¹) * ι := by group
        _ = ((y : A) * (x : A)⁻¹) * ι := by rw [h']
    have := hC _ hyx hcomm
    rw [mul_inv_eq_one] at this
    exact Subtype.ext this.symm
  intro z hz
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hf ⟨z, hz⟩
  have hz' : z = (x : A)⁻¹ * (ι * x * ι⁻¹) := (congrArg Subtype.val hx).symm
  rw [hz', hιinv]
  calc ι * ((x : A)⁻¹ * (ι * x * ι)) * ι = ι * (x : A)⁻¹ * ι * x * (ι * ι) := by group
    _ = ((x : A)⁻¹ * (ι * x * ι))⁻¹ := by
        rw [hι, mul_one]
        simp only [mul_inv_rev, inv_inv, hιinv]
        group

@[expose] def fixV (X : Subgroup (MulAut d.V)) : Subgroup G where
  carrier := {m | ∃ h : m ∈ d.V, ∀ α ∈ X, α ⟨m, h⟩ = ⟨m, h⟩}
  one_mem' := ⟨d.V.one_mem, fun α _ => map_one α⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨d.V.mul_mem ha hb, fun α hα => ?_⟩
    have := map_mul α ⟨a, ha⟩ ⟨b, hb⟩
    rw [ha' α hα, hb' α hα] at this
    exact this
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨d.V.inv_mem ha, fun α hα => ?_⟩
    have := map_inv α ⟨a, ha⟩
    rw [ha' α hα] at this
    exact this

theorem fixV_le_V (X : Subgroup (MulAut d.V)) : d.fixV X ≤ d.V := fun _ ⟨h, _⟩ => h

theorem mem_fixV {X : Subgroup (MulAut d.V)} {m : d.V} :
    (m : G) ∈ d.fixV X ↔ ∀ α ∈ X, α m = m := by
  constructor
  · rintro ⟨_, h⟩ α hα
    exact h α hα
  · intro h
    exact ⟨m.2, h⟩

theorem fixV_ne_bot {X : Subgroup (MulAut d.V)} (hX : IsPGroup 3 X) : d.fixV X ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := hX.card_modEq_card_fixedPoints d.V
  rw [d.card_V] at hmod
  have h3 : 3 ∣ Nat.card (MulAction.fixedPoints X d.V) := by
    have h0 : 3 ^ (2 * d.n) ≡ 0 [MOD 3] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self 3 (by have := d.three_le_n; omega))
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans h0)
  intro hbot
  have hone : Nat.card (MulAction.fixedPoints X d.V) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, fun x => smul_one x⟩⟩⟩
    have key : ∀ r : MulAction.fixedPoints X d.V, r = ⟨1, fun x => smul_one x⟩ := by
      intro r
      apply Subtype.ext
      apply Subtype.ext
      have hr : ((r : d.V) : G) ∈ d.fixV X := d.mem_fixV.mpr fun α hα => r.2 ⟨α, hα⟩
      rw [hbot, Subgroup.mem_bot] at hr
      exact hr
    rw [key a, key b]
  rw [hone] at h3
  norm_num at h3

theorem mem_normalizer_fixV {X : Subgroup (MulAut d.V)} {g : G} (hg : g ∈ d.NV)
    (hgX : d.φ ⟨g, hg⟩ ∈ Subgroup.normalizer (X : Set (MulAut d.V))) :
    g ∈ Subgroup.normalizer (d.fixV X : Set G) := by
  apply Sec53.mem_normalizer_of_conj_le
  rintro m ⟨hm, hfix⟩
  have hgm : g * m * g⁻¹ ∈ d.V := (Subgroup.mem_normalizer_iff.mp hg m).mp hm
  refine ⟨hgm, fun α hα => ?_⟩
  have h1 : (d.φ ⟨g, hg⟩)⁻¹ * α * d.φ ⟨g, hg⟩ ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgX) α).mp hα
    simpa using this
  have h2 := hfix _ h1
  have hm' : (⟨g * m * g⁻¹, hgm⟩ : d.V) = d.φ ⟨g, hg⟩ ⟨m, hm⟩ := rfl
  rw [hm', ← MulAut.mul_apply]
  have : α * d.φ ⟨g, hg⟩ = d.φ ⟨g, hg⟩ * ((d.φ ⟨g, hg⟩)⁻¹ * α * d.φ ⟨g, hg⟩) := by group
  rw [this, MulAut.mul_apply, h2]

theorem exists_decomp {R : Subgroup G} (hRV : R ≤ d.V)
    (hJR : d.J ∈ Subgroup.normalizer (R : Set G)) {m : G} (hm : m ∈ R) :
    ∃ a ∈ R ⊓ d.P₁, ∃ b ∈ R ⊓ d.P₂, a * b = m := by
  obtain ⟨a, ha, b, hb, rfl⟩ := d.mem_V.mp (hRV hm)
  have hJm : d.J * (a * b) * d.J⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hJR _).mp hm
  rw [d.J_conj_V ha hb] at hJm
  have ha2 : a * b * (a * b⁻¹) = a ^ 2 := by
    calc a * b * (a * b⁻¹) = a * (b * a) * b⁻¹ := by group
      _ = a * (a * b) * b⁻¹ := by rw [← d.P₁_comm_P₂ a ha b hb]
      _ = a ^ 2 := by rw [sq]; group
  have haR : a ∈ R := by
    have h1 : a ^ 2 ∈ R := ha2 ▸ R.mul_mem hm hJm
    have : a = (a ^ 2) ^ 2 := by
      rw [← pow_mul]
      have h3 := d.P₁_pow ha
      calc a = a ^ 3 * a := by rw [h3, one_mul]
        _ = a ^ (2 * 2) := by rw [← pow_succ]
    rw [this]
    exact R.pow_mem h1 2
  have hbR : b ∈ R := by
    have : b = a⁻¹ * (a * b) := by group
    rw [this]
    exact R.mul_mem (R.inv_mem haR) hm
  exact ⟨a, Subgroup.mem_inf.mpr ⟨haR, ha⟩, b, Subgroup.mem_inf.mpr ⟨hbR, hb⟩, rfl⟩

theorem Jbar_apply_coe (m : d.V) : ((d.Jbar m : d.V) : G) = d.J * m * d.J⁻¹ := rfl

theorem mul_Jbar_mem_P₁ (m : d.V) : (m : G) * (d.Jbar m : G) ∈ d.P₁ := by
  obtain ⟨a, ha, b, hb, hab⟩ := d.mem_V.mp m.2
  rw [Jbar_apply_coe, ← hab, d.J_conj_V ha hb]
  have : a * b * (a * b⁻¹) = a * a := by
    calc a * b * (a * b⁻¹) = a * (b * a) * b⁻¹ := by group
      _ = a * (a * b) * b⁻¹ := by rw [← d.P₁_comm_P₂ a ha b hb]
      _ = a * a := by group
  rw [this]
  exact d.P₁.mul_mem ha ha

theorem inv_mul_Jbar_mem_P₂ (m : d.V) : (m : G)⁻¹ * (d.Jbar m : G) ∈ d.P₂ := by
  obtain ⟨a, ha, b, hb, hab⟩ := d.mem_V.mp m.2
  rw [Jbar_apply_coe, ← hab, d.J_conj_V ha hb]
  have : (a * b)⁻¹ * (a * b⁻¹) = b⁻¹ * b⁻¹ := by
    calc (a * b)⁻¹ * (a * b⁻¹) = b⁻¹ * (a⁻¹ * a) * b⁻¹ := by group
      _ = b⁻¹ * b⁻¹ := by group
  rw [this]
  exact d.P₂.mul_mem (d.P₂.inv_mem hb) (d.P₂.inv_mem hb)

theorem Jbar_apply_of_mem_P₁ {m : d.V} (hm : (m : G) ∈ d.P₁) : d.Jbar m = m := by
  apply Subtype.ext
  rw [Jbar_apply_coe, d.J_comm_P₁ hm, mul_inv_cancel_right]

theorem Jbar_apply_of_mem_P₂ {m : d.V} (hm : (m : G) ∈ d.P₂) : (d.Jbar m : G) = (m : G)⁻¹ := by
  rw [Jbar_apply_coe, d.J_inv m hm]

theorem inv_apply_mul_mem {P : Subgroup G} (hP : P = d.P₁ ∨ P = d.P₂) {α : MulAut d.V}
    (hαP : ∀ m : d.V, (m : G) ∈ P → α m = m) (hαJ : d.Jbar * α * d.Jbar⁻¹ = α⁻¹) (m : d.V) :
    ((α m : d.V) : G)⁻¹ * ((α⁻¹ m : d.V) : G) ∈ P := by
  have hinv : α⁻¹ m = d.Jbar (α (d.Jbar m)) := by
    rw [← hαJ, d.Jbar_inv]
    rfl
  rw [hinv]
  set y : d.V := α m with hy
  rcases hP with rfl | rfl
  ·
    set p : d.V := m * d.Jbar m with hp
    have hpP : (p : G) ∈ d.P₁ := d.mul_Jbar_mem_P₁ m
    have hJm : d.Jbar m = m⁻¹ * p := by rw [hp, inv_mul_cancel_left]
    set q : d.V := y * d.Jbar y with hq
    have hqP : (q : G) ∈ d.P₁ := d.mul_Jbar_mem_P₁ y
    have hJy : d.Jbar y = y⁻¹ * q := by rw [hq, inv_mul_cancel_left]
    have h1 : d.Jbar (α (d.Jbar m)) = q⁻¹ * y * p := by
      rw [hJm, map_mul, map_inv, hαP p hpP, map_mul, map_inv, ← hy, hJy,
        d.Jbar_apply_of_mem_P₁ hpP]
      group
    rw [h1]
    have hc : ((y : G))⁻¹ * ((q⁻¹ * y * p : d.V) : G) = (q : G)⁻¹ * p := by
      push_cast
      rw [d.V_comm (d.V.inv_mem q.2) y.2]
      group
    rw [hc]
    exact d.P₁.mul_mem (d.P₁.inv_mem hqP) hpP
  ·
    set p : d.V := m⁻¹ * d.Jbar m with hp
    have hpP : (p : G) ∈ d.P₂ := d.inv_mul_Jbar_mem_P₂ m
    have hJm : d.Jbar m = m * p := by rw [hp, mul_inv_cancel_left]
    set q : d.V := y⁻¹ * d.Jbar y with hq
    have hqP : (q : G) ∈ d.P₂ := d.inv_mul_Jbar_mem_P₂ y
    have hJy : d.Jbar y = y * q := by rw [hq, mul_inv_cancel_left]
    have hJp : d.Jbar p = p⁻¹ := Subtype.ext (by rw [d.Jbar_apply_of_mem_P₂ hpP]; rfl)
    have h1 : d.Jbar (α (d.Jbar m)) = y * q * p⁻¹ := by
      rw [hJm, map_mul, hαP p hpP, map_mul, ← hy, hJy, hJp]
    rw [h1]
    have hc : ((y : G))⁻¹ * ((y * q * p⁻¹ : d.V) : G) = (q : G) * (p : G)⁻¹ := by
      push_cast
      group
    rw [hc]
    exact d.P₂.mul_mem hqP (d.P₂.inv_mem hpP)

theorem inv_mul_apply_mem {P : Subgroup G} (hP : P = d.P₁ ∨ P = d.P₂) {α : MulAut d.V}
    (hαP : ∀ m : d.V, (m : G) ∈ P → α m = m) (hαJ : d.Jbar * α * d.Jbar⁻¹ = α⁻¹)
    (hodd : Odd (orderOf α)) (m : d.V) : (m : G)⁻¹ * ((α m : d.V) : G) ∈ P := by
  have h2 : ∀ m : d.V, (m : G)⁻¹ * (((α * α) m : d.V) : G) ∈ P := by
    intro m
    have := d.inv_apply_mul_mem hP hαP hαJ (α m)
    rw [show α⁻¹ (α m) = m from by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]]
      at this
    have := P.inv_mem this
    rw [mul_inv_rev, inv_inv] at this
    exact this
  have hmul : ∀ β γ : MulAut d.V, (∀ m : d.V, (m : G)⁻¹ * ((β m : d.V) : G) ∈ P) →
      (∀ m : d.V, (m : G)⁻¹ * ((γ m : d.V) : G) ∈ P) →
      ∀ m : d.V, (m : G)⁻¹ * (((β * γ) m : d.V) : G) ∈ P := by
    intro β γ hβ hγ m
    rw [MulAut.mul_apply]
    have : (m : G)⁻¹ * ((β (γ m) : d.V) : G) =
        ((m : G)⁻¹ * ((γ m : d.V) : G)) * (((γ m : d.V) : G)⁻¹ * ((β (γ m) : d.V) : G)) := by
      group
    rw [this]
    exact P.mul_mem (hγ m) (hβ (γ m))
  have hpow : ∀ k : ℕ, ∀ m : d.V, (m : G)⁻¹ * ((((α * α) ^ k) m : d.V) : G) ∈ P := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      rw [pow_succ]
      exact hmul _ _ ih h2
  obtain ⟨t, ht⟩ := hodd
  have hα : α = (α * α) ^ (t + 1) := by
    rw [← sq, ← pow_mul]
    have : 2 * (t + 1) = orderOf α + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hα]
  exact hpow (t + 1) m

theorem mem_normalizer_inf_centralizer_Jbar {X : Subgroup (MulAut d.V)} {g : MulAut d.V}
    (hgX : g ∈ Subgroup.normalizer (X : Set (MulAut d.V))) (hgJ : g * d.Jbar = d.Jbar * g) :
    g ∈ Subgroup.normalizer
      ((X ⊓ Subgroup.centralizer ({d.Jbar} : Set (MulAut d.V)) : Subgroup _) : Set _) := by
  apply Sec53.mem_normalizer_of_conj_le
  intro y hy
  obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.mp hy
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgX y).mp hyX, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
  have hgJ' : g⁻¹ * d.Jbar = d.Jbar * g⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgJ, mul_inv_cancel_right]
  calc g * y * g⁻¹ * d.Jbar = g * y * (g⁻¹ * d.Jbar) := by group
    _ = g * (y * d.Jbar) * g⁻¹ := by rw [hgJ']; group
    _ = g * (d.Jbar * y) * g⁻¹ := by rw [hyC]
    _ = (g * d.Jbar) * y * g⁻¹ := by group
    _ = d.Jbar * (g * y * g⁻¹) := by rw [hgJ]; group

theorem odd_orderOf_of_isPGroup {X : Subgroup (MulAut d.V)} (hX : IsPGroup 3 X) {α : MulAut d.V}
    (hα : α ∈ X) : Odd (orderOf α) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hX ⟨α, hα⟩
  have h1 : α ^ (3 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : orderOf α ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  rw [hj]
  exact Odd.pow (by decide)

theorem eq_bot_of_normalized
    {v : ℕ} [hv : Fact v.Prime] (hvn : orderOf (3 : ZMod v) = d.n)
    {X : Subgroup (MulAut d.V)} (hXN : X ≤ d.Nbar) (hX : IsPGroup 3 X)
    (hJX : d.Jbar ∈ Subgroup.normalizer (X : Set (MulAut d.V)))
    (hUX : d.bar (d.U v) ≤ Subgroup.normalizer (X : Set (MulAut d.V))) : X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hY := d.eq_bot_of_comm_Jbar (D := d.U v) d.U_le_B d.H_le_normalizer_U
    (d.P₀_faithful_U hvn) (X := X ⊓ Subgroup.centralizer ({d.Jbar} : Set (MulAut d.V)))
    (inf_le_left.trans hXN)
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2)
    (hX.to_le inf_le_left) (by
      rintro _ ⟨u, hu, rfl⟩
      exact d.mem_normalizer_inf_centralizer_Jbar (hUX (d.φ_mem_bar hu))
        (d.phi_comm_Jbar_of_comm u.2 (Subgroup.mem_centralizer_singleton_iff.mp
          (d.U_le_centralizer_J hu))))
  have hCX : ∀ x ∈ X, d.Jbar * x = x * d.Jbar → x = 1 := by
    intro x hx hxJ
    have : x ∈ X ⊓ Subgroup.centralizer ({d.Jbar} : Set (MulAut d.V)) :=
      Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxJ.symm⟩
    rw [hY, Subgroup.mem_bot] at this
    exact this
  have hinv : ∀ z ∈ X, d.Jbar * z * d.Jbar⁻¹ = z⁻¹ :=
    conj_eq_inv_of_fpf d.Jbar_mul_Jbar hJX hCX
  set R := d.fixV X with hRdef
  have hRV := d.fixV_le_V X
  have hR1 := d.fixV_ne_bot hX
  have hJR : d.J ∈ Subgroup.normalizer (R : Set G) := d.mem_normalizer_fixV d.J_mem_NV hJX
  have hUR : d.U v ≤ Subgroup.normalizer (R : Set G) := fun u hu =>
    d.mem_normalizer_fixV (d.U_le_NV hu) (hUX (d.φ_mem_bar hu))
  have hR₁ := d.eq_bot_or_eq_of_U_le_normalizer hvn (Or.inl rfl) (inf_le_right : R ⊓ d.P₁ ≤ d.P₁)
    (fun u hu => Sec54.mem_normalizer_inf (hUR hu)
      (d.B_le_normalizer₁ (d.U_le_B hu)))
  have hR₂ := d.eq_bot_or_eq_of_U_le_normalizer hvn (Or.inr rfl) (inf_le_right : R ⊓ d.P₂ ≤ d.P₂)
    (fun u hu => Sec54.mem_normalizer_inf (hUR hu)
      (d.B_le_normalizer₂ (d.U_le_B hu)))
  have hdec := fun {r : G} (hr : r ∈ R) => d.exists_decomp hRV hJR hr
  have key : ∀ α ∈ X, ∀ m : d.V, (m : G)⁻¹ * ((α m : d.V) : G) ∈ R := by
    intro α hα m
    have hαJ : d.Jbar * α * d.Jbar⁻¹ = α⁻¹ := hinv α hα
    have hodd := d.odd_orderOf_of_isPGroup hX hα
    rcases hR₁ with h₁ | h₁ <;> rcases hR₂ with h₂ | h₂
    · exfalso
      apply hR1
      rw [eq_bot_iff]
      intro r hr
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec hr
      rw [h₁, Subgroup.mem_bot] at ha
      rw [h₂, Subgroup.mem_bot] at hb
      rw [ha, hb, mul_one]
      exact Subgroup.one_mem _
    ·
      have hRP : R = d.P₂ := by
        apply le_antisymm
        · intro r hr
          obtain ⟨a, ha, b, hb, rfl⟩ := hdec hr
          rw [h₁, Subgroup.mem_bot] at ha
          rw [ha, one_mul]
          exact (Subgroup.mem_inf.mp hb).2
        · rw [← h₂]
          exact inf_le_left
      rw [hRP]
      refine d.inv_mul_apply_mem (Or.inr rfl) (fun z hz => ?_) hαJ hodd m
      have hzR : (z : G) ∈ R := hRP ▸ hz
      exact d.mem_fixV.mp hzR α hα
    ·
      have hRP : R = d.P₁ := by
        apply le_antisymm
        · intro r hr
          obtain ⟨a, ha, b, hb, rfl⟩ := hdec hr
          rw [h₂, Subgroup.mem_bot] at hb
          rw [hb, mul_one]
          exact (Subgroup.mem_inf.mp ha).2
        · rw [← h₁]
          exact inf_le_left
      rw [hRP]
      refine d.inv_mul_apply_mem (Or.inl rfl) (fun z hz => ?_) hαJ hodd m
      have hzR : (z : G) ∈ R := hRP ▸ hz
      exact d.mem_fixV.mp hzR α hα
    ·
      have hmR : (m : G) ∈ R := by
        obtain ⟨a, ha, b, hb, hab⟩ := d.mem_V.mp m.2
        rw [← hab]
        exact R.mul_mem (h₁ ▸ ha |> fun h => (Subgroup.mem_inf.mp
          (show a ∈ R ⊓ d.P₁ by rw [h₁]; exact ha)).1)
          ((Subgroup.mem_inf.mp (show b ∈ R ⊓ d.P₂ by rw [h₂]; exact hb)).1)
      rw [d.mem_fixV.mp hmR α hα, inv_mul_cancel]
      exact R.one_mem
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  obtain ⟨x, rfl⟩ := hXN hα
  rw [d.φ_eq_one_iff]
  apply d.mem_CV_of_quadratic x.2
  intro m hm
  have hw := key _ hα ⟨m, hm⟩
  rw [d.φ_apply_coe] at hw
  have hwV : m⁻¹ * ((x : G) * m * (x : G)⁻¹) ∈ d.V := hRV hw
  have hw' : ((⟨_, hwV⟩ : d.V) : G) ∈ d.fixV X := hw
  have hfix := d.mem_fixV.mp hw' (d.φ x) hα
  exact congrArg Subtype.val hfix


end P56AbData

end CFSG.Walter.W67
