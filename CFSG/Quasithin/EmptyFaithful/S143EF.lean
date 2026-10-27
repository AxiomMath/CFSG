module

public import CFSG.Quasithin.EmptyFaithful.S143ED

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section General

variable {G : Type*} [Group G]

theorem exists_odd_lift {G B : Type*} [Group G] [Finite G] [Group B] (ρ : G →* B) {c : B}
    (hc : c ∈ ρ.range) (hodd : Odd (orderOf c)) : ∃ h : G, Odd (orderOf h) ∧ ρ h = c := by
  obtain ⟨h₀, rfl⟩ := hc
  have hn : orderOf h₀ ≠ 0 := (orderOf_pos h₀).ne'
  obtain ⟨a, n', hn', hn2⟩ := Nat.exists_eq_two_pow_mul_odd hn
  set m := orderOf (ρ h₀) with hm
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos
    (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])) (orderOf_pos h₀)
  have hcop : Nat.Coprime 2 m := (Nat.coprime_two_left).mpr hodd
  have h1 : 2 ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
  have hφ : 0 < Nat.totient m := Nat.totient_pos.mpr hmpos
  have hle : a ≤ Nat.totient m * a := Nat.le_mul_of_pos_left a hφ
  refine ⟨h₀ ^ (2 ^ (Nat.totient m * a)), ?_, ?_⟩
  · have hdvd : orderOf (h₀ ^ (2 ^ (Nat.totient m * a))) ∣ n' := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul]
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      have : 2 ^ (Nat.totient m * a) * n' = orderOf h₀ * 2 ^ d := by
        rw [hn2, hd, pow_add]
        ring
      rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat hn' hdvd
  · rw [map_pow]
    have h2 : 2 ^ (Nat.totient m * a) ≡ 1 [MOD m] := by
      rw [pow_mul]
      simpa using h1.pow a
    calc (ρ h₀) ^ (2 ^ (Nat.totient m * a)) = (ρ h₀) ^ 1 := pow_eq_pow_iff_modEq.mpr h2
      _ = ρ h₀ := pow_one _

theorem mem_of_odd_of_two_pow {K N : Subgroup G} (hKN : K ≤ Subgroup.normalizer (N : Set G))
    {x y : G} (hxK : x ∈ K) (hyK : y ∈ K) (hx : Odd (orderOf x))
    (hy : ∃ k : ℕ, y ^ (2 ^ k) = 1) (hxy : x * y⁻¹ ∈ N) : x ∈ N := by
  have hnorm : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKN
  let π : ↥K →* ↥K ⧸ N.subgroupOf K := QuotientGroup.mk' _
  have hπ : π ⟨x, hxK⟩ = π ⟨y, hyK⟩ := by
    show ((⟨x, hxK⟩ : ↥K) : ↥K ⧸ N.subgroupOf K) = ((⟨y, hyK⟩ : ↥K) : ↥K ⧸ N.subgroupOf K)
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa [div_eq_mul_inv] using hxy
  obtain ⟨k, hk⟩ := hy
  have h1 : orderOf (π ⟨x, hxK⟩) ∣ orderOf x := by
    have := orderOf_map_dvd π (⟨x, hxK⟩ : ↥K)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (π ⟨y, hyK⟩) ∣ 2 ^ k := by
    have h3 := orderOf_map_dvd π (⟨y, hyK⟩ : ↥K)
    rw [Subgroup.orderOf_mk] at h3
    exact h3.trans (orderOf_dvd_of_pow_eq_one hk)
  rw [← hπ] at h2
  have hodd : Odd (orderOf (π ⟨x, hxK⟩)) := Odd.of_dvd_nat hx h1
  have h4 : orderOf (π ⟨x, hxK⟩) = 1 :=
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)).eq_one_of_dvd h2
  have h5 : π ⟨x, hxK⟩ = 1 := orderOf_eq_one_iff.mp h4
  have h6 : (⟨x, hxK⟩ : ↥K) ∈ N.subgroupOf K := (QuotientGroup.eq_one_iff _).mp h5
  exact Subgroup.mem_subgroupOf.mp h6

theorem le_of_central_sylow {Γ : Type*} [Group Γ] [Finite Γ] {U Y : Subgroup Γ} [U.Normal]
    [Y.Normal] (hUY : U ≤ Y) (hY2 : IsPGroup 2 Y) (hodd : Odd Y.index)
    (hcomm : ∀ k : Γ, ∀ y ∈ Y, k * y * k⁻¹ * y⁻¹ ∈ U)
    (hgen : (⊤ : Subgroup Γ) ≤ Subgroup.closure {x : Γ | Odd (orderOf x)}) : Y ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hY2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Y) Y.index := by
    rw [hj]
    exact Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  obtain ⟨P, hP⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  have hPY : P ⊓ Y = ⊥ := disjoint_iff.mp hP.disjoint
  have hdec : ∀ g : Γ, ∃ p ∈ P, ∃ y ∈ Y, p * y = g := fun g => by
    have : g ∈ P ⊔ Y := by rw [hP.sup_eq_top]; exact Subgroup.mem_top g
    exact Subgroup.mem_sup_of_normal_right.mp this
  have hYN : ∀ y ∈ Y, ∀ n ∈ P ⊔ U, y * n * y⁻¹ ∈ P ⊔ U := by
    intro y hy n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hn
    have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a * (y * b * y⁻¹) := by group
    rw [e]
    have h1 : y * a * y⁻¹ * a⁻¹ ∈ U := by
      have := U.inv_mem (hcomm a y hy)
      have e2 : (a * y * a⁻¹ * y⁻¹)⁻¹ = y * a * y⁻¹ * a⁻¹ := by group
      rwa [e2] at this
    refine (P ⊔ U).mul_mem ((P ⊔ U).mul_mem (Subgroup.mem_sup_right h1)
      (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right ?_)
    exact (Subgroup.Normal.conj_mem inferInstance b hb y)
  have hNnormal : (P ⊔ U).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨p, hp, y, hy, rfl⟩ := hdec g
    have e : p * y * n * (p * y)⁻¹ = p * (y * n * y⁻¹) * p⁻¹ := by group
    rw [e]
    exact (P ⊔ U).mul_mem ((P ⊔ U).mul_mem (Subgroup.mem_sup_left hp) (hYN y hy n hn))
      ((P ⊔ U).inv_mem (Subgroup.mem_sup_left hp))
  have hodd_mem : ∀ x : Γ, Odd (orderOf x) → x ∈ P ⊔ U := by
    intro x hx
    obtain ⟨p, hp, y, hy, rfl⟩ := hdec x
    have hy2 : ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hY2 ⟨y, hy⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    refine mem_of_odd_of_two_pow (K := ⊤) (N := P ⊔ U) ?_ (Subgroup.mem_top _)
      (Subgroup.mem_top y) hx hy2 ?_
    · intro g _
      rw [Subgroup.mem_normalizer_iff]
      intro z
      exact ⟨fun hz => hNnormal.conj_mem z hz g, fun hz => by
        have := hNnormal.conj_mem _ hz g⁻¹
        simpa [mul_assoc] using this⟩
    · simpa using Subgroup.mem_sup_left hp
  have hall : P ⊔ U = ⊤ := by
    rw [eq_top_iff]
    refine hgen.trans ((Subgroup.closure_le _).mpr fun x hx => hodd_mem x hx)
  intro y hy
  have hyN : y ∈ P ⊔ U := by rw [hall]; exact Subgroup.mem_top y
  obtain ⟨p, hp, u, hu, hpu⟩ := Subgroup.mem_sup_of_normal_right.mp hyN
  have hpY : p ∈ Y := by
    have : p = y * u⁻¹ := by rw [← hpu]; group
    rw [this]
    exact Y.mul_mem hy (Y.inv_mem (hUY hu))
  have hp1 : p = 1 := by
    have : p ∈ P ⊓ Y := ⟨hp, hpY⟩
    rw [hPY, Subgroup.mem_bot] at this
    exact this
  rw [hp1, one_mul] at hpu
  rw [← hpu]
  exact hu

end General

section Odd

theorem sl2_cube_mul : ∀ x y : S1417.SL2, x ^ 3 = 1 → y ^ 3 = 1 → (x * y) ^ 3 = 1 := by decide

structure OddFacts {W : Type*} [Group W] (X : Subgroup (MulAut W)) : Prop where
  card_sylow : ∀ T' : Subgroup (MulAut W), IsSylowTwoOf T' X → Nat.card T' = 8
  exists_ffp : ∃ c ∈ X, Odd (orderOf c) ∧ ∀ w : W, c w = w → w = 1
  central : ∀ T' : Subgroup (MulAut W), IsSylowTwoOf T' X → ∃ r ∈ T', r ≠ 1 ∧
    (∀ z ∈ T', (∀ x ∈ T', x * z = z * x) → z = 1 ∨ z = r) ∧
    (∀ y ∈ X, Odd (orderOf y) → r * y * r⁻¹ = y⁻¹)
  cube_of_odd : ∀ y ∈ X, Odd (orderOf y) → y ^ 3 = 1
  cube_mul : ∀ y ∈ X, ∀ y' ∈ X, y ^ 3 = 1 → y' ^ 3 = 1 → (y * y') ^ 3 = 1

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
theorem cube_mul_of_ofourStruct (h : OfourStruct X L₁ L₂ t) {y y' : MulAut W} (hy : y ∈ X)
    (hy' : y' ∈ X) (hy3 : y ^ 3 = 1) (hy'3 : y' ^ 3 = 1) : (y * y') ^ 3 = 1 := by
  have hodd : ∀ z : MulAut W, z ^ 3 = 1 → Odd (orderOf z) := fun z hz =>
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hz)
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl, ha₁3, ha₂3⟩ :=
    h.odd_decomp (h.odd_mem_sup hy (hodd y hy3)) (hodd y hy3)
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl, hb₁3, hb₂3⟩ :=
    h.odd_decomp (h.odd_mem_sup hy' (hodd y' hy'3)) (hodd y' hy'3)
  have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b := fun a ha b hb => h.comm a ha b hb
  have e : a₁ * a₂ * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by
    calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
      _ = a₁ * (b₁ * a₂) * b₂ := by rw [(hcomm b₁ hb₁ a₂ ha₂).eq.symm]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
  have hc1 : (a₁ * b₁) ^ 3 = 1 := by
    obtain ⟨e₁, -, -⟩ := h.nat₁
    have := sl2_cube_mul (e₁ ⟨a₁, ha₁⟩) (e₁ ⟨b₁, hb₁⟩)
      (by rw [← map_pow]; have : (⟨a₁, ha₁⟩ : ↥L₁) ^ 3 = 1 := Subtype.ext ha₁3
          rw [this, map_one])
      (by rw [← map_pow]; have : (⟨b₁, hb₁⟩ : ↥L₁) ^ 3 = 1 := Subtype.ext hb₁3
          rw [this, map_one])
    rw [← map_mul, ← map_pow] at this
    have h2 := e₁.injective (this.trans (map_one e₁).symm)
    exact congrArg Subtype.val h2
  have hc2 : (a₂ * b₂) ^ 3 = 1 := by
    obtain ⟨e₂, -, -⟩ := h.nat₂
    have := sl2_cube_mul (e₂ ⟨a₂, ha₂⟩) (e₂ ⟨b₂, hb₂⟩)
      (by rw [← map_pow]; have : (⟨a₂, ha₂⟩ : ↥L₂) ^ 3 = 1 := Subtype.ext ha₂3
          rw [this, map_one])
      (by rw [← map_pow]; have : (⟨b₂, hb₂⟩ : ↥L₂) ^ 3 = 1 := Subtype.ext hb₂3
          rw [this, map_one])
    rw [← map_mul, ← map_pow] at this
    have h2 := e₂.injective (this.trans (map_one e₂).symm)
    exact congrArg Subtype.val h2
  rw [e, Commute.mul_pow (hcomm _ (L₁.mul_mem ha₁ hb₁) _ (L₂.mul_mem ha₂ hb₂)), hc1, hc2, one_mul]

theorem OddFacts.of_ofourStruct (h : OfourStruct X L₁ L₂ t) : OddFacts X where
  card_sylow T' hT' := h.card_T hT'
  exists_ffp := by
    obtain ⟨x₁, hx₁, hx₁3, hx₁1⟩ := S1417.exists_orderThree h.nat₁
    obtain ⟨x₂, hx₂, hx₂3, hx₂1⟩ := S1417.exists_orderThree h.nat₂
    have hcomm : x₁ * x₂ = x₂ * x₁ := h.comm x₁ hx₁ x₂ hx₂
    refine ⟨x₁ * x₂, X.mul_mem (h.L₁_le hx₁) (h.L₂_le hx₂), ?_, fun w hw => ?_⟩
    · have h3 : (x₁ * x₂) ^ 3 = 1 := by
        rw [Commute.mul_pow hcomm, hx₁3, hx₂3, one_mul]
      exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)
    · obtain ⟨hf₁, hf₂⟩ := h.fix_of_fix_mul hx₁ hx₂ (by simpa using hw)
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h.exists_decomp_W w
      have hodd3 : Odd (3 : ℕ) := by decide
      have hx₁odd : Odd (orderOf x₁) := Odd.of_dvd_nat hodd3 (orderOf_dvd_of_pow_eq_one hx₁3)
      have hx₂odd : Odd (orderOf x₂) := Odd.of_dvd_nat hodd3 (orderOf_dvd_of_pow_eq_one hx₂3)
      have e1 : x₁ u₂ = u₂ := h.L₁_fix₂ hx₁ hu₂
      have e2 : x₂ u₁ = u₁ := h.L₂_fix₁ hx₂ hu₁
      have hu₁1 : u₁ = 1 := by
        by_contra hne
        apply hx₁1
        refine S1417.eq_one_of_odd_of_fixed h.nat₁
          (fun l hl u hu => commV_stable L₁ hl hu) hx₁ hx₁odd hu₁ hne ?_
        have : x₁ (u₁ * u₂) = u₁ * u₂ := hf₁
        rw [map_mul, e1] at this
        exact mul_right_cancel this
      have hu₂1 : u₂ = 1 := by
        by_contra hne
        apply hx₂1
        refine S1417.eq_one_of_odd_of_fixed h.nat₂
          (fun l hl u hu => commV_stable L₂ hl hu) hx₂ hx₂odd hu₂ hne ?_
        have : x₂ (u₁ * u₂) = u₁ * u₂ := hf₂
        rw [map_mul, e2] at this
        exact mul_left_cancel this
      rw [hu₁1, hu₂1, mul_one]
  central T' hT' := by
    obtain ⟨r, hrT, hr1, -, hrc, hrcen, hrinv⟩ := h.exists_central hT'
    exact ⟨r, hrT, hr1, hrcen, hrinv⟩
  cube_of_odd y hy hodd := by
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl, h1, h2⟩ := h.odd_decomp (h.odd_mem_sup hy hodd) hodd
    rw [Commute.mul_pow (h.comm l₁ hl₁ l₂ hl₂), h1, h2, one_mul]
  cube_mul y hy y' hy' hy3 hy'3 := cube_mul_of_ofourStruct h hy hy' hy3 hy'3

end Odd

section Model

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Counter.oddFacts {g : G} (c : Counter T M g) :
    OddFacts (autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) := by
  have h := c.h1281
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
    { (inferInstance : Group ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) with
      mul_comm := fun a b => (tilde_isMulCommutative h).is_comm.comm a b }
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType
    (W := ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) (q := q)
    (tilde_mul_self h) hq4 hq1 hq2 hq3
  rw [hq6]
  exact OddFacts.of_ofourStruct hS

end Model

end S143

end CFSG.Quasithin
