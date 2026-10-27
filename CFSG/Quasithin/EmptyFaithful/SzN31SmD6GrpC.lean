module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.SzN31

namespace SmD6GrpC

section Counting

variable {G : Type*} [Group G]

theorem mul_comm_of_card_nine {P : Subgroup G} (hP : Nat.card P = 9) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := P)
    (by rw [hP]; norm_num)
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := P)).comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem pow_card_eq_one_of_mem {K : Subgroup G} {x : G} (hx : x ∈ K) : x ^ Nat.card K = 1 := by
  have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : K)))
  simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h

theorem pow_three_eq_one_of_card_three {K : Subgroup G} (hK : Nat.card K = 3) {x : G}
    (hx : x ∈ K) : x ^ 3 = 1 := by
  have h := pow_card_eq_one_of_mem hx
  rwa [hK] at h

theorem pow_nine_eq_one_of_card_nine {P : Subgroup G} (hP : Nat.card P = 9) {x : G} (hx : x ∈ P) :
    x ^ 9 = 1 := by
  have h := pow_card_eq_one_of_mem hx
  rwa [hP] at h

theorem eq_one_of_mem_inter {K K' : Subgroup G} (hK : Nat.card K = 3) (hK' : Nat.card K' = 3)
    (hne : K ≠ K') {x : G} (hx : x ∈ K) (hx' : x ∈ K') : x = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Finite K' := Nat.finite_of_card_ne_zero (by omega)
  have hdvd : Nat.card ↥(K ⊓ K') ∣ 3 := hK ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · have hbot : K ⊓ K' = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hx2 : x ∈ K ⊓ K' := ⟨hx, hx'⟩
    rw [hbot] at hx2
    exact Subgroup.mem_bot.mp hx2
  · exfalso
    apply hne
    have e1 : K ⊓ K' = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have e2 : K ⊓ K' = K' := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    rw [← e1, e2]

theorem finite_coe_of_card_three {K : Subgroup G} (hK : Nat.card K = 3) : (K : Set G).Finite := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  exact Set.toFinite _

theorem ncard_coe_of_card_three {K : Subgroup G} (hK : Nat.card K = 3) :
    (K : Set G).ncard = 3 := by
  rw [← Nat.card_coe_set_eq]
  exact hK

theorem ncard_union_three {K₀ K₁ K₂ : Subgroup G} (c₀ : Nat.card K₀ = 3) (c₁ : Nat.card K₁ = 3)
    (c₂ : Nat.card K₂ = 3) (d₀₁ : K₀ ≠ K₁) (d₀₂ : K₀ ≠ K₂) (d₁₂ : K₁ ≠ K₂) :
    ((K₀ : Set G) ∪ K₁ ∪ K₂).ncard = 7 := by
  have f₀ := finite_coe_of_card_three c₀
  have f₁ := finite_coe_of_card_three c₁
  have f₂ := finite_coe_of_card_three c₂
  have n₀ := ncard_coe_of_card_three c₀
  have n₁ := ncard_coe_of_card_three c₁
  have n₂ := ncard_coe_of_card_three c₂
  have i₀₁ : (K₀ : Set G) ∩ K₁ = {1} := by
    ext x
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_singleton_iff]
    exact ⟨fun ⟨a, b⟩ => eq_one_of_mem_inter c₀ c₁ d₀₁ a b, fun h => h ▸ ⟨one_mem _, one_mem _⟩⟩
  have h01 := Set.ncard_union_add_ncard_inter (K₀ : Set G) K₁ f₀ f₁
  rw [i₀₁, Set.ncard_singleton] at h01
  have i : ((K₀ : Set G) ∪ K₁) ∩ K₂ = {1} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union, SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | h, h2⟩
      · exact eq_one_of_mem_inter c₀ c₂ d₀₂ h h2
      · exact eq_one_of_mem_inter c₁ c₂ d₁₂ h h2
    · rintro rfl
      exact ⟨Or.inl (one_mem _), one_mem _⟩
  have h2 := Set.ncard_union_add_ncard_inter ((K₀ : Set G) ∪ K₁) K₂ (f₀.union f₁) f₂
  rw [i, Set.ncard_singleton] at h2
  omega

theorem ncard_outside_three {P K₀ K₁ K₂ : Subgroup G} (hP : Nat.card P = 9) (h₀ : K₀ ≤ P)
    (h₁ : K₁ ≤ P) (h₂ : K₂ ≤ P) (c₀ : Nat.card K₀ = 3) (c₁ : Nat.card K₁ = 3)
    (c₂ : Nat.card K₂ = 3) (d₀₁ : K₀ ≠ K₁) (d₀₂ : K₀ ≠ K₂) (d₁₂ : K₁ ≠ K₂) :
    ((P : Set G) \ ((K₀ : Set G) ∪ K₁ ∪ K₂)).ncard = 2 := by
  have hsub : ((K₀ : Set G) ∪ K₁ ∪ K₂) ⊆ (P : Set G) :=
    Set.union_subset (Set.union_subset (SetLike.coe_subset_coe.mpr h₀)
      (SetLike.coe_subset_coe.mpr h₁)) (SetLike.coe_subset_coe.mpr h₂)
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have hfin : (P : Set G).Finite := Set.toFinite _
  have h := Set.ncard_sdiff_add_ncard_of_subset hsub hfin
  have hP' : (P : Set G).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hP
  have h7 := ncard_union_three c₀ c₁ c₂ d₀₁ d₀₂ d₁₂
  omega

theorem eq_one_of_sq_eq_one {P : Subgroup G} (hP : Nat.card P = 9) {x : G} (hx : x ∈ P)
    (h : x ^ 2 = 1) : x = 1 := by
  simpa using pow_gcd_eq_one.mpr ⟨pow_nine_eq_one_of_card_nine hP hx, h⟩

def cubeSubgroup (P : Subgroup G) (hc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) : Subgroup G where
  carrier := {x | x ∈ P ∧ x ^ 3 = 1}
  one_mem' := ⟨one_mem P, one_pow 3⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨mul_mem ha.1 hb.1, by
      rw [(show Commute a b from hc a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem pow_three_eq_one_of_three {P K₀ K₁ K₂ : Subgroup G} (hP : Nat.card P = 9) (h₀ : K₀ ≤ P)
    (h₁ : K₁ ≤ P) (h₂ : K₂ ≤ P) (c₀ : Nat.card K₀ = 3) (c₁ : Nat.card K₁ = 3)
    (c₂ : Nat.card K₂ = 3) (d₀₁ : K₀ ≠ K₁) (d₀₂ : K₀ ≠ K₂) (d₁₂ : K₁ ≠ K₂) :
    ∀ x ∈ P, x ^ 3 = 1 := by
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have hc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb => mul_comm_of_card_nine hP ha hb
  have hTP : cubeSubgroup P hc ≤ P := fun x hx => hx.1
  have hUT : ((K₀ : Set G) ∪ K₁ ∪ K₂) ⊆ (cubeSubgroup P hc : Set G) := by
    rintro x ((hx | hx) | hx)
    · exact ⟨h₀ hx, pow_three_eq_one_of_card_three c₀ hx⟩
    · exact ⟨h₁ hx, pow_three_eq_one_of_card_three c₁ hx⟩
    · exact ⟨h₂ hx, pow_three_eq_one_of_card_three c₂ hx⟩
  have hfin : (cubeSubgroup P hc : Set G).Finite := by
    have : Finite (cubeSubgroup P hc) := Finite.of_injective (Subgroup.inclusion hTP)
      (Subgroup.inclusion_injective hTP)
    exact Set.toFinite _
  have h7 : 7 ≤ Nat.card (cubeSubgroup P hc) := by
    have h := Set.ncard_le_ncard hUT hfin
    rw [ncard_union_three c₀ c₁ c₂ d₀₁ d₀₂ d₁₂] at h
    rw [← Nat.card_coe_set_eq] at h
    exact h
  have hdvd : Nat.card (cubeSubgroup P hc) ∣ 9 := hP ▸ Subgroup.card_dvd_of_le hTP
  have h9 : Nat.card (cubeSubgroup P hc) = 9 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (cubeSubgroup P hc) = m at h7 hdvd hle ⊢
    interval_cases m <;> omega
  have hTeq : cubeSubgroup P hc = P := Subgroup.eq_of_le_of_card_ge hTP (by rw [h9, hP])
  intro x hx
  have hx' : x ∈ cubeSubgroup P hc := by rw [hTeq]; exact hx
  exact hx'.2

end Counting

section Unipotent

theorem endo_unipotent {V : Type*} [Group V] (hcomm : ∀ a b : V, a * b = b * a)
    (hV : Nat.card V = 9) (hexp : ∀ x : V, x ^ 3 = 1) (σ : V →* V)
    (hσ : ∀ x, σ (σ (σ x)) = x) {h : V} (hh1 : h ≠ 1) (hσh : σ h ∈ Subgroup.zpowers h) :
    σ h = h ∧ ∀ x, σ x * x⁻¹ ∈ Subgroup.zpowers h := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf h = 3 := orderOf_eq_prime (hexp h) hh1
  have hinj : Function.Injective σ := fun x y hxy =>
    calc x = σ (σ (σ x)) := (hσ x).symm
      _ = σ (σ (σ y)) := by rw [hxy]
      _ = y := hσ y
  have hfix : σ h = h := by
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp hσh
    obtain ⟨r, hr, he'⟩ : ∃ r : ℕ, r < 3 ∧ σ h = h ^ r := by
      refine ⟨(e % 3).toNat, by omega, ?_⟩
      have := zpow_mod_orderOf h e
      rw [hord] at this
      rw [← he, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      simpa using this.symm
    interval_cases r
    · exfalso
      rw [pow_zero] at he'
      exact hh1 (hinj (by rw [he', map_one]))
    · rw [pow_one] at he'
      exact he'
    · have hs2 : σ (σ h) = h := by
        rw [he', map_pow, he', ← pow_mul]
        calc h ^ (2 * 2) = h ^ 3 * h := by rw [← pow_succ]
          _ = h := by rw [hexp h, one_mul]
      have := hσ h
      rwa [hs2] at this
  refine ⟨hfix, ?_⟩
  have hHfix : ∀ z ∈ Subgroup.zpowers h, σ z = z := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_zpow, hfix]
  by_cases hall : ∀ x : V, x ∈ Subgroup.zpowers h
  · intro x
    exact mul_mem (hall _) (inv_mem (hall x))
  · push Not at hall
    obtain ⟨y, hy⟩ := hall
    have hy1 : y ≠ 1 := fun h1 => hy (by rw [h1]; exact one_mem _)
    have hy3 := hexp y
    have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hsup : Subgroup.zpowers h ⊔ Subgroup.zpowers y = ⊤ := by
      have : Finite V := Nat.finite_of_card_ne_zero (by omega)
      have hle : Subgroup.zpowers h ≤ Subgroup.zpowers h ⊔ Subgroup.zpowers y := le_sup_left
      have hdvd3 : 3 ∣ Nat.card ↥(Subgroup.zpowers h ⊔ Subgroup.zpowers y) := by
        have := Subgroup.card_dvd_of_le hle
        rwa [Nat.card_zpowers, hord] at this
      have hdvd9 : Nat.card ↥(Subgroup.zpowers h ⊔ Subgroup.zpowers y) ∣ 9 :=
        hV ▸ Subgroup.card_subgroup_dvd_card _
      have hne3 : Nat.card ↥(Subgroup.zpowers h ⊔ Subgroup.zpowers y) ≠ 3 := by
        intro h3
        have heq : Subgroup.zpowers h = Subgroup.zpowers h ⊔ Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [h3, Nat.card_zpowers, hord])
        apply hy
        rw [heq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      have h9 : Nat.card ↥(Subgroup.zpowers h ⊔ Subgroup.zpowers y) = 9 := by
        have hle9 := Nat.le_of_dvd (by norm_num) hdvd9
        generalize Nat.card ↥(Subgroup.zpowers h ⊔ Subgroup.zpowers y) = m at hdvd3 hdvd9 hne3 hle9 ⊢
        interval_cases m <;> omega
      exact (Subgroup.card_eq_iff_eq_top _).mp (by rw [h9, hV])
    have hdecomp : ∀ x : V, ∃ z ∈ Subgroup.zpowers h, ∃ n : ℤ, z * y ^ n = x := by
      intro x
      have hx : x ∈ Subgroup.zpowers h ⊔ Subgroup.zpowers y := by
        rw [hsup]
        exact Subgroup.mem_top x
      obtain ⟨z, hz, w, hw, hzw⟩ := Subgroup.mem_sup.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact ⟨z, hz, n, hzw⟩
    have hred : ∀ n : ℤ, ∃ r : ℕ, r < 3 ∧ y ^ n = y ^ r := by
      intro n
      refine ⟨(n % 3).toNat, by omega, ?_⟩
      have := zpow_mod_orderOf y n
      rw [hyord] at this
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      simpa using this.symm
    have hkey : σ y * y⁻¹ ∈ Subgroup.zpowers h := by
      obtain ⟨z, hz, n, hzn⟩ := hdecomp (σ y)
      obtain ⟨r, hr, hyn⟩ := hred n
      rw [hyn] at hzn
      interval_cases r
      · exfalso
        rw [pow_zero, mul_one] at hzn
        apply hy
        have : σ y = σ z := by rw [← hzn, hHfix z hz]
        rw [hinj this]
        exact hz
      · rw [pow_one] at hzn
        rw [← hzn, mul_inv_cancel_right]
        exact hz
      · have hs : σ (σ y) = y := by
          rw [← hzn, map_mul, hHfix z hz, map_pow, ← hzn]
          have hz3 := hexp z
          calc z * (z * y ^ 2) ^ 2 = z ^ 3 * (y ^ 3 * y) := by
                simp only [pow_succ, pow_zero, one_mul, mul_comm, mul_left_comm]
            _ = y := by rw [hz3, hy3, one_mul, one_mul]
        have h1 : σ y = y := by
          have := hσ y
          rwa [hs] at this
        rw [h1, mul_inv_cancel]
        exact one_mem _
    intro x
    obtain ⟨z', hz', m, rfl⟩ := hdecomp x
    obtain ⟨u, hu⟩ : ∃ u, u = σ y * y⁻¹ := ⟨_, rfl⟩
    have huH : u ∈ Subgroup.zpowers h := by rw [hu]; exact hkey
    have hσy : σ y = u * y := by rw [hu, inv_mul_cancel_right]
    have hσx : σ (z' * y ^ m) = u ^ m * (z' * y ^ m) := by
      rw [map_mul, map_zpow, hHfix z' hz', hσy, mul_zpow]
      simp only [mul_assoc, mul_comm]
    rw [hσx, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ huH m

end Unipotent

section Glue

variable {Γ : Type*} [Group Γ]

theorem conj_acts_unipotently {P : Subgroup Γ} [P.Normal] (hP9 : Nat.card P = 9)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) {h : Γ} (hh : h ∈ P) (hh1 : h ≠ 1)
    (hH : ∀ g : Γ, g * h * g⁻¹ ∈ Subgroup.zpowers h) {g : Γ} (hg : g ^ 3 ∈ P) :
    g * h = h * g ∧ ∀ x ∈ P, g * x * g⁻¹ * x⁻¹ ∈ Subgroup.zpowers h := by
  let σ : P →* P := (MulAut.conjNormal g).toMonoidHom
  have hσ : ∀ x : P, (σ x : Γ) = g * x * g⁻¹ := fun x => MulAut.conjNormal_apply g x
  have hσ3 : ∀ x : P, σ (σ (σ x)) = x := by
    intro x
    apply Subtype.ext
    rw [hσ, hσ, hσ]
    have hc : g * g * g * (x : Γ) = x * (g * g * g) := by
      rw [← pow_three']
      exact mul_comm_of_card_nine hP9 hg x.2
    calc g * (g * (g * (x : Γ) * g⁻¹) * g⁻¹) * g⁻¹ = g * g * g * x * (g * g * g)⁻¹ := by group
      _ = x := by rw [hc]; group
  have hexp' : ∀ x : P, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hh1' : (⟨h, hh⟩ : P) ≠ 1 := fun e => hh1 (congrArg Subtype.val e)
  have hσh : σ ⟨h, hh⟩ ∈ Subgroup.zpowers (⟨h, hh⟩ : P) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hH g)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [hσ]
    simpa using hk
  obtain ⟨hfix, hall⟩ := endo_unipotent
    (fun a b => Subtype.ext (mul_comm_of_card_nine hP9 a.2 b.2)) hP9 hexp' σ hσ3 hh1' hσh
  refine ⟨?_, ?_⟩
  · have := congrArg Subtype.val hfix
    rw [hσ] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  · intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hall ⟨x, hx⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa [hσ] using this

end Glue

section Nsub

variable {Γ : Type*} [Group Γ]

theorem zpowers_normal {h : Γ} (hH : ∀ g : Γ, g * h * g⁻¹ ∈ Subgroup.zpowers h) :
    (Subgroup.zpowers h).Normal where
  conj_mem n hn g := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hH g) k

def actTrivSub (P H : Subgroup Γ) [P.Normal] [H.Normal] : Subgroup Γ where
  carrier := {n | ∀ x ∈ P, n * x * n⁻¹ * x⁻¹ ∈ H}
  one_mem' := fun x _ => by simp
  mul_mem' := fun {a b} ha hb x hx => by
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem (Subgroup.Normal.conj_mem inferInstance _ (hb x hx) a) (ha x hx)
  inv_mem' := fun {a} ha x hx => by
    have hx' : a⁻¹ * x * a ∈ P := Subgroup.Normal.conj_mem' inferInstance x hx a
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = (a * (a⁻¹ * x * a) * a⁻¹ * (a⁻¹ * x * a)⁻¹)⁻¹ := by group
    show a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ ∈ H
    rw [e]
    exact inv_mem (ha _ hx')

theorem mem_actTrivSub {P H : Subgroup Γ} [P.Normal] [H.Normal] {n : Γ} :
    n ∈ actTrivSub P H ↔ ∀ x ∈ P, n * x * n⁻¹ * x⁻¹ ∈ H := Iff.rfl

instance actTrivSub_normal (P H : Subgroup Γ) [P.Normal] [H.Normal] :
    (actTrivSub P H).Normal where
  conj_mem n hn γ x hx := by
    have hx' : γ⁻¹ * x * γ ∈ P := Subgroup.Normal.conj_mem' inferInstance x hx γ
    have e : γ * n * γ⁻¹ * x * (γ * n * γ⁻¹)⁻¹ * x⁻¹ =
        γ * (n * (γ⁻¹ * x * γ) * n⁻¹ * (γ⁻¹ * x * γ)⁻¹) * γ⁻¹ := by group
    show γ * n * γ⁻¹ * x * (γ * n * γ⁻¹)⁻¹ * x⁻¹ ∈ H
    rw [e]
    exact Subgroup.Normal.conj_mem inferInstance _ ((mem_actTrivSub.mp hn) _ hx') γ

theorem mem_centralizer_zpowers_iff {n h : Γ} :
    n ∈ Subgroup.centralizer (Subgroup.zpowers h : Set Γ) ↔ n * h = h * n := by
  constructor
  · intro hn
    exact (hn h (Subgroup.mem_zpowers h)).symm
  · intro hnh z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute h n from hnh.symm) k).eq

def nsub (P : Subgroup Γ) [P.Normal] (h : Γ) [(Subgroup.zpowers h).Normal] : Subgroup Γ :=
  actTrivSub P (Subgroup.zpowers h) ⊓ Subgroup.centralizer (Subgroup.zpowers h : Set Γ)

theorem mem_nsub {P : Subgroup Γ} [P.Normal] {h : Γ} [(Subgroup.zpowers h).Normal] {n : Γ} :
    n ∈ nsub P h ↔ (∀ x ∈ P, n * x * n⁻¹ * x⁻¹ ∈ Subgroup.zpowers h) ∧ n * h = h * n := by
  rw [nsub, Subgroup.mem_inf, mem_actTrivSub, mem_centralizer_zpowers_iff]

instance nsub_normal (P : Subgroup Γ) [P.Normal] (h : Γ) [(Subgroup.zpowers h).Normal] :
    (nsub P h).Normal := by
  unfold nsub
  infer_instance

theorem pow_nine_eq_one_of_mem_nsub {P : Subgroup Γ} [P.Normal] (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hC : ∀ g : Γ, (∀ x ∈ P, g * x = x * g) → g ∈ P) {h : Γ} (hh : h ∈ P)
    [(Subgroup.zpowers h).Normal] {n : Γ} (hn : n ∈ nsub P h) : n ^ 9 = 1 := by
  obtain ⟨hnH, hnh⟩ := mem_nsub.mp hn
  have hcomm : ∀ z ∈ Subgroup.zpowers h, n * z = z * n := fun z hz =>
    (mem_centralizer_zpowers_iff.mpr hnh) z hz |>.symm
  have hHP : ∀ z ∈ Subgroup.zpowers h, z ∈ P := fun z hz => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Subgroup.zpow_mem P hh k
  have h3 : n ^ 3 ∈ P := by
    apply hC
    intro x hx
    obtain ⟨c, hc_def⟩ : ∃ c, c = n * x * n⁻¹ * x⁻¹ := ⟨_, rfl⟩
    have hcH : c ∈ Subgroup.zpowers h := by rw [hc_def]; exact hnH x hx
    have hc3 : c ^ 3 = 1 := hexp c (hHP c hcH)
    have hcc : n * c * n⁻¹ = c := by rw [mul_inv_eq_iff_eq_mul]; exact hcomm c hcH
    have e1 : n * x * n⁻¹ = c * x := by rw [hc_def]; group
    have e2 : n * (c * x) * n⁻¹ = c * (c * x) := by
      calc n * (c * x) * n⁻¹ = (n * c * n⁻¹) * (n * x * n⁻¹) := by group
        _ = c * (c * x) := by rw [hcc, e1]
    have e3 : n * (c * (c * x)) * n⁻¹ = c * (c * (c * x)) := by
      calc n * (c * (c * x)) * n⁻¹ = (n * c * n⁻¹) * (n * (c * x) * n⁻¹) := by group
        _ = c * (c * (c * x)) := by rw [hcc, e2]
    have e4 : n ^ 3 * x * (n ^ 3)⁻¹ = x := by
      calc n ^ 3 * x * (n ^ 3)⁻¹ = n * (n * (n * x * n⁻¹) * n⁻¹) * n⁻¹ := by
            rw [pow_three']
            group
        _ = c * (c * (c * x)) := by rw [e1, e2, e3]
        _ = c ^ 3 * x := by
            rw [pow_three']
            group
        _ = x := by rw [hc3, one_mul]
    exact mul_inv_eq_iff_eq_mul.mp e4
  calc n ^ 9 = (n ^ 3) ^ 3 := by rw [← pow_mul]
    _ = 1 := hexp _ h3

theorem isPGroup_nsub {P : Subgroup Γ} [P.Normal] (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hC : ∀ g : Γ, (∀ x ∈ P, g * x = x * g) → g ∈ P) {h : Γ} (hh : h ∈ P)
    [(Subgroup.zpowers h).Normal] : IsPGroup 3 (nsub P h) := fun n =>
  ⟨2, Subtype.ext (by simpa using pow_nine_eq_one_of_mem_nsub hexp hC hh n.2)⟩

end Nsub

end SmD6GrpC

theorem exists_outside_three_subgroups {G : Type*} [Group G] {P K₀ K₁ K₂ : Subgroup G}
    (hP : Nat.card P = 9) (h₀ : K₀ ≤ P) (h₁ : K₁ ≤ P) (h₂ : K₂ ≤ P)
    (c₀ : Nat.card K₀ = 3) (c₁ : Nat.card K₁ = 3) (c₂ : Nat.card K₂ = 3)
    (d₀₁ : K₀ ≠ K₁) (d₀₂ : K₀ ≠ K₂) (d₁₂ : K₁ ≠ K₂) :
    ∃ h : G, h ∈ P ∧ h ≠ 1 ∧ h ∉ K₀ ∧ h ∉ K₁ ∧ h ∉ K₂ ∧ h ^ 3 = 1 ∧ (∀ x ∈ P, x ^ 3 = 1) ∧
      ∀ x ∈ P, x ∉ K₀ → x ∉ K₁ → x ∉ K₂ → x ∈ Subgroup.zpowers h := by
  have hS := SmD6GrpC.ncard_outside_three hP h₀ h₁ h₂ c₀ c₁ c₂ d₀₁ d₀₂ d₁₂
  have hexp := SmD6GrpC.pow_three_eq_one_of_three hP h₀ h₁ h₂ c₀ c₁ c₂ d₀₁ d₀₂ d₁₂
  obtain ⟨a, b, hab, hSab⟩ := Set.ncard_eq_two.mp hS
  have hmem : ∀ x : G, x ∈ (P : Set G) \ ((K₀ : Set G) ∪ K₁ ∪ K₂) ↔
      x ∈ P ∧ x ∉ K₀ ∧ x ∉ K₁ ∧ x ∉ K₂ := fun x => by
    simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_union, not_or, and_assoc]
  have haS : a ∈ (P : Set G) \ ((K₀ : Set G) ∪ K₁ ∪ K₂) := by
    rw [hSab]
    exact Set.mem_insert _ _
  obtain ⟨haP, haK₀, haK₁, haK₂⟩ := (hmem a).mp haS
  have ha1 : a ≠ 1 := fun h => haK₀ (by rw [h]; exact one_mem K₀)
  have hainvS : a⁻¹ ∈ (P : Set G) \ ((K₀ : Set G) ∪ K₁ ∪ K₂) :=
    (hmem a⁻¹).mpr ⟨inv_mem haP, fun h => haK₀ (inv_mem_iff.mp h),
      fun h => haK₁ (inv_mem_iff.mp h), fun h => haK₂ (inv_mem_iff.mp h)⟩
  have hainvne : a⁻¹ ≠ a := fun h =>
    ha1 (SmD6GrpC.eq_one_of_sq_eq_one hP haP (by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr h.symm))
  have hb : b = a⁻¹ := by
    rw [hSab] at hainvS
    rcases Set.mem_insert_iff.mp hainvS with h | h
    · exact absurd h hainvne
    · exact (Set.mem_singleton_iff.mp h).symm
  refine ⟨a, haP, ha1, haK₀, haK₁, haK₂, hexp a haP, hexp, ?_⟩
  intro x hxP hx₀ hx₁ hx₂
  have hxS : x ∈ (P : Set G) \ ((K₀ : Set G) ∪ K₁ ∪ K₂) := (hmem x).mpr ⟨hxP, hx₀, hx₁, hx₂⟩
  rw [hSab] at hxS
  rcases Set.mem_insert_iff.mp hxS with h | h
  · rw [h]
    exact Subgroup.mem_zpowers a
  · rw [Set.mem_singleton_iff.mp h, hb]
    exact inv_mem (Subgroup.mem_zpowers a)

theorem not_three_dvd_index_of_normal_line {Γ' : Type*} [Group Γ'] [Finite Γ']
    (P' : Subgroup Γ') [P'.Normal] (hP9 : Nat.card P' = 9) (hexp : ∀ x ∈ P', x ^ 3 = 1)
    (hC : ∀ g : Γ', (∀ x ∈ P', g * x = x * g) → g ∈ P')
    (hO : ∀ N : Subgroup Γ', N.Normal → IsPGroup 3 N → N ≤ P')
    {h : Γ'} (hh : h ∈ P') (hh1 : h ≠ 1) (hH : ∀ g : Γ', g * h * g⁻¹ ∈ Subgroup.zpowers h) :
    ¬ 3 ∣ P'.index := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHn : (Subgroup.zpowers h).Normal := SmD6GrpC.zpowers_normal hH
  have hcard : 3 ∣ Nat.card (Γ' ⧸ P') := by
    rw [← Subgroup.index_eq_card]
    exact h3
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 hcard
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hg3 : g ^ 3 ∈ P' := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    rw [← hq]
    exact pow_orderOf_eq_one _
  have hgP : g ∉ P' := by
    intro hg
    have h1 : (g : Γ' ⧸ P') = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    rw [h1, orderOf_one] at hq
    omega
  obtain ⟨hgh, hgx⟩ := SmD6GrpC.conj_acts_unipotently hP9 hexp hh hh1 hH hg3
  have hgN : g ∈ SmD6GrpC.nsub P' h := SmD6GrpC.mem_nsub.mpr ⟨hgx, hgh⟩
  exact hgP (hO _ inferInstance (SmD6GrpC.isPGroup_nsub hexp hC hh) hgN)

end CFSG.Quasithin.SzN31
