module

public import CFSG.Quasithin.H13.L32A727j

public section

namespace CFSG.Quasithin.H13.L32A.E9

open CFSG.Quasithin CFSG.Quasithin.FixR

variable {W : Type} [CommGroup W]

theorem exists_zpow_mul_zpow {x y : MulAut W} (hxy : x * y = y * x) {z : MulAut W}
    (hz : z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) : ∃ a b : ℤ, z = x ^ a * y ^ b := by
  let S : Subgroup (MulAut W) :=
    { carrier := {g | ∃ a b : ℤ, g = x ^ a * y ^ b}
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
        refine ⟨a + c, b + d, ?_⟩
        have hc : y ^ b * x ^ c = x ^ c * y ^ b := (Commute.zpow_zpow hxy.symm b c).eq
        rw [zpow_add, zpow_add]
        calc x ^ a * y ^ b * (x ^ c * y ^ d) = x ^ a * (y ^ b * x ^ c) * y ^ d := by
              simp only [mul_assoc]
          _ = x ^ a * (x ^ c * y ^ b) * y ^ d := by rw [hc]
          _ = x ^ a * x ^ c * (y ^ b * y ^ d) := by simp only [mul_assoc]
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        refine ⟨-a, -b, ?_⟩
        rw [mul_inv_rev, zpow_neg, zpow_neg]
        exact (Commute.zpow_zpow hxy.symm b a).inv_inv.eq }
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ S :=
    sup_le (Subgroup.zpowers_le.mpr ⟨1, 0, by simp⟩) (Subgroup.zpowers_le.mpr ⟨0, 1, by simp⟩)
  exact hle hz

theorem zpowers_eq_of_mem [Finite W] {u v : MulAut W} (hu3 : u ^ 3 = 1) (hv1 : v ≠ 1)
    (hv : v ∈ Subgroup.zpowers u) : Subgroup.zpowers v = Subgroup.zpowers u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hv
    exact hv1 hv
  have hv3 : v ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hv) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hu3 hu1, orderOf_eq_prime hv3 hv1]

theorem ne_one_of_not_mem {x w : MulAut W} (hw : w ∉ Subgroup.zpowers x) : w ≠ 1 :=
  fun h => hw (h ▸ Subgroup.one_mem _)

theorem mem_of_mul_self_mem {x y : MulAut W} (hy3 : y ^ 3 = 1)
    (h : y * y ∈ Subgroup.zpowers x) : y ∈ Subgroup.zpowers x := by
  have hy4 : y = (y * y) * (y * y) := by
    calc y = y * y ^ 3 := by rw [hy3, mul_one]
      _ = (y * y) * (y * y) := by rw [pow_three]; simp only [mul_assoc]
  rw [hy4]
  exact (Subgroup.zpowers x).mul_mem h h

theorem zpowers_eq_of_ne [Finite W] {x y z : MulAut W} (hxy : x * y = y * x) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy3 : (x * y) ^ 3 = 1) (hxyy3 : (x * y * y) ^ 3 = 1)
    (hz : z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) (hzx : z ∉ Subgroup.zpowers x)
    (hzy : z ∉ Subgroup.zpowers y) :
    Subgroup.zpowers z = Subgroup.zpowers (x * y) ∨
      Subgroup.zpowers z = Subgroup.zpowers (x * y * y) := by
  obtain ⟨a, b, rfl⟩ := exists_zpow_mul_zpow hxy hz
  rw [zpow_eq_zpow_emod' a hx3, zpow_eq_zpow_emod' b hy3] at hzx hzy ⊢
  simp only [Nat.cast_ofNat] at hzx hzy ⊢
  have hyyx : y * y * x = x * (y * y) := (Commute.mul_left hxy.symm hxy.symm).eq
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp only [ha, hb, zpow_zero, zpow_one, zpow_two, mul_one, one_mul] at hzx hzy ⊢
  · exact absurd (Subgroup.one_mem _) hzx
  · exact absurd (Subgroup.mem_zpowers y) hzy
  · exact absurd ((Subgroup.zpowers y).mul_mem (Subgroup.mem_zpowers y)
      (Subgroup.mem_zpowers y)) hzy
  · exact absurd (Subgroup.mem_zpowers x) hzx
  · exact Or.inl trivial
  · exact Or.inr (by rw [mul_assoc])
  · exact absurd ((Subgroup.zpowers x).mul_mem (Subgroup.mem_zpowers x)
      (Subgroup.mem_zpowers x)) hzx
  ·
    right
    refine zpowers_eq_of_mem hxyy3 (ne_one_of_not_mem hzx) (Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩)
    rw [zpow_two]
    calc x * y * y * (x * y * y) = x * (y * y * x) * y * y := by simp only [mul_assoc]
      _ = x * (x * (y * y)) * y * y := by rw [hyyx]
      _ = x * x * (y * y * y) * y := by simp only [mul_assoc]
      _ = x * x * y := by rw [← pow_three', hy3, mul_one]
  ·
    left
    refine zpowers_eq_of_mem hxy3 (ne_one_of_not_mem hzx) (Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩)
    rw [zpow_two]
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [← hxy]
      _ = x * x * (y * y) := by simp only [mul_assoc]

theorem tp_conj_eq_bot {P : Subgroup (MulAut W)} {g x : MulAut W}
    (hg : g ∈ Subgroup.normalizer (P : Set (MulAut W))) (h : tp P (Subgroup.zpowers x) = ⊥) :
    tp P (Subgroup.zpowers (g * x * g⁻¹)) = ⊥ := by
  have := map_tp P (Subgroup.zpowers x) hg
  rw [h, Subgroup.map_bot, MonoidHom.map_zpowers] at this
  rw [this]
  rfl

theorem conj_three {g : MulAut W} (hg3 : g ^ 3 = 1) (w : MulAut W) :
    g * (g * (g * w * g⁻¹) * g⁻¹) * g⁻¹ = w := by
  rw [show g * (g * (g * w * g⁻¹) * g⁻¹) * g⁻¹ = g ^ 3 * w * (g ^ 3)⁻¹ by
    rw [pow_three']; group, hg3]
  group

theorem tp_ne_bot [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {X P : Subgroup (MulAut W)} [Fintype ↥P]
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 9)
    (hP3 : ∀ κ ∈ P, κ ^ 3 = 1) (hXP : ∀ g ∈ X, ∀ κ ∈ P, g * κ * g⁻¹ ∈ P)
    (htrans : ∀ x ∈ P, x ≠ 1 → ∃ g ∈ X, g ^ 3 = 1 ∧ g * x * g⁻¹ ∉ Subgroup.zpowers x)
    {x : MulAut W} (hx : x ∈ P) (hx1 : x ≠ 1) : tp P (Subgroup.zpowers x) ≠ ⊥ := by
  intro hbot
  obtain ⟨g, hgX, hg3, hgx⟩ := htrans x hx hx1
  have hgN : g ∈ Subgroup.normalizer (P : Set (MulAut W)) :=
    Subgroup.mem_normalizer_fintype fun κ hκ => hXP g hgX κ hκ
  have hyP : g * x * g⁻¹ ∈ P := hXP g hgX x hx
  have hzP : g * (g * x * g⁻¹) * g⁻¹ ∈ P := hXP g hgX _ hyP
  have hby : tp P (Subgroup.zpowers (g * x * g⁻¹)) = ⊥ := tp_conj_eq_bot hgN hbot
  have hbz : tp P (Subgroup.zpowers (g * (g * x * g⁻¹) * g⁻¹)) = ⊥ := tp_conj_eq_bot hgN hby
  have hzx : g * (g * x * g⁻¹) * g⁻¹ ∉ Subgroup.zpowers x := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    apply hgx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k * k, ?_⟩
    calc x ^ (k * k) = (x ^ k) ^ k := zpow_mul x k k
      _ = (g * (g * x * g⁻¹) * g⁻¹) ^ k := by rw [hk]
      _ = g * (g * x ^ k * g⁻¹) * g⁻¹ := by rw [conj_zpow, conj_zpow]
      _ = g * (g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹) * g⁻¹ := by rw [hk]
      _ = g * x * g⁻¹ := conj_three hg3 _
  have hzy : g * (g * x * g⁻¹) * g⁻¹ ∉ Subgroup.zpowers (g * x * g⁻¹) := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    apply hgx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    calc x ^ k = g⁻¹ * (g * x * g⁻¹) ^ k * g := by rw [conj_zpow]; group
      _ = g⁻¹ * (g * (g * x * g⁻¹) * g⁻¹) * g := by rw [hk]
      _ = g * x * g⁻¹ := by group
  have hxy : x * (g * x * g⁻¹) = (g * x * g⁻¹) * x := hPc _ hx _ hyP
  have hc3 : ∀ κ ∈ P, κ ^ 3 = 1 := hP3
  have hP' : Nat.card P = 9 := by rw [Nat.card_eq_fintype_card, hP]
  have hx3 : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hP3 x hx) hx1]
  have hy3 : Nat.card (Subgroup.zpowers (g * x * g⁻¹)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hP3 _ hyP) (ne_one_of_not_mem hgx)]
  have hne : Subgroup.zpowers x ≠ Subgroup.zpowers (g * x * g⁻¹) := fun h =>
    hgx (h ▸ Subgroup.mem_zpowers _)
  have hsup := sup_eq_of_ne9 hP ((Subgroup.zpowers_le).mpr hx) ((Subgroup.zpowers_le).mpr hyP)
    hx3 hy3 hne
  rcases zpowers_eq_of_ne hxy (hP3 x hx) (hP3 _ hyP) (hP3 _ (P.mul_mem hx hyP))
      (hP3 _ (P.mul_mem (P.mul_mem hx hyP) hyP)) (hsup ▸ hzP) hzx hzy with h | h
  · rw [h] at hbz
    exact false_of_tp_eq_bot hW hPc hP3 hx hyP hgx hbot hby hbz
  · rw [h] at hbz
    have hyy : g * x * g⁻¹ * (g * x * g⁻¹) ∈ P := P.mul_mem hyP hyP
    have hyyx : g * x * g⁻¹ * (g * x * g⁻¹) ∉ Subgroup.zpowers x := fun hm =>
      hgx (mem_of_mul_self_mem (hP3 _ hyP) hm)
    have hyy1 : g * x * g⁻¹ * (g * x * g⁻¹) ≠ 1 := ne_one_of_not_mem hyyx
    have hzz : Subgroup.zpowers (g * x * g⁻¹ * (g * x * g⁻¹)) =
        Subgroup.zpowers (g * x * g⁻¹) :=
      zpowers_eq_of_mem (hP3 _ hyP) hyy1
        ((Subgroup.zpowers (g * x * g⁻¹)).mul_mem (Subgroup.mem_zpowers _)
          (Subgroup.mem_zpowers _))
    refine false_of_tp_eq_bot hW hPc hP3 hx hyy hyyx hbot (by rw [hzz]; exact hby) ?_
    rw [← mul_assoc]
    exact hbz

theorem six_le_rk_commV [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {X P : Subgroup (MulAut W)}
    [Fintype ↥P] (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 9)
    (hP3 : ∀ κ ∈ P, κ ^ 3 = 1) (hXP : ∀ g ∈ X, ∀ κ ∈ P, g * κ * g⁻¹ ∈ P)
    (htrans : ∀ x ∈ P, x ≠ 1 → ∃ g ∈ X, g ^ 3 = 1 ∧ g * x * g⁻¹ ∉ Subgroup.zpowers x)
    {c : MulAut W} (hc : c ∈ P) (hc1 : c ≠ 1) : 6 ≤ rk (commV (Subgroup.zpowers c)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP' : Nat.card P = 9 := by rw [Nat.card_eq_fintype_card, hP]
  have hc3 : c ^ 3 = 1 := hP3 c hc
  have hcard3 : ∀ u ∈ P, u ≠ 1 → Nat.card (Subgroup.zpowers u) = 3 := fun u hu hu1 => by
    rw [Nat.card_zpowers, orderOf_eq_prime (hP3 u hu) hu1]
  obtain ⟨y, hyP, hyc⟩ : ∃ y ∈ P, y ∉ Subgroup.zpowers c := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show P ≤ Subgroup.zpowers c from h)
    rw [hP', hcard3 c hc hc1] at h1
    omega
  have hy1 : y ≠ 1 := ne_one_of_not_mem hyc
  have hcy : c * y = y * c := hPc c hc y hyP
  have hy3 : y ^ 3 = 1 := hP3 y hyP
  have hcyP : c * y ∈ P := P.mul_mem hc hyP
  have hcyyP : c * y * y ∈ P := P.mul_mem hcyP hyP
  have d1 : c * y ∉ Subgroup.zpowers c := fun h => hyc (by
    have := (Subgroup.zpowers c).mul_mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) h
    rwa [inv_mul_cancel_left] at this)
  have d2 : c * y * y ∉ Subgroup.zpowers c := fun h => hyc (by
    refine mem_of_mul_self_mem hy3 ?_
    have := (Subgroup.zpowers c).mul_mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) h
    rwa [mul_assoc, inv_mul_cancel_left] at this)
  have hcmem : c ∉ Subgroup.zpowers y := fun h => hyc (by
    rw [zpowers_eq_of_mem hy3 hc1 h]
    exact Subgroup.mem_zpowers y)
  have d3 : c * y ∉ Subgroup.zpowers y := fun h => hcmem (by
    have := (Subgroup.zpowers y).mul_mem h (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
    rwa [mul_inv_cancel_right] at this)
  have d4 : c * y * y ∉ Subgroup.zpowers y := fun h => hcmem (by
    have := (Subgroup.zpowers y).mul_mem ((Subgroup.zpowers y).mul_mem h
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))) (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
    rwa [mul_inv_cancel_right, mul_inv_cancel_right] at this)
  have d5 : c * y * y ∉ Subgroup.zpowers (c * y) := by
    intro h
    have hy : y ∈ Subgroup.zpowers (c * y) := by
      have := (Subgroup.zpowers (c * y)).mul_mem h
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers (c * y)))
      have e : c * y * y * (c * y)⁻¹ = y := by
        calc c * y * y * (c * y)⁻¹ = (c * y) * y * (c * y)⁻¹ := rfl
          _ = (y * c) * y * (y * c)⁻¹ := by rw [hcy]
          _ = y * (c * y) * c⁻¹ * y⁻¹ := by group
          _ = y * (y * c) * c⁻¹ * y⁻¹ := by rw [hcy]
          _ = y := by group
      rwa [e] at this
    apply d3
    rw [zpowers_eq_of_mem (hP3 _ hcyP) hy1 hy]
    exact Subgroup.mem_zpowers _
  have hcy1 : c * y ≠ 1 := ne_one_of_not_mem d1
  have hcyy1 : c * y * y ≠ 1 := ne_one_of_not_mem d2
  set L₁ := Subgroup.zpowers y with hL₁
  set L₂ := Subgroup.zpowers (c * y) with hL₂
  set L₃ := Subgroup.zpowers (c * y * y) with hL₃
  have h₁ : L₁ ≤ P := (Subgroup.zpowers_le).mpr hyP
  have h₂ : L₂ ≤ P := (Subgroup.zpowers_le).mpr hcyP
  have h₃ : L₃ ≤ P := (Subgroup.zpowers_le).mpr hcyyP
  have c₁ : Nat.card L₁ = 3 := hcard3 y hyP hy1
  have c₂ : Nat.card L₂ = 3 := hcard3 _ hcyP hcy1
  have c₃ : Nat.card L₃ = 3 := hcard3 _ hcyyP hcyy1
  have ne : ∀ {a b : MulAut W}, a ∉ Subgroup.zpowers b →
      Subgroup.zpowers b ≠ Subgroup.zpowers a := fun hab h => hab (h ▸ Subgroup.mem_zpowers _)
  have n₁₂ : L₁ ≠ L₂ := ne d3
  have n₁₃ : L₁ ≠ L₃ := ne d4
  have n₂₃ : L₂ ≠ L₃ := ne d5
  have m₁ : Subgroup.zpowers c ≠ L₁ := ne hyc
  have m₂ : Subgroup.zpowers c ≠ L₂ := ne d1
  have m₃ : Subgroup.zpowers c ≠ L₃ := ne d2
  have t₁ := tp_ne_bot hW hPc hP hP3 hXP htrans hyP hy1
  have t₂ := tp_ne_bot hW hPc hP hP3 hXP htrans hcyP hcy1
  have t₃ := tp_ne_bot hW hPc hP hP3 hXP htrans hcyyP hcyy1
  have s₁ := four_le_card_tp hW hPc hP h₁ t₁
  have s₂ := four_le_card_tp hW hPc hP h₂ t₂
  have s₃ := four_le_card_tp hW hPc hP h₃ t₃
  have hb12 : tp P L₁ ⊓ tp P L₂ = ⊥ :=
    tp_inf_tp9 hW P L₁ L₂ hP (sup_eq_of_ne9 hP h₁ h₂ c₁ c₂ n₁₂)
  have hb3 : tp P L₃ ⊓ (tp P L₁ ⊔ tp P L₂) = ⊥ :=
    tp_sup_inf9 hW hPc hP h₁ h₂ h₃ c₁ c₂ c₃ n₁₂ n₁₃ n₂₃
  have e12 : Nat.card ↥(tp P L₁ ⊔ tp P L₂) = Nat.card (tp P L₁) * Nat.card (tp P L₂) := by
    have := card_sup_mul_card_inf (tp P L₁) (tp P L₂)
    rwa [hb12, Subgroup.card_bot, mul_one] at this
  have e123 : Nat.card ↥((tp P L₁ ⊔ tp P L₂) ⊔ tp P L₃) =
      Nat.card ↥(tp P L₁ ⊔ tp P L₂) * Nat.card (tp P L₃) := by
    have := card_sup_mul_card_inf (tp P L₁ ⊔ tp P L₂) (tp P L₃)
    rwa [inf_comm, hb3, Subgroup.card_bot, mul_one] at this
  have hker : (nu3Hom c).ker ≤ commV (Subgroup.zpowers c) := fun w hw =>
    mem_commV_of_nu3_eq_one hW (MonoidHom.mem_ker.mp hw)
  have hY : (tp P L₁ ⊔ tp P L₂) ⊔ tp P L₃ ≤ commV (Subgroup.zpowers c) :=
    (sup_le (sup_le (tp_le_ker_nu3 hW hPc hP hc hc3 hc1 h₁ c₁ m₁)
      (tp_le_ker_nu3 hW hPc hP hc hc3 hc1 h₂ c₂ m₂))
      (tp_le_ker_nu3 hW hPc hP hc hc3 hc1 h₃ c₃ m₃)).trans hker
  have h64 : 64 ≤ Nat.card (commV (Subgroup.zpowers c)) := by
    have h1 := Subgroup.card_le_of_le hY
    rw [e123, e12] at h1
    calc 64 = 4 * 4 * 4 := by norm_num
      _ ≤ Nat.card (tp P L₁) * Nat.card (tp P L₂) * Nat.card (tp P L₃) :=
        Nat.mul_le_mul (Nat.mul_le_mul s₁ s₂) s₃
      _ ≤ _ := h1
  rw [card_eq_two_pow hW] at h64
  by_contra hlt
  push Not at hlt
  have : 2 ^ rk (commV (Subgroup.zpowers c)) ≤ 2 ^ 5 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.Quasithin.H13.L32A.E9
