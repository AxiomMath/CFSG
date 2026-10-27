module

public import CFSG.Quasithin.Background.D2Y4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem zpow_cube_eq_one {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) (n : ℤ) :
    (g ^ n) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  have : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
  simp [this]

omit [Finite V] in
theorem cube_eq_one_of_mem_E {a b y : MulAut V} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a) {i j : ℤ} (hy : y = a ^ i * b ^ j) : y ^ 3 = 1 := by
  have hc : Commute (a ^ i) (b ^ j) := (show Commute a b from hab).zpow_zpow i j
  rw [hy, hc.mul_pow, zpow_cube_eq_one ha3, zpow_cube_eq_one hb3, one_mul]

omit [Finite V] in
theorem zpowers_conj (g y : MulAut V) :
    Subgroup.zpowers (g * y * g⁻¹) = conjBy g (Subgroup.zpowers y) := by
  rw [conjBy, MonoidHom.map_zpowers]
  rfl

theorem rk_commV_zpowers_conj (g y : MulAut V) :
    rk (commV (Subgroup.zpowers (g * y * g⁻¹))) = rk (commV (Subgroup.zpowers y)) := by
  rw [zpowers_conj, rk_commV_conjBy]

section E

variable {X : Subgroup (MulAut V)}

theorem sub_E_cases {a b y : MulAut V} (hao : orderOf a = 3) (hbo : orderOf b = 3)
    (hab : a * b = b * a) (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b)
    (hy : y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) (hy1 : y ≠ 1) :
    Subgroup.zpowers y = Subgroup.zpowers a ∨ Subgroup.zpowers y = Subgroup.zpowers b ∨
      Subgroup.zpowers y = Subgroup.zpowers (a * b) ∨
      Subgroup.zpowers y = Subgroup.zpowers (a * b * b) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have ha3 : a ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  obtain ⟨-, -, hform⟩ := E9_data hao hbo hab hne
  obtain ⟨i, j, hij⟩ := hform y hy
  have hcab : Commute a b := hab
  have hab3 : (a * b) ^ 3 = 1 := by rw [hcab.mul_pow, ha3, hb3, mul_one]
  have hc : Commute (a * b) b := Commute.mul_left hcab (Commute.refl b)
  have habb3 : (a * b * b) ^ 3 = 1 := by rw [hc.mul_pow, hab3, hb3, mul_one]
  have hab1 : a * b ≠ 1 := by
    intro e
    apply hne
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [this, Subgroup.zpowers_inv]
  have habb1 : a * b * b ≠ 1 := by
    intro e
    apply hne
    have : a = b := by
      calc a = a * b ^ 3 := by rw [hb3, mul_one]
        _ = (a * b * b) * b := by rw [pow_three']; simp only [mul_assoc]
        _ = b := by rw [e, one_mul]
    rw [this]
  have hcard_a : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hao]
  have hcard_b : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hbo]
  have hcard_ab : Nat.card (Subgroup.zpowers (a * b)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hab3 hab1]
  have hcard_abb : Nat.card (Subgroup.zpowers (a * b * b)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime habb3 habb1]
  rcases mem_four_subgroups ha3 hb3 hab hij hy1 with h | h | h | h
  · exact Or.inl (zpowers_eq_of_prime_card hcard_a h hy1)
  · exact Or.inr (Or.inl (zpowers_eq_of_prime_card hcard_b h hy1))
  · exact Or.inr (Or.inr (Or.inl (zpowers_eq_of_prime_card hcard_ab h hy1)))
  · exact Or.inr (Or.inr (Or.inr (zpowers_eq_of_prime_card hcard_abb h hy1)))

structure EData (X : Subgroup (MulAut V)) (t x y : MulAut V) : Prop where
  h : InvPair X t x
  hy : y ∈ centR X x
  hy3 : y ^ 3 = 1
  hyx : y ∉ Subgroup.zpowers x
  hY : Subgroup.zpowers y ∈ Yinv X

namespace EData

variable {t x y : MulAut V}

omit [Finite V] in
theorem hy1 (d : EData X t x y) : y ≠ 1 := fun e =>
  d.hyx (by rw [e]; exact Subgroup.one_mem _)

omit [Finite V] in
theorem orderOf_y (d : EData X t x y) : orderOf y = 3 := orderOf_eq_prime d.hy3 d.hy1

omit [Finite V] in
theorem comm (d : EData X t x y) : x * y = y * x := (mem_centR.mp d.hy).2.symm

omit [Finite V] in
theorem hne (d : EData X t x y) : Subgroup.zpowers x ≠ Subgroup.zpowers y := fun e =>
  d.hyx (by rw [e]; exact Subgroup.mem_zpowers y)

theorem orderOf_x (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (d : EData X t x y) : orderOf x = 3 :=
  (inverted_data hV c hX1 d.h.ht d.h.hx d.h.hx1 d.h.hinv).1

theorem hx3 (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (d : EData X t x y) : x ^ 3 = 1 := by
  rw [← d.orderOf_x hV c hX1]
  exact pow_orderOf_eq_one x

theorem rk_x (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (d : EData X t x y) : rk (commV (Subgroup.zpowers x)) = 4 :=
  (inverted_data hV c hX1 d.h.ht d.h.hx d.h.hx1 d.h.hinv).2.1

theorem rk_y (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (d : EData X t x y) : rk (commV (Subgroup.zpowers y)) = 4 := by
  obtain ⟨-, -, -, -, -, hrk⟩ := Yinv_data hV c hX1 d.hY
  exact hrk

omit [Finite V] in
theorem hyR (d : EData X t x y) : y ∈ pCoreOf 3 X := (mem_centR.mp d.hy).1

end EData

variable {t x y : MulAut V}

theorem conj_mem_E (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (d : EData X t x y) {g e : MulAut V} (hg : ∀ p ∈ centR X x, g * p * g⁻¹ ∈ centR X x)
    (he : e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    g * e * g⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
  have hxP : x ∈ centR X x := mem_centR.mpr ⟨d.h.hx, rfl⟩
  have hEP : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ centR X x :=
    sup_le (Subgroup.zpowers_le.mpr hxP) (Subgroup.zpowers_le.mpr d.hy)
  obtain ⟨-, -, hform⟩ := E9_data (d.orderOf_x hV c hX1) d.orderOf_y d.comm d.hne
  obtain ⟨i, j, hij⟩ := hform e he
  have he3 : e ^ 3 = 1 := cube_eq_one_of_mem_E (d.hx3 hV c hX1) d.hy3 d.comm hij
  have hge3 : (g * e * g⁻¹) ^ 3 = 1 := by rw [conj_pow, he3]; group
  exact mem_E_of_cube hV c hX1 d.h d.hy d.hy3 d.hyx (hg e (hEP he)) hge3

theorem commV_le_fixV_of_trivial (hV : ∀ v : V, v ^ 2 = 1) {x q : MulAut V}
    (hxc : Nat.card (Subgroup.zpowers x) = 3) (hqx : q * x = x * q)
    (hq : ∀ w ∈ commV (Subgroup.zpowers x), q w = w) :
    commV (Subgroup.zpowers q) ≤ fixV (Subgroup.zpowers x) := by
  obtain ⟨hdec, -, -, -⟩ := commV_card_three hV hxc
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  have hv : v ∈ commV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers x) := by
    rw [hdec]; exact Subgroup.mem_top v
  obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
  have hgw : g w = w := by
    have hs : Subgroup.zpowers q ≤ MulAction.stabilizer (MulAut V) w :=
      Subgroup.zpowers_le.mpr (hq w hw)
    exact hs hg
  have hgc : g c ∈ fixV (Subgroup.zpowers x) := by
    refine fixV_smul_mem (fun p hp => ?_) hc
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hcom : Commute (q ^ k) (x ^ m) := ((show Commute q x from hqx).zpow_zpow k m)
    have e : (q ^ k)⁻¹ * x ^ m * q ^ k = x ^ m := by
      rw [mul_assoc, ← hcom.eq, inv_mul_cancel_left]
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) m
  have : g (w * c) * (w * c)⁻¹ = g c * c⁻¹ := by
    rw [map_mul, hgw, mul_inv_rev]
    calc w * g c * (c⁻¹ * w⁻¹) = (g c * c⁻¹) * (w * w⁻¹) := by ac_rfl
      _ = g c * c⁻¹ := by rw [mul_inv_cancel, mul_one]
  rw [this]
  exact (fixV (Subgroup.zpowers x)).mul_mem hgc ((fixV (Subgroup.zpowers x)).inv_mem hc)

theorem E_faithful_pattern6 (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) (d : EData X t x y)
    (h6 : rk (commV (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) = 6) {q : MulAut V}
    (hq : q ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y)
    (hqW : ∀ w ∈ commV (Subgroup.zpowers x), q w = w) : q = 1 := by
  by_contra hq1
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hxo := d.orderOf_x hV c hX1
  obtain ⟨-, hEcomm, hform⟩ := E9_data hxo d.orderOf_y d.comm d.hne
  obtain ⟨i, j, hij⟩ := hform q hq
  have hq3 : q ^ 3 = 1 := cube_eq_one_of_mem_E (d.hx3 hV c hX1) d.hy3 d.comm hij
  have hqo : orderOf q = 3 := orderOf_eq_prime hq3 hq1
  have hqcard : Nat.card (Subgroup.zpowers q) = 3 := by rw [Nat.card_zpowers, hqo]
  have hqE : Subgroup.zpowers q ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    Subgroup.zpowers_le.mpr hq
  have hEP : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ pCoreOf 3 X :=
    sup_le (Subgroup.zpowers_le.mpr d.h.hx) (Subgroup.zpowers_le.mpr d.hyR)
  have h4 := four_le_rk_commV hV c hX1 (hqE.trans hEP) hqcard
  have hxc : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
  have hqx : q * x = x * q :=
    hEcomm q hq x (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hle := commV_le_fixV_of_trivial hV hxc hqx hqW
  have hbot : commV (Subgroup.zpowers x) ⊓ commV (Subgroup.zpowers q) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h1 : v ∈ commV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers x) := ⟨hv.1, hle hv.2⟩
    obtain ⟨-, hinf, -, -⟩ := commV_card_three hV hxc
    rw [hinf] at h1
    exact h1
  have hsum := rk_sup_add_rk_inf (commV (Subgroup.zpowers x)) (commV (Subgroup.zpowers q))
  rw [hbot, rk_bot, d.rk_x hV c hX1] at hsum
  have hle2 : (commV (Subgroup.zpowers x) ⊔ commV (Subgroup.zpowers q) : Subgroup V) ≤
      commV (Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    sup_le (commV_mono le_sup_left) (commV_mono hqE)
  have := rk_mono hle2
  omega

theorem centR_faithful_pattern6 (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) (d : EData X t x y)
    (h6 : rk (commV (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) = 6) {p : MulAut V}
    (hp : p ∈ centR X x) (hpW : ∀ w ∈ commV (Subgroup.zpowers x), p w = w) : p = 1 := by
  by_contra hp1
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hpR, -⟩ := mem_centR.mp hp
  obtain ⟨a, ha⟩ := exists_orderOf_eq_pow (pCoreOf_isPGroup 3 X) hpR
  have ha1 : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at ha
    exact hp1 ha
  have h3 : 3 ∣ orderOf p := by rw [ha]; exact dvd_pow_self 3 (by omega)
  have hco : orderOf p ≠ 0 := (orderOf_pos p).ne'
  obtain ⟨q, hq⟩ : ∃ q, q = p ^ (orderOf p / 3) := ⟨_, rfl⟩
  have hqo : orderOf q = 3 := by rw [hq]; exact orderOf_pow_orderOf_div hco h3
  have hq3 : q ^ 3 = 1 := by rw [← hqo]; exact pow_orderOf_eq_one q
  have hq1 : q ≠ 1 := fun e => by rw [e, orderOf_one] at hqo; omega
  have hqP : q ∈ centR X x := by rw [hq]; exact (centR X x).pow_mem hp _
  have hqW : ∀ w ∈ commV (Subgroup.zpowers x), q w = w := fun w hw => by
    have hs : p ∈ MulAction.stabilizer (MulAut V) w := hpW w hw
    rw [hq]
    exact Subgroup.pow_mem _ hs _
  have hqE := mem_E_of_cube hV c hX1 d.h d.hy d.hy3 d.hyx hqP hq3
  exact hq1 (E_faithful_pattern6 hV c hX1 d h6 hqE hqW)

theorem card_dvd_nine_of_faithful (hV : ∀ v : V, v ^ 2 = 1) {P : Subgroup (MulAut V)}
    (hP : IsPGroup 3 P) {W : Subgroup V} (hW : rk W = 4)
    (hinv : ∀ g ∈ P, ∀ w ∈ W, g w ∈ W)
    (hfaith : ∀ g ∈ P, (∀ w ∈ W, g w = w) → g = 1) : Nat.card P ∣ 9 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPs : P ≤ stabSub W := fun g hg u =>
    ⟨fun h => by
      have := hinv g⁻¹ (P.inv_mem hg) (g u) h
      simpa using this, hinv g hg u⟩
  have hcard := card_autSub_mul hPs
  have hinf : P ⊓ centSub W = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    exact (Subgroup.mem_bot).mpr (hfaith g hg.1 hg.2)
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  have h3 : IsPGroup 3 ↥(autSub P W) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    exact (IsPGroup.iff_card).mpr ⟨n, by rw [hcard, hn]⟩
  have hW2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hV v)
  have := three_group_card_dvd_nine (V := ↥W) hW2 hW h3
  rw [hcard] at this
  exact this

theorem centR_eq_E (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (d : EData X t x y) (h6 : rk (commV (Subgroup.zpowers x ⊔ Subgroup.zpowers y)) = 6) :
    centR X x = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hxo := d.orderOf_x hV c hX1
  obtain ⟨hEcard, hEcomm, -⟩ := E9_data hxo d.orderOf_y d.comm d.hne
  have hxP : x ∈ centR X x := mem_centR.mpr ⟨d.h.hx, rfl⟩
  have hEP : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ centR X x :=
    sup_le (Subgroup.zpowers_le.mpr hxP) (Subgroup.zpowers_le.mpr d.hy)
  have hPp : IsPGroup 3 (centR X x) :=
    (pCoreOf_isPGroup 3 X).of_injective (Subgroup.inclusion (inf_le_left : centR X x ≤ _))
      (Subgroup.inclusion_injective _)
  have hdvd : Nat.card (centR X x) ∣ 9 := by
    refine card_dvd_nine_of_faithful hV hPp (d.rk_x hV c hX1) (fun g hg w hw => ?_)
      (fun g hg hgW => centR_faithful_pattern6 hV c hX1 d h6 hg hgW)
    refine commV_smul_mem (fun p hp => ?_) hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hcom : Commute g (x ^ m) :=
      (show Commute g x from (mem_centR.mp hg).2).zpow_right m
    rw [hcom.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) m
  have hle : Nat.card (centR X x) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  exact (Subgroup.eq_of_le_of_card_ge hEP (by rw [hEcard]; exact hle)).symm

end E

end CFSG.Quasithin
