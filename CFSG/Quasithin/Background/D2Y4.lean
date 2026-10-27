module

public import CFSG.Quasithin.Background.D2Y3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commV_sup_le (A B : Subgroup (MulAut V)) : commV (A ⊔ B) ≤ commV A ⊔ commV B :=
  CFSG.Quasithin.FixVLat.commV_sup_le A B

omit [Finite V] in
theorem commV_sup (A B : Subgroup (MulAut V)) : commV (A ⊔ B) = commV A ⊔ commV B :=
  le_antisymm (commV_sup_le A B) (sup_le (commV_mono le_sup_left) (commV_mono le_sup_right))

omit [Finite V] in
theorem mem_four_subgroups {a b y : MulAut V} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a) {i j : ℤ} (hy : y = a ^ i * b ^ j) (hy1 : y ≠ 1) :
    y ∈ Subgroup.zpowers a ∨ y ∈ Subgroup.zpowers b ∨ y ∈ Subgroup.zpowers (a * b) ∨
      y ∈ Subgroup.zpowers (a * b * b) := by
  have hcab : Commute a b := hab
  have hred : ∀ (g : MulAut V) (n : ℤ), g ^ 3 = 1 → g ^ n = g ^ (n % 3) := by
    intro g n hg
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
    rw [zpow_add, zpow_mul]
    have : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
    rw [this, one_zpow, mul_one]
  rw [hred a i ha3, hred b j hb3] at hy
  have hb4 : b ^ (4 : ℤ) = b := by
    have : b ^ (3 : ℤ) = 1 := by exact_mod_cast hb3
    calc b ^ (4 : ℤ) = b ^ (1 + 3 : ℤ) := by norm_num
      _ = b ^ (1 : ℤ) * b ^ (3 : ℤ) := zpow_add _ _ _
      _ = b := by rw [this, mul_one, zpow_one]
  have e22 : a ^ (2 : ℤ) * b ^ (2 : ℤ) = (a * b) ^ (2 : ℤ) := (hcab.mul_zpow 2).symm
  have e21 : a ^ (2 : ℤ) * b = (a * b * b) ^ (2 : ℤ) := by
    have h1 : a * b * b = a * b ^ (2 : ℤ) := by rw [zpow_two, mul_assoc]
    have h2 : (a * b ^ (2 : ℤ)) ^ (2 : ℤ) = a ^ (2 : ℤ) * (b ^ (2 : ℤ)) ^ (2 : ℤ) :=
      ((hcab.zpow_right 2).mul_zpow 2)
    have h3 : (b ^ (2 : ℤ)) ^ (2 : ℤ) = b := by
      calc (b ^ (2 : ℤ)) ^ (2 : ℤ) = b ^ ((2 : ℤ) * 2) := (zpow_mul b 2 2).symm
        _ = b ^ (4 : ℤ) := by norm_num
        _ = b := hb4
    rw [h1, h2, h3]
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;> rw [hi, hj] at hy
  · exact absurd (by simpa using hy) hy1
  · right; left; rw [hy]; simp
  · right; left; rw [hy]; simp
  · left; rw [hy]; simp
  · right; right; left; rw [hy]; simp
  · right; right; right; rw [hy]
    have : a ^ (1 : ℤ) * b ^ (2 : ℤ) = a * b * b := by rw [zpow_one, zpow_two, mul_assoc]
    rw [this]
    exact Subgroup.mem_zpowers _
  · left; rw [hy]; simp
  · right; right; right; rw [hy]
    have : a ^ (2 : ℤ) * b ^ (1 : ℤ) = a ^ (2 : ℤ) * b := by rw [zpow_one]
    rw [this, e21]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) 2
  · right; right; left; rw [hy, e22]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) 2

theorem E9_data {a b : MulAut V} (hao : orderOf a = 3) (hbo : orderOf b = 3)
    (hab : a * b = b * a) (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b) :
    Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup (MulAut V)) = 9 ∧
      (∀ x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b,
        x * y = y * x) ∧
      (∀ y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, ∃ i j : ℤ, y = a ^ i * b ^ j) := by
  have hcard_a : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hao]
  have hcard_b : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hbo]
  have hcomm_ab : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hab) m n).eq
  obtain ⟨hEcard, hEprod⟩ := sup_structure hcard_a hcard_b hne hcomm_ab
  refine ⟨hEcard, sup_comm_elements hcard_a hcard_b hne hcomm_ab, fun y hy => ?_⟩
  obtain ⟨x, hx, z, hz, rfl⟩ := hEprod y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ⟨i, j, rfl⟩

section Pattern

variable {X : Subgroup (MulAut V)}

theorem mem_E_of_cube (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {t x y₁ y : MulAut V} (h : InvPair X t x) (hy₁ : y₁ ∈ centR X x) (hy₁3 : y₁ ^ 3 = 1)
    (hy₁x : y₁ ∉ Subgroup.zpowers x) (hy : y ∈ centR X x) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y₁ := by
  have hcyc := isCyclic_pCoreOf_inf_centralizer hV c h.ht
  have := hcyc
  have hxord := (inverted_data hV c hX1 h.ht h.hx h.hx1 h.hinv).1
  have hx3 : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  obtain ⟨hyR, hyc⟩ := mem_centR.mp hy
  obtain ⟨hy₁R, hy₁c⟩ := mem_centR.mp hy₁
  obtain ⟨k, hk⟩ := exists_zpow_commute hV c hX1 h hy
  obtain ⟨k₁, hk₁⟩ := exists_zpow_commute hV c hX1 h hy₁
  have hxk : ∀ n : ℤ, x ^ n ∈ pCoreOf 3 X := fun n => (pCoreOf 3 X).zpow_mem h.hx n
  have hcx : ∀ n : ℤ, Commute y (x ^ n) := fun n =>
    (show Commute y x from hyc).zpow_right n
  have hcx₁ : ∀ n : ℤ, Commute y₁ (x ^ n) := fun n =>
    (show Commute y₁ x from hy₁c).zpow_right n
  have hzC : y * x ^ k ∈ pCoreOf 3 X ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) :=
    ⟨(pCoreOf 3 X).mul_mem hyR (hxk k), Subgroup.mem_centralizer_singleton_iff.mpr hk.symm⟩
  have hz₁C : y₁ * x ^ k₁ ∈ pCoreOf 3 X ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) :=
    ⟨(pCoreOf 3 X).mul_mem hy₁R (hxk k₁), Subgroup.mem_centralizer_singleton_iff.mpr hk₁.symm⟩
  have hx3z : ∀ n : ℤ, (x ^ n) ^ 3 = 1 := fun n => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    simp [this]
  have hz3 : (y * x ^ k) ^ 3 = 1 := by
    rw [(hcx k).mul_pow, hy3, hx3z, one_mul]
  have hz₁3 : (y₁ * x ^ k₁) ^ 3 = 1 := by
    rw [(hcx₁ k₁).mul_pow, hy₁3, hx3z, one_mul]
  have hz₁1 : y₁ * x ^ k₁ ≠ 1 := by
    intro e
    apply hy₁x
    have : y₁ = (x ^ k₁)⁻¹ := eq_inv_of_mul_eq_one_left e
    rw [this, ← zpow_neg]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  have hmem := mem_zpowers_of_cube
    (G := ↥(pCoreOf 3 X ⊓ Subgroup.centralizer ({t} : Set (MulAut V))))
    (z := ⟨y * x ^ k, hzC⟩) (z₁ := ⟨y₁ * x ^ k₁, hz₁C⟩) (Subtype.ext hz3) (Subtype.ext hz₁3)
    (fun e => hz₁1 (congrArg Subtype.val e))
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hm' : (y₁ * x ^ k₁) ^ m = y * x ^ k := congrArg Subtype.val hm
  have hyeq : y = y₁ ^ m * (x ^ (k₁ * m) * (x ^ k)⁻¹) := by
    have h1 : y = (y * x ^ k) * (x ^ k)⁻¹ := (mul_inv_cancel_right _ _).symm
    rw [h1, ← hm', (hcx₁ k₁).mul_zpow, ← zpow_mul, mul_assoc]
  rw [hyeq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y₁) _))
    (Subgroup.mem_sup_left (Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _)
      (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _))))

theorem pattern_E9 (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    {a b : MulAut V} (ha : a ∈ pCoreOf 3 X) (hb : b ∈ pCoreOf 3 X) (hao : orderOf a = 3)
    (hbo : orderOf b = 3) (hab : a * b = b * a)
    (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b)
    (hra : rk (commV (Subgroup.zpowers a)) = 4) (hrb : rk (commV (Subgroup.zpowers b)) = 4) :
    (rk (commV (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) = 6 ∧
      ((rk (commV (Subgroup.zpowers (a * b))) = 4 ∧
          rk (commV (Subgroup.zpowers (a * b * b))) = 6) ∨
        (rk (commV (Subgroup.zpowers (a * b))) = 6 ∧
          rk (commV (Subgroup.zpowers (a * b * b))) = 4))) ∨
    (rk (commV (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) = 8 ∧
      rk (commV (Subgroup.zpowers (a * b))) = 8 ∧
      rk (commV (Subgroup.zpowers (a * b * b))) = 8) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have ha3 : a ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  obtain ⟨hEcard, hEcomm, -⟩ := E9_data hao hbo hab hne
  have hweights := rk_commV_sum_E9 hV hao hbo hab hne
  obtain ⟨E, hE⟩ : ∃ E, E = Subgroup.zpowers a ⊔ Subgroup.zpowers b := ⟨_, rfl⟩
  rw [← hE] at hEcard hEcomm hweights ⊢
  have haE : a ∈ E := by rw [hE]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hbE : b ∈ E := by rw [hE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have habE : a * b ∈ E := E.mul_mem haE hbE
  have habbE : a * b * b ∈ E := E.mul_mem habE hbE
  have hEodd : Odd (Nat.card E) := by rw [hEcard]; exact ⟨4, rfl⟩
  have hEX : E ≤ pCoreOf 3 X := by
    rw [hE]
    exact sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
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
  have hord_ab : orderOf (a * b) = 3 := orderOf_eq_prime hab3 hab1
  have hord_abb : orderOf (a * b * b) = 3 := orderOf_eq_prime habb3 habb1
  have hcard_ab : Nat.card (Subgroup.zpowers (a * b)) = 3 := by rw [Nat.card_zpowers, hord_ab]
  have hcard_abb : Nat.card (Subgroup.zpowers (a * b * b)) = 3 := by
    rw [Nat.card_zpowers, hord_abb]
  have h4ab := four_le_rk_commV hV c hX1
    ((Subgroup.zpowers_le.mpr habE).trans hEX) hcard_ab
  have h4abb := four_le_rk_commV hV c hX1
    ((Subgroup.zpowers_le.mpr habbE).trans hEX) hcard_abb
  obtain ⟨-, -, -, hev_ab⟩ := commV_card_three hV hcard_ab
  obtain ⟨-, -, -, hev_abb⟩ := commV_card_three hV hcard_abb
  have hle_ab : rk (commV (Subgroup.zpowers (a * b))) ≤ rk (commV E) :=
    rk_mono (commV_mono (Subgroup.zpowers_le.mpr habE))
  have hle_abb : rk (commV (Subgroup.zpowers (a * b * b))) ≤ rk (commV E) :=
    rk_mono (commV_mono (Subgroup.zpowers_le.mpr habbE))
  have hle8 : rk (commV E) ≤ 8 := by
    have h1 : rk (commV E) ≤
        rk (commV (Subgroup.zpowers a) ⊔ commV (Subgroup.zpowers b) : Subgroup V) := by
      rw [hE, commV_sup]
    have h2 := rk_sup_add_rk_inf (commV (Subgroup.zpowers a)) (commV (Subgroup.zpowers b))
    omega
  have hge4 : 4 ≤ rk (commV E) := by
    have := rk_mono (commV_mono (Subgroup.zpowers_le.mpr haE))
    omega
  have hRE5 : 5 ≤ rk (commV E) := by
    by_contra hlt
    have h4 : rk (commV E) = 4 := by omega
    obtain ⟨hdec1, hdec2⟩ :=
      coprime_decomp hEodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
    rw [← commV_eq_commSub, top_inf_eq] at hdec1 hdec2
    have hEU : ∀ g ∈ E, ∀ u ∈ commV E, g u ∈ commV E := fun g hg u hu =>
      commV_smul_mem (fun p hp => by
        rw [hEcomm g hg p hp, mul_inv_cancel_right]
        exact hp) hu
    have hEC : ∀ g ∈ E, ∀ v ∈ fixV E, g v = v := fun g hg v hv => hv g hg
    obtain ⟨Y, hY⟩ := exists_Xk_of_card_nine hV c hEX hEcard (U := commV E) (C := fixV E)
      ⟨hdec1, hdec2⟩ h4 hEU hEC
    exact hX1 Y hY
  obtain ⟨m3, hm3⟩ := hev_ab
  obtain ⟨m4, hm4⟩ := hev_abb
  rw [hra, hrb] at hweights
  omega

end Pattern

end CFSG.Quasithin
