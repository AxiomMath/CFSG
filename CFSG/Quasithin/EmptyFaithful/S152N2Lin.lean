module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.EmptyFaithful.S145Cop

public section

namespace CFSG.Quasithin

namespace S152N2

variable {V : Type*} [CommGroup V]

@[expose] def commHom (b : MulAut V) : V →* V where
  toFun v := b v * v⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv]
    ac_rfl

theorem commHom_apply (b : MulAut V) (v : V) : commHom b v = b v * v⁻¹ := rfl

theorem zpow_apply_eq_of_apply_eq {b : MulAut V} {v : V} (h : b v = v) (k : ℤ) :
    (b ^ k) v = v := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, MulAut.mul_apply, h, ih]
  | pred n ih =>
    have h' : b.symm v = v := (MulEquiv.symm_apply_eq b).mpr h.symm
    rw [zpow_sub_one, MulAut.mul_apply, MulAut.inv_apply, h', ih]

theorem mem_fixV_zpowers_iff {b : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers b) ↔ b v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem ker_commHom (b : MulAut V) : (commHom b).ker = fixV (Subgroup.zpowers b) := by
  ext v
  rw [MonoidHom.mem_ker, commHom_apply, mem_fixV_zpowers_iff, mul_inv_eq_one]

theorem zpow_eq_one_or_self {b : MulAut V} (hb : b * b = 1) (k : ℤ) :
    b ^ k = 1 ∨ b ^ k = b := by
  have h2 : b ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hb
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    have : k = 2 * (k / 2) := by omega
    rw [this, zpow_mul, h2, one_zpow]
  · right
    have : k = 2 * (k / 2) + 1 := by omega
    rw [this, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem range_commHom_eq_commV {b : MulAut V} (hb : b * b = 1) :
    (commHom b).range = commV (Subgroup.zpowers b) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨b, Subgroup.mem_zpowers b, v, rfl⟩
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases zpow_eq_one_or_self hb k with h | h
    · rw [h]
      exact ⟨1, by simp [commHom_apply]⟩
    · rw [h]
      exact ⟨v, rfl⟩

theorem card_fixV_mul_card_commV [Finite V] {b : MulAut V} (hb : b * b = 1) :
    Nat.card (fixV (Subgroup.zpowers b)) * Nat.card (commV (Subgroup.zpowers b)) =
      Nat.card V := by
  have h1 := Subgroup.card_mul_index (commHom b).ker
  rw [Subgroup.index_ker, ker_commHom, range_commHom_eq_commV hb] at h1
  exact h1

theorem commV_le_fixV_of_sq (hV : ∀ v : V, v ^ 2 = 1) {b : MulAut V} (hb : b * b = 1) :
    commV (Subgroup.zpowers b) ≤ fixV (Subgroup.zpowers b) := by
  rw [← range_commHom_eq_commV hb]
  rintro _ ⟨v, rfl⟩
  rw [mem_fixV_zpowers_iff, commHom_apply, map_mul, map_inv]
  have hbb : b (b v) = v := by
    have := congrArg (fun φ : MulAut V => φ v) hb
    simpa using this
  rw [hbb]
  have h2 : (b v * v⁻¹)⁻¹ = b v * v⁻¹ := by
    have h3 : (b v * v⁻¹) * (b v * v⁻¹) = 1 := by
      have e1 : (b v) ^ 2 = 1 := hV _
      have e2 : v ^ 2 = 1 := hV _
      calc (b v * v⁻¹) * (b v * v⁻¹) = (b v) ^ 2 * (v ^ 2)⁻¹ := by
            rw [pow_two, pow_two, mul_inv]; ac_rfl
        _ = 1 := by rw [e1, e2]; simp
    exact inv_eq_of_mul_eq_one_right h3
  calc v * (b v)⁻¹ = (b v * v⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
    _ = b v * v⁻¹ := h2

theorem fixV_eq_commV_of_card [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {b : MulAut V}
    (hb : b * b = 1) (hcard : Nat.card V = 16)
    (hc : Nat.card (commV (Subgroup.zpowers b)) = 4) :
    fixV (Subgroup.zpowers b) = commV (Subgroup.zpowers b) := by
  have h := card_fixV_mul_card_commV hb
  rw [hcard, hc] at h
  have hf : Nat.card (fixV (Subgroup.zpowers b)) = 4 := by omega
  symm
  exact Subgroup.eq_of_le_of_card_ge (commV_le_fixV_of_sq hV hb) (by rw [hf, hc])

theorem eq_one_of_centralizes_commV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {b y : MulAut V}
    (hy : y ^ 3 = 1) (hcomm : b * y = y * b)
    (hfix : fixV (Subgroup.zpowers b) ≤ commV (Subgroup.zpowers b))
    (hcen : ∀ w ∈ commV (Subgroup.zpowers b), y w = w) : y = 1 := by
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) (fun f g h => DFunLike.coe_injective h)
  have : Finite (Subgroup.zpowers y) := inferInstance
  have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers]
    have hd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact ⟨1, rfl⟩
  have hc := isCompl_fixV_commV_of_odd (Subgroup.zpowers y) hodd hV
  have hkey : ∀ x ∈ Subgroup.zpowers y, ∀ v : V, y (x v * v⁻¹) = x v * v⁻¹ := by
    intro x hx v
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hbx : b * y ^ k = y ^ k * b := (Commute.zpow_right hcomm k)
    set u : V := b v * v⁻¹ with hu
    have huc : u ∈ commV (Subgroup.zpowers b) :=
      Subgroup.subset_closure ⟨b, Subgroup.mem_zpowers b, v, rfl⟩
    have hyu : y u = u := hcen u huc
    have hxu : (y ^ k) u = u := zpow_apply_eq_of_apply_eq hyu k
    have hbv : b v = u * v := by rw [hu]; group
    have hc1 : b ((y ^ k) v * v⁻¹) = (y ^ k) v * v⁻¹ := by
      have e1 : b ((y ^ k) v) = (y ^ k) (b v) := by
        have := congrArg (fun φ : MulAut V => φ v) hbx
        simpa [MulAut.mul_apply] using this
      rw [map_mul, map_inv, e1, hbv, map_mul, hxu]
      calc u * (y ^ k) v * (u * v)⁻¹ = (u * u⁻¹) * ((y ^ k) v * v⁻¹) := by
            rw [mul_inv]; ac_rfl
        _ = (y ^ k) v * v⁻¹ := by rw [mul_inv_cancel, one_mul]
    have hmem : (y ^ k) v * v⁻¹ ∈ fixV (Subgroup.zpowers b) := mem_fixV_zpowers_iff.mpr hc1
    exact hcen _ (hfix hmem)
  have hle : commV (Subgroup.zpowers y) ≤ fixV (Subgroup.zpowers y) := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    exact mem_fixV_zpowers_iff.mpr (hkey x hx v)
  have hbot : commV (Subgroup.zpowers y) = ⊥ := by
    have := hc.disjoint
    rw [Subgroup.disjoint_def] at this
    refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => this (hle hw) hw
  ext v
  have h1 : y v * v⁻¹ ∈ commV (Subgroup.zpowers y) :=
    Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, v, rfl⟩
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
  simpa using h1

theorem apply_mem_commV_zpowers {b y : MulAut V} (hcomm : b * y = y * b) {w : V}
    (hw : w ∈ commV (Subgroup.zpowers b)) : y w ∈ commV (Subgroup.zpowers b) := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨c, hc, y v, ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hbx : b ^ k * y = y * b ^ k := (Commute.zpow_left hcomm k)
    have e1 : (b ^ k) (y v) = y ((b ^ k) v) := by
      have := congrArg (fun φ : MulAut V => φ v) hbx
      simpa [MulAut.mul_apply] using this
    rw [map_mul, map_inv, e1]
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem exists_zpowers_eq_of_card_two {Γ : Type*} [Group Γ] {B : Subgroup Γ}
    (h : Nat.card B = 2) : ∃ b : Γ, b ≠ 1 ∧ b * b = 1 ∧ B = Subgroup.zpowers b := by
  have h2 : 2 ∣ Nat.card B := by rw [h]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hord : orderOf (c : Γ) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
  refine ⟨c, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hord
    omega
  · have := pow_orderOf_eq_one (c : Γ)
    rw [hord, sq] at this
    exact this
  · symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact (Subgroup.zpowers_le).mpr c.2
    · rw [Nat.card_zpowers, hord, h]

theorem fixed_of_pow_three [Finite V] {W : Subgroup V}
    (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hcard : Nat.card W = 4) {y : MulAut V} (hy3 : y ^ 3 = 1)
    (hyW : ∀ w ∈ W, y w ∈ W) {w' : V} (hw'W : w' ∈ W) (hw'1 : w' ≠ 1) (hf : y w' = w') :
    ∀ w ∈ W, y w = w := by
  set K : Subgroup V := Subgroup.zpowers w' with hK
  have hKW : K ≤ W := (Subgroup.zpowers_le).mpr hw'W
  have hordw' : orderOf w' = 2 := orderOf_eq_prime (by simpa [sq] using hW2 w' hw'W) hw'1
  have hcardK : Nat.card K = 2 := by rw [hK, Nat.card_zpowers, hordw']
  have hidx : (K.subgroupOf W).index = 2 := by
    have h1 := (K.subgroupOf W).card_mul_index
    have h2 : Nat.card (K.subgroupOf W) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKW).toEquiv, hcardK]
    rw [h2, hcard] at h1
    omega
  have hyK : ∀ k ∈ K, y k = k := by
    intro k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rw [map_zpow, hf]
  have hy3' : ∀ v : V, y (y (y v)) = v := by
    intro v
    have := congrArg (fun φ : MulAut V => φ v) hy3
    simpa [pow_succ, MulAut.mul_apply] using this
  intro w hw
  by_cases hwK : w ∈ K
  · exact hyK w hwK
  · have hywK : y w ∉ K := by
      intro h
      apply hwK
      have h1 : y (y w) = y w := hyK _ h
      have h3 := hy3' w
      rw [h1, h1] at h3
      rw [← h3]; exact h
    have hmem : (⟨w, hw⟩ : W)⁻¹ * ⟨y w, hyW w hw⟩ ∈ K.subgroupOf W := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      have ha : (⟨w, hw⟩ : W)⁻¹ ∉ K.subgroupOf W := by
        intro h
        exact hwK (Subgroup.mem_subgroupOf.mp ((K.subgroupOf W).inv_mem_iff.mp h))
      have hb : (⟨y w, hyW w hw⟩ : W) ∉ K.subgroupOf W := fun h =>
        hywK (Subgroup.mem_subgroupOf.mp h)
      exact ⟨fun h => absurd h ha, fun h => absurd h hb⟩
    have hmem' : w⁻¹ * y w ∈ K := Subgroup.mem_subgroupOf.mp hmem
    have hcW : w⁻¹ * y w ∈ W := W.mul_mem (W.inv_mem hw) (hyW w hw)
    have hc2 : (w⁻¹ * y w) * (w⁻¹ * y w) = 1 := by
      have := hW2 _ hcW
      rwa [sq] at this
    have hyc : y (w⁻¹ * y w) = w⁻¹ * y w := hyK _ hmem'
    have hyw : y w = w * (w⁻¹ * y w) := by simp
    have hyyw : y (y w) = w := by
      calc y (y w) = y (w * (w⁻¹ * y w)) := by rw [← hyw]
        _ = y w * (w⁻¹ * y w) := by rw [map_mul, hyc]
        _ = w * ((w⁻¹ * y w) * (w⁻¹ * y w)) := by rw [hyw]; group
        _ = w := by rw [hc2, mul_one]
    have h3 := hy3' w
    rw [hyyw] at h3
    exact h3

theorem exists_three_power_lift {Γ Λ : Type*} [Group Γ] [Group Λ] (φ : Γ →* Λ) (g₀ : Γ)
    (hfin : IsOfFinOrder g₀) (hy3 : φ g₀ ^ 3 = 1) (hy1 : φ g₀ ≠ 1) :
    ∃ g : Γ, ∃ a : ℕ, g ^ (3 ^ a) = 1 ∧ φ g = φ g₀ := by
  have hn0 : orderOf g₀ ≠ 0 := hfin.orderOf_pos.ne'
  set n := orderOf g₀ with hn
  have hprime : Nat.Prime 3 := Nat.prime_three
  set a := n.factorization 3 with ha
  set m := n / 3 ^ a with hm
  have hnm : 3 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 3
  have hcop : Nat.Coprime 3 m := Nat.coprime_ordCompl hprime hn0
  have hcop' : Nat.Coprime (3 ^ a) m := Nat.Coprime.pow_left a hcop
  have ha1 : 1 ≤ a := by
    by_contra hlt
    have ha0 : a = 0 := by omega
    have h3n : ¬ 3 ∣ n := by
      intro h
      have : 0 < n.factorization 3 := (hprime.factorization_pos_of_dvd hn0 h)
      omega
    have hord : orderOf (φ g₀) ∣ n := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow, hn, pow_orderOf_eq_one, map_one]
    have hord3 : orderOf (φ g₀) ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have hcop3 : Nat.Coprime (orderOf (φ g₀)) n := by
      rcases (Nat.dvd_prime hprime).mp hord3 with h | h
      · rw [h]; exact Nat.coprime_one_left n
      · rw [h]; exact (Nat.Prime.coprime_iff_not_dvd hprime).mpr h3n
    have : orderOf (φ g₀) = 1 := Nat.Coprime.eq_one_of_dvd hcop3 hord
    exact hy1 (orderOf_eq_one_iff.mp this)
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hcop' 1 0
  refine ⟨g₀ ^ k, a, ?_, ?_⟩
  · rw [← pow_mul]
    have : n ∣ k * 3 ^ a := by
      have hmk : m ∣ k := (Nat.modEq_zero_iff_dvd).mp hk0
      obtain ⟨t, ht⟩ := hmk
      refine ⟨t, ?_⟩
      rw [ht, ← hnm]; ring
    exact orderOf_dvd_iff_pow_eq_one.mp this
  · have h3k : k % 3 = 1 := by
      have h1 : k % 3 ^ a = 1 % 3 ^ a := hk1
      have h3a : 3 ∣ 3 ^ a := dvd_pow_self 3 (by omega)
      have : k % 3 = (k % 3 ^ a) % 3 := (Nat.mod_mod_of_dvd k h3a).symm
      rw [this, h1]
      have h13 : 1 < 3 ^ a := Nat.one_lt_pow (by omega) (by norm_num)
      rw [Nat.mod_eq_of_lt h13]
    have hkdecomp : k = 3 * (k / 3) + 1 := by omega
    rw [map_pow, hkdecomp, pow_succ, pow_mul, hy3, one_pow, one_mul]

theorem exists_central_of_normalized {G : Type*} [Group G] [Finite G] {T W : Subgroup G}
    (hT : IsPGroup 2 T) (hWT : W ≤ T)
    (hN : T ≤ Subgroup.normalizer (W : Set G)) (hW1 : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 1 ∧ ∀ t ∈ T, t * w = w * t := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnorm : (W.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWT).mpr hN
  have hne : W.subgroupOf T ≠ ⊥ := by
    intro h
    apply hW1
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hWT hx⟩ : T) ∈ W.subgroupOf T := hx
    rw [h, Subgroup.mem_bot] at hmem
    have := congrArg Subtype.val hmem
    simpa using this
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨m, hm⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  have hmW : m ∈ W.subgroupOf T := (Subgroup.mem_inf.mp hm).1
  have hmZ : m ∈ Subgroup.center T := (Subgroup.mem_inf.mp hm).2
  refine ⟨m, hmW, ?_, fun t ht => ?_⟩
  · intro h1
    apply hm1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  · have := Subgroup.mem_center_iff.mp hmZ ⟨t, ht⟩
    have h2 := congrArg Subtype.val this
    simpa using h2

end S152N2

end CFSG.Quasithin
