module

public import CFSG.Quasithin.Vol2.Ch11SecCB51Ord
public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.FFC4Ext
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace O8

theorem shape_eq {a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 2 ^ a * ((2 ^ a - 1) * (2 ^ b - 1)) = 2 ^ c * ((2 ^ c - 1) * (2 ^ d - 1))) :
    a = c ∧ b = d := by
  have hac : a = c := SecA.eq_of_two_pow_mul_odd
    ((SecA.odd_two_pow_sub_one ha).mul (SecA.odd_two_pow_sub_one hb))
    ((SecA.odd_two_pow_sub_one hc).mul (SecA.odd_two_pow_sub_one hd)) h
  subst hac
  have h1 := Nat.eq_of_mul_eq_mul_left (by positivity) h
  have h2 := Nat.eq_of_mul_eq_mul_left (SecA.odd_two_pow_sub_one ha).pos h1
  have h3 : 2 ^ b = 2 ^ d := by
    have := Nat.one_le_two_pow (n := b)
    have := Nat.one_le_two_pow (n := d)
    omega
  exact ⟨rfl, Nat.pow_right_injective le_rfl h3⟩

theorem sq_sub_one_eq (x : ℕ) : x ^ 2 - 1 = (x - 1) * (x + 1) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rfl
  · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring_nf
    omega

theorem sl2_shape_ne {m c d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hdc : d < c)
    (h : 2 ^ m * ((2 ^ m) ^ 2 - 1) = 2 ^ c * ((2 ^ c - 1) * (2 ^ d - 1))) : False := by
  have hodd : Odd ((2 ^ m) ^ 2 - 1) := by
    rw [← pow_mul]
    exact SecA.odd_two_pow_sub_one (by omega)
  have hmc : m = c := SecA.eq_of_two_pow_mul_odd hodd
    ((SecA.odd_two_pow_sub_one (by omega)).mul (SecA.odd_two_pow_sub_one hd)) h
  subst hmc
  have h1 := Nat.eq_of_mul_eq_mul_left (by positivity) h
  rw [sq_sub_one_eq] at h1
  have h2 := Nat.eq_of_mul_eq_mul_left (SecA.odd_two_pow_sub_one hm).pos h1
  have h3 : 2 ^ d < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hdc
  generalize 2 ^ d = y at h2 h3
  generalize 2 ^ m = x at h2 h3
  omega

theorem sl5_shape_ne {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 9999360 = 2 ^ c * ((2 ^ c - 1) * (2 ^ d - 1))) : False := by
  rw [show (9999360 : ℕ) = 2 ^ 10 * 9765 by norm_num] at h
  have h10 : 10 = c := SecA.eq_of_two_pow_mul_odd ⟨4882, by norm_num⟩
    ((SecA.odd_two_pow_sub_one hc).mul (SecA.odd_two_pow_sub_one hd)) h
  subst h10
  have h1 := Nat.eq_of_mul_eq_mul_left (by positivity) h
  norm_num at h1
  omega

theorem big_of_shape {c d : ℕ} (hc : 6 ≤ c) (hd : 4 ≤ d) :
    60480 ≤ 2 ^ c * ((2 ^ c - 1) * (2 ^ d - 1)) := by
  have h1 : 2 ^ 6 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc
  have h2 : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  calc (60480 : ℕ) = 2 ^ 6 * ((2 ^ 6 - 1) * (2 ^ 4 - 1)) := by norm_num
    _ ≤ _ := Nat.mul_le_mul h1
        (Nat.mul_le_mul (Nat.sub_le_sub_right h1 1) (Nat.sub_le_sub_right h2 1))

theorem card_statedSL_two (K : Type) [Field K] [Finite K] :
    Nat.card ↥(Assembly.LowTwoRank.StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two K

theorem card_quasithinG2 {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    Nat.card ↥(quasithinG2 K) =
      Nat.card K ^ 6 * ((Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1)) := by
  have := KGNat.charP_two_of_card (by have := B51.one_le_of_card_eq hK; omega) hK
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
  exact KGNat.card_cayleyGroup

theorem card_alt (n : ℕ) (hn : 2 ≤ n) :
    Nat.card ↥(alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [nat_card_alternatingGroup, Nat.card_fin]

theorem card_of_isHat {X S : Type} [Group X] [Group S] (h : IsHat X S)
    (hS : Nat.card S = 360) : Nat.card X = 1080 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv,
    hS, hc]

section Cases

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem card_le_of_alt {k : ℕ} (hk2 : 2 ≤ k) (hk : k ≤ 7)
    {π : ↥(alternatingGroup (Fin k)) →* ↥H} (hπ : Function.Surjective π) :
    Nat.card ↥H ≤ 2520 := by
  refine (Nat.card_le_card_of_surjective π hπ).trans ?_
  rw [card_alt k hk2]
  interval_cases k <;> decide

theorem card_eq_of_faithful {D : FFModel} (hD : D.Faithful) {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : Nat.card ↥H = Nat.card D.Gam :=
  (Nat.card_congr (Equiv.ofBijective π ⟨FFC.injective_of_faithful_sec hD h, h.1⟩)).symm

theorem b42_cases {c d : ℕ} (hc : 6 ≤ c) (hd : 4 ≤ d) (hdc : d < c)
    (hH : Nat.card ↥H = 2 ^ c * ((2 ^ c - 1) * (2 ^ d - 1))) (hB : B42ModulePair H U Z) :
    (∃ m, c = 3 * m ∧ d = 2 * m ∧ BinaryNaturalSL H U Z 3 m) ∨
      (∃ m, c = 4 * m ∧ d = 2 * m ∧ BinaryNaturalSp4 H U Z m) ∨
      (∃ m, c = 6 * m ∧ d = 2 * m ∧ G2Natural H U Z m) := by
  have hbig := big_of_shape hc hd
  rcases hB with ⟨m, K, _, _, hK, π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩ | ⟨m, K, _, _, hK, π, hπ⟩ |
      ⟨m, K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ |
      ⟨α, π, hπ⟩ | ⟨K, _, _, Γ₀, hK, -, hhat, -, π, hπ⟩ | h4 | h5 | ⟨π, hπ⟩ | ⟨π, hπ⟩
  ·
    exfalso
    have h1 := card_eq_of_faithful (FFModel.nat_faithful _) hπ
    change Nat.card ↥H = Nat.card ↥(Assembly.LowTwoRank.StatedSL 2 K) at h1
    rw [card_statedSL_two K, hK, hH] at h1
    exact sl2_shape_ne (B51.one_le_of_card_eq hK) (by omega) hdc h1.symm
  ·
    have hm := B51.one_le_of_card_eq hK
    have h1 := card_eq_of_faithful (FFModel.nat_faithful _) hπ
    change Nat.card ↥H = Nat.card ↥(Assembly.LowTwoRank.StatedSL 3 K) at h1
    rw [hH, ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
      B51.card_SL3_eq_pow hK] at h1
    obtain ⟨h3, h2⟩ := shape_eq (by omega) (by omega) (by omega) (by omega) h1
    exact Or.inl ⟨m, h3, h2, K, inferInstance, inferInstance, hK, π, hπ⟩
  ·
    have hm := B51.one_le_of_card_eq hK
    have h1 := card_eq_of_faithful (FFModel.nat_faithful _) hπ
    change Nat.card ↥H = Nat.card ↥(Assembly.LowTwoRank.StatedSp 2 K) at h1
    rw [hH, B51.card_Sp4_eq_pow hK, mul_comm (2 ^ (2 * m) - 1)] at h1
    obtain ⟨h3, h2⟩ := shape_eq (by omega) (by omega) (by omega) (by omega) h1
    exact Or.inr (Or.inl ⟨m, h3, h2, K, inferInstance, inferInstance, hK, π, hπ⟩)
  ·
    have hm := B51.one_le_of_card_eq hK
    have := KGNat.charP_two_of_card (by omega) hK
    have h1 := card_eq_of_faithful (FFC.zornQ_faithful _ le_rfl) hπ
    change Nat.card ↥H = Nat.card ↥(quasithinG2 K) at h1
    rw [hH, card_quasithinG2 hK, hK, ← pow_mul, ← pow_mul, mul_comm m 6,
      mul_comm m 2] at h1
    obtain ⟨h3, h2⟩ := shape_eq (by omega) (by omega) (by omega) (by omega) h1
    exact Or.inr (Or.inr ⟨m, h3, h2, K, inferInstance, inferInstance, hK, π, hπ⟩)
  ·
    exfalso
    have hG2 := card_quasithinG2 hK
    have : Finite ↥(quasithinG2 K) := Nat.finite_of_card_ne_zero (by rw [hG2, hK]; norm_num)
    have h2 : Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ ≤ 12096 := by
      refine (Subgroup.card_le_of_le (Subgroup.commutator_le.2 fun a ha b hb => ?_)).trans
        (by rw [hG2, hK]; norm_num)
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have : Finite ↥⁅quasithinG2 K, quasithinG2 K⁆ := inferInstance
    have h1 : Nat.card ↥H ≤ Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
      Nat.card_le_card_of_surjective π hπ.1
    omega
  ·
    have := card_le_of_alt (k := 5) (by norm_num) (by norm_num) hπ.1
    omega
  ·
    have := card_le_of_alt (k := 6) (by norm_num) (by norm_num) hπ.1
    omega
  ·
    have := card_le_of_alt (k := 7) (by norm_num) (by norm_num) hπ.1
    omega
  ·
    have := card_le_of_alt (k := 7) (by norm_num) (by norm_num) hπ.1
    omega
  ·
    have h2 : Nat.card ↥Γ₀ = 1080 := card_of_isHat hhat (by
      rw [card_alt 6 (by norm_num)]
      norm_num [Nat.factorial])
    have h1 : Nat.card ↥H ≤ Nat.card ↥Γ₀ := Nat.card_le_card_of_surjective π hπ.1
    omega
  ·
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h4
    have h1 : Nat.card ↥H ≤ Nat.card ↥(Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
      Nat.card_le_card_of_surjective π hπ.1
    rw [B51.card_statedSL_four] at h1
    omega
  ·
    exfalso
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h5
    have h1 := card_eq_of_faithful (FFModel.nat_faithful _) hπ
    change Nat.card ↥H = Nat.card ↥(Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) at h1
    rw [B51.card_statedSL_five, hH] at h1
    exact sl5_shape_ne (by omega) (by omega) h1.symm
  ·
    have h1 : Nat.card ↥H ≤ Nat.card ↥(Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
      Nat.card_le_card_of_surjective π hπ.1
    rw [B51.card_statedSL_four] at h1
    omega
  ·
    exfalso
    have h1 := card_eq_of_faithful (FFC.extSq_faithful (by norm_num)) hπ
    change Nat.card ↥H = Nat.card ↥(Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) at h1
    rw [B51.card_statedSL_five, hH] at h1
    exact sl5_shape_ne (by omega) (by omega) h1.symm

end Cases

end O8

end CFSG.Quasithin.Vol2.Ch11.SecC
