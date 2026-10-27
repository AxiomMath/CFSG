module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

variable {G : Type*} [Group G]

@[expose] def layer (U : Subgroup G) (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (j : ℕ) :
    Subgroup G where
  carrier := {u | u ∈ U ∧ u ^ 2 ^ j = 1}
  mul_mem' {a b} ha hb := by
    refine ⟨U.mul_mem ha.1 hb.1, ?_⟩
    rw [(Commute.mul_pow (hU a ha.1 b hb.1) (2 ^ j)), ha.2, hb.2, one_mul]
  one_mem' := ⟨U.one_mem, one_pow _⟩
  inv_mem' {a} ha := ⟨U.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem mem_layer {U : Subgroup G} {hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a} {j : ℕ} {u : G} :
    u ∈ layer U hU j ↔ u ∈ U ∧ u ^ 2 ^ j = 1 :=
  Iff.rfl

theorem layer_le (U : Subgroup G) (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (j : ℕ) :
    layer U hU j ≤ U :=
  fun _ hu => hu.1

theorem layer_mono (U : Subgroup G) (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {i j : ℕ}
    (hij : i ≤ j) : layer U hU i ≤ layer U hU j := by
  intro u hu
  refine ⟨hu.1, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [pow_add, pow_mul, hu.2, one_pow]

theorem layer_zero (U : Subgroup G) (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) :
    layer U hU 0 = ⊥ := by
  ext u
  rw [mem_layer, Subgroup.mem_bot, pow_zero, pow_one]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ U.one_mem, h⟩⟩

variable [Finite G]

theorem card_layer_le (U : Subgroup G) (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (j : ℕ) :
    Nat.card (layer U hU j) ≤ Nat.card (layer U hU 1) ^ j := by
  induction j with
  | zero => rw [layer_zero, Subgroup.card_bot, pow_zero]
  | succ j ih =>
    let sq : layer U hU (j + 1) →* layer U hU j :=
      { toFun := fun u => ⟨(u : G) ^ 2, U.pow_mem u.2.1 2, by
          rw [← pow_mul, ← pow_succ', u.2.2]⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          simp only [Subgroup.coe_mul]
          exact (Commute.mul_pow (hU a a.2.1 b b.2.1) 2)) }
    have hker : Nat.card sq.ker ≤ Nat.card (layer U hU 1) := by
      refine Nat.card_le_card_of_injective
        (fun x => (⟨((x : layer U hU (j + 1)) : G), ⟨(x : layer U hU (j + 1)).2.1, ?_⟩⟩ :
          layer U hU 1)) ?_
      · have hx : sq (x : layer U hU (j + 1)) = 1 := x.2
        have hx' := congrArg Subtype.val hx
        simpa [sq] using hx'
      · intro x y hxy
        have h := congrArg (fun z : layer U hU 1 => (z : G)) hxy
        exact Subtype.ext (Subtype.ext h)
    have hrange : Nat.card sq.range ≤ Nat.card (layer U hU j) := Subgroup.card_le_card_group _
    have h := Subgroup.card_ker_mul_card_range sq
    rw [← h, pow_succ, mul_comm (Nat.card (layer U hU 1) ^ j)]
    exact Nat.mul_le_mul hker (hrange.trans ih)

theorem eq_pow_of_mem_zpowers_of_sq {w z : G} {j : ℕ} (hw : orderOf w = 2 ^ (j + 1))
    (hz : z ∈ Subgroup.zpowers w) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : z = w ^ 2 ^ j := by
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hz
  obtain ⟨k, rfl⟩ := hz
  have hdvd : 2 ^ (j + 1) ∣ k * 2 := by
    rw [← hw]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hz2)
  have hk : 2 ^ j ∣ k := by
    rw [pow_succ] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hdvd
  obtain ⟨m, rfl⟩ := hk
  have ht2 : (w ^ 2 ^ j) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, ← hw, pow_orderOf_eq_one]
  rw [pow_mul] at hz1 ⊢
  rcases Nat.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exfalso
    apply hz1
    rw [← two_mul, pow_mul, ht2, one_pow]
  · rw [pow_succ, pow_mul, ht2, one_pow, one_mul]

theorem eq_layer_of_invariant (U : Subgroup G) (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU2 : IsPGroup 2 U) {c : G} (hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U)
    (hfix : ∀ u ∈ U, c * u * c⁻¹ = u → u = 1) (hΩ : Nat.card (layer U hU 1) ≤ 4)
    {W : Subgroup G} (hWU : W ≤ U) (hWc : ∀ w ∈ W, c * w * c⁻¹ ∈ W) :
    ∃ j : ℕ, W = layer U hU j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hwW, hwmax⟩ : ∃ w ∈ W, ∀ w' ∈ W, orderOf w' ≤ orderOf w := by
    have := Fintype.ofFinite W
    obtain ⟨⟨w, hw⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset W)
      (fun x : W => orderOf (x : G)) Finset.univ_nonempty
    exact ⟨w, hw, fun w' hw' => hmax ⟨w', hw'⟩ (Finset.mem_univ _)⟩
  have hW2 : IsPGroup 2 W := hU2.to_le hWU
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hW2) ⟨w, hwW⟩
  rw [Subgroup.orderOf_mk] at hj
  have hWle : W ≤ layer U hU j := by
    intro w' hw'
    refine ⟨hWU hw', ?_⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hW2) ⟨w', hw'⟩
    rw [Subgroup.orderOf_mk] at hk
    have hle : 2 ^ k ≤ 2 ^ j := by rw [← hk, ← hj]; exact hwmax w' hw'
    have hkj : k ≤ j := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    exact pow_dvd_pow 2 hkj
  refine ⟨j, le_antisymm hWle ?_⟩
  set v := c * w * c⁻¹ with hv
  have hvW : v ∈ W := hWc w hwW
  have hvo : orderOf v = 2 ^ j := by
    rw [hv, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hj]
  have hcomm : ∀ x ∈ Subgroup.zpowers w, ∀ y ∈ Subgroup.zpowers v, x * y = y * x := by
    intro x hx y hy
    exact hU x (Subgroup.zpowers_le.mpr (hWU hwW) hx) y (Subgroup.zpowers_le.mpr (hWU hvW) hy)
  have hinf : Subgroup.zpowers w ⊓ Subgroup.zpowers v = ⊥ := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      rw [hj, Subgroup.zpowers_one_eq_bot, bot_inf_eq]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    by_contra hne
    have hI2 : IsPGroup 2 ↥(Subgroup.zpowers w ⊓ Subgroup.zpowers v) :=
      hU2.to_le (inf_le_left.trans (Subgroup.zpowers_le.mpr (hWU hwW)))
    obtain ⟨n, hn⟩ := hI2.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hn, pow_zero]))
    obtain ⟨⟨z, hz⟩, hzo⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers w ⊓
      Subgroup.zpowers v)) 2 (by rw [hn]; exact dvd_pow_self 2 hn0)
    rw [Subgroup.orderOf_mk] at hzo
    have hz2 : z ^ 2 = 1 := by rw [← hzo, pow_orderOf_eq_one]
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hzo
      omega
    have h1 := eq_pow_of_mem_zpowers_of_sq hj (Subgroup.mem_inf.mp hz).1 hz2 hz1
    have h2 := eq_pow_of_mem_zpowers_of_sq hvo (Subgroup.mem_inf.mp hz).2 hz2 hz1
    rw [hv, conj_pow] at h2
    apply hz1
    refine hfix z ((Subgroup.zpowers_le.mpr (hWU hwW)) (Subgroup.mem_inf.mp hz).1) ?_
    calc c * z * c⁻¹ = c * w ^ 2 ^ i * c⁻¹ := by rw [h1]
      _ = z := h2.symm
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hj, hvo] at hcard
  have hsupW : Subgroup.zpowers w ⊔ Subgroup.zpowers v ≤ W :=
    sup_le (Subgroup.zpowers_le.mpr hwW) (Subgroup.zpowers_le.mpr hvW)
  have hW4 : 4 ^ j ≤ Nat.card W := by
    have := Subgroup.card_le_of_le hsupW
    rw [hcard, ← mul_pow] at this
    exact this
  have hL4 : Nat.card (layer U hU j) ≤ 4 ^ j :=
    (card_layer_le U hU j).trans (Nat.pow_le_pow_left hΩ j)
  have heq : W = layer U hU j := Subgroup.eq_of_le_of_card_ge hWle (hL4.trans hW4)
  rw [heq]

theorem layer_one_le_of_invariant (U : Subgroup G) (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU2 : IsPGroup 2 U) {c : G} (hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U)
    (hfix : ∀ u ∈ U, c * u * c⁻¹ = u → u = 1) (hΩ : Nat.card (layer U hU 1) ≤ 4)
    {W : Subgroup G} (hWU : W ≤ U) (hWc : ∀ w ∈ W, c * w * c⁻¹ ∈ W) (hW1 : W ≠ ⊥) :
    layer U hU 1 ≤ W := by
  obtain ⟨j, rfl⟩ := eq_layer_of_invariant U hU hU2 hcU hfix hΩ hWU hWc
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact absurd (layer_zero U hU) hW1
  · exact layer_mono U hU hj

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
