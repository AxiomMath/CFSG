module

public import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {D : Set G}

@[expose] def IsTriangle (D : Set G) (u w v : G) : Prop :=
  u ∈ D ∧ v ∈ D ∧ w ∈ D ∧ u ≠ v ∧ Commute u v ∧ ¬ Commute u w ∧ ¬ Commute v w

@[expose] def IsThirdKind (u w v : G) : Prop :=
  ∃ n : ℕ, Odd n ∧ 1 < n ∧ orderOf (u * v * w) = 2 * n

theorem zpow_mul_conj_eq {x w : G} (hx : x * x = 1) (hw : w * w = 1) (j : ℤ) :
    (x * w) ^ j * w * ((x * w) ^ j)⁻¹ = (x * w) ^ (2 * j) * w := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hwy : w * (x * w) * w⁻¹ = (x * w)⁻¹ := by
    calc w * (x * w) * w⁻¹ = w * x := by group
      _ = (x * w)⁻¹ := by rw [mul_inv_rev, hwi, hxi]
  have hj : w * (x * w) ^ (-j) * w⁻¹ = (x * w) ^ j := by
    rw [← conj_zpow, hwy, inv_zpow', neg_neg]
  calc (x * w) ^ j * w * ((x * w) ^ j)⁻¹
        = (x * w) ^ j * (w * (x * w) ^ (-j) * w⁻¹) * w := by group
    _ = (x * w) ^ (2 * j) * w := by rw [hj, ← zpow_add, two_mul]

theorem dihedral_center {x w : G} (hx : x * x = 1) (hw : w * w = 1) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * w) = 2 * n) :
    (x * w) ^ n * (x * w) ^ n = 1 ∧ (x * w) ^ n ≠ 1 ∧ Commute ((x * w) ^ n) x ∧
      Commute ((x * w) ^ n) w ∧ ∃ g : G, x * (x * w) ^ n = g * w * g⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hwy : w * (x * w) * w⁻¹ = (x * w)⁻¹ := by
    calc w * (x * w) * w⁻¹ = w * x := by group
      _ = (x * w)⁻¹ := by rw [mul_inv_rev, hwi, hxi]
  have hxy : x * (x * w) * x⁻¹ = (x * w)⁻¹ := by
    calc x * (x * w) * x⁻¹ = x * x * w * x⁻¹ := by group
      _ = w * x := by rw [hx, one_mul, hxi]
      _ = (x * w)⁻¹ := by rw [mul_inv_rev, hwi, hxi]
  have hpos : 0 < n := hn.pos
  have hzz : (x * w) ^ n * (x * w) ^ n = 1 := by
    rw [← pow_add, ← two_mul, ← hord, pow_orderOf_eq_one]
  have hzi : ((x * w) ^ n)⁻¹ = (x * w) ^ n := inv_eq_of_mul_eq_one_right hzz
  refine ⟨hzz, pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; omega), ?_, ?_, ?_⟩
  · have e : x * (x * w) ^ n * x⁻¹ = (x * w) ^ n := by rw [← conj_pow, hxy, inv_pow, hzi]
    show (x * w) ^ n * x = x * (x * w) ^ n
    calc (x * w) ^ n * x = x * (x * w) ^ n * x⁻¹ * x := by rw [e]
      _ = x * (x * w) ^ n := by group
  · have e : w * (x * w) ^ n * w⁻¹ = (x * w) ^ n := by rw [← conj_pow, hwy, inv_pow, hzi]
    show (x * w) ^ n * w = w * (x * w) ^ n
    calc (x * w) ^ n * w = w * (x * w) ^ n * w⁻¹ * w := by rw [e]
      _ = w * (x * w) ^ n := by group
  · obtain ⟨k, rfl⟩ := hn
    refine ⟨(x * w) ^ (-(k : ℤ)), ?_⟩
    rw [zpow_mul_conj_eq hx hw]
    have e : w * (x * w) ^ (2 * k + 1) * w⁻¹ = ((x * w) ^ (2 * k + 1))⁻¹ := by
      rw [← conj_pow, hwy, inv_pow]
    have hwyn : w * (x * w) ^ (2 * k + 1) = ((x * w) ^ (2 * k + 1))⁻¹ * w := by
      calc w * (x * w) ^ (2 * k + 1) = w * (x * w) ^ (2 * k + 1) * w⁻¹ * w := by group
        _ = ((x * w) ^ (2 * k + 1))⁻¹ * w := by rw [e]
    calc x * (x * w) ^ (2 * k + 1) = (x * w) * (w * (x * w) ^ (2 * k + 1)) := by
          rw [← mul_assoc, mul_assoc x w w, hw, mul_one]
      _ = (x * w) * ((x * w) ^ (2 * k + 1))⁻¹ * w := by rw [hwyn]; simp only [mul_assoc]
      _ = (x * w) ^ (2 * -(k : ℤ)) * w := by group

namespace IsTriangle

variable {u v w : G}

theorem uv_mul_self (hD : IsOddTransp D) (h : IsTriangle D u w v) : u * v * (u * v) = 1 := by
  calc u * v * (u * v) = u * (v * u) * v := by group
    _ = u * (u * v) * v := by rw [h.2.2.2.2.1.eq]
    _ = 1 := by
      rw [← mul_assoc, hD.mul_self_eq_one h.1, one_mul, hD.mul_self_eq_one h.2.1]

theorem not_commute_mul (hD : IsOddTransp D) (h : IsTriangle D u w v) :
    ¬ Commute w (u * v) := fun hc =>
  h.2.2.2.2.2.1 ((hD.commute_mul_iff h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1).mp hc).1.symm

theorem orderOf_cases [Finite G] (hD : IsOddTransp D) (hN : IsNormalSet D)
    (h : IsTriangle D u w v) :
    (Odd (orderOf (u * v * w)) ∧ 1 < orderOf (u * v * w)) ∨ orderOf (u * v * w) = 4 ∨
      IsThirdKind u w v := by
  set x := u * v with hxdef
  have hx : x * x = 1 := h.uv_mul_self hD
  have hw : w * w = 1 := hD.mul_self_eq_one h.2.2.1
  have hxw : x ≠ w := fun he => h.not_commute_mul hD (he ▸ Commute.refl _)
  have hpos : 0 < orderOf (x * w) := orderOf_pos _
  have hne1 : orderOf (x * w) ≠ 1 := by
    intro h1
    rw [orderOf_eq_one_iff] at h1
    apply hxw
    rw [← inv_eq_of_mul_eq_one_right hw]
    exact eq_inv_of_mul_eq_one_left h1
  rcases Nat.even_or_odd (orderOf (x * w)) with ⟨k, hk⟩ | hodd
  ·
    set a := x * w * x⁻¹ with ha
    have haD : a ∈ D := hN x w h.2.2.1
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have haw : a * w = (x * w) ^ 2 := by rw [ha, hxi, pow_two]; group
    have hak : orderOf (a * w) = k := by
      rw [haw, orderOf_pow' _ (by norm_num), hk, show k + k = 2 * k by ring,
        Nat.gcd_mul_right_left]
      · omega
    have haw1 : a ≠ w := by
      intro hea
      apply h.not_commute_mul hD
      have h1 : x * w * x⁻¹ = w := ha ▸ hea
      show w * x = x * w
      calc w * x = x * w * x⁻¹ * x := by rw [h1]
        _ = x * w := by group
    have hk1 : k ≠ 1 ∨ k = 1 := by omega
    rcases hD.2 a haD w h.2.2.1 with h2 | h2
    · rw [hak] at h2
      have hk0 : k ≠ 0 := by omega
      have hk' : k = 1 ∨ k = 2 := by
        have := Nat.le_of_dvd (by norm_num) h2
        omega
      rcases hk' with rfl | rfl
      · exact absurd (by rw [orderOf_eq_one_iff] at hak; exact hD.eq_of_mul_eq_one haD hak) haw1
      · right; left; rw [hk]
    · rw [hak] at h2
      have hk1' : k ≠ 1 := by
        rintro rfl
        rw [orderOf_eq_one_iff] at hak
        exact haw1 (hD.eq_of_mul_eq_one haD hak)
      right; right
      exact ⟨k, h2, by have := h2.pos; omega, by rw [hk]; ring⟩
  · left
    exact ⟨hodd, by omega⟩

theorem third_kind (hD : IsOddTransp D) (hN : IsNormalSet D) (h : IsTriangle D u w v) {n : ℕ}
    (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) :
    (u * v * w) ^ n * (u * v * w) ^ n = 1 ∧ (u * v * w) ^ n ≠ 1 ∧
      Commute ((u * v * w) ^ n) u ∧ Commute ((u * v * w) ^ n) v ∧
      Commute ((u * v * w) ^ n) w ∧ u * v * (u * v * w) ^ n ∈ D := by
  have hx : u * v * (u * v) = 1 := h.uv_mul_self hD
  obtain ⟨hzz, hz1, hzx, hzw, g, hg⟩ :=
    dihedral_center hx (hD.mul_self_eq_one h.2.2.1) hn hord
  have hxz : u * v * (u * v * w) ^ n ∈ D := by
    rw [hg]
    exact hN g w h.2.2.1
  have hxzx : Commute (u * v * (u * v * w) ^ n) (u * v) := (Commute.refl _).mul_left hzx
  have hcu := (hD.commute_mul_iff h.1 h.2.1 hxz h.2.2.2.1 h.2.2.2.2.1).mp hxzx
  have hzeq : (u * v * w) ^ n = u * v * (u * v * (u * v * w) ^ n) := by
    rw [← mul_assoc, hx, one_mul]
  have hux : Commute u (u * v) := (Commute.refl u).mul_right h.2.2.2.2.1
  have hvx : Commute v (u * v) := h.2.2.2.2.1.symm.mul_right (Commute.refl v)
  refine ⟨hzz, hz1, ?_, ?_, hzw, hxz⟩
  · rw [hzeq]
    exact hux.symm.mul_left hcu.1
  · rw [hzeq]
    exact hvx.symm.mul_left hcu.2

theorem mul_mem_of_odd (hD : IsOddTransp D) (hN : IsNormalSet D) (h : IsTriangle D u w v)
    (hodd : Odd (orderOf (u * v * w))) : u * v ∈ D := by
  obtain ⟨g, -, hg⟩ := exists_conj_of_odd_orderOf_mul (h.uv_mul_self hD)
    (hD.mul_self_eq_one h.2.2.1) hodd
  have := hN g⁻¹ w h.2.2.1
  rw [← hg] at this
  simpa [mul_assoc] using this

end IsTriangle

theorem IsTriangle.commute_iff_of_odd [Finite G] (hS : Setup G D) {u v w : G}
    (h : IsTriangle D u w v) (hodd : Odd (orderOf (u * v * w))) :
    u * v ∈ D ∧ ∀ x ∈ D, (Commute x u ↔ Commute x (u * v)) := by
  classical
  have huv := h.mul_mem_of_odd hS.oddT hS.normal hodd
  refine ⟨huv, ?_⟩
  set A := {x | x ∈ D ∧ Commute x u}
  set B := {x | x ∈ D ∧ Commute x (u * v)}
  have hBA : B ⊆ A := fun x hx =>
    ⟨hx.1, ((hS.oddT.commute_mul_iff h.1 h.2.1 hx.1 h.2.2.2.1 h.2.2.2.2.1).mp hx.2).1⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (hS.isConj h.1 huv)
  have hcard : A.ncard = B.ncard := by
    have himage : (fun x => c * x * c⁻¹) '' A = B := by
      ext y
      constructor
      · rintro ⟨x, ⟨hxD, hxu⟩, rfl⟩
        exact ⟨hS.conj_mem c hxD, hc ▸ (Commute.conj_iff c).mpr hxu⟩
      · rintro ⟨hyD, hyc⟩
        refine ⟨c⁻¹ * y * c⁻¹⁻¹, ⟨hS.conj_mem c⁻¹ hyD, ?_⟩, by group⟩
        have := (Commute.conj_iff c⁻¹).mpr hyc
        rw [← hc] at this
        simpa [mul_assoc] using this
    rw [← himage, Set.ncard_image_of_injective _ (fun a b hab => by simpa using hab)]
  have hAB : A = B := (Set.eq_of_subset_of_ncard_le hBA (by rw [hcard]) (Set.toFinite _)).symm
  intro x hx
  constructor
  · intro hxu
    have : x ∈ B := hAB ▸ ⟨hx, hxu⟩
    exact this.2
  · intro hxuv
    exact (hBA ⟨hx, hxuv⟩).2

theorem commute_of_mem_odd_normal [Finite G] (hD : IsOddTransp D) (hN : IsNormalSet D)
    {N : Subgroup G} [N.Normal] (hodd : Odd (Nat.card N)) {u v : G} (hu : u ∈ D) (hv : v ∈ D)
    (huv : u ≠ v) (hc : Commute u v) {n : G} (hn : n ∈ N) (hnc : Commute n (u * v)) :
    Commute n u := by
  by_contra hnu
  have hu2 := hD.mul_self_eq_one hu
  have hui : u⁻¹ = u := hD.inv_eq hu
  set x := n⁻¹ * (u * n * u) with hxdef
  have hunu : u * n * u ∈ N := by
    have := ‹N.Normal›.conj_mem n hn u
    rwa [hui] at this
  have hxN : x ∈ N := N.mul_mem (N.inv_mem hn) hunu
  have hx1 : x ≠ 1 := by
    intro h1
    apply hnu
    have : u * n * u = n := by
      rw [hxdef, inv_mul_eq_one] at h1
      exact h1.symm
    show n * u = u * n
    calc n * u = u * n * u * u := by rw [this]
      _ = u * n := by rw [mul_assoc, hu2, mul_one]
  have huuv : Commute u (u * v) := (Commute.refl u).mul_right hc
  have hxc : Commute x (u * v) := by
    have h1 : Commute (u * n * u) (u * v) := (huuv.mul_left hnc).mul_left huuv
    exact hnc.inv_left.mul_left h1
  have hux : u * x * u = x⁻¹ := by
    rw [hxdef]
    calc u * (n⁻¹ * (u * n * u)) * u = u * n⁻¹ * u * n * (u * u) := by group
      _ = u * n⁻¹ * u * n := by rw [hu2, mul_one]
      _ = (n⁻¹ * (u * n * u))⁻¹ := by simp only [mul_inv_rev, inv_inv, hui]; group
  have hxodd : Odd (orderOf x) := by
    have hdvd : orderOf x ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hodd hdvd
  obtain ⟨m, hm⟩ := hxodd
  set y := x ^ (m + 1) with hydef
  have hyy : y * y = x := by
    rw [hydef, ← pow_add, show m + 1 + (m + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have huy : u * y * u = y⁻¹ := by
    rw [hydef]
    have : u * x ^ (m + 1) * u⁻¹ = (u * x * u⁻¹) ^ (m + 1) := (conj_pow).symm
    rw [hui] at this
    rw [this, hux, inv_pow]
  have huxD : u * x ∈ D := by
    have := hN y⁻¹ u hu
    have e : y⁻¹ * u * y⁻¹⁻¹ = u * x := by
      rw [inv_inv, ← hyy]
      calc y⁻¹ * u * y = u * (u * y⁻¹ * u) * y := by rw [← mul_assoc, ← mul_assoc, hu2, one_mul]
        _ = u * (u * y * u)⁻¹ * y := by rw [mul_inv_rev, mul_inv_rev, hui]; group
        _ = u * (y * y) := by rw [huy, inv_inv, mul_assoc]
    rwa [e] at this
  have hord2 : orderOf (u * v) = 2 := hD.orderOf_mul_eq_two hu hv huv hc
  have hcop : Nat.Coprime (orderOf (u * v)) (orderOf x) := by
    rw [hord2, Nat.coprime_two_left]
    exact ⟨m, hm⟩
  have hprod : v * (u * x) = u * v * x := by
    rw [← mul_assoc, ← hc.eq]
  have hordp : orderOf (v * (u * x)) = 2 * orderOf x := by
    rw [hprod, hxc.symm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hord2]
  have hx1' : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  rcases hD.2 v hv (u * x) huxD with h2 | h2
  · rw [hordp] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    have := orderOf_pos x
    omega
  · rw [hordp] at h2
    exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) h2

end CFSG.Timmesfeld.Bridge.Asc72
