module

public import CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof2121
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

@[expose] def Item2120Omega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Config2119 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 3 →
      ∀ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 → x * c * x⁻¹ = c →
        ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ L

namespace Item21Late2Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inv_conj_zpow (k y : G) (j : ℤ) : k⁻¹ * y ^ j * k = (k⁻¹ * y * k) ^ j := by
  have h := map_zpow (MulAut.conj k⁻¹) y j
  simp only [MulAut.conj_apply, inv_inv] at h
  exact h

theorem exists_pow_mul_pow_of_mem_sup {c d : G} (hcd : c * d = d * c) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) {x : G} (hx : x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    ∃ i < 3, ∃ j < 3, x = c ^ i * d ^ j := by
  have hc : ∀ y ∈ Subgroup.zpowers c, ∀ z ∈ Subgroup.zpowers d, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_zpow hcd i j).eq
  have hx' : x ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := hx
  rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).2] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  obtain ⟨i, hi, rfl⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hc3 hy
  obtain ⟨j, hj, rfl⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 hz
  exact ⟨i, hi, j, hj, rfl⟩

omit [Finite G] in
theorem mem_zpowers_or_mem_zpowers {c d : G} (hcd : c * d = d * c) (hd3 : d ^ 3 = 1)
    {i j : ℕ} (hi : i < 3) (hj : j < 3) (hi0 : i ≠ 0) (hj0 : j ≠ 0) :
    c ^ i * d ^ j ∈ Subgroup.zpowers (c * d) ∨ c ^ i * d ^ j ∈ Subgroup.zpowers (c * d⁻¹) := by
  have hc : Commute c d := hcd
  have hd2 : d ^ 2 = d⁻¹ := Item21LateProof.sq_eq_inv_of_pow_three hd3
  have hd4 : d⁻¹ ^ 2 = d := by rw [inv_pow, hd2, inv_inv]
  have hi1 : 1 ≤ i := Nat.pos_of_ne_zero hi0
  have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
  interval_cases i <;> interval_cases j
  · left
    rw [pow_one, pow_one]
    exact Subgroup.mem_zpowers _
  · right
    rw [pow_one, hd2]
    exact Subgroup.mem_zpowers _
  · right
    have h1 : (c * d⁻¹) ^ 2 = c ^ 2 * d ^ 1 := by
      rw [(hc.inv_right).mul_pow, hd4, pow_one]
    rw [← h1]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  · left
    rw [← hc.mul_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2

theorem mem_zpowers_of_mem {y x x' : G} (hy3 : y ^ 3 = 1) (hx : x ∈ Subgroup.zpowers y)
    (hx1 : x ≠ 1) (hx' : x' ∈ Subgroup.zpowers y) : x' ∈ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hx1 (by simpa using hx)
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hZ : Subgroup.zpowers x = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hy3 hy1,
        orderOf_eq_prime hx3 hx1])
  rw [hZ]
  exact hx'

theorem exists_conj_mem_zpowers {W : Subgroup G} {c d : G} (hcd : c * d = d * c)
    (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hBW : ∀ g ∈ W, ∀ x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d,
      g * x * g⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    {t : G} (htW : t ∈ W) (htc : t * c * t⁻¹ = c) (htd : t * d * t⁻¹ = d⁻¹)
    {h : G} (hhW : h ∈ W) (hhc : h * c * h⁻¹ ∉ Subgroup.zpowers c)
    {g₀ : G} (hg₀W : g₀ ∈ W) (hg₀d : g₀ * d * g₀⁻¹ ∉ Subgroup.zpowers d) :
    ∃ k ∈ W, k * c * k⁻¹ ∈ Subgroup.zpowers d := by
  by_contra hno
  push Not at hno
  have hcB : c ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hdB : d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hconjpow : ∀ (g x : G) (k : ℕ), g * x ^ k * g⁻¹ = (g * x * g⁻¹) ^ k := fun g x k => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  obtain ⟨i, hi, j, hj, hy⟩ := exists_pow_mul_pow_of_mem_sup hcd hc3 hd3 (hBW h hhW c hcB)
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hhc
    rw [hy, pow_zero, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) i
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hno h hhW
    rw [hy, pow_zero, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j
  obtain ⟨i', hi', j', hj', hy'⟩ := exists_pow_mul_pow_of_mem_sup hcd hc3 hd3 (hBW g₀ hg₀W d hdB)
  have hi'0 : i' ≠ 0 := by
    rintro rfl
    apply hg₀d
    rw [hy', pow_zero, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j'
  have hj'0 : j' ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hy'
    apply hno g₀⁻¹ (W.inv_mem hg₀W)
    have h1 : g₀⁻¹ * c ^ i' * g₀⁻¹⁻¹ = d := by rw [← hy']; group
    rw [hconjpow] at h1
    have hc' : (g₀⁻¹ * c * g₀⁻¹⁻¹) ^ 3 = 1 := by rw [← hconjpow, hc3]; group
    have hd1 : d ≠ 1 := by
      intro hd
      apply hg₀d
      rw [hd]
      simp
    have hmem := mem_zpowers_of_mem hc' (h1 ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i')
      hd1 (Subgroup.mem_zpowers (g₀⁻¹ * c * g₀⁻¹⁻¹))
    exact hmem
  have hY := mem_zpowers_or_mem_zpowers hcd hd3 hi hj hi0 hj0
  have hY' := mem_zpowers_or_mem_zpowers hcd hd3 hi' hj' hi'0 hj'0
  rw [← hy] at hY
  rw [← hy'] at hY'
  have htl : ∀ x, x ∈ Subgroup.zpowers (c * d) → t * x * t⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply,
      show t * (c * d) * t⁻¹ = (t * c * t⁻¹) * (t * d * t⁻¹) by group, htc, htd]
    exact Subgroup.zpow_mem_zpowers _ k
  have htl' : ∀ x, x ∈ Subgroup.zpowers (c * d⁻¹) → t * x * t⁻¹ ∈ Subgroup.zpowers (c * d) := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply,
      show t * (c * d⁻¹) * t⁻¹ = (t * c * t⁻¹) * (t * d * t⁻¹)⁻¹ by group, htc, htd, inv_inv]
    exact Subgroup.zpow_mem_zpowers _ k
  have hy'1 : g₀ * d * g₀⁻¹ ≠ 1 := fun h1 => hg₀d (by rw [h1]; exact one_mem _)
  have hcube : ∀ x : G, x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d → x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, -, j, -, rfl⟩ := exists_pow_mul_pow_of_mem_sup hcd hc3 hd3 hx
    rw [(Commute.pow_pow hcd i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j,
      pow_mul, pow_mul, hc3, hd3, one_pow, one_pow, one_mul]
  have hu1 : (c * d) ^ 3 = 1 := hcube _ (mul_mem hcB hdB)
  have hu2 : (c * d⁻¹) ^ 3 = 1 := hcube _ (mul_mem hcB (inv_mem hdB))
  have hfin : ∀ h' ∈ W, h' * c * h'⁻¹ ∈ Subgroup.zpowers (g₀ * d * g₀⁻¹) → False := by
    intro h' hh'W hmem
    apply hno (g₀⁻¹ * h') (W.mul_mem (W.inv_mem hg₀W) hh'W)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [show g₀⁻¹ * h' * c * (g₀⁻¹ * h')⁻¹ = g₀⁻¹ * (h' * c * h'⁻¹) * g₀⁻¹⁻¹ by group, ← hk,
      ← MulAut.conj_apply, map_zpow, MulAut.conj_apply,
      show g₀⁻¹ * (g₀ * d * g₀⁻¹) * g₀⁻¹⁻¹ = d by group]
    exact Subgroup.zpow_mem_zpowers _ k
  have hth : t * h ∈ W := W.mul_mem htW hhW
  have e1 : (t * h) * c * (t * h)⁻¹ = t * (h * c * h⁻¹) * t⁻¹ := by group
  rcases hY with hY | hY <;> rcases hY' with hY' | hY'
  · exact hfin h hhW (mem_zpowers_of_mem hu1 hY' hy'1 hY)
  · exact hfin (t * h) hth (by rw [e1]; exact mem_zpowers_of_mem hu2 hY' hy'1 (htl _ hY))
  · exact hfin (t * h) hth (by rw [e1]; exact mem_zpowers_of_mem hu1 hY' hy'1 (htl' _ hY))
  · exact hfin h hhW (mem_zpowers_of_mem hu2 hY' hy'1 hY)

end Item21Late2Proof

open Item21Late2Proof

theorem item2120_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hΩ : Item2120Omega) :
    Item2120 := by
  intro G _ _ A E U c L hcfg d hdB hd1 hdT hBW
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcL, d₀, hd₀B, hd₀1, -, hTU, -, hHd, hHW, ⟨w, ⟨hwL, hwN⟩, hw31, hwd, hwA, hwmove⟩, t,
    ⟨htL, htN⟩, htd⟩ := Item21Late2Proof.frame_of h45 h66 hcfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc3 : c ^ 3 = 1 := h3 c hcA
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A c hpairs.2.2.1)
  have hfixc : ∀ {y : G}, y ∈ L → y * c * y⁻¹ = c := fun hy => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hy), mul_inv_cancel_right]
  have hd₀A : d₀ ∈ A := hd₀B.1
  have hd₀L : d₀ ∈ L := hd₀B.2
  have hd₀3 : d₀ ^ 3 = 1 := h3 d₀ hd₀A
  have hdd₀ : d ∈ Subgroup.zpowers d₀ ∧ d₀ ∈ Subgroup.zpowers d := by
    rcases hTU d hdB hd1 hdT with rfl | rfl
    · exact ⟨Subgroup.mem_zpowers _, Subgroup.mem_zpowers _⟩
    · refine ⟨(Subgroup.zpowers d₀).inv_mem (Subgroup.mem_zpowers _), ?_⟩
      have h1 := (Subgroup.zpowers d₀⁻¹).inv_mem (Subgroup.mem_zpowers d₀⁻¹)
      rwa [inv_inv] at h1
  have hZ : Subgroup.zpowers d = Subgroup.zpowers d₀ :=
    le_antisymm (Subgroup.zpowers_le.mpr hdd₀.1) (Subgroup.zpowers_le.mpr hdd₀.2)
  rw [hZ] at hBW ⊢
  suffices hsuff : ∀ g ∈ Subgroup.normalizer (A : Set G), g * d₀ * g⁻¹ ∈ Subgroup.zpowers d₀ by
    intro g hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdd₀.1
    rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact (Subgroup.zpowers d₀).zpow_mem (hsuff g hg) k
  by_contra hno
  push Not at hno
  obtain ⟨g₀, hg₀W, hg₀d⟩ := hno
  have hH : ∀ h ∈ Subgroup.normalizer (A : Set G), h * c * h⁻¹ ∈ Subgroup.zpowers c →
      h * d₀ * h⁻¹ ∈ Subgroup.zpowers d₀ := by
    intro h hhW hhc
    have hhN : h ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      exact (Subgroup.zpowers c).zpow_mem hhc k
    rcases hHd h ⟨hhN, hhW⟩ with h1 | h1
    · rw [h1]
      exact Subgroup.mem_zpowers d₀
    · rw [h1]
      exact (Subgroup.zpowers d₀).inv_mem (Subgroup.mem_zpowers d₀)
  obtain ⟨h, hhW, hhc⟩ : ∃ h ∈ Subgroup.normalizer (A : Set G),
      h * c * h⁻¹ ∉ Subgroup.zpowers c := by
    by_contra hno'
    push Not at hno'
    exact hg₀d (hH g₀ hg₀W (hno' g₀ hg₀W))
  obtain ⟨k, hkW, hkc⟩ := exists_conj_mem_zpowers (hcomm c hcA d₀ hd₀A) hc3 hd₀3 hBW htN
    (hfixc htL) htd hhW hhc hg₀W hg₀d
  have hkc1 : k * c * k⁻¹ ≠ 1 := by
    intro h1
    apply hpairs.2.1
    calc c = k⁻¹ * (k * c * k⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  have hkd : k⁻¹ * d₀ * k ∈ Subgroup.zpowers c := by
    have h1 := mem_zpowers_of_mem hd₀3 hkc hkc1 (Subgroup.mem_zpowers d₀)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← hj, inv_conj_zpow, show k⁻¹ * (k * c * k⁻¹) * k = c by group]
    exact Subgroup.zpow_mem_zpowers c j
  set x := k⁻¹ * w * k with hx
  have hxW : x ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkW) hwN) hkW
  have hx3 : x ^ 3 = 1 := by
    have h1 := conj_pow (a := k⁻¹) (b := w) (i := 3)
    rw [inv_inv] at h1
    rw [hx, h1, hw31]
    group
  have hxc : x * c * x⁻¹ = c := by
    have hwfix : w * (k * c * k⁻¹) * w⁻¹ = k * c * k⁻¹ :=
      Item21LateProof.conj_eq_of_mem_zpowers hwd hkc
    calc x * c * x⁻¹ = k⁻¹ * (w * (k * c * k⁻¹) * w⁻¹) * k := by rw [hx]; group
      _ = c := by rw [hwfix]; group
  have hxA : ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ Subgroup.zpowers c := by
    intro a ha
    have ha' : k * a * k⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hkW a).mp ha
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hwA _ ha')
    have e : a⁻¹ * (x * a * x⁻¹) =
        k⁻¹ * ((k * a * k⁻¹)⁻¹ * (w * (k * a * k⁻¹) * w⁻¹)) * k := by rw [hx]; group
    rw [e, ← hj, inv_conj_zpow]
    exact (Subgroup.zpowers c).zpow_mem hkd j
  have hxmove : ∃ a ∈ A, x * a * x⁻¹ ≠ a := by
    obtain ⟨a, ha, hne⟩ := hwmove
    refine ⟨k⁻¹ * a * k, ?_, fun h' => hne ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkW) a).mp ha
      simpa using h1
    · calc w * a * w⁻¹ = k * (x * (k⁻¹ * a * k) * x⁻¹) * k⁻¹ := by rw [hx]; group
        _ = a := by rw [h']; group
  have hxH : x ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [Item21LateProof.conj_eq_of_mem_zpowers hxc hz]
    exact hz
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := hHW ⟨hxH, hxW⟩
  have hxAL : ∀ a ∈ A ⊓ L, x * a * x⁻¹ = a := by
    intro a ha
    have h1 : a⁻¹ * (x * a * x⁻¹) ∈ L :=
      L.mul_mem (L.inv_mem ha.2) ((Subgroup.mem_normalizer_iff.mp hxL a).mp ha.2)
    have h2 := Item21Late2Proof.eq_one_of_pow_mem hc3 hcL (hxA a ha.1) h1
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  have hAL3 : Nat.card (A ⊓ L : Subgroup G) = 3 := by
    have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases m
    · exfalso
      have hbot := Subgroup.eq_bot_of_card_eq (A ⊓ L) (by rw [hm, pow_zero])
      have h1 := hd₀B
      rw [hbot, Subgroup.mem_bot] at h1
      exact hd₀1 h1
    · rw [hm, pow_one]
    · exfalso
      obtain ⟨a, ha, hne⟩ := hxmove
      exact hne (Item21Late2Proof.conj_eq_of_fix hcomm h3 inf_le_left
        (by rw [hA27, hm]; norm_num) hcA (fun h' => hcL h'.2) hxAL hxc a ha)
    · exfalso
      have heq : A ⊓ L = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hm, hA27]; norm_num)
      have h1 : c ∈ A ⊓ L := by rw [heq]; exact hcA
      exact hcL h1.2
  obtain ⟨a, ha, hne⟩ := hxmove
  apply hne
  have h1 := hΩ G A E U c L hcfg hAL3 x hxW hx3 hxc a ha
  have h2 := Item21Late2Proof.eq_one_of_pow_mem hc3 hcL (hxA a ha) h1
  rw [inv_mul_eq_one] at h2
  exact h2.symm

end CFSG.RankThree.PartTwo.Sec21
