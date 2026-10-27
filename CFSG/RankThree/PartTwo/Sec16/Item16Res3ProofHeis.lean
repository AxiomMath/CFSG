module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveHeisNF
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res3U35

open scoped commutatorElement

section Heis

variable {G : Type*} [Group G] {x y : G}

theorem conj_y_x_pow (hzx : Commute ⁅y, x⁆ x) (i : ℕ) :
    y * x ^ i * y⁻¹ = ⁅y, x⁆ ^ i * x ^ i := by
  have h1 : y * x * y⁻¹ = ⁅y, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [← conj_pow, h1, hzx.mul_pow]

theorem conj_x_y_pow (hzy : Commute ⁅y, x⁆ y) (j : ℕ) :
    x * y ^ j * x⁻¹ = (⁅y, x⁆ ^ j)⁻¹ * y ^ j := by
  have h1 : x * y * x⁻¹ = ⁅y, x⁆⁻¹ * y := by
    rw [commutatorElement_def]
    group
  rw [← conj_pow, h1, hzy.inv_left.mul_pow, inv_pow]

theorem fin_eq_of_pow_eq {z : G} (hz : orderOf z = 5) {a b : Fin 5}
    (h : z ^ (a : ℕ) = z ^ (b : ℕ)) : a = b := by
  rw [pow_inj_mod, hz, Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at h
  exact Fin.ext h

theorem card_closure_heis (hx5 : x ^ 5 = 1) (hy5 : y ^ 5 = 1) (hzx : Commute ⁅y, x⁆ x)
    (hzy : Commute ⁅y, x⁆ y) (hz1 : ⁅y, x⁆ ≠ 1) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 125 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set z := ⁅y, x⁆ with hz
  have hz5 : z ^ 5 = 1 := CGT.PushingUpLit.CGT6M.commutator_pow_eq_one_of_commute hzx hx5
  have hoz : orderOf z = 5 := orderOf_eq_prime hz5 hz1
  set R := Subgroup.closure ({x, y} : Set G) with hR
  have hxR : x ∈ R := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyR : y ∈ R := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hzR : z ∈ R := by
    rw [hz, commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hyR hxR) (R.inv_mem hyR)) (R.inv_mem hxR)
  let f : Fin 5 × Fin 5 × Fin 5 → R := fun q =>
    ⟨x ^ (q.1 : ℕ) * y ^ (q.2.1 : ℕ) * z ^ (q.2.2 : ℕ),
      R.mul_mem (R.mul_mem (R.pow_mem hxR _) (R.pow_mem hyR _)) (R.pow_mem hzR _)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨u, hu⟩
    obtain ⟨i, j, k, rfl⟩ := CGT.PushingUpLit.CGT6M.heis_normal_form hx5 hy5 hzx hzy u hu
    refine ⟨(⟨i % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩,
      ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩), Subtype.ext ?_⟩
    change x ^ (i % 5) * y ^ (j % 5) * z ^ (k % 5) = x ^ i * y ^ j * z ^ k
    rw [← pow_eq_pow_mod i hx5, ← pow_eq_pow_mod j hy5, ← pow_eq_pow_mod k hz5]
  have hinj : Function.Injective f := by
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    have h' : x ^ (i : ℕ) * y ^ (j : ℕ) * z ^ (k : ℕ) =
        x ^ (i' : ℕ) * y ^ (j' : ℕ) * z ^ (k' : ℕ) := congrArg Subtype.val h
    have hconj : ∀ a b c : ℕ,
        y * (x ^ a * y ^ b * z ^ c) * y⁻¹ = z ^ a * (x ^ a * y ^ b * z ^ c) := by
      intro a b c
      have hyz : y * z ^ c * y⁻¹ = z ^ c := by
        rw [((hzy.pow_left c).eq).symm]
        group
      calc y * (x ^ a * y ^ b * z ^ c) * y⁻¹ =
          (y * x ^ a * y⁻¹) * y ^ b * (y * z ^ c * y⁻¹) := by group
        _ = z ^ a * x ^ a * y ^ b * z ^ c := by rw [conj_y_x_pow hzx, hyz]
        _ = z ^ a * (x ^ a * y ^ b * z ^ c) := by group
    have hi : i = i' := by
      have e1 := hconj i j k
      have e2 := hconj i' j' k'
      rw [h'] at e1
      have e3 : z ^ (i : ℕ) * (x ^ (i' : ℕ) * y ^ (j' : ℕ) * z ^ (k' : ℕ)) =
          z ^ (i' : ℕ) * (x ^ (i' : ℕ) * y ^ (j' : ℕ) * z ^ (k' : ℕ)) := e1.symm.trans e2
      exact fin_eq_of_pow_eq hoz (mul_right_cancel e3)
    subst hi
    have h2 : y ^ (j : ℕ) * z ^ (k : ℕ) = y ^ (j' : ℕ) * z ^ (k' : ℕ) := by
      have : x ^ (i : ℕ) * (y ^ (j : ℕ) * z ^ (k : ℕ)) =
          x ^ (i : ℕ) * (y ^ (j' : ℕ) * z ^ (k' : ℕ)) := by
        rw [← mul_assoc, ← mul_assoc]
        exact h'
      exact mul_left_cancel this
    have hconj' : ∀ b c : ℕ, x * (y ^ b * z ^ c) * x⁻¹ = (z ^ b)⁻¹ * (y ^ b * z ^ c) := by
      intro b c
      have hxz : x * z ^ c * x⁻¹ = z ^ c := by
        rw [((hzx.pow_left c).eq).symm]
        group
      calc x * (y ^ b * z ^ c) * x⁻¹ = (x * y ^ b * x⁻¹) * (x * z ^ c * x⁻¹) := by group
        _ = (z ^ b)⁻¹ * y ^ b * z ^ c := by rw [conj_x_y_pow hzy, hxz]
        _ = (z ^ b)⁻¹ * (y ^ b * z ^ c) := by group
    have hj : j = j' := by
      have e1 := hconj' j k
      have e2 := hconj' j' k'
      rw [h2] at e1
      have e3 := mul_right_cancel (e1.symm.trans e2)
      exact fin_eq_of_pow_eq hoz (inv_injective e3)
    subst hj
    have hk : k = k' := fin_eq_of_pow_eq hoz (mul_left_cancel h2)
    subst hk
    rfl
  rw [← Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩]
  simp

end Heis

section Index

variable {U : Type*} [Group U] [Finite U]

theorem exists_inv_mul_mem_of_relIndex_le {H R N : Subgroup U} (hRN : R ≤ N)
    (h : H.relIndex N ≤ H.relIndex R) {n : U} (hn : n ∈ N) : ∃ r ∈ R, r⁻¹ * n ∈ H := by
  set f := Subgroup.quotientSubgroupOfEmbeddingOfLE H hRN with hf
  have hsurj : Function.Surjective f := (f.injective.bijective_of_nat_card_le h).2
  obtain ⟨q, hq⟩ := hsurj (QuotientGroup.mk ⟨n, hn⟩)
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
  rw [hf, Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hq
  refine ⟨r, r.2, ?_⟩
  simpa using hq

omit [Finite U] in
theorem exists_mul_pow_eq {R : Subgroup U} {r t : U} (hr : r ∈ R)
    (ht : t ∈ Subgroup.normalizer (R : Set U)) (n : ℕ) : ∃ r' ∈ R, (r * t) ^ n = r' * t ^ n := by
  induction n with
  | zero => exact ⟨1, R.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨r', hr', e⟩ := ih
    have htn : t ^ n * r * (t ^ n)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht n) r).mp hr
    refine ⟨r' * (t ^ n * r * (t ^ n)⁻¹), R.mul_mem hr' htn, ?_⟩
    rw [pow_succ, e, pow_succ]
    group

omit [Finite U] in
theorem conj_pow_eq_pow {s a : U} {k : ℕ} (h : s * a * s⁻¹ = a ^ k) (n : ℕ) :
    s ^ n * a * (s ^ n)⁻¹ = a ^ (k ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc s ^ (n + 1) * a * (s ^ (n + 1))⁻¹ = s * (s ^ n * a * (s ^ n)⁻¹) * s⁻¹ := by
          rw [pow_succ']
          group
      _ = (s * a * s⁻¹) ^ (k ^ n) := by rw [ih, conj_pow]
      _ = a ^ (k ^ (n + 1)) := by rw [h, ← pow_mul, pow_succ', mul_comm]

theorem pow_four_mod_five : ∀ k : Fin 5, k ≠ 0 → (k : ℕ) ^ 4 % 5 = 1 := by decide

theorem card_ne_5040 (hs : IsSimpleGroup U) (hU : Nat.card U = 126000) {R Z : Subgroup U}
    (hR : Nat.card R = 125) (hZc : ∀ a ∈ Z, ∀ r ∈ R, a * r = r * a)
    (hRZ : ∀ a ∈ R, ∀ b ∈ R, a * b * a⁻¹ * b⁻¹ ∈ Z) {t : U}
    (htR : t ∈ Subgroup.normalizer (R : Set U))
    (hinv : ∀ r ∈ R, t ^ 4 * r * (t ^ 4)⁻¹ * r ∈ Z) (H : Subgroup U) : Nat.card H ≠ 5040 := by
  intro hH
  have hHi : H.index = 25 := by
    have := H.card_mul_index
    rw [hH, hU] at this
    omega
  have hrel_le : ∀ N : Subgroup U, H.relIndex N ≤ 25 := fun N => by
    have := Subgroup.relIndex_le_of_le_right (le_top : N ≤ ⊤)
      (by rw [Subgroup.relIndex_top_right, hHi]; norm_num)
    rwa [Subgroup.relIndex_top_right, hHi] at this
  have hmul := Subgroup.relIndex_mul_card (H := H) (K := R)
  rw [hR] at hmul
  have hdvd5 : Nat.card (H ⊓ R : Subgroup U) ∣ 5 := by
    have h1 : Nat.card (H ⊓ R : Subgroup U) ∣ 125 := hR ▸ Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.card (H ⊓ R : Subgroup U) ∣ 5040 := hH ▸ Subgroup.card_dvd_of_le inf_le_left
    have h3 := Nat.dvd_gcd h1 h2
    norm_num at h3
    exact h3
  have hcard5 : Nat.card (H ⊓ R : Subgroup U) = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd5 with h1 | h1
    · rw [h1] at hmul
      have := hrel_le R
      omega
    · exact h1
  have hrelR : H.relIndex R = 25 := by
    rw [hcard5] at hmul
    omega
  have hcov : ∀ {N : Subgroup U}, R ≤ N → ∀ n ∈ N, ∃ r ∈ R, r⁻¹ * n ∈ H :=
    fun hRN n hn => exists_inv_mul_mem_of_relIndex_le hRN (by rw [hrelR]; exact hrel_le _) hn
  have hHZ : ∀ a ∈ H, a ∈ Z → a = 1 := by
    intro a haH haZ
    have hcore : a ∈ H.normalCore := by
      intro b
      obtain ⟨r, hr, hrb⟩ := hcov (le_top : R ≤ ⊤) b⁻¹ (Subgroup.mem_top _)
      have hra : r⁻¹ * a * r = a := by
        calc r⁻¹ * a * r = r⁻¹ * (a * r) := by group
          _ = r⁻¹ * (r * a) := by rw [hZc a haZ r hr]
          _ = a := by group
      have e : b * a * b⁻¹ = (r⁻¹ * b⁻¹)⁻¹ * (r⁻¹ * a * r) * (r⁻¹ * b⁻¹) := by group
      rw [e, hra]
      exact H.mul_mem (H.mul_mem (H.inv_mem hrb) haH) hrb
    have hbot : H.normalCore = ⊥ := by
      rcases hs.eq_bot_or_eq_top_of_normal H.normalCore with h | h
      · exact h
      · exfalso
        have hHt : H = ⊤ := top_le_iff.mp (h ▸ H.normalCore_le)
        rw [hHt, Subgroup.card_top, hU] at hH
        norm_num at hH
    rw [hbot] at hcore
    exact Subgroup.mem_bot.mp hcore
  obtain ⟨r, hr, hrt⟩ := hcov (le_sup_left : R ≤ R ⊔ Subgroup.zpowers t) t
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  set s := r⁻¹ * t with hsdef
  have hsN : s ∈ Subgroup.normalizer (R : Set U) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hr)) htR
  have hs4 : ∀ b ∈ R, s ^ 4 * b * (s ^ 4)⁻¹ * b ∈ Z := by
    obtain ⟨r', hr', e⟩ := exists_mul_pow_eq (R.inv_mem hr) htR 4
    intro b hb
    set w := t ^ 4 * b * (t ^ 4)⁻¹ * b with hw
    have hwZ : w ∈ Z := hinv b hb
    have hwr : w * r' = r' * w := hZc w hwZ r' hr'
    have e2 : s ^ 4 * b * (s ^ 4)⁻¹ * b = w * (r' * b⁻¹ * r'⁻¹ * b⁻¹⁻¹) := by
      rw [hsdef, e]
      calc r' * t ^ 4 * b * (r' * t ^ 4)⁻¹ * b = r' * w * b⁻¹ * r'⁻¹ * b := by
            rw [hw]
            group
        _ = (r' * w) * (b⁻¹ * r'⁻¹ * b) := by group
        _ = (w * r') * (b⁻¹ * r'⁻¹ * b) := by rw [hwr]
        _ = w * (r' * b⁻¹ * r'⁻¹ * b⁻¹⁻¹) := by group
    rw [e2]
    exact Z.mul_mem hwZ (hRZ r' hr' b⁻¹ (R.inv_mem hb))
  have : Nontrivial (H ⊓ R : Subgroup U) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard5]; norm_num)
  obtain ⟨⟨a, haHR⟩, ha1⟩ := exists_ne (1 : (H ⊓ R : Subgroup U))
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have ha5 : a ^ 5 = 1 := by
    have h1 := pow_card_eq_one' (G := (H ⊓ R : Subgroup U)) (x := ⟨a, haHR⟩)
    rw [hcard5] at h1
    exact congrArg Subtype.val h1
  have hoa : orderOf a = 5 := orderOf_eq_prime ha5 ha1'
  have hHR : H ⊓ R = Subgroup.zpowers a := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haHR) ?_).symm
    rw [Nat.card_zpowers, hoa, hcard5]
  have hsa : s * a * s⁻¹ ∈ H ⊓ R :=
    ⟨H.mul_mem (H.mul_mem hrt haHR.1) (H.inv_mem hrt),
      (Subgroup.mem_normalizer_iff.mp hsN a).mp haHR.2⟩
  rw [hHR] at hsa
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hsa
  have h5 : ((5 : ℕ) : ℤ) ≠ 0 := by norm_num
  set k : Fin 5 := ⟨(i % ((5 : ℕ) : ℤ)).toNat, by
    have := Int.emod_lt_of_pos i (by norm_num : (0 : ℤ) < ((5 : ℕ) : ℤ))
    have := Int.emod_nonneg i h5
    omega⟩ with hk
  have hsak : s * a * s⁻¹ = a ^ (k : ℕ) := by
    rw [← hi, zpow_eq_zpow_emod' i ha5, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg i h5)]
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, Fin.val_zero, pow_zero] at hsak
    apply ha1'
    calc a = s⁻¹ * (s * a * s⁻¹) * s := by group
      _ = 1 := by rw [hsak]; group
  have hs4a : s ^ 4 * a * (s ^ 4)⁻¹ = a := by
    rw [conj_pow_eq_pow hsak 4, pow_eq_pow_mod _ ha5, pow_four_mod_five k hk0, pow_one]
  have ha2Z : a * a ∈ Z := by
    have := hs4 a haHR.2
    rwa [hs4a] at this
  have ha2 : a * a = 1 := hHZ _ (H.mul_mem haHR.1 haHR.1) ha2Z
  apply ha1'
  calc a = a ^ 5 * (a * a)⁻¹ * (a * a)⁻¹ := by group
    _ = 1 := by rw [ha5, ha2]; group

end Index

end CFSG.RankThree.PartTwo.Sec16.Res3U35
