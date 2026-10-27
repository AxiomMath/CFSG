module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace Sylow155T

theorem eq_pow_sq_of_odd {Q : Type*} [Group Q] {y : Q} (hy : Odd (orderOf y)) :
    ∃ m : ℕ, y = (y ^ 2) ^ m := by
  obtain ⟨m, hm⟩ := hy
  refine ⟨m + 1, ?_⟩
  rw [← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

theorem conj_eq_of_card_le_three {Q : Type*} [Group Q] {Z : Subgroup Q} [Finite Z]
    (hZ : Nat.card Z ≤ 3) {a : Q} (haZ : a ∈ Subgroup.normalizer (Z : Set Q)) {k : ℕ}
    (ha : a ^ 3 ^ k = 1) {z : Q} (hz : z ∈ Z) : a * z * a⁻¹ = z := by
  by_contra hne
  have hconj : ∀ y : Q, a * y * a⁻¹ = 1 → y = 1 := fun y hy => by
    have : y = a⁻¹ * (a * y * a⁻¹) * a := by group
    rw [this, hy]
    group
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hne (by group)
  set w := a * z * a⁻¹ with hw
  set u := a * w * a⁻¹ with hu
  have hwZ : w ∈ Z := (Subgroup.mem_normalizer_iff.mp haZ z).mp hz
  have huZ : u ∈ Z := (Subgroup.mem_normalizer_iff.mp haZ w).mp hwZ
  have hw1 : w ≠ 1 := fun h => hz1 (hconj z h)
  have hu1 : u ≠ 1 := fun h => hw1 (hconj w h)
  have huw : u ≠ w := by
    intro h
    apply hne
    have : w = a⁻¹ * u * a := by rw [hu]; group
    rw [this, h, hw]
    group
  have huz : u = z := by
    by_contra huz
    have hsub : ({1, z, w, u} : Set Q) ⊆ (Z : Set Q) := by
      intro y hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact Z.one_mem
      · exact hz
      · exact hwZ
      · exact huZ
    have h4 : ({1, z, w, u} : Set Q).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair huw.symm]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => hne h.symm, fun h => huz h.symm⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hz1.symm, hw1.symm, hu1.symm⟩
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h4, ← Nat.card_coe_set_eq] at hle
    have : Nat.card ((Z : Set Q)) = Nat.card Z := rfl
    omega
  have hc2 : Commute (a ^ 2) z := by
    show a ^ 2 * z = z * a ^ 2
    have hu2 : u = a ^ 2 * z * (a ^ 2)⁻¹ := by
      rw [hu, hw, pow_two, mul_inv_rev]
      simp only [mul_assoc]
    have h1 : a ^ 2 * z * (a ^ 2)⁻¹ = z := by
      rw [← hu2]
      exact huz
    calc a ^ 2 * z = a ^ 2 * z * (a ^ 2)⁻¹ * a ^ 2 := by group
      _ = z * a ^ 2 := by rw [h1]
  have hodd : Odd (orderOf a) :=
    (Odd.pow (by decide : Odd 3)).of_dvd_nat (orderOf_dvd_of_pow_eq_one ha)
  obtain ⟨m, hm⟩ := eq_pow_sq_of_odd hodd
  have hc : Commute a z := by
    rw [hm]
    exact hc2.pow_left m
  apply hne
  show a * z * a⁻¹ = z
  rw [hc.eq]
  group

theorem exists_fixed_coset {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [hp : Fact p.Prime]
    {T S Z : Subgroup Q} (hT : IsPGroup p T) (hST : S ≤ T)
    (hTS : T ≤ Subgroup.normalizer (S : Set Q)) (hTZ : T ≤ Subgroup.normalizer (Z : Set Q))
    (hSZ : ¬ S ≤ Z) :
    ∃ x ∈ S, x ∉ Z ∧ x ^ p ∈ Z ∧ ∀ t ∈ T, x⁻¹ * (t * x * t⁻¹) ∈ Z := by
  classical
  set K : Subgroup T := Z.subgroupOf T with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk t => ?_⟩
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hTZ t.2) k).mp hk
  set S' : Subgroup T := S.subgroupOf T with hS'
  have hS'n : S'.Normal := by
    refine ⟨fun k hk t => ?_⟩
    rw [hS', Subgroup.mem_subgroupOf] at hk ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hTS t.2) k).mp hk
  set π := QuotientGroup.mk' K with hπ
  set H : Subgroup (T ⧸ K) := S'.map π with hH
  have hHn : H.Normal := hS'n.map π (QuotientGroup.mk'_surjective K)
  have hpg : IsPGroup p (T ⧸ K) := hT.to_quotient K
  have hnil : Group.IsNilpotent (T ⧸ K) := hpg.isNilpotent
  have hHne : H ≠ ⊥ := by
    intro hbot
    apply hSZ
    intro s hs
    have hmem : π ⟨s, hST hs⟩ ∈ H :=
      Subgroup.mem_map_of_mem _ (by rw [hS', Subgroup.mem_subgroupOf]; exact hs)
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      hK, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  have hHZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  set L := H ⊓ Subgroup.center (T ⧸ K) with hL
  have hLp : IsPGroup p L := hpg.to_subgroup L
  obtain ⟨n, hn⟩ := hLp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hHZ (Subgroup.eq_bot_of_card_eq L hn)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := L) p
    (by rw [hn]; exact dvd_pow_self p hn0)
  obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp (y.2.1 : (y : T ⧸ K) ∈ H)
  have hyc : (y : T ⧸ K) ∈ Subgroup.center (T ⧸ K) := y.2.2
  have hyo : orderOf (y : T ⧸ K) = p := by rw [Subgroup.orderOf_coe, hy]
  refine ⟨(t : Q), by rw [hS', Subgroup.mem_subgroupOf] at ht; exact ht, ?_, ?_, ?_⟩
  · intro htZ
    have h1 : π t = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf]
      exact htZ
    rw [hty] at h1
    rw [h1, orderOf_one] at hyo
    exact hp.out.one_lt.ne hyo
  · have h1 : π (t ^ p) = 1 := by
      rw [map_pow, hty, ← hyo, pow_orderOf_eq_one]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · intro u hu
    set u' : T := ⟨u, hu⟩
    have h1 : π (t⁻¹ * (u' * t * u'⁻¹)) = 1 := by
      have hcomm := Subgroup.mem_center_iff.mp hyc (π u')
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hty, hcomm]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf] at h1
    simpa [u'] using h1

theorem le_normalizer_inf_of_le {Q : Type*} [Group Q] {P X Y : Subgroup Q}
    (hX : P ≤ Subgroup.normalizer (X : Set Q)) (hY : P ≤ Subgroup.normalizer (Y : Set Q)) :
    P ≤ Subgroup.normalizer ((X ⊓ Y : Subgroup Q) : Set Q) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp (hX hg) h)
    (Subgroup.mem_normalizer_iff.mp (hY hg) h)

theorem le_normalizer_centralizer {Q : Type*} [Group Q] {W P : Subgroup Q}
    (hP : P ≤ Subgroup.normalizer (W : Set Q)) :
    P ≤ Subgroup.normalizer (Subgroup.centralizer (W : Set Q) : Set Q) := by
  intro g hg
  have hgW := Subgroup.mem_normalizer_iff.mp (hP hg)
  rw [Subgroup.mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc h hh
    have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    have hh' : g⁻¹ * h * g ∈ W := (hgW _).mpr (by rw [e]; exact hh)
    have h1 := hc _ hh'
    calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * h := by group
  · intro hc h hh
    have h1 := hc _ ((hgW h).mp hh)
    have h2 : g * (h * c) * g⁻¹ = g * (c * h) * g⁻¹ := by
      calc g * (h * c) * g⁻¹ = g * h * g⁻¹ * (g * c * g⁻¹) := by group
        _ = g * c * g⁻¹ * (g * h * g⁻¹) := h1
        _ = g * (c * h) * g⁻¹ := by group
    simpa using h2

theorem le_normalizer_inf_centralizer {Q : Type*} [Group Q] {W P : Subgroup Q}
    (hP : P ≤ Subgroup.normalizer (W : Set Q)) :
    P ≤ Subgroup.normalizer ((W ⊓ Subgroup.centralizer (W : Set Q) : Subgroup Q) : Set Q) :=
  le_normalizer_inf_of_le hP (le_normalizer_centralizer hP)

theorem antidiag_false {Q : Type*} [Group Q] {W W₂ : Subgroup Q} {d x : Q}
    (hcomm : ∀ w ∈ W, ∀ w₂ ∈ W₂, w * w₂ = w₂ * w)
    (hW₂ : W.map (MulAut.conj d).toMonoidHom = W₂)
    (hW : W.map (MulAut.conj (d ^ 2)).toMonoidHom = W)
    (hx : x ∈ W) (hodd : Odd (orderOf x)) (hxw : ∃ w ∈ W, w * x ≠ x * w)
    (hfix : d * (x * (d * x * d⁻¹)⁻¹) * d⁻¹ = x * (d * x * d⁻¹)⁻¹) : False := by
  have hconj : ∀ g : Q, g ∈ W → d * g * d⁻¹ ∈ W₂ := fun g hg => by
    rw [← hW₂]
    exact ⟨g, hg, by simp [MulAut.conj_apply]⟩
  set y := d * x * d⁻¹ with hy
  have hyW₂ : y ∈ W₂ := hconj x hx
  set x' := d * y * d⁻¹ with hx'
  have hx'W : x' ∈ W := by
    rw [← hW]
    exact ⟨x, hx, by simp [MulAut.conj_apply, hx', hy, pow_two, mul_assoc]⟩
  have h1 : y * x'⁻¹ = x * y⁻¹ := by
    rw [← hfix, hx', hy]
    group
  have hxy : x * y = y * x := hcomm x hx y hyW₂
  have hy2 : y ^ 2 = x * x' := by
    have h2 : x * y⁻¹ = y⁻¹ * x := by
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y) * y⁻¹ := by rw [hxy]
        _ = y⁻¹ * x := by group
    calc y ^ 2 = y * (y * x'⁻¹) * x' := by simp [pow_two, mul_assoc]
      _ = y * (y⁻¹ * x) * x' := by rw [h1, h2]
      _ = x * x' := by group
  have hy2W : y ^ 2 ∈ W := hy2 ▸ W.mul_mem hx hx'W
  have hyodd : Odd (orderOf y) := by
    have : orderOf y = orderOf x := by
      rw [hy, ← MulAut.conj_apply]
      exact orderOf_injective (MulAut.conj d).toMonoidHom (MulEquiv.injective _) x
    rw [this]
    exact hodd
  obtain ⟨m, hm⟩ := eq_pow_sq_of_odd hyodd
  have hyc : ∀ w₂ ∈ W₂, Commute y w₂ := fun w₂ hw₂ => by
    have h3 : Commute (y ^ 2) w₂ := hcomm _ hy2W w₂ hw₂
    rw [hm]
    exact h3.pow_left m
  obtain ⟨w, hw, hwx⟩ := hxw
  apply hwx
  have h4 : y * (d * w * d⁻¹) = d * w * d⁻¹ * y := (hyc _ (hconj w hw)).eq
  have h5 : d * (w * x) * d⁻¹ = d * (x * w) * d⁻¹ := by
    calc d * (w * x) * d⁻¹ = d * w * d⁻¹ * y := by rw [hy]; group
      _ = y * (d * w * d⁻¹) := h4.symm
      _ = d * (x * w) * d⁻¹ := by rw [hy]; group
  simpa using h5

theorem exists_isPGroup_inf_not_le {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [hp : Fact p.Prime]
    {W Ā : Subgroup Q} (hĀ : IsPGroup p Ā) (hĀW : Ā ≤ Subgroup.normalizer (W : Set Q)) {f : Q}
    (hfW : f ∈ W) (hfp : f ^ p = 1) (hfC : f ∉ Subgroup.centralizer (W : Set Q)) :
    ∃ T : Subgroup Q, IsPGroup p T ∧ Ā ≤ T ∧ T ≤ Subgroup.normalizer (W : Set Q) ∧
      ¬ T ⊓ W ≤ W ⊓ Subgroup.centralizer (W : Set Q) := by
  set H := Subgroup.normalizer (W : Set Q) with hH
  have hfH : f ∈ H := Subgroup.le_normalizer hfW
  obtain ⟨T₀, hT₀⟩ := (hĀ.comap_of_injective H.subtype H.subtype_injective).exists_le_sylow
  have hf' : IsPGroup p (Subgroup.zpowers (⟨f, hfH⟩ : H)) := by
    have ho : orderOf (⟨f, hfH⟩ : H) ∣ p ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hfp))
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).mp ho
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  obtain ⟨R₀, hR₀⟩ := hf'.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq H R₀ T₀
  have hfk : k * ⟨f, hfH⟩ * k⁻¹ ∈ (T₀ : Subgroup H) := by
    rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv,
      show k⁻¹ * (k * ⟨f, hfH⟩ * k⁻¹) * k = ⟨f, hfH⟩ by group]
    exact hR₀ (Subgroup.mem_zpowers _)
  refine ⟨(T₀ : Subgroup H).map H.subtype, T₀.isPGroup'.map H.subtype,
    fun a ha => ⟨⟨a, hĀW ha⟩, hT₀ ha, rfl⟩, Subgroup.map_subtype_le _, fun hle => hfC ?_⟩
  have hf'W : (k : Q) * f * (k : Q)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp k.2 f).mp hfW
  have hf'T : (k : Q) * f * (k : Q)⁻¹ ∈ (T₀ : Subgroup H).map H.subtype :=
    ⟨_, hfk, by simp⟩
  have hf'C := (hle ⟨hf'T, hf'W⟩).2
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_centralizer (P := H) le_rfl k.2) f).mpr
    hf'C

theorem false_of_fixed {Q : Type*} [Group Q] [Finite Q] {W W₂ Ā T : Subgroup Q} {d : Q}
    (hcomm : ∀ w ∈ W, ∀ w₂ ∈ W₂, w * w₂ = w₂ * w)
    (hW₂ : W.map (MulAut.conj d).toMonoidHom = W₂)
    (hW : W.map (MulAut.conj (d ^ 2)).toMonoidHom = W)
    (hT : IsPGroup 3 T) (hĀT : Ā ≤ T) (hTW : T ≤ Subgroup.normalizer (W : Set Q))
    (hdĀ : ∀ a ∈ Ā, a * d = d * a)
    (hL : ∀ q ∈ Subgroup.centralizer (Ā : Set Q), q ^ 3 = 1 → d * q * d⁻¹ = q)
    (hZ : Nat.card ↥(W ⊓ Subgroup.centralizer (W : Set Q)) ≤ 3)
    (hTWZ : ¬ T ⊓ W ≤ W ⊓ Subgroup.centralizer (W : Set Q)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTZ : T ≤ Subgroup.normalizer
      ((W ⊓ Subgroup.centralizer (W : Set Q) : Subgroup Q) : Set Q) :=
    le_normalizer_inf_centralizer hTW
  have hTS : T ≤ Subgroup.normalizer ((T ⊓ W : Subgroup Q) : Set Q) :=
    le_normalizer_inf_of_le Subgroup.le_normalizer hTW
  have hpow : ∀ t ∈ T, ∃ k : ℕ, t ^ 3 ^ k = 1 := fun t ht => by
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hZ3 : ∀ z ∈ W ⊓ Subgroup.centralizer (W : Set Q), z ∈ T → z ^ 3 = 1 := by
    intro z hz hzT
    obtain ⟨k, hk⟩ := hpow z hzT
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
    have hle : orderOf z ≤ 3 :=
      (Nat.le_of_dvd Nat.card_pos (Subgroup.orderOf_dvd_natCard _ hz)).trans hZ
    have h3 : orderOf z ∣ 3 := by
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · interval_cases j <;> simp [hj]
      · have h9 : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
        rw [← hj] at h9
        norm_num at h9
        omega
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  have hfix : ∀ z ∈ W ⊓ Subgroup.centralizer (W : Set Q), z ∈ T → d * z * d⁻¹ = z := by
    intro z hz hzT
    refine hL z ?_ (hZ3 z hz hzT)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨k, hk⟩ := hpow a (hĀT ha)
    have h1 := conj_eq_of_card_le_three hZ (hTZ (hĀT ha)) hk hz
    calc a * z = a * z * a⁻¹ * a := by group
      _ = z * a := by rw [h1]
  obtain ⟨x, hxTW, hxZ, hx3Z, hxT⟩ := exists_fixed_coset (p := 3) hT inf_le_left hTS hTZ hTWZ
  have hxT' : x ∈ T := hxTW.1
  have hxW : x ∈ W := hxTW.2
  obtain ⟨y, hy⟩ : ∃ y, d * x * d⁻¹ = y := ⟨_, rfl⟩
  have hyW₂ : y ∈ W₂ := by
    rw [← hW₂, ← hy]
    exact ⟨x, hxW, by simp [MulAut.conj_apply]⟩
  have hhC : x * y⁻¹ ∈ Subgroup.centralizer (Ā : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hzZ := hxT a (hĀT ha)
    have hzT : x⁻¹ * (a * x * a⁻¹) ∈ T :=
      T.mul_mem (T.inv_mem hxT') (T.mul_mem (T.mul_mem (hĀT ha) hxT') (T.inv_mem (hĀT ha)))
    have hdz := hfix _ hzZ hzT
    have hda : a * d = d * a := hdĀ a ha
    have e1 : a * x * a⁻¹ = x * (x⁻¹ * (a * x * a⁻¹)) := by group
    have e2 : a * y * a⁻¹ = y * (x⁻¹ * (a * x * a⁻¹)) := by
      rw [← hy]
      calc a * (d * x * d⁻¹) * a⁻¹ = (a * d) * x * (a * d)⁻¹ := by group
        _ = (d * a) * x * (d * a)⁻¹ := by rw [hda]
        _ = d * (a * x * a⁻¹) * d⁻¹ := by group
        _ = d * (x * (x⁻¹ * (a * x * a⁻¹))) * d⁻¹ := by rw [← e1]
        _ = (d * x * d⁻¹) * (d * (x⁻¹ * (a * x * a⁻¹)) * d⁻¹) := by group
        _ = d * x * d⁻¹ * (x⁻¹ * (a * x * a⁻¹)) := by rw [hdz]
    have e3 : a * (x * y⁻¹) * a⁻¹ = x * y⁻¹ := by
      calc a * (x * y⁻¹) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹)⁻¹ := by group
        _ = x * (x⁻¹ * (a * x * a⁻¹)) * (y * (x⁻¹ * (a * x * a⁻¹)))⁻¹ := by rw [← e1, e2]
        _ = x * y⁻¹ := by group
    calc a * (x * y⁻¹) = a * (x * y⁻¹) * a⁻¹ * a := by group
      _ = x * y⁻¹ * a := by rw [e3]
  have hxy : Commute x y := hcomm x hxW y hyW₂
  have hh3 : (x * y⁻¹) ^ 3 = 1 := by
    have hy3 : y ^ 3 = x ^ 3 := by
      rw [← hy, conj_pow, hfix _ hx3Z (T.pow_mem hxT' 3)]
    rw [hxy.inv_right.mul_pow, inv_pow, hy3, mul_inv_cancel]
  have hhfix : d * (x * y⁻¹) * d⁻¹ = x * y⁻¹ := hL _ hhC hh3
  have hxodd : Odd (orderOf x) := by
    obtain ⟨k, hk⟩ := hpow x hxT'
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hk)
  have hxnc : ∃ w ∈ W, w * x ≠ x * w := by
    by_contra hall
    push Not at hall
    exact hxZ ⟨hxW, Subgroup.mem_centralizer_iff.mpr hall⟩
  subst hy
  exact antidiag_false hcomm hW₂ hW hxW hxodd hxnc hhfix

end Sylow155T

end CFSG.RankThree.PartTwo.Sec15
