module

public import CFSG.Sporadic.HN.PGroupAut

public section

namespace CFSG.Sporadic.HN

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem eq_top_of_conjProd_mem {a b g : G} (hgen : closure {a, b} = ⊤) (ha : a ^ 2 = 1)
    (hb : b ^ 3 = 1) {N : Subgroup G} [N.Normal] (hx : a * (g⁻¹ * b * g) ∈ N) : N = ⊤ := by
  let f := QuotientGroup.mk' N
  have hx' : f a * ((f g)⁻¹ * f b * f g) = 1 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact (QuotientGroup.eq_one_iff _).2 hx
  have ha' : f a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hb' : f b ^ 3 = 1 := by rw [← map_pow, hb, map_one]
  have hA : f a = (f g)⁻¹ * (f b)⁻¹ * f g := by
    calc f a = f a * ((f g)⁻¹ * f b * f g) * ((f g)⁻¹ * f b * f g)⁻¹ := by group
      _ = (f g)⁻¹ * (f b)⁻¹ * f g := by rw [hx']; group
  have hA3 : f a ^ 3 = 1 := by
    have e : ((f g)⁻¹ * (f b)⁻¹ * f g) ^ 3 = (f g)⁻¹ * (f b ^ 3)⁻¹ * f g := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [hA, e, hb']
    group
  have hA1 : f a = 1 := by
    have e : f a = f a ^ 3 * (f a ^ 2)⁻¹ := by group
    rw [e, hA3, ha']
    group
  have hB1 : f b = 1 := by
    have e : f b = f g * ((f g)⁻¹ * (f b)⁻¹ * f g)⁻¹ * (f g)⁻¹ := by group
    rw [e, ← hA, hA1]
    group
  have haN : a ∈ N := (QuotientGroup.eq_one_iff a).1 hA1
  have hbN : b ∈ N := (QuotientGroup.eq_one_iff b).1 hB1
  rw [eq_top_iff, ← hgen, closure_le]
  rintro y (rfl | rfl)
  · exact haN
  · exact hbN

theorem mem_of_dvd_card {q : ℕ} [hq : Fact q.Prime] {x : G} (hx : orderOf x = q)
    (hq2 : ¬ q ^ 2 ∣ Nat.card G) {N : Subgroup G} [hN : N.Normal] (hNq : q ∣ Nat.card N) :
    x ∈ N := by
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) q hNq
  have hy' : orderOf (y : G) = q := by rw [Subgroup.orderOf_coe, hy]
  have hcz : ∀ z : G, orderOf z = q → Nat.card (zpowers z) = q := fun z hz => by
    rw [Nat.card_zpowers, hz]
  have hpz : ∀ z : G, orderOf z = q → IsPGroup q (zpowers z) := fun z hz =>
    IsPGroup.of_card (n := 1) (by rw [hcz z hz, pow_one])
  obtain ⟨P, hP⟩ := (hpz _ hy').exists_le_sylow
  obtain ⟨P', hP'⟩ := (hpz _ hx).exists_le_sylow
  have hcard : ∀ (S : Sylow q G) (z : G), orderOf z = q → zpowers z ≤ S →
      (S : Subgroup G) = zpowers z := by
    intro S z hz hS
    symm
    apply Subgroup.eq_of_le_of_card_ge hS
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have h1 : q ∣ q ^ k := by
      have := Subgroup.card_dvd_of_le hS
      rwa [hcz z hz, hk] at this
    have h2 : q ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card _
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · rcases Nat.lt_or_ge k 1 with h' | h'
        · rw [show k = 0 by omega, pow_zero] at h1
          exact absurd (Nat.le_of_dvd one_pos h1) (by have := hq.out.two_le; omega)
        · omega
      · exact absurd ((pow_dvd_pow q h).trans h2) hq2
    rw [hk, hk1, pow_one, hcz z hz]
  have e1 := hcard P _ hy' hP
  have e2 := hcard P' _ hx hP'
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P P'
  have hxP' : x ∈ (P' : Subgroup G) := by rw [e2]; exact mem_zpowers x
  rw [← hc, Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hxP'
  obtain ⟨z, hz, rfl⟩ := hxP'
  have hzN : z ∈ N := by
    rw [e1] at hz
    exact (zpowers_le.2 y.2) hz
  exact hN.conj_mem z hzN c

theorem le_centralizer_of_not_dvd_card {q : ℕ} [hq : Fact q.Prime] {x : G} (hx : orderOf x = q)
    (hGL : ∀ p e : ℕ, p.Prime → p ≠ q → p ^ e ∣ Nat.card G →
      ∀ r ≤ e, ¬ q ∣ Nat.card (GL (Fin r) (ZMod p)))
    {N : Subgroup G} [hN : N.Normal] (hNq : ¬ q ∣ Nat.card N) :
    N ≤ centralizer {x} := by
  let C : Subgroup N := (centralizer {x}).comap N.subtype
  have key : ∀ p : ℕ, p.Prime → p ^ (Nat.card N).factorization p ∣ Nat.card C := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    by_cases hpq : p = q
    · subst hpq
      rw [Nat.factorization_eq_zero_of_not_dvd hNq, pow_zero]
      exact one_dvd _
    let φ : zpowers x →* MulAut N := (MulAut.conjNormal (H := N)).comp (zpowers x).subtype
    letI : MulDistribMulAction (zpowers x) N := MulDistribMulAction.compHom N φ
    have hZ : IsPGroup q (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨P0⟩ : Nonempty (Sylow p N) := inferInstance
    have hS : ¬ q ∣ Nat.card (Sylow p N) := fun h =>
      hNq (h.trans ((Sylow.card_dvd_index P0).trans (index_dvd_card _)))
    obtain ⟨P, hP⟩ := hZ.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p N) hS
    have hinv : ∀ h : zpowers x, ∀ z ∈ (P : Subgroup N), φ h z ∈ (P : Subgroup N) := by
      intro h z hz
      have h1 := smul_mem_pointwise_smul z h (P : Subgroup N) hz
      rw [← Sylow.pointwise_smul_def, hP h] at h1
      exact h1
    have hval : ∀ (h : zpowers x) (z : N), ((φ h z : N) : G) = (h : G) * z * (h : G)⁻¹ :=
      fun h z => rfl
    let xg : zpowers x := ⟨x, mem_zpowers x⟩
    let ψ : MulAut (P : Subgroup N) :=
      { toFun := fun z => ⟨φ xg (z : N), hinv xg z z.2⟩
        invFun := fun z => ⟨φ xg⁻¹ (z : N), hinv xg⁻¹ z z.2⟩
        left_inv := fun z => by
          apply Subtype.ext
          apply Subtype.ext
          change ((φ xg⁻¹ (φ xg (z : N)) : N) : G) = ((z : N) : G)
          rw [hval, hval]
          change x⁻¹ * (x * ((z : N) : G) * x⁻¹) * x⁻¹⁻¹ = ((z : N) : G)
          group
        right_inv := fun z => by
          apply Subtype.ext
          apply Subtype.ext
          change ((φ xg (φ xg⁻¹ (z : N)) : N) : G) = ((z : N) : G)
          rw [hval, hval]
          change x * (x⁻¹ * ((z : N) : G) * x⁻¹⁻¹) * x⁻¹ = ((z : N) : G)
          group
        map_mul' := fun z w => by
          apply Subtype.ext
          exact map_mul (φ xg) (z : N) (w : N) }
    have hψv : ∀ (z : (P : Subgroup N)), (((ψ z : N) : G)) = x * ((z : N) : G) * x⁻¹ :=
      fun z => rfl
    have hpow : ∀ (k : ℕ) (z : (P : Subgroup N)),
        ((((ψ ^ k) z : N)) : G) = x ^ k * ((z : N) : G) * (x ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => intro z; simp
      | succ k ih =>
        intro z
        rw [pow_succ', MulAut.mul_apply, hψv, ih]
        group
    have hψq : ψ ^ q = 1 := by
      ext z
      have := hpow q z
      have hxq : x ^ q = 1 := hx ▸ pow_orderOf_eq_one x
      rw [hxq] at this
      simpa using this
    have hNG : Nat.card N ∣ Nat.card G := card_subgroup_dvd_card N
    have hPcard : Nat.card (P : Subgroup N) = p ^ (Nat.card N).factorization p :=
      P.card_eq_multiplicity
    have hle : (Nat.card N).factorization p ≤ (Nat.card G).factorization p :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hNG p
    have hψ1 : ψ = 1 :=
      eq_one_of_pow_eq_one hq.out (Ne.symm hpq) P.isPGroup'
        (hPcard ▸ pow_dvd_pow p hle)
        (hGL p _ hp hpq (Nat.ordProj_dvd _ _)) hψq
    have hPC : (P : Subgroup N) ≤ C := by
      intro z hz
      have := congrArg (fun f : MulAut (P : Subgroup N) => (((f ⟨z, hz⟩ : N)) : G)) hψ1
      simp only [hψv, MulAut.one_apply] at this
      change (z : G) ∈ centralizer {x}
      rw [mem_centralizer_singleton_iff]
      calc (z : G) * x = x * z * x⁻¹ * x := by rw [this]
        _ = x * z := by group
    rw [← hPcard]
    exact card_dvd_of_le hPC
  have hdvd : Nat.card N ∣ Nat.card C := by
    rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.le_def]
    intro p
    by_cases hp : p.Prime
    · exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (key p hp)
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _
  have hC : C = ⊤ :=
    eq_top_of_card_eq C (le_antisymm (card_le_card_group C) (Nat.le_of_dvd Nat.card_pos hdvd))
  intro n hn
  have : (⟨n, hn⟩ : N) ∈ C := hC ▸ mem_top _
  exact this

theorem isSimpleGroup_of_conjProd {a b g : G} {q : ℕ} (hq : q.Prime)
    (hgen : closure {a, b} = ⊤) (ha : a ^ 2 = 1) (hb : b ^ 3 = 1)
    (hx : orderOf (a * (g⁻¹ * b * g)) = q) (hq2 : ¬ q ^ 2 ∣ Nat.card G) (hZ : center G = ⊥)
    (hGL : ∀ p e : ℕ, p.Prime → p ≠ q → p ^ e ∣ Nat.card G →
      ∀ r ≤ e, ¬ q ∣ Nat.card (GL (Fin r) (ZMod p))) :
    IsSimpleGroup G := by
  have : Fact q.Prime := ⟨hq⟩
  set x := a * (g⁻¹ * b * g)
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx
    exact hq.one_lt.ne hx
  have : Nontrivial G := nontrivial_of_ne x 1 hx1
  refine ⟨fun N hN => ?_⟩
  by_cases hNq : q ∣ Nat.card N
  · exact Or.inr (eq_top_of_conjProd_mem hgen ha hb (mem_of_dvd_card hx hq2 hNq))
  · left
    have hxC : x ∈ centralizer (N : Set G) := by
      rw [mem_centralizer_iff]
      intro n hn
      have := le_centralizer_of_not_dvd_card hx hGL hNq hn
      rw [mem_centralizer_singleton_iff] at this
      exact this
    have hCN : centralizer (N : Set G) = ⊤ := eq_top_of_conjProd_mem hgen ha hb hxC
    rw [eq_bot_iff, ← hZ]
    intro n hn
    rw [mem_center_iff]
    intro y
    have := (mem_centralizer_iff.1 (hCN ▸ mem_top y : y ∈ centralizer (N : Set G))) n hn
    exact this.symm

theorem pow_le_of_dvd_hn {p e m : ℕ} (hp : 1 < p) (hd : p ^ e ∣ 273030912000000)
    (hm : ¬ p ^ (m + 1) ∣ 273030912000000) : e ≤ m := by
  by_contra h
  exact hm ((pow_dvd_pow p (by omega)).trans hd)

theorem hn_GL_condition : ∀ p e : ℕ, p.Prime → p ≠ 19 → p ^ e ∣ 273030912000000 →
    ∀ r ≤ e, ¬ 19 ∣ Nat.card (GL (Fin r) (ZMod p)) := by
  intro p e hp hpq hd r hr
  have : Fact p.Prime := ⟨hp⟩
  refine not_dvd_card_GL (by norm_num) (Ne.symm hpq) fun k hk1 hkr => ?_
  have hpN : p ∣ 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 :=
    (dvd_pow_self p (by omega : e ≠ 0)).trans hd
  have hpl : ∀ l : ℕ, l.Prime → p ∣ l → p = l := fun l hl h => (Nat.prime_dvd_prime_iff_eq hp hl).1 h
  rcases (Nat.Prime.dvd_mul hp).1 hpN with h | h19
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h11
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h7
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
        · rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
          · obtain rfl := hpl 2 (by norm_num) (hp.dvd_of_dvd_pow h2)
            have : k ≤ 14 := le_trans hkr <| le_trans hr <| pow_le_of_dvd_hn (m := 14) (by norm_num) hd (by norm_num)
            interval_cases k <;> norm_num
          · obtain rfl := hpl 3 (by norm_num) (hp.dvd_of_dvd_pow h3)
            have : k ≤ 6 := le_trans hkr <| le_trans hr <| pow_le_of_dvd_hn (m := 6) (by norm_num) hd (by norm_num)
            interval_cases k <;> norm_num
        · obtain rfl := hpl 5 (by norm_num) (hp.dvd_of_dvd_pow h5)
          have : k ≤ 6 := le_trans hkr <| le_trans hr <| pow_le_of_dvd_hn (m := 6) (by norm_num) hd (by norm_num)
          interval_cases k <;> norm_num
      · obtain rfl := hpl 7 (by norm_num) h7
        have : k ≤ 1 := le_trans hkr <| le_trans hr <| pow_le_of_dvd_hn (m := 1) (by norm_num) hd (by norm_num)
        interval_cases k <;> norm_num
    · obtain rfl := hpl 11 (by norm_num) h11
      have : k ≤ 1 := le_trans hkr <| le_trans hr <| pow_le_of_dvd_hn (m := 1) (by norm_num) hd (by norm_num)
      interval_cases k <;> norm_num
  · exact absurd (hpl 19 (by norm_num) h19) hpq

end CFSG.Sporadic.HN
