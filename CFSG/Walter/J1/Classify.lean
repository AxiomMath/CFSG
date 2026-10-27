module

public import CFSG.Walter.J1.MaxInv
public import CFSG.Walter.J1.Fusion

public section

namespace CFSG.Walter.J1

section General

variable {G : Type*} [Group G]

theorem commute_of_mem_four {a b s : G} (hT : IsFour a b)
    (hs : s = 1 ∨ s = a ∨ s = b ∨ s = a * b) : s * a = a * s := by
  rcases hs with rfl | rfl | rfl | rfl
  · simp
  · rfl
  · exact hT.2.2.2.symm
  · rw [mul_assoc, ← hT.2.2.2, ← mul_assoc]

theorem mem_normalizer_of_mem_four {a b s : G} {M : Subgroup G} (hM : IsInv a b M)
    (hs : s = 1 ∨ s = a ∨ s = b ∨ s = a * b) : s ∈ Subgroup.normalizer (M : Set G) := by
  rcases hs with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hM.2.1
  · exact hM.2.2
  · exact hM.mul_mem

theorem pow_card_eq_one_of_mem {X : Subgroup G} {x : G} (hx : x ∈ X) :
    x ^ Nat.card X = 1 := by
  rw [← Subgroup.coe_mk X x hx, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]

theorem odd_orderOf_of_mem {X : Subgroup G} (hX : Odd (Nat.card X)) {x : G} (hx : x ∈ X) :
    Odd (orderOf x) := Odd.of_dvd_nat hX (Subgroup.orderOf_dvd_natCard X hx)

theorem odd_orderOf_of_pow {p : ℕ} (hp : Odd p) {x : G} {k : ℕ} (hk : x ^ p ^ k = 1) :
    Odd (orderOf x) := Odd.of_dvd_nat (hp.pow) (orderOf_dvd_of_pow_eq_one hk)

theorem sq_eq_one_of_conj_inv {w y : G} {m : ℕ} (hm : Odd m) (hwm : w ^ m = 1)
    (hwy : w * y * w⁻¹ = y⁻¹) : y * y = 1 := by
  have key : ∀ i : ℕ, w ^ (2 * i) * y * (w ^ (2 * i))⁻¹ = y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, pow_add, pow_two]
      calc w ^ (2 * i) * (w * w) * y * (w ^ (2 * i) * (w * w))⁻¹ =
          w ^ (2 * i) * (w * (w * y * w⁻¹) * w⁻¹) * (w ^ (2 * i))⁻¹ := by group
        _ = w ^ (2 * i) * (w * y⁻¹ * w⁻¹) * (w ^ (2 * i))⁻¹ := by rw [hwy]
        _ = w ^ (2 * i) * (w * y * w⁻¹)⁻¹ * (w ^ (2 * i))⁻¹ := by group
        _ = y := by rw [hwy, inv_inv, ih]
  obtain ⟨i, rfl⟩ := hm
  have h1 : w ^ (2 * i + 1) * y * (w ^ (2 * i + 1))⁻¹ = y⁻¹ := by
    calc w ^ (2 * i + 1) * y * (w ^ (2 * i + 1))⁻¹ =
        w ^ (2 * i) * (w * y * w⁻¹) * (w ^ (2 * i))⁻¹ := by rw [pow_succ]; group
      _ = w ^ (2 * i) * y⁻¹ * (w ^ (2 * i))⁻¹ := by rw [hwy]
      _ = (w ^ (2 * i) * y * (w ^ (2 * i))⁻¹)⁻¹ := by group
      _ = y⁻¹ := by rw [key]
  rw [hwm, one_mul, inv_one, mul_one] at h1
  calc y * y = y * y⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel y

theorem eq_one_of_mul_self_of_odd {y : G} (hy : Odd (orderOf y)) (h2 : y * y = 1) : y = 1 := by
  have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hy
    exact absurd hy (by decide)

theorem factorization_mul_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (p * p * q).factorization p = 2 := by
  rw [Nat.factorization_mul (Nat.mul_ne_zero hp.ne_zero hp.ne_zero) hq.ne_zero,
    Nat.factorization_mul hp.ne_zero
    hp.ne_zero, Finsupp.add_apply, Finsupp.add_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))]

theorem exists_sylow_of_card_mixed [Finite G] {M : Subgroup G} {p q : ℕ}
    (hpq : (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3)) (hM : Nat.card M = p * p * q) :
    ∃ P : Subgroup G, P ≤ M ∧ Nat.card P = p * p ∧
      ∀ x ∈ M, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ P := by
  have hp : p.Prime := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hq : q.Prime := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hpq' : p ≠ q := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  let Q : Sylow p M := default
  have hQ : Nat.card (Q : Subgroup M) = p * p := by
    rw [Sylow.card_eq_multiplicity, hM, factorization_mul_mul hp hq hpq', pow_two]
  have hidx : (Q : Subgroup M).index = q := by
    have := (Q : Subgroup M).card_mul_index
    rw [hQ, hM] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos hp.pos) this
  have hone : Nat.card (Sylow p M) = 1 := by
    have hdvd := Sylow.card_dvd_index Q
    rw [hidx] at hdvd
    have hmod := card_sylow_modEq_one p M
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hmod
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert hmod <;> decide
  have hsub : Subsingleton (Sylow p M) := (Nat.card_eq_one_iff_unique.mp hone).1
  refine ⟨(Q : Subgroup M).map M.subtype, Subgroup.map_subtype_le _, ?_, fun x hx hxp => ?_⟩
  · rw [Subgroup.card_map_of_injective M.subtype_injective, hQ]
  · obtain ⟨k, hk⟩ := hxp
    have hZ : IsPGroup p (Subgroup.zpowers (⟨x, hx⟩ : M)) := by
      have hdvd : orderOf (⟨x, hx⟩ : M) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
        apply Subtype.ext
        simpa using hk)
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    obtain ⟨Q', hQ'⟩ := hZ.exists_le_sylow
    rw [Subsingleton.elim Q' Q] at hQ'
    exact ⟨⟨x, hx⟩, hQ' (Subgroup.mem_zpowers _), rfl⟩

theorem map_conj_eq_of_mem_normalizer {C : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (C : Set G)) : C.map (MulAut.conj x).toMonoidHom = C := by
  ext y
  rw [mem_map_conj]
  constructor
  · intro hy
    have := (Subgroup.mem_normalizer_iff.mp hx _).mp hy
    simpa [mul_assoc] using this
  · intro hy
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
    simpa using this

theorem mem_normalizer_sup [Finite G] {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  have h1 : (A ⊔ B).map (MulAut.conj x).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]
  rw [← h1]
  exact conj_mem_map_conj hy

theorem commute_of_central_of_card [Finite G] {M D : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hDM : D ≤ M) (hcard : Nat.card M = p * Nat.card D)
    (hD : ∀ d ∈ D, ∀ m ∈ M, d * m = m * d) : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
  intro x hx y hy
  by_cases hxD : x ∈ D
  · exact hD x hxD y hy
  set C := M ⊓ Subgroup.centralizer ({x} : Set G)
  have hDC : D ≤ C := fun d hd =>
    ⟨hDM hd, Subgroup.mem_centralizer_singleton_iff.mpr (hD d hd x hx)⟩
  have hxC : x ∈ C := ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hDC
  have hCM : Nat.card C ∣ Nat.card M := Subgroup.card_dvd_of_le inf_le_left
  have hDpos : 0 < Nat.card D := Nat.card_pos
  rw [hk, hcard, mul_comm p] at hCM
  have hkp : k ∣ p := (Nat.mul_dvd_mul_iff_left hDpos).mp hCM
  have hk1 : k ≠ 1 := by
    intro hk1
    rw [hk1, mul_one] at hk
    exact hxD ((Subgroup.eq_of_le_of_card_ge hDC hk.le) ▸ hxC)
  have hkp' : k = p := ((Nat.dvd_prime hp).mp hkp).resolve_left hk1
  have hCeq : C = M := Subgroup.eq_of_le_of_card_ge inf_le_left (by
    rw [hk, hkp', hcard, mul_comm])
  have hyC : y ∈ C := hCeq ▸ hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp hyC.2).symm

end General

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem false_of_two {a b : G} (hT : IsFour a b) {M : Subgroup G}
    (hM : IsMaxInv a b M) (hab : M ⊓ Subgroup.centralizer ({a * b} : Set G) = ⊥) {p : ℕ}
    (hp : p = 3 ∨ p = 5) (ha : Nat.card (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = p)
    (hb : Nat.card (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = p) : False := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  have hpodd : Odd p := by rcases hp with rfl | rfl <;> decide
  have hMcard : Nat.card M = p ^ 2 := by
    rw [h.card_eq_mul hT hM.1, ha, hb, hab, Subgroup.card_bot, mul_one, pow_two]
  have habel := commute_of_inf_eq_bot hT.mul_self_mul hM.1.mul_mem hab
  have hMa1 : M ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at ha
    exact hpp.one_lt.ne ha
  obtain ⟨hN, hdec⟩ := h.maxInv_normalizer hT hM hM.1 hMa1 hab
    Subgroup.le_normalizer
  have hMp : IsPGroup p M := IsPGroup.of_card hMcard
  set P := sylowOfNormalizer M hMp fun g hg ⟨k, hk⟩ => hN g hg (odd_orderOf_of_pow hpodd hk)
  have : IsMulCommutative (P : Subgroup G) :=
    ⟨⟨fun x y => Subtype.ext (habel x x.2 y y.2)⟩⟩
  obtain ⟨g, hg⟩ := h.exists_conj_of_good hp ha hb hT.1 hT.2.1 inf_le_right inf_le_right
  obtain ⟨y, hy, hy1⟩ := exists_ne_one_of_card ha hpp.one_lt
  have hgy : g * y * g⁻¹ ∈ M ⊓ Subgroup.centralizer ({b} : Set G) := by
    rw [← hg]
    exact conj_mem_map_conj hy
  obtain ⟨n, hn, hny⟩ := exists_normalizer_conj P (x := y) (g := g) hy.1 hgy.1
  obtain ⟨m, hm, s, hs, rfl⟩ := hdec n hn
  have hsM := mem_normalizer_of_mem_four hM.1 hs
  have hsa := mem_normalizer_inf_centralizer hsM (commute_of_mem_four hT hs).symm
  have hsy : s * y * s⁻¹ ∈ M ⊓ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hsa y).mp hy
  have hmy : m * s * y * (m * s)⁻¹ = s * y * s⁻¹ := by
    rw [show m * s * y * (m * s)⁻¹ = m * (s * y * s⁻¹) * m⁻¹ by group,
      habel m hm _ hsy.1, mul_inv_cancel_right]
  rw [hmy] at hny
  have h0 : g * y * g⁻¹ ∈ M ⊓ Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer ({b} : Set G) := ⟨by rw [← hny]; exact hsy, hgy.2⟩
  rw [h.inf_centralizer_four_eq_bot hT hM.1.1, Subgroup.mem_bot] at h0
  apply hy1
  have := congrArg (fun w => g⁻¹ * w * g) h0
  simpa [mul_assoc] using this

include h in
theorem false_of_mixed {a b : G} (hT : IsFour a b) {M : Subgroup G} (hM : IsMaxInv a b M)
    {p q : ℕ} (hpq : (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3))
    (ha : Nat.card (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = p)
    (hb : Nat.card (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = p)
    (hab : Nat.card (M ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) = q) : False := by
  have hp : p.Prime := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hq : q.Prime := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hqodd : Odd q := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hp35 : p = 3 ∨ p = 5 := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hcop : Nat.Coprime (p * p) q := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  set Ma := M ⊓ Subgroup.centralizer ({a} : Set G)
  set Mb := M ⊓ Subgroup.centralizer ({b} : Set G)
  set Mab := M ⊓ Subgroup.centralizer ({a * b} : Set G)
  have hMcard : Nat.card M = p * p * q := by rw [h.card_eq_mul hT hM.1, ha, hb, hab]
  obtain ⟨P, hPM, hPcard, hPp⟩ := exists_sylow_of_card_mixed hpq hMcard
  have hpelt : ∀ {X : Subgroup G}, Nat.card X = p → ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k = 1 :=
    fun hX x hx => ⟨1, by rw [pow_one, ← hX]; exact pow_card_eq_one_of_mem hx⟩
  have hMaP : Ma ≤ P := fun x hx => hPp x hx.1 (hpelt ha x hx)
  have hMbP : Mb ≤ P := fun x hx => hPp x hx.1 (hpelt hb x hx)
  have hNP : ∀ y ∈ Subgroup.normalizer (M : Set G), y ∈ Subgroup.normalizer (P : Set G) := by
    intro y hy
    refine mem_normalizer_of_conj_mem fun x hx => hPp _ ((Subgroup.mem_normalizer_iff.mp hy x).mp
      (hPM hx)) ⟨2, ?_⟩
    rw [conj_pow, show p ^ 2 = Nat.card P by rw [hPcard, pow_two], pow_card_eq_one_of_mem hx]
    group
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := fun m hm => hNP m (Subgroup.le_normalizer hm)
  have hPab : P ⊓ Subgroup.centralizer ({a * b} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have h1 : orderOf y ∣ p * p := hPcard ▸ Subgroup.orderOf_dvd_natCard P hy.1
    have h2 : orderOf y ∣ q := hab ▸ Subgroup.orderOf_dvd_natCard Mab ⟨hPM hy.1, hy.2⟩
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop)
      h2)
  have hPinv : IsInv a b P := ⟨by rw [hPcard]; exact hpodd.mul hpodd, hNP a hM.1.2.1,
    hNP b hM.1.2.2⟩
  have hPa : P ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥ := by
    intro h0
    have : Ma ≤ P ⊓ Subgroup.centralizer ({a} : Set G) := le_inf hMaP inf_le_right
    rw [h0, le_bot_iff] at this
    rw [this, Subgroup.card_bot] at ha
    exact hp.one_lt.ne ha
  obtain ⟨hN, hdec⟩ := h.maxInv_normalizer hT hM hPinv hPa hPab hMP
  have hPabel := commute_of_inf_eq_bot hT.mul_self_mul hPinv.mul_mem hPab
  have hPpg : IsPGroup p P := IsPGroup.of_card (n := 2) (by rw [hPcard, pow_two])
  set S := sylowOfNormalizer P hPpg fun g hg ⟨k, hk⟩ =>
    hPp g (hN g hg (odd_orderOf_of_pow hpodd hk)) ⟨k, hk⟩
  have : IsMulCommutative (S : Subgroup G) :=
    ⟨⟨fun x y => Subtype.ext (hPabel x x.2 y y.2)⟩⟩
  obtain ⟨g, hg⟩ := h.exists_conj_of_good hp35 ha hb hT.1 hT.2.1 inf_le_right inf_le_right
  obtain ⟨y, hy, hy1⟩ := exists_ne_one_of_card ha hp.one_lt
  have hgy : g * y * g⁻¹ ∈ Mb := by
    rw [← hg]
    exact conj_mem_map_conj hy
  obtain ⟨n, hn, hny⟩ := exists_normalizer_conj S (x := y) (g := g) (hMaP hy) (hMbP hgy)
  obtain ⟨m, hm, s, hs, rfl⟩ := hdec n hn
  have hsM := mem_normalizer_of_mem_four hM.1 hs
  have hsa := mem_normalizer_inf_centralizer hsM (commute_of_mem_four hT hs).symm
  set y' := s * y * s⁻¹
  have hy' : y' ∈ Ma := (Subgroup.mem_normalizer_iff.mp hsa y).mp hy
  have hy'1 : y' ≠ 1 := by
    intro h1
    apply hy1
    have := congrArg (fun w => s⁻¹ * w * s) h1
    simpa [y', mul_assoc] using this
  have hMabN : Mab ≤ Subgroup.normalizer (P : Set G) := fun z hz => hMP hz.1
  have hdisj : Disjoint P Mab := by
    rw [disjoint_iff, eq_bot_iff]
    intro w hw
    have : w ∈ P ⊓ Subgroup.centralizer ({a * b} : Set G) := ⟨hw.1, hw.2.2⟩
    rwa [hPab] at this
  have hsup : P ⊔ Mab = M := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hPM inf_le_left)
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P Mab hMabN hdisj, hPcard,
      hab, hMcard]
  have hmPM : m ∈ ((P ⊔ Mab : Subgroup G) : Set G) := by rw [hsup]; exact hm
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P Mab hMabN] at hmPM
  obtain ⟨x, hx, z, hz, rfl⟩ := hmPM
  beta_reduce at hm hn hny ⊢
  have hzy : z * y' * z⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hMabN hz) y').mp (hMaP hy')
  have hc : g * y * g⁻¹ = z * y' * z⁻¹ := by
    rw [← hny, show x * z * s * y * (x * z * s)⁻¹ = x * (z * y' * z⁻¹) * x⁻¹ by
      simp only [y']; group, hPabel x hx _ hzy, mul_inv_cancel_right]
  have hbinv : ∀ X : Subgroup G, X ⊓ Subgroup.centralizer ({b} : Set G) = ⊥ →
      b ∈ Subgroup.normalizer (X : Set G) → ∀ w ∈ X, b * w * b⁻¹ = w⁻¹ :=
    fun X hXb hbX => inv_of_inf_centralizer_eq_bot hT.mul_self_b hbX hXb
  have hfour := h.inf_centralizer_four_eq_bot hT hM.1.1
  have hbz : b * z * b⁻¹ = z⁻¹ := by
    refine hbinv Mab ?_ (mem_normalizer_inf_centralizer hM.1.2.2 ?_) z hz
    · rw [eq_bot_iff]
      intro w hw
      have hwa : w * a = a * w := by
        have h1 : w * (a * b) = (a * b) * w := Subgroup.mem_centralizer_singleton_iff.mp hw.1.2
        have h2 : w * b = b * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
        calc w * a = w * (a * b) * b := by rw [mul_assoc, mul_assoc, hT.mul_self_b, mul_one]
          _ = a * b * w * b := by rw [h1]
          _ = a * (b * w) * b := by group
          _ = a * (w * b) * b := by rw [h2]
          _ = a * w := by rw [mul_assoc, mul_assoc, hT.mul_self_b, mul_one]
      have : w ∈ M ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :=
        ⟨⟨hw.1.1, Subgroup.mem_centralizer_singleton_iff.mpr hwa⟩, hw.2⟩
      rwa [hfour] at this
    · rw [hT.b_mul_mul, mul_assoc, hT.mul_self_b, mul_one]
  have hby : b * y' * b⁻¹ = y'⁻¹ := by
    refine hbinv Ma ?_ (mem_normalizer_inf_centralizer hM.1.2.2 hT.2.2.2) y' hy'
    rw [← hfour]
  have hbc : b * (z * y' * z⁻¹) * b⁻¹ = z * y' * z⁻¹ := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hc ▸ hgy).2
    calc b * (z * y' * z⁻¹) * b⁻¹ = (b * (z * y' * z⁻¹)) * b⁻¹ := rfl
      _ = ((z * y' * z⁻¹) * b) * b⁻¹ := by rw [this]
      _ = z * y' * z⁻¹ := by group
  have hw : (z * z) * y' * (z * z)⁻¹ = y'⁻¹ := by
    have h1 : b * (z * y' * z⁻¹) * b⁻¹ = (b * z * b⁻¹) * (b * y' * b⁻¹) * (b * z * b⁻¹)⁻¹ := by
      group
    rw [hbc, hbz, hby] at h1
    calc (z * z) * y' * (z * z)⁻¹ = z * (z * y' * z⁻¹) * z⁻¹ := by group
      _ = z * (z⁻¹ * y'⁻¹ * z⁻¹⁻¹) * z⁻¹ := by rw [← h1]
      _ = y'⁻¹ := by group
  have hzq : (z * z) ^ q = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, ← hab, pow_card_eq_one_of_mem hz, one_pow]
  have := sq_eq_one_of_conj_inv hqodd hzq hw
  exact hy'1 (eq_one_of_mul_self_of_odd (odd_orderOf_of_mem (by rw [ha]; exact hpodd) hy') this)

include h in
theorem commute_of_central {a b : G} (hT : IsFour a b) {M : Subgroup G} (hM : IsMaxInv a b M)
    {p : ℕ} (hp : p = 3 ∨ p = 5)
    (ha : Nat.card (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = p)
    (hb : Nat.card (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = p)
    (hab : Nat.card (M ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) = p)
    (hcent : ∀ z ∈ M ⊓ Subgroup.centralizer ({a} : Set G), ∀ m ∈ M, z * m = m * z) :
    ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hpodd : Odd p := by rcases hp with rfl | rfl <;> decide
  set Ma := M ⊓ Subgroup.centralizer ({a} : Set G)
  set Mb := M ⊓ Subgroup.centralizer ({b} : Set G)
  have hMcard : Nat.card M = p ^ 3 := by
    rw [h.card_eq_mul hT hM.1, ha, hb, hab, pow_three, mul_assoc]
  have hfour := h.inf_centralizer_four_eq_bot hT hM.1.1
  have hMaodd : Odd (Nat.card Ma) := by rw [ha]; exact hpodd
  have hMbodd : Odd (Nat.card Mb) := by rw [hb]; exact hpodd
  have hMainv : IsInv a b Ma := ⟨hMaodd,
    mem_normalizer_inf_centralizer hM.1.2.1 rfl,
    mem_normalizer_inf_centralizer hM.1.2.2 hT.2.2.2⟩
  have hMaa : Ma ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥ := by
    have hle : Ma ≤ Ma ⊓ Subgroup.centralizer ({a} : Set G) := le_inf le_rfl inf_le_right
    intro h0
    rw [h0, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at ha
    exact hpp.one_lt.ne ha
  have hfour' : ∀ {X : Subgroup G}, X ≤ M →
      X ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({a * b} : Set G) = ⊥ := by
    intro X hX
    rw [eq_bot_iff]
    intro w hw
    have hwb : w * b = b * w := by
      have h1 : w * (a * b) = (a * b) * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
      have h2 : w * a = a * w := Subgroup.mem_centralizer_singleton_iff.mp hw.1.2
      calc w * b = w * (a * (a * b)) := by rw [hT.a_mul_mul]
        _ = a * (w * (a * b)) := by rw [← mul_assoc, h2, mul_assoc]
        _ = a * (a * b * w) := by rw [h1]
        _ = b * w := by rw [← mul_assoc, ← mul_assoc, hT.mul_self_a, one_mul]
    have : w ∈ M ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :=
      ⟨⟨hX hw.1.1, hw.1.2⟩, Subgroup.mem_centralizer_singleton_iff.mpr hwb⟩
    rwa [hfour] at this
  have hMaab : Ma ⊓ Subgroup.centralizer ({a * b} : Set G) = ⊥ := by
    have := hfour' (X := Ma) inf_le_left
    rwa [inf_of_le_left (inf_le_right : Ma ≤ _)] at this
  have hMMa : M ≤ Subgroup.normalizer (Ma : Set G) := by
    intro m hm
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    rw [← hcent z hz m hm, mul_inv_cancel_right]
    exact hz
  obtain ⟨hN₁, -⟩ := h.maxInv_normalizer hT hM hMainv hMaa hMaab hMMa
  obtain ⟨g, hg⟩ := h.exists_conj_of_good hp ha hb hT.1 hT.2.1 inf_le_right inf_le_right
  set Mt := M.map (MulAut.conj g).toMonoidHom
  have hMtcard : Nat.card Mt = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hMcard]
  have hN₂ : ∀ y ∈ Subgroup.normalizer (Mb : Set G), Odd (orderOf y) → y ∈ Mt := by
    intro y hy hyodd
    rw [mem_map_conj]
    refine hN₁ _ (mem_normalizer_of_conj_mem fun x hx => ?_) (by
      rw [show g⁻¹ * y * g = MulAut.conj g⁻¹ y by simp,
        MulEquiv.orderOf_eq]
      exact hyodd)
    have hgx : g * x * g⁻¹ ∈ Mb := by rw [← hg]; exact conj_mem_map_conj hx
    have := (Subgroup.mem_normalizer_iff.mp hy _).mp hgx
    rw [← hg, mem_map_conj] at this
    simpa [mul_assoc] using this
  have hMaN : Ma ≤ Subgroup.normalizer (Mb : Set G) := by
    intro z hz
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    rw [hcent z hz w hw.1, mul_inv_cancel_right]
    exact hw
  have hMaMt : Ma ≤ Mt := fun z hz => hN₂ z (hMaN hz) (odd_orderOf_of_mem hMaodd hz)
  have hMbMt : Mb ≤ Mt := fun z hz => hN₂ z (Subgroup.le_normalizer hz)
    (odd_orderOf_of_mem hMbodd hz)
  set D := Mb ⊔ Ma
  have hdisj : Disjoint Mb Ma := by
    rw [disjoint_iff, eq_bot_iff]
    intro w hw
    have : w ∈ M ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :=
      ⟨hw.2, hw.1.2⟩
    rwa [hfour] at this
  have hDcard : Nat.card D = p * p := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Mb Ma hMaN hdisj, ha, hb]
  have hnormal : ∀ {K : Subgroup G}, Nat.card K = p ^ 3 → D ≤ K →
      K ≤ Subgroup.normalizer (D : Set G) := by
    intro K hK hDK
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hDK]
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hK, hpp.pow_minFac (by norm_num)]
    have := (D.subgroupOf K).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDcard, hK] at this
    have hp0 : 0 < p * p := Nat.mul_pos hpp.pos hpp.pos
    rw [pow_three] at this
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  have hDM : D ≤ M := sup_le inf_le_left inf_le_left
  have hDMt : D ≤ Mt := sup_le hMbMt hMaMt
  have hMD := hnormal hMcard hDM
  have hMtD := hnormal hMtcard hDMt
  have hDinv : IsInv a b D := ⟨by rw [hDcard]; exact hpodd.mul hpodd,
    mem_normalizer_sup (mem_normalizer_inf_centralizer hM.1.2.1 hT.2.2.2.symm) hMainv.2.1,
    mem_normalizer_sup (mem_normalizer_inf_centralizer hM.1.2.2 rfl) hMainv.2.2⟩
  have hDa : D ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥ := by
    intro h0
    have : Ma ≤ D ⊓ Subgroup.centralizer ({a} : Set G) := le_inf le_sup_right inf_le_right
    rw [h0, le_bot_iff] at this
    rw [this, Subgroup.card_bot] at ha
    exact hpp.one_lt.ne ha
  have hDab : D ⊓ Subgroup.centralizer ({a * b} : Set G) = ⊥ := by
    have hBW := h.card_eq_mul hT hDinv
    have h1 : p ≤ Nat.card (D ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
      ha ▸ Subgroup.card_le_of_le (le_inf le_sup_right inf_le_right)
    have h2 : p ≤ Nat.card (D ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) :=
      hb ▸ Subgroup.card_le_of_le (le_inf le_sup_left inf_le_right)
    rw [hDcard] at hBW
    have hpos : 0 < Nat.card (D ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) :=
      Nat.card_pos
    have h3 : Nat.card (D ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) = 1 := by
      by_contra hne
      have h4 : 2 ≤ Nat.card (D ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) := by
        omega
      have : p * p * 2 ≤ p * p := by
        calc p * p * 2 ≤ Nat.card (D ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) *
              Nat.card (D ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) *
              Nat.card (D ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) :=
            Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
          _ = p * p := hBW.symm
      have hp0 : 0 < p * p := Nat.mul_pos hpp.pos hpp.pos
      omega
    exact Subgroup.card_eq_one.mp h3
  obtain ⟨hN₃, -⟩ := h.maxInv_normalizer hT hM hDinv hDa hDab hMD
  have hMtodd : Odd (Nat.card Mt) := by rw [hMtcard]; exact hpodd.pow
  have hMtM : Mt ≤ M := fun y hy => hN₃ y (hMtD hy) (odd_orderOf_of_mem hMtodd hy)
  have hMteq : Mt = M := Subgroup.eq_of_le_of_card_ge hMtM (by rw [hMcard, hMtcard])
  have hcentb : ∀ z ∈ Mb, ∀ m ∈ M, z * m = m * z := by
    intro z hz m hm
    have hz' : g⁻¹ * z * g ∈ Ma := by
      rw [← hg, mem_map_conj] at hz
      exact hz
    have hm' : g⁻¹ * m * g ∈ M := by
      rw [← hMteq, mem_map_conj] at hm
      exact hm
    have := hcent _ hz' _ hm'
    have := congrArg (fun w => g * w * g⁻¹) this
    simpa [mul_assoc] using this
  refine commute_of_central_of_card hpp hDM (by rw [hMcard, hDcard]; ring) ?_
  intro d hd m hm
  set Z := M ⊓ Subgroup.centralizer (M : Set G)
  have hZ : D ≤ Z := sup_le (fun z hz => ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (hcentb z hz w hw).symm⟩)
    (fun z hz => ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun w hw => (hcent z hz w hw).symm⟩)
  exact (Subgroup.mem_centralizer_iff.mp (hZ hd).2 m hm).symm

include h in
theorem exists_central_of_pure {a b : G} (hT : IsFour a b) {M : Subgroup G}
    (hM : IsMaxInv a b M) {p : ℕ} (hp : p = 3 ∨ p = 5) (hMcard : Nat.card M = p ^ 3)
    (ha : Nat.card (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = p)
    (hb : Nat.card (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = p)
    (hab : Nat.card (M ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) = p)
    (hnab : ¬ ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) :
    ∃ x : G, (x = a ∨ x = b ∨ x = a * b) ∧
      ∀ z ∈ M ⊓ Subgroup.centralizer ({x} : Set G), ∀ m ∈ M, z * m = m * z := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hpp⟩
  have hpodd : Odd p := by rcases hp with rfl | rfl <;> decide
  set Z := M ⊓ Subgroup.centralizer (M : Set G)
  have hZcent : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z := fun z hz m hm =>
    (Subgroup.mem_centralizer_iff.mp hz.2 m hm).symm
  have hMp : IsPGroup p M := IsPGroup.of_card hMcard
  have hZ1 : Z ≠ ⊥ := by
    have : Nontrivial M := by
      rw [← Finite.one_lt_card_iff_nontrivial, hMcard]
      exact Nat.one_lt_pow (by norm_num) hpp.one_lt
    have : Nontrivial (Subgroup.center M) := hMp.center_nontrivial
    obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : Subgroup.center M)
    intro h0
    apply hz1
    have hzZ : (z : G) ∈ Z := ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun m hm =>
      (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzc) ⟨m, hm⟩))⟩
    rw [h0, Subgroup.mem_bot] at hzZ
    exact Subtype.ext (Subtype.ext hzZ)
  have hZM : Z ≤ M := inf_le_left
  have hZp : Nat.card Z = p := by
    have hdvd : Nat.card Z ∣ p ^ 3 := hMcard ▸ Subgroup.card_dvd_of_le hZM
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hpp).mp hdvd
    interval_cases k
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hk]; rfl)) hZ1
    · rw [hk, pow_one]
    · exfalso
      exact hnab (commute_of_central_of_card hpp hZM (by rw [hMcard, hk]; ring) hZcent)
    · exfalso
      have hZeq : Z = M := Subgroup.eq_of_le_of_card_ge hZM (by rw [hMcard, hk])
      exact hnab fun x hx y hy => hZcent x (hZeq ▸ hx) y hy
  have hZN : ∀ s ∈ Subgroup.normalizer (M : Set G), s ∈ Subgroup.normalizer (Z : Set G) := by
    intro s hs
    refine mem_normalizer_of_conj_mem fun z hz => ⟨(Subgroup.mem_normalizer_iff.mp hs z).mp hz.1,
      Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
    have hm' : s⁻¹ * m * s ∈ M := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) m).mp hm
      simpa using this
    have := hZcent z hz _ hm'
    calc m * (s * z * s⁻¹) = s * ((s⁻¹ * m * s) * z) * s⁻¹ := by group
      _ = s * (z * (s⁻¹ * m * s)) * s⁻¹ := by rw [this]
      _ = s * z * s⁻¹ * m := by group
  have hZinv : IsInv a b Z := ⟨by rw [hZp]; exact hpodd, hZN a hM.1.2.1, hZN b hM.1.2.2⟩
  have hBW := h.card_eq_mul hT hZinv
  rw [hZp] at hBW
  have hza := h.card_inf_centralizer hT.1 hZinv.1
  have hzb := h.card_inf_centralizer hT.2.1 hZinv.1
  have hzab := h.card_inf_centralizer hT.orderOf_mul hZinv.1
  have key : ∀ x : G, Nat.card (M ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = p →
      Nat.card (Z ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = p →
      ∀ z ∈ M ⊓ Subgroup.centralizer ({x} : Set G), ∀ m ∈ M, z * m = m * z := by
    intro x hMx hx
    have hZx : Z ⊓ Subgroup.centralizer ({x} : Set G) = Z :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hx, hZp])
    have hle : Z ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := by
      rw [← hZx]
      exact inf_le_inf_right _ hZM
    have hZeq : Z = M ⊓ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hMx, hZp])
    intro z hz m hm
    exact hZcent z (hZeq ▸ hz) m hm
  rcases hza with hza | hza | hza <;> rcases hzb with hzb | hzb | hzb <;>
    rcases hzab with hzab | hzab | hzab <;>
    rw [hza, hzb, hzab] at hBW <;> rcases hp with rfl | rfl <;> norm_num at hBW
  all_goals first
    | exact ⟨a, Or.inl rfl, key a ha hza⟩
    | exact ⟨b, Or.inr (Or.inl rfl), key b hb hzb⟩
    | exact ⟨a * b, Or.inr (Or.inr rfl), key (a * b) hab hzab⟩

include h in
theorem abelian_and_card {a b : G} (hT : IsFour a b) {M : Subgroup G} (hM : IsMaxInv a b M) :
    (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) ∧
      (Nat.card M = 1 ∨ Nat.card M = 3 ∨ Nat.card M = 5 ∨ Nat.card M = 15 ∨
        Nat.card M = 27 ∨ Nat.card M = 125) := by
  have hcard := h.card_eq_mul hT hM.1
  have e1 : b * (a * b) = a := hT.b_mul_mul
  have e2 : a * (a * b) = b := hT.a_mul_mul
  have e3 : a * b * a = b := hT.mul_mul_a
  have e4 : b * a = a * b := hT.2.2.2.symm
  have hT1 : IsFour b (a * b) := by have := hT.swap.mul_right; rwa [e4] at this
  have hM1 : IsMaxInv b (a * b) M := by have := hM.swap.mul_right hT.swap; rwa [e4] at this
  have hT2 : IsFour a (a * b) := hT.mul_right
  have hM2 : IsMaxInv a (a * b) M := hM.mul_right hT
  have hT3 : IsFour (a * b) a := hT.mul_right.swap
  have hM3 : IsMaxInv (a * b) a M := (hM.mul_right hT).swap
  have pure : ∀ {p : ℕ}, p = 3 ∨ p = 5 →
      Nat.card (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = p →
      Nat.card (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = p →
      Nat.card (M ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) = p →
      (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) ∧
        (Nat.card M = 1 ∨ Nat.card M = 3 ∨ Nat.card M = 5 ∨ Nat.card M = 15 ∨
          Nat.card M = 27 ∨ Nat.card M = 125) := by
    intro p hp hA hB hC
    have hMcard : Nat.card M = p ^ 3 := by rw [hcard, hA, hB, hC]; ring
    refine ⟨?_, by rcases hp with rfl | rfl <;> rw [hMcard] <;> norm_num⟩
    by_contra hnab
    obtain ⟨x, hx, hcent⟩ := h.exists_central_of_pure hT hM hp hMcard hA hB hC hnab
    rcases hx with rfl | rfl | rfl
    · exact hnab (h.commute_of_central hT hM hp hA hB hC hcent)
    · exact hnab (h.commute_of_central hT.swap hM.swap hp hB hA (by rw [e4]; exact hC) hcent)
    · exact hnab (h.commute_of_central hT3 hM3 hp hC hA (by rw [e3]; exact hB) hcent)
  have hA := h.card_inf_centralizer hT.1 hM.1.1
  have hB := h.card_inf_centralizer hT.2.1 hM.1.1
  have hC := h.card_inf_centralizer hT.orderOf_mul hM.1.1
  rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB <;>
    rcases hC with hC | hC | hC
  all_goals
    have abA := fun (hA : Nat.card (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = 1) =>
      commute_of_inf_eq_bot hT.mul_self_a hM.1.2.1 (Subgroup.card_eq_one.mp hA)
    have abB := fun (hB : Nat.card (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = 1) =>
      commute_of_inf_eq_bot hT.mul_self_b hM.1.2.2 (Subgroup.card_eq_one.mp hB)
    have abC := fun (hC : Nat.card (M ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) =
      1) => commute_of_inf_eq_bot hT.mul_self_mul hM.1.mul_mem (Subgroup.card_eq_one.mp hC)
  ·
    exact ⟨abA hA, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact ⟨abA hA, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact ⟨abA hA, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact ⟨abA hA, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact (h.false_of_two hT1 hM1 (by rw [e1]; exact Subgroup.card_eq_one.mp hA)
      (Or.inl rfl) hB hC).elim
  ·
    exact ⟨abA hA, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact ⟨abA hA, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact ⟨abA hA, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact (h.false_of_two hT1 hM1 (by rw [e1]; exact Subgroup.card_eq_one.mp hA)
      (Or.inr rfl) hB hC).elim
  ·
    exact ⟨abB hB, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact (h.false_of_two hT2 hM2 (by rw [e2]; exact Subgroup.card_eq_one.mp hB)
      (Or.inl rfl) hA hC).elim
  ·
    exact ⟨abB hB, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact (h.false_of_two hT hM (Subgroup.card_eq_one.mp hC) (Or.inl rfl) hA hB).elim
  ·
    exact pure (Or.inl rfl) hA hB hC
  ·
    exact (h.false_of_mixed hT hM (Or.inl ⟨rfl, rfl⟩) hA hB hC).elim
  ·
    exact ⟨abC hC, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact (h.false_of_mixed hT2 hM2 (Or.inl ⟨rfl, rfl⟩) hA hC
      (by rw [e2]; exact hB)).elim
  ·
    exact (h.false_of_mixed hT1 hM1 (Or.inr ⟨rfl, rfl⟩) hB hC
      (by rw [e1]; exact hA)).elim
  ·
    exact ⟨abB hB, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact ⟨abB hB, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact (h.false_of_two hT2 hM2 (by rw [e2]; exact Subgroup.card_eq_one.mp hB)
      (Or.inr rfl) hA hC).elim
  ·
    exact ⟨abC hC, by rw [hcard, hA, hB, hC]; norm_num⟩
  ·
    exact (h.false_of_mixed hT1 hM1 (Or.inl ⟨rfl, rfl⟩) hB hC
      (by rw [e1]; exact hA)).elim
  ·
    exact (h.false_of_mixed hT2 hM2 (Or.inr ⟨rfl, rfl⟩) hA hC
      (by rw [e2]; exact hB)).elim
  ·
    exact (h.false_of_two hT hM (Subgroup.card_eq_one.mp hC) (Or.inr rfl) hA hB).elim
  ·
    exact (h.false_of_mixed hT hM (Or.inr ⟨rfl, rfl⟩) hA hB hC).elim
  ·
    exact pure (Or.inr rfl) hA hB hC

end JankoHyp

end CFSG.Walter.J1
