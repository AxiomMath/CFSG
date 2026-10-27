module

public import CFSG.Walter.J1.Good

public section

namespace CFSG.Walter.J1

variable {G : Type*} [Group G]

theorem conj_eq_of_conj_sq_eq {n x : G} {m : ℕ} (hm : Odd m) (hnm : n ^ m = 1)
    (hx : n * (n * x * n⁻¹) * n⁻¹ = x) : n * x * n⁻¹ = x := by
  have hpow : ∀ k : ℕ, n ^ (2 * k) * x * (n ^ (2 * k))⁻¹ = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_two]
      calc n ^ (2 * k) * (n * n) * x * (n ^ (2 * k) * (n * n))⁻¹ =
          n ^ (2 * k) * (n * (n * x * n⁻¹) * n⁻¹) * (n ^ (2 * k))⁻¹ := by group
        _ = x := by rw [hx, ih]
  obtain ⟨k, rfl⟩ := hm
  calc n * x * n⁻¹ = n * (n ^ (2 * k) * x * (n ^ (2 * k))⁻¹) * n⁻¹ := by rw [hpow]
    _ = n ^ (2 * k + 1) * x * (n ^ (2 * k + 1))⁻¹ := by rw [pow_succ']; group
    _ = x := by rw [hnm]; group

theorem cycle_of_odd {a b n : G} (hT : IsFour a b) {m : ℕ} (hm : Odd m) (hnm : n ^ m = 1)
    (hnT : ∀ x, x = a ∨ x = b → n * x * n⁻¹ = a * b ∨ n * x * n⁻¹ = a ∨ n * x * n⁻¹ = b)
    (hnc : ¬ (n * a * n⁻¹ = a ∧ n * b * n⁻¹ = b)) :
    (n * a * n⁻¹ = b ∧ n * b * n⁻¹ = a * b) ∨ (n * a * n⁻¹ = a * b ∧ n * b * n⁻¹ = a) := by
  have hinj : ∀ x y : G, n * x * n⁻¹ = n * y * n⁻¹ → x = y := fun x y hxy => by
    simpa using hxy
  have hconj_mul : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
  rcases hnT a (Or.inl rfl) with h1 | h1 | h1 <;> rcases hnT b (Or.inr rfl) with h2 | h2 | h2
  · exact absurd (hinj _ _ (h1.trans h2.symm)) hT.2.2.1
  · exact Or.inr ⟨h1, h2⟩
  ·
    exfalso
    have h3 : n * (a * b) * n⁻¹ = a := by
      rw [hconj_mul, h1, h2, mul_assoc, hT.mul_self_b, mul_one]
    have := conj_eq_of_conj_sq_eq hm hnm (x := a) (by rw [h1, h3])
    exact hT.mul_ne_a (h1.symm.trans this)
  ·
    exfalso
    have h3 : n * (a * b) * n⁻¹ = b := by
      rw [hconj_mul, h1, h2, hT.a_mul_mul]
    have := conj_eq_of_conj_sq_eq hm hnm (x := b) (by rw [h2, h3])
    exact hT.mul_ne_b (h2.symm.trans this)
  · exact absurd (hinj _ _ (h1.trans h2.symm)) hT.2.2.1
  · exact absurd ⟨h1, h2⟩ hnc
  · exact Or.inl ⟨h1, h2⟩
  ·
    exfalso
    have := conj_eq_of_conj_sq_eq hm hnm (x := a) (by rw [h1, h2])
    exact hT.2.2.1 (this.symm.trans h1)
  · exact absurd (hinj _ _ (h1.trans h2.symm)) hT.2.2.1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem false_of_burnside {a b : G} (hT : IsFour a b) {M : Subgroup G} (hM : IsInv a b M)
    {p : ℕ} (hp : p = 3 ∨ p = 5) (hMp : IsPGroup p M) (habel : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (ha : Nat.card (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = p)
    (hb : Nat.card (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = p)
    (hN : ∀ g ∈ Subgroup.normalizer (M : Set G), Odd (orderOf g) → g ∈ M)
    (hdec : ∀ g ∈ Subgroup.normalizer (M : Set G), ∃ m ∈ M, ∃ s : G,
      (s = 1 ∨ s = a ∨ s = b ∨ s = a * b) ∧ g = m * s) : False := by
  have hpp := prime_of_three_or_five hp
  have : Fact p.Prime := ⟨hpp⟩
  have hpodd := odd_of_three_or_five hp
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
  have hsM := mem_normalizer_of_mem_four hM hs
  have hsa := mem_normalizer_inf_centralizer hsM (commute_of_mem_four hT hs).symm
  have hsy : s * y * s⁻¹ ∈ M ⊓ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hsa y).mp hy
  have hmy : m * s * y * (m * s)⁻¹ = s * y * s⁻¹ := by
    rw [show m * s * y * (m * s)⁻¹ = m * (s * y * s⁻¹) * m⁻¹ by group,
      habel m hm _ hsy.1, mul_inv_cancel_right]
  rw [hmy] at hny
  have h0 : g * y * g⁻¹ ∈ M ⊓ Subgroup.centralizer ({a} : Set G) ⊓
      Subgroup.centralizer ({b} : Set G) := ⟨by rw [← hny]; exact hsy, hgy.2⟩
  rw [h.inf_centralizer_four_eq_bot hT hM.1, Subgroup.mem_bot] at h0
  apply hy1
  have := congrArg (fun w => g⁻¹ * w * g) h0
  simpa [mul_assoc] using this

include h in
theorem exists_not_commute_normalizer {a b : G} (hT : IsFour a b) {M : Subgroup G}
    (hM : IsMaxInv a b M) {p : ℕ} (hp : p = 3 ∨ p = 5) (hMp : IsPGroup p M)
    (habel : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (ha : Nat.card (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = p)
    (hb : Nat.card (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = p) :
    ∃ n ∈ Subgroup.normalizer (M : Set G),
      n ∈ Subgroup.normalizer ((GorensteinWalter.kleinFourOfCommutingInvolutions a b
        hT.mul_self_a hT.mul_self_b hT.2.2.2 : Subgroup G) : Set G) ∧
      ¬ (n * a = a * n ∧ n * b = b * n) := by
  classical
  by_contra hcon
  push Not at hcon
  set K := Subgroup.normalizer (M : Set G)
  set T := GorensteinWalter.kleinFourOfCommutingInvolutions a b hT.mul_self_a hT.mul_self_b
    hT.2.2.2
  have hT4 : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    a b hT.mul_self_a hT.mul_self_b hT.a_ne_one hT.b_ne_one hT.2.2.1 _
  have hpp := prime_of_three_or_five hp
  have hM1 : M ≠ ⊥ := by
    intro h0
    have : M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by rw [h0, bot_inf_eq]
    rw [this, Subgroup.card_bot] at ha
    exact hpp.one_lt.ne ha
  have hTK : T ≤ K := kleinFour_le_normalizer hT hM.1
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4.card_four]; norm_num)
  obtain ⟨O, hOK, hON, hO2, hOcard, hOodd⟩ := exists_odd_complement hTK hT2
    (by
      intro R hRK hR2 hTR
      have h4 := h.card_dvd_four_of_le_normalizer hM.1.1 hM1 hR2 hRK
      exact (Subgroup.eq_of_le_of_card_ge hTR (by
        rw [hT4.card_four]; exact Nat.le_of_dvd (by norm_num) h4)).symm)
    (by
      intro n hn hnT x hx
      obtain ⟨h1, h2⟩ := hcon n hn hnT
      rcases (mem_kleinFour_iff hT.mul_self_a hT.mul_self_b hT.2.2.2).mp hx with
        rfl | rfl | rfl | rfl
      · rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
      · exact h1
      · exact h2
      · simp)
  rw [hT4.card_four] at hOcard
  obtain ⟨hN, hdec⟩ := maxInv_of_complement hT hM hM.1 Subgroup.le_normalizer hOK hON hO2
    hOcard hOodd
  exact h.false_of_burnside hT hM.1 hp hMp habel ha hb hN hdec

include h in
theorem sq_eq_one_of_commute_four {a b x : G} (hT : IsFour a b) (hxa : x * a = a * x)
    (hxb : x * b = b * x) : x * x = 1 := by
  have hn0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨e, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hodd : x ^ 2 ^ e = 1 := by
    have h1 : Odd (orderOf (x ^ 2 ^ e)) := by
      rw [orderOf_pow' x (pow_ne_zero _ two_ne_zero), hxm, Nat.gcd_mul_right_left]
      rw [Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
      exact hm
    exact h.eq_one_of_commute_four hT.1 hT.2.1 hT.2.2.1 hT.2.2.2 h1
      ((Commute.pow_left hxa _).eq) ((Commute.pow_left hxb _).eq)
  exact h.sq_eq_one_of_pow hodd

include h in
theorem exists_nu {a b : G} (hT : IsFour a b) {M : Subgroup G}
    (hM : IsMaxInv a b M) {p : ℕ} (hp : p = 3 ∨ p = 5) (hMp : IsPGroup p M)
    (habel : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (ha : Nat.card (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = p)
    (hb : Nat.card (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = p) :
    ∃ ν ∈ Subgroup.normalizer (M : Set G), orderOf ν = 3 ∧
      ((ν * a * ν⁻¹ = b ∧ ν * b * ν⁻¹ = a * b) ∨
        (ν * a * ν⁻¹ = a * b ∧ ν * b * ν⁻¹ = a)) := by
  obtain ⟨n, hnM, hnT, hnc⟩ := h.exists_not_commute_normalizer hT hM hp hMp habel ha hb
  set T := GorensteinWalter.kleinFourOfCommutingInvolutions a b hT.mul_self_a hT.mul_self_b
    hT.2.2.2
  have hT4 : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    a b hT.mul_self_a hT.mul_self_b hT.a_ne_one hT.b_ne_one hT.2.2.1 _
  have hmemT := fun x => mem_kleinFour_iff (x := x) hT.mul_self_a hT.mul_self_b hT.2.2.2
  have hn0 : orderOf n ≠ 0 := (orderOf_pos n).ne'
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  set ν := n ^ 2 ^ e
  have hνm : ν ^ m = 1 := by rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hνM : ν ∈ Subgroup.normalizer (M : Set G) := Subgroup.pow_mem _ hnM _
  have hνT : ν ∈ Subgroup.normalizer (T : Set G) := Subgroup.pow_mem _ hnT _
  have hconjT : ∀ y ∈ Subgroup.normalizer (T : Set G), ∀ x, x = a ∨ x = b →
      y * x * y⁻¹ = a * b ∨ y * x * y⁻¹ = a ∨ y * x * y⁻¹ = b := by
    intro y hy x hx
    have hxT : x ∈ T := by
      rcases hx with rfl | rfl
      · exact (hmemT _).mpr (Or.inr (Or.inl rfl))
      · exact (hmemT _).mpr (Or.inr (Or.inr (Or.inl rfl)))
    have hx1 : x ≠ 1 := by rcases hx with rfl | rfl; exacts [hT.a_ne_one, hT.b_ne_one]
    rcases (hmemT _).mp ((Subgroup.mem_normalizer_iff.mp hy x).mp hxT) with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
    · exfalso
      apply hx1
      have := congrArg (fun z => y⁻¹ * z * y) h1
      simpa [mul_assoc] using this
  have hνc : ¬ (ν * a * ν⁻¹ = a ∧ ν * b * ν⁻¹ = b) := by
    rintro ⟨h1, h2⟩
    apply hnc
    set n₂ := n ^ m
    have hn₂ : n₂ ^ 2 ^ e = 1 := by rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
    have hM1 : M ≠ ⊥ := by
      intro h0
      have : M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by rw [h0, bot_inf_eq]
      rw [this, Subgroup.card_bot] at ha
      exact (prime_of_three_or_five hp).one_lt.ne ha
    have hn₂T : n₂ ∈ T := by
      have hZ : IsPGroup 2 (Subgroup.zpowers n₂) := by
        have hdvd : orderOf n₂ ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hn₂
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
      have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4.card_four]; norm_num)
      have hR := IsPGroup.to_sup_of_normal_left' hT2 hZ (by
        rw [Subgroup.zpowers_le]
        exact Subgroup.pow_mem _ hnT _)
      have hRK : T ⊔ Subgroup.zpowers n₂ ≤ Subgroup.normalizer (M : Set G) :=
        sup_le (kleinFour_le_normalizer hT hM.1) ((Subgroup.zpowers_le).mpr
          (Subgroup.pow_mem _ hnM _))
      have h4 := h.card_dvd_four_of_le_normalizer hM.1.1 hM1 hR hRK
      have heq : T ⊔ Subgroup.zpowers n₂ = T := (Subgroup.eq_of_le_of_card_ge le_sup_left (by
        rw [hT4.card_four]; exact Nat.le_of_dvd (by norm_num) h4)).symm
      rw [← heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hn₂c : ∀ y ∈ T, n₂ * y = y * n₂ := fun y hy =>
      congrArg Subtype.val (hT4.isMulCommutative.is_comm.comm ⟨n₂, hn₂T⟩ ⟨y, hy⟩)
    have hcop : Nat.Coprime m (2 ^ e) := Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hm)
    have hbez : (1 : ℤ) = m * m.gcdA (2 ^ e) + 2 ^ e * m.gcdB (2 ^ e) := by
      have := Nat.gcd_eq_gcd_ab m (2 ^ e)
      rw [hcop.gcd_eq_one] at this
      exact_mod_cast this
    have hn : n = n₂ ^ m.gcdA (2 ^ e) * ν ^ m.gcdB (2 ^ e) := by
      calc n = n ^ (1 : ℤ) := (zpow_one n).symm
        _ = n ^ ((m : ℤ) * m.gcdA (2 ^ e) + (2 ^ e : ℕ) * m.gcdB (2 ^ e)) := by
          rw [hbez]; push_cast; ring_nf
        _ = n₂ ^ m.gcdA (2 ^ e) * ν ^ m.gcdB (2 ^ e) := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    have hνa : ν * a = a * ν := by
      calc ν * a = (ν * a * ν⁻¹) * ν := by group
        _ = a * ν := by rw [h1]
    have hνb : ν * b = b * ν := by
      calc ν * b = (ν * b * ν⁻¹) * ν := by group
        _ = b * ν := by rw [h2]
    have haT : a ∈ T := (hmemT _).mpr (Or.inr (Or.inl rfl))
    have hbT : b ∈ T := (hmemT _).mpr (Or.inr (Or.inr (Or.inl rfl)))
    rw [hn]
    exact ⟨((Commute.zpow_left (hn₂c a haT) _).mul_left (Commute.zpow_left hνa _)).eq,
      ((Commute.zpow_left (hn₂c b hbT) _).mul_left (Commute.zpow_left hνb _)).eq⟩
  have hcyc := cycle_of_odd hT hm hνm (hconjT ν hνT) hνc
  have hν3 : ν ^ 3 = 1 := by
    have hodd3 : Odd (orderOf (ν ^ 3)) := by
      refine Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)
      rw [← pow_mul, mul_comm, pow_mul, hνm, one_pow]
    have hconj3 : ∀ x, ν * (ν * (ν * x * ν⁻¹) * ν⁻¹) * ν⁻¹ = ν ^ 3 * x * (ν ^ 3)⁻¹ := by
      intro x; rw [pow_three]; group
    have hab : ν * (a * b) * ν⁻¹ = (ν * a * ν⁻¹) * (ν * b * ν⁻¹) := by group
    have h3a : ν ^ 3 * a * (ν ^ 3)⁻¹ = a := by
      rw [← hconj3]
      rcases hcyc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hab, h1, h2, hT.b_mul_mul]
      · rw [h1, hab, h1, h2, hT.mul_mul_a, h2]
    have h3b : ν ^ 3 * b * (ν ^ 3)⁻¹ = b := by
      rw [← hconj3]
      rcases hcyc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, hab, h1, h2, hT.b_mul_mul, h1]
      · rw [h2, h1, hab, h1, h2, hT.mul_mul_a]
    have hca : ν ^ 3 * a = a * ν ^ 3 := by
      calc ν ^ 3 * a = (ν ^ 3 * a * (ν ^ 3)⁻¹) * ν ^ 3 := by group
        _ = a * ν ^ 3 := by rw [h3a]
    have hcb : ν ^ 3 * b = b * ν ^ 3 := by
      calc ν ^ 3 * b = (ν ^ 3 * b * (ν ^ 3)⁻¹) * ν ^ 3 := by group
        _ = b * ν ^ 3 := by rw [h3b]
    exact h.eq_one_of_commute_four hT.1 hT.2.1 hT.2.2.1 hT.2.2.2 hodd3 hca hcb
  have hν1 : ν ≠ 1 := by
    rintro h1
    apply hνc
    rw [h1]
    simp
  exact ⟨ν, hνM, orderOf_eq_prime hν3 hν1, hcyc⟩

include h in
theorem exists_involution_commute {a b ν : G} (hT : IsFour a b) (hν : orderOf ν = 3)
    (hνT : ν ∈ Subgroup.normalizer ((GorensteinWalter.kleinFourOfCommutingInvolutions a b
      hT.mul_self_a hT.mul_self_b hT.2.2.2 : Subgroup G) : Set G)) :
    ∃ s : G, orderOf s = 2 ∧ s * a = a * s ∧ s * b = b * s ∧ s * ν = ν * s := by
  classical
  set T := GorensteinWalter.kleinFourOfCommutingInvolutions a b hT.mul_self_a hT.mul_self_b
    hT.2.2.2
  have hmemT := fun x => mem_kleinFour_iff (x := x) hT.mul_self_a hT.mul_self_b hT.2.2.2
  have haT : a ∈ T := (hmemT _).mpr (Or.inr (Or.inl rfl))
  have hbT : b ∈ T := (hmemT _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  set K := Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)
  have hK2 : IsPGroup 2 K := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have hxa : x.1 * a = a * x.1 := Subgroup.mem_centralizer_singleton_iff.mp x.2.1
    have hxb : x.1 * b = b * x.1 := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
    simpa [pow_two] using h.sq_eq_one_of_commute_four hT hxa hxb
  obtain ⟨S, hKS⟩ := hK2.exists_le_sylow
  have hTS : (Subgroup.zpowers a) ≤ (S : Subgroup G) := by
    rw [Subgroup.zpowers_le]
    exact hKS ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
      Subgroup.mem_centralizer_singleton_iff.mpr hT.2.2.2⟩
  have hSab := h.abelian_sylow S
  have hSK : (S : Subgroup G) ≤ K := by
    intro x hx
    have haS : a ∈ S := hTS (Subgroup.mem_zpowers a)
    have hbS : b ∈ S := hKS ⟨Subgroup.mem_centralizer_singleton_iff.mpr hT.2.2.2.symm,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hSab.is_comm.comm ⟨x, hx⟩ ⟨a, haS⟩)),
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hSab.is_comm.comm ⟨x, hx⟩ ⟨b, hbS⟩))⟩
  have hK8 : Nat.card K = 8 := by
    rw [le_antisymm hKS hSK, h.card_sylow' S]
  have hνK : ν ∈ Subgroup.normalizer (K : Set G) := by
    have hinvT : ν⁻¹ ∈ Subgroup.normalizer (T : Set G) := Subgroup.inv_mem _ hνT
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have hx' : ∀ y ∈ T, x * y = y * x := by
      intro y hy
      rcases (hmemT y).mp hy with rfl | rfl | rfl | rfl
      · have hxa := Subgroup.mem_centralizer_singleton_iff.mp hx.1
        have hxb := Subgroup.mem_centralizer_singleton_iff.mp hx.2
        rw [← mul_assoc, hxa, mul_assoc, hxb, mul_assoc]
      · exact Subgroup.mem_centralizer_singleton_iff.mp hx.1
      · exact Subgroup.mem_centralizer_singleton_iff.mp hx.2
      · simp
    have key : ∀ y ∈ T, ν * x * ν⁻¹ * y = y * (ν * x * ν⁻¹) := by
      intro y hy
      have hy' : ν⁻¹ * y * ν ∈ T := by
        have := (Subgroup.mem_normalizer_iff.mp hinvT y).mp hy
        simpa using this
      have := hx' _ hy'
      calc ν * x * ν⁻¹ * y = ν * (x * (ν⁻¹ * y * ν)) * ν⁻¹ := by group
        _ = ν * ((ν⁻¹ * y * ν) * x) * ν⁻¹ := by rw [this]
        _ = y * (ν * x * ν⁻¹) := by group
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (key a haT),
      Subgroup.mem_centralizer_singleton_iff.mpr (key b hbT)⟩
  set V := Subgroup.zpowers ν
  have hVK : V ≤ Subgroup.normalizer (K : Set G) := (Subgroup.zpowers_le).mpr hνK
  let := conjAct V K hVK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV3 : IsPGroup 3 V := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hν, pow_one])
  have hmod := hV3.card_modEq_card_fixedPoints K
  rw [hK8] at hmod
  have hfix2 : 2 ≤ Nat.card (MulAction.fixedPoints V K) := by
    have : Nat.card (MulAction.fixedPoints V K) % 3 = 2 := by
      have := hmod.symm
      unfold Nat.ModEq at this
      omega
    omega
  obtain ⟨k, hk, hk1⟩ : ∃ k ∈ MulAction.fixedPoints V K, k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : MulAction.fixedPoints V K ⊆ {1} := fun k hk => hcon k hk
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq] at this
    omega
  refine ⟨k, ?_, Subgroup.mem_centralizer_singleton_iff.mp k.2.1,
    Subgroup.mem_centralizer_singleton_iff.mp k.2.2, ?_⟩
  · refine (orderOf_eq_two_iff).mpr ⟨?_, fun h1 => hk1 (Subtype.ext h1)⟩
    exact h.sq_eq_one_of_commute_four hT (Subgroup.mem_centralizer_singleton_iff.mp k.2.1)
      (Subgroup.mem_centralizer_singleton_iff.mp k.2.2)
  · have := congrArg Subtype.val (hk ⟨ν, Subgroup.mem_zpowers ν⟩)
    change ν * k * ν⁻¹ = k at this
    calc (k : G) * ν = (ν * k * ν⁻¹)⁻¹⁻¹ * ν := by rw [this, inv_inv]
      _ = ν * k := by group

end JankoHyp

end CFSG.Walter.J1
