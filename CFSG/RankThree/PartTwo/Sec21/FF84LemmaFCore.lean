module

public import CFSG.Quasithin.H13.GoldschmidtC137S168Syl

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open scoped Pointwise

section Core

variable {C : Type*} [CommGroup C]

private theorem hbn (a b : MulAut C) (hba : b * a = a ^ 2 * b) :
    ∀ n : ℕ, b * a ^ n = a ^ (2 * n) * b := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc b * a ^ (n + 1) = (b * a ^ n) * a := by rw [pow_succ, mul_assoc]
      _ = a ^ (2 * n) * (b * a) := by rw [ih, mul_assoc]
      _ = a ^ (2 * (n + 1)) * b := by
        rw [hba, ← mul_assoc, ← pow_add]
        congr 2

private theorem hbn2 (a b : MulAut C) (hba : b * a = a ^ 2 * b) :
    ∀ n : ℕ, b ^ 2 * a ^ n = a ^ (4 * n) * b ^ 2 := by
  intro n
  have h := hbn a b hba n
  have h2 := hbn a b hba (2 * n)
  calc b ^ 2 * a ^ n = b * (b * a ^ n) := by rw [pow_two, mul_assoc]
    _ = b * (a ^ (2 * n) * b) := by rw [h]
    _ = (b * a ^ (2 * n)) * b := by rw [mul_assoc]
    _ = a ^ (2 * (2 * n)) * b * b := by rw [h2]
    _ = a ^ (4 * n) * b ^ 2 := by
      rw [mul_assoc, ← pow_two]
      congr 2
      ring

private theorem prod_perm (f : ℕ → C) (m : ℕ) (hm : ∀ b < 7, ∃ k < 7, m * k % 7 = b)
    (hinj : ∀ x < 7, ∀ y < 7, m * x % 7 = m * y % 7 → x = y)
    (hf : ∀ n, f n = f (n % 7)) :
    ∏ k ∈ Finset.range 7, f (m * k) = ∏ k ∈ Finset.range 7, f k := by
  refine Finset.prod_nbij (fun k => m * k % 7) ?_ ?_ ?_ ?_
  · intro k _; simp only [Finset.mem_range]; omega
  · intro x hx y hy h
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    exact hinj x hx y hy h
  · intro b hb
    simp only [Finset.coe_range, Set.mem_Iio] at hb
    obtain ⟨k, hk, hkb⟩ := hm b hb
    exact ⟨k, by simpa using hk, hkb⟩
  · intro k _; exact hf _

theorem eq_one_of_frobenius (hC : ∀ c : C, c * c = 1) (a b : MulAut C)
    (ha : a ^ 7 = 1) (hb : b ^ 3 = 1) (hba : b * a = a ^ 2 * b)
    (hfpf : ∀ c : C, b c = c → c = 1) : a = 1 := by
  have hmod : ∀ n : ℕ, a ^ n = a ^ (n % 7) := fun n => pow_eq_pow_mod n ha
  have happ : ∀ (f g : MulAut C) (c : C), f (g c) = (f * g) c := fun _ _ _ => rfl
  have hE : ∀ v : C, v * b v * (b ^ 2) v = 1 := by
    intro v
    apply hfpf
    have h3 : (b ^ 3) v = v := by rw [hb]; rfl
    have e1 : b ((b ^ 2) v) = v := by
      rw [happ, ← pow_succ']; exact h3
    have e2 : b (b v) = (b ^ 2) v := by rw [pow_two]; rfl
    rw [map_mul, map_mul, e1, e2]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  have hk1 : ∀ k : ℕ, a ^ k * b * a ^ (6 * k) = a ^ (6 * k) * b := by
    intro k
    rw [mul_assoc, hbn a b hba (6 * k), ← mul_assoc, ← pow_add]
    have : a ^ (k + 2 * (6 * k)) = a ^ (6 * k) := by
      rw [hmod, hmod (6 * k)]; congr 1; omega
    rw [this]
  have hk2 : ∀ k : ℕ, a ^ k * b ^ 2 * a ^ (6 * k) = a ^ (4 * k) * b ^ 2 := by
    intro k
    rw [mul_assoc, hbn2 a b hba (6 * k), ← mul_assoc, ← pow_add]
    have : a ^ (k + 4 * (6 * k)) = a ^ (4 * k) := by
      rw [hmod, hmod (4 * k)]; congr 1; omega
    rw [this]
  have hEk : ∀ (c : C) (k : ℕ),
      c * (a ^ (6 * k)) (b c) * (a ^ (4 * k)) ((b ^ 2) c) = 1 := by
    intro c k
    have h := hE ((a ^ (6 * k)) c)
    have h' := congrArg (fun x => (a ^ k) x) h
    simp only [map_mul, map_one] at h'
    have e0 : (a ^ k) ((a ^ (6 * k)) c) = c := by
      have : a ^ k * a ^ (6 * k) = 1 := by
        rw [← pow_add, hmod]
        have : (k + 6 * k) % 7 = 0 := by omega
        rw [this]; simp
      have := congrArg (fun f : MulAut C => f c) this
      exact this
    have e1 : (a ^ k) (b ((a ^ (6 * k)) c)) = (a ^ (6 * k)) (b c) :=
      congrArg (fun f : MulAut C => f c) (hk1 k)
    have e2 : (a ^ k) ((b ^ 2) ((a ^ (6 * k)) c)) = (a ^ (4 * k)) ((b ^ 2) c) :=
      congrArg (fun f : MulAut C => f c) (hk2 k)
    rw [e0, e1, e2] at h'
    exact h'
  have hf : ∀ w : C, ∀ n : ℕ, (a ^ n) w = (a ^ (n % 7)) w := fun w n => by rw [← hmod n]
  have hperm : ∀ (w : C) (m : ℕ), (∀ b < 7, ∃ k < 7, m * k % 7 = b) →
      (∀ x < 7, ∀ y < 7, m * x % 7 = m * y % 7 → x = y) →
      ∏ k ∈ Finset.range 7, (a ^ (m * k)) w = ∏ k ∈ Finset.range 7, (a ^ k) w :=
    fun w m h1 h2 => prod_perm (fun n => (a ^ n) w) m h1 h2 (hf w)
  have h6 : ∀ w : C, ∏ k ∈ Finset.range 7, (a ^ (6 * k)) w = ∏ k ∈ Finset.range 7, (a ^ k) w :=
    fun w => hperm w 6 (by decide) (by decide)
  have h4 : ∀ w : C, ∏ k ∈ Finset.range 7, (a ^ (4 * k)) w = ∏ k ∈ Finset.range 7, (a ^ k) w :=
    fun w => hperm w 4 (by decide) (by decide)
  set P : C → C := fun w => ∏ k ∈ Finset.range 7, (a ^ k) w with hP
  have hPmul : ∀ x y : C, P (x * y) = P x * P y := by
    intro x y
    simp only [hP, map_mul, Finset.prod_mul_distrib]
  have hc7 : ∀ c : C, c ^ 7 = c := by
    intro c
    rw [show (7 : ℕ) = 2 * 3 + 1 from rfl, pow_succ, pow_mul, pow_two, hC c, one_pow, one_mul]
  have hfix : ∀ c : C, c = P c := by
    intro c
    have hprod : ∏ k ∈ Finset.range 7,
        (c * (a ^ (6 * k)) (b c) * (a ^ (4 * k)) ((b ^ 2) c)) = 1 :=
      Finset.prod_eq_one (fun k _ => hEk c k)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range, h6, h4, hc7] at hprod
    have hall : P c * P (b c) * P ((b ^ 2) c) = 1 := by
      rw [← hPmul, ← hPmul, hE c]
      simp [hP]
    have h1 : c * (P (b c) * P ((b ^ 2) c)) = 1 := by rw [← mul_assoc]; exact hprod
    have h2 : P c * (P (b c) * P ((b ^ 2) c)) = 1 := by rw [← mul_assoc]; exact hall
    exact mul_right_cancel (h1.trans h2.symm)
  have hafix : ∀ c : C, a (P c) = P c := by
    intro c
    have hshift : a (P c) = ∏ k ∈ Finset.range 7, (a ^ (k + 1)) c := by
      simp only [hP, map_prod]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      rw [pow_succ']; rfl
    rw [hshift]
    set f : ℕ → C := fun n => (a ^ n) c with hf'
    have h8a : ∏ k ∈ Finset.range 8, f k = (∏ k ∈ Finset.range 7, f k) * f 7 :=
      Finset.prod_range_succ f 7
    have h8b : ∏ k ∈ Finset.range 8, f k = (∏ k ∈ Finset.range 7, f (k + 1)) * f 0 :=
      Finset.prod_range_succ' f 7
    have h70 : f 7 = f 0 := by simp [hf', ha]
    rw [h70] at h8a
    exact mul_right_cancel (h8b.symm.trans h8a)
  ext c
  have : a c = c := by
    calc a c = a (P c) := by rw [← hfix c]
      _ = P c := hafix c
      _ = c := (hfix c).symm
  simpa using this

end Core

section Simple168

variable {S : Type} [Group S] [Finite S]

private theorem exists_sylow_three_eq_zpowers (hcard : Nat.card S = 168) {g : S}
    (hg : orderOf g = 3) : ∃ Q : Sylow 3 S, (Q : Subgroup S) = Subgroup.zpowers g := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hz : Nat.card (Subgroup.zpowers g) = 3 ^ 1 := by rw [Nat.card_zpowers, hg]; rfl
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hz).exists_le_sylow
  refine ⟨Q, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge hQ ?_
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 Q.isPGroup'
  have hdvd : Nat.card (Q : Subgroup S) ∣ 168 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  rw [hn] at hdvd ⊢
  rw [hz]
  have hn1 : n ≤ 1 := by
    by_contra hlt
    have h2 : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    have := h2.trans hdvd
    omega
  exact Nat.pow_le_pow_right (by norm_num) hn1

theorem exists_frobenius_pair [IsSimpleGroup S] (hcard : Nat.card S = 168) {y : S}
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    ∃ d η : S, (η = y ∨ η = y⁻¹) ∧ d ^ 7 = 1 ∧ d ≠ 1 ∧ η * d * η⁻¹ = d ^ 2 := by
  obtain ⟨x, y0, -, -, hxo, hy0o, hrel⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.S168.exists_frobenius hcard
      (Classical.choice (Sylow.nonempty (p := 7) (G := S)))
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨Q0, hQ0⟩ := exists_sylow_three_eq_zpowers hcard hy0o
  obtain ⟨Q1, hQ1⟩ := exists_sylow_three_eq_zpowers hcard hyo
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq S Q0 Q1
  have hyQ1 : y ∈ (Q1 : Subgroup S) := hQ1 ▸ Subgroup.mem_zpowers y
  have hc : (Q1 : Subgroup S) = MulAut.conj h • (Q0 : Subgroup S) := by
    rw [← hh]; exact Sylow.coe_subgroup_smul
  have hmem : y ∈ MulAut.conj h • (Q0 : Subgroup S) := by rw [← hc]; exact hyQ1
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hQ0] at hmem
  have e : (MulAut.conj h)⁻¹ • y = h⁻¹ * y * h := by
    simp [MulAut.smul_def]
  rw [e] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hy : y = (h * y0 * h⁻¹) ^ k := by
    rw [conj_zpow, hk]; group
  set y1 : S := h * y0 * h⁻¹ with hy1def
  set d1 : S := h * x * h⁻¹ with hd1def
  have hy0three : y0 ^ 3 = 1 := hy0o ▸ pow_orderOf_eq_one y0
  have hx7 : x ^ 7 = 1 := hxo ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hxo; omega
  have hy13 : y1 ^ 3 = 1 := by
    rw [hy1def, conj_pow, hy0three]; group
  have hy1ne : y1 ≠ 1 := by
    intro h1
    have : y0 = 1 := by
      have h2 : h * y0 * h⁻¹ = h * 1 * h⁻¹ := by rw [← hy1def, h1]; group
      simpa using h2
    rw [this, orderOf_one] at hy0o; omega
  have hy1o : orderOf y1 = 3 := orderOf_eq_prime hy13 hy1ne
  refine ⟨d1, y1, ?_, ?_, ?_, ?_⟩
  · have hm := zpow_mod_orderOf y1 k
    rw [hy1o] at hm
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · exfalso; apply hy1; rw [hy, ← hm]; simp [h0]
    · left; rw [hy, ← hm]; simp [h1]
    · right
      have h2' : y1 ^ 2 = y1⁻¹ := by
        have : y1 ^ 2 * y1 = 1 := by rw [← pow_succ]; exact hy13
        exact eq_inv_of_mul_eq_one_left this
      rw [hy, ← hm]; simp [h2, h2']
  · rw [hd1def, conj_pow, hx7]; group
  · intro h1
    apply hx1
    have : h * x * h⁻¹ = h * 1 * h⁻¹ := by rw [← hd1def, h1]; group
    simpa using this
  · rw [hy1def, hd1def]
    calc h * y0 * h⁻¹ * (h * x * h⁻¹) * (h * y0 * h⁻¹)⁻¹ = h * (y0 * x * y0⁻¹) * h⁻¹ := by group
      _ = h * x ^ 2 * h⁻¹ := by rw [hrel]
      _ = (h * x * h⁻¹) ^ 2 := by rw [conj_pow]

theorem eq_one_of_fixedPointFree_simple168 [IsSimpleGroup S] (hcard : Nat.card S = 168)
    {C : Type*} [CommGroup C] (hC : ∀ c : C, c * c = 1) (ρ : S →* MulAut C) {y : S}
    (hy3 : y ^ 3 = 1) (hfpf : ∀ c : C, ρ y c = c → c = 1) : ∀ c : C, c = 1 := by
  by_cases hy1 : y = 1
  · intro c; apply hfpf; rw [hy1, map_one]; rfl
  obtain ⟨d, η, hη, hd7, hd1, hrel⟩ := exists_frobenius_pair hcard hy3 hy1
  have hη3 : η ^ 3 = 1 := by
    rcases hη with rfl | rfl
    · exact hy3
    · rw [inv_pow, hy3, inv_one]
  have hfpf' : ∀ c : C, ρ η c = c → c = 1 := by
    rcases hη with rfl | rfl
    · exact hfpf
    · intro c hc
      apply hfpf
      have h1 : ρ y (ρ y⁻¹ c) = c := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
      rw [hc] at h1
      exact h1
  have hker : ρ d = 1 :=
    eq_one_of_frobenius hC (ρ d) (ρ η) (by rw [← map_pow, hd7, map_one])
      (by rw [← map_pow, hη3, map_one])
      (by rw [← map_mul, ← map_pow, ← map_mul]; congr 1; exact mul_inv_eq_iff_eq_mul.1 hrel)
      hfpf'
  have htop : ρ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exfalso
      apply hd1
      have : d ∈ ρ.ker := hker
      rw [h] at this
      exact this
    · exact h
  intro c
  apply hfpf
  have : y ∈ ρ.ker := by rw [htop]; trivial
  rw [MonoidHom.mem_ker] at this
  rw [this]; rfl

end Simple168

section Quotient

theorem eq_one_of_simple168_quotient {J : Type} [Group J] [Finite J] (Zs : Subgroup J)
    [Zs.Normal] (hZ : IsPGroup 2 Zs) [IsSimpleGroup (J ⧸ Zs)]
    (hcard : Nat.card (J ⧸ Zs) = 168) {E : Type} [CommGroup E] [Finite E]
    (hE : ∀ e : E, e * e = 1) [MulDistribMulAction J E] {y : J} (hy3 : y ^ 3 = 1)
    (hfpf : ∀ e : E, y • e = e → e = 1) : ∀ e : E, e = 1 := by
  by_contra hne
  push Not at hne
  obtain ⟨e0, he0⟩ := hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hZ.card_modEq_card_fixedPoints E
  have hord : orderOf e0 = 2 := orderOf_eq_prime (by rw [pow_two]; exact hE e0) he0
  have heven : 2 ∣ Nat.card E := hord ▸ orderOf_dvd_natCard e0
  have hfp : 2 ∣ Nat.card (MulAction.fixedPoints Zs E) := by
    unfold Nat.ModEq at hmod
    omega
  have hnt : ∃ c ∈ MulAction.fixedPoints Zs E, c ≠ 1 := by
    by_contra hall
    push Not at hall
    have hone : Nat.card (MulAction.fixedPoints Zs E) = 1 := by
      refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, ?_⟩⟩⟩
      · rw [hall a a.2, hall b b.2]
      · intro z; exact smul_one z
    omega
  obtain ⟨c0, hc0, hc01⟩ := hnt
  let C := FixedPoints.subgroup Zs E
  have hall : ∀ c : C, c = 1 :=
    eq_one_of_fixedPointFree_simple168 (S := J ⧸ Zs) hcard (C := C)
      (fun c => Subtype.ext (hE c)) (MulDistribMulAction.toMulAut (J ⧸ Zs) C)
      (y := (y : J ⧸ Zs)) (by rw [← QuotientGroup.mk_pow, hy3]; rfl)
      (fun c hc => by
        apply Subtype.ext
        apply hfpf
        exact congrArg Subtype.val hc)
  apply hc01
  exact congrArg Subtype.val (hall ⟨c0, hc0⟩)

end Quotient


end CFSG.RankThree.PartTwo.Sec21.FF84
