module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def ActsAsInvolution (t : G) (B : Subgroup G) : Prop :=
  (∀ b ∈ B, t ^ 2 * b * (t ^ 2)⁻¹ = b) ∧ ∃ b ∈ B, t * b * t⁻¹ ≠ b

@[expose] def Choice214U (D : Data G) : Choice2011 G := fun _ B0 =>
  (B0 ≠ ⊥ → ∀ t ∈ D.T, t ∈ normalizer (B0 : Set G) → ¬ ∀ b ∈ B0, t * b * t⁻¹ = b⁻¹) ∧
  (IsCyclic B0 → ∀ s ∈ D.T, ∀ t ∈ D.T, s ∈ normalizer (B0 : Set G) →
    t ∈ normalizer (B0 : Set G) → ActsAsInvolution s B0 → ActsAsInvolution t B0 →
      ∀ b ∈ B0, s * b * s⁻¹ = t * b * t⁻¹)

@[expose] def ChoiceExists2011 (D : Data G) (Ch : Choice2011 G) : Prop :=
  ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
    ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
      AlphaCond D.T B0 n ∧ B0 ≤ D.M

@[expose] def Ctx21.mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (c : Ctx21 D Ch') : Ctx21 D Ch :=
  { c with hch := h c.L0 c.B0 c.hch }

theorem s21_3_mono {D : Data G} {Ch Ch' : Choice2011 G}
    (h : ∀ L₀ B₀ : Subgroup G, Ch' L₀ B₀ → Ch L₀ B₀) (h3 : S21_3 D Ch) : S21_3 D Ch' :=
  fun hH c => h3 hH (c.mono h)

theorem ctx21_transfer {D : Data G} {Ch Ch' : Choice2011 G} (hex : ChoiceExists2011 D Ch')
    (c : Ctx21 D Ch) : ∃ c' : Ctx21 D Ch', c'.L0 = c.L0 ∧ c'.n = c.n ∧ c'.B = c'.B0 := by
  obtain ⟨B0, hch, hB0, hpi, hα, hBM⟩ := hex c.L0 c.hL0 c.n c.hn
  exact ⟨⟨c.L0, B0, B0, c.n, c.hL0, c.hn, hB0, hpi, hα, hBM, hch, hB0, le_rfl⟩, rfl, rfl, rfl⟩

theorem s21_12a_transfer {D : Data G} {Ch Ch' : Choice2011 G}
    (hex : H1930 D → ChoiceExists2011 D Ch') (h : S21_12a D Ch') : S21_12a D Ch := by
  intro hH c L hL p hp hp2 hch
  obtain ⟨c', -, -, -⟩ := ctx21_transfer (hex hH) c
  exact h hH c' L hL p hp hp2 hch

theorem ch214_ne_zero {B : Subgroup G} {n : ℕ} (h : piSet B = etaSet n) : n ≠ 0 := by
  rintro rfl
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (Nat.card B + 1)
  have hpB : p ∈ piSet B := by
    rw [h]
    exact ⟨hp, by simp⟩
  have := Nat.le_of_dvd Nat.card_pos hpB.2
  omega

theorem ch214_odd_card {B : Subgroup G} {n : ℕ} (h : piSet B = etaSet n) : Odd (Nat.card B) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have h2 : (2 : ℕ) ∈ piSet B := ⟨Nat.prime_two, even_iff_two_dvd.1 hev⟩
  rw [h] at h2
  obtain ⟨-, hd⟩ := h2
  have hn := ch214_ne_zero h
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

theorem ch214_eq_one_of_sq {B : Subgroup G} (hB : Odd (Nat.card B)) {b : G} (hb : b ∈ B)
    (h : b ^ 2 = 1) : b = 1 := by
  have h2 : b ^ Nat.card B = 1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨b, hb⟩ : B)))
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one h2)
  rw [(Nat.coprime_two_left.2 hB).gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem ch214_eq_one {T B : Subgroup G} (hT : IsPGroup 2 T) (hB : Odd (Nat.card B)) {x : G}
    (hxB : x ∈ B) (hxT : x ∈ T) : x = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨x, hxT⟩
  have h1 : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : x ^ Nat.card B = 1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hxB⟩ : B)))
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [(Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hB)).gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem ch214_conj_eq {T B : Subgroup G} (hT : IsPGroup 2 T) (hB : Odd (Nat.card B)) {x t : G}
    (hxB : x ∈ B) (hxT : x ∈ normalizer (T : Set G)) (htT : t ∈ T)
    (htB : t ∈ normalizer (B : Set G)) : t * x * t⁻¹ = x := by
  have h1 : x * t * x⁻¹ * t⁻¹ ∈ T := T.mul_mem ((mem_normalizer_iff.1 hxT t).1 htT) (T.inv_mem htT)
  have h2 : x * t * x⁻¹ * t⁻¹ ∈ B := by
    have h := B.mul_mem hxB ((mem_normalizer_iff.1 htB x⁻¹).1 (B.inv_mem hxB))
    simpa [mul_assoc] using h
  have h3 := ch214_eq_one hT hB h2 h1
  have h4 : x * t = t * x := by
    have := congrArg (· * (t * x)) h3
    simpa [mul_assoc] using this
  rw [← h4, mul_inv_cancel_right]

theorem ch214_le_oPi {B : Subgroup G} {α : Set ℕ} (h : piSet B ⊆ α) : B ≤ oPi α B :=
  le_iSup₂_of_le (f := fun (N : Subgroup G) (_ : N ≤ B ∧ (N.subgroupOf B).Normal ∧ piSet N ⊆ α) => N)
    B ⟨le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance, h⟩ le_rfl

theorem ch214_le_normalizer_of_odd {T B₀ : Subgroup G} {n : ℕ} (hn : Odd n)
    (hpi : piSet B₀ = etaSet n) (hα : AlphaCond T B₀ n) : B₀ ≤ normalizer (T : Set G) :=
  (ch214_le_oPi (α := {p | p.Prime ∧ p ∣ 2 ^ n - 1}) (by rw [hpi]; exact fun p hp => hp)).trans
    (hα 0 n hn (by rw [pow_zero, one_mul]))

theorem choice214U_of_odd (D : Data G) {L₀ B₀ : Subgroup G} {n : ℕ} (hn : Odd n)
    (hpi : piSet B₀ = etaSet n) (hα : AlphaCond D.T B₀ n) : Choice214U D L₀ B₀ := by
  have hBN := ch214_le_normalizer_of_odd hn hpi hα
  have hodd := ch214_odd_card hpi
  have hc : ∀ t ∈ D.T, t ∈ normalizer (B₀ : Set G) → ∀ b ∈ B₀, t * b * t⁻¹ = b :=
    fun t htT htB b hb => ch214_conj_eq D.sylowM.isPGroup hodd hb (hBN hb) htT htB
  refine ⟨fun hne t htT htB hinv => hne ?_, fun _ s hsT t _ hsB _ hs _ => ?_⟩
  · rw [eq_bot_iff]
    intro b hb
    have h1 := hinv b hb
    rw [hc t htT htB b hb] at h1
    rw [Subgroup.mem_bot]
    refine ch214_eq_one_of_sq hodd hb ?_
    rw [sq]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel b
  · obtain ⟨-, b, hb, hne⟩ := hs
    exact absurd (hc s hsT hsB b hb) hne

theorem ch214_inv_of_not_powTwo (D : Data G) {B₀ : Subgroup G} {n : ℕ} (hn : ¬ IsPowTwo n)
    (hab : IsMulCommutative B₀) (hpi : piSet B₀ = etaSet n) (hα : AlphaCond D.T B₀ n) :
    ∀ t ∈ D.T, t ∈ normalizer (B₀ : Set G) → ¬ ∀ b ∈ B₀, t * b * t⁻¹ = b⁻¹ := by
  intro t htT htB hinv
  have hodd := ch214_odd_card hpi
  obtain ⟨e, m, hm, hnem⟩ := Nat.exists_eq_two_pow_mul_odd (ch214_ne_zero hpi)
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hn ⟨e, by rw [hnem, mul_one]⟩
  have hm3 : 3 ≤ m := by
    obtain ⟨k, rfl⟩ := hm
    omega
  have h8 : 8 ≤ 2 ^ m :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ m - 1 ≠ 1 by omega)
  have hdvd : 2 ^ m - 1 ∣ 2 ^ n - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 (2 ^ e)
    rwa [one_pow, ← pow_mul, mul_comm, ← hnem] at h
  have hpB : p ∣ Nat.card B₀ := by
    have : p ∈ piSet B₀ := by
      rw [hpi]
      exact ⟨hp, hpd.trans hdvd⟩
    exact this.2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B₀) p hpB
  have hxo : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx]
  have hzle : zpowers (x : G) ≤ B₀ := Subgroup.zpowers_le.2 x.2
  have hN : ((zpowers (x : G)).subgroupOf B₀).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hzle]
    intro a k ha hk
    rw [Subgroup.mul_comm_of_mem_isMulCommutative B₀ hk (hzle ha), mul_inv_cancel_right]
    exact ha
  have hsub : piSet (zpowers (x : G)) ⊆ {q | q.Prime ∧ q ∣ 2 ^ m - 1} := by
    rintro q ⟨hq, hqd⟩
    rw [Nat.card_zpowers, hxo] at hqd
    rw [(Nat.prime_dvd_prime_iff_eq hq hp).1 hqd]
    exact ⟨hp, hpd⟩
  have hxα : (x : G) ∈ oPi {q | q.Prime ∧ q ∣ 2 ^ m - 1} B₀ :=
    le_iSup₂_of_le (f := fun (N : Subgroup G)
      (_ : N ≤ B₀ ∧ (N.subgroupOf B₀).Normal ∧ piSet N ⊆ {q | q.Prime ∧ q ∣ 2 ^ m - 1}) => N)
      (zpowers (x : G)) ⟨hzle, hN, hsub⟩ le_rfl (mem_zpowers _)
  have hc := ch214_conj_eq D.sylowM.isPGroup hodd x.2 (hα e m hm hnem hxα) htT htB
  have h1 := hinv x x.2
  rw [hc] at h1
  have hx1 : (x : G) = 1 := by
    refine ch214_eq_one_of_sq hodd x.2 ?_
    rw [sq]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel _
  rw [hx1, orderOf_one] at hxo
  exact hp.one_lt.ne hxo

end CFSG.LocalAnalysis.UniquenessCase.UC22
