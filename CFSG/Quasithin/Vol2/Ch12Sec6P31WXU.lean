module

public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXF
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31
  Equiv CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

@[expose] def U3BorelFacts : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (Y : Type) [Group Y] [Finite Y] (X U : Subgroup Y),
    Group.IsPerfect ↥X → IsPSU 3 2 n (↥X ⧸ Subgroup.center ↥X) → IsSylowTwoOf U X →
      Nat.card ↥(Subgroup.center ↥X) ∣ Nat.gcd 3 (2 ^ n + 1) ∧
      Nat.card ↥(X ⊓ Subgroup.normalizer (U : Set Y)) * Nat.gcd 3 (2 ^ n + 1) =
        Nat.card ↥U * (4 ^ n - 1) * Nat.card ↥(Subgroup.center ↥X) ∧
      IsCoatom ((X ⊓ Subgroup.normalizer (U : Set Y)).subgroupOf X) ∧
      (∃ g ∈ X ⊓ Subgroup.normalizer (U : Set Y), ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
        ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ U) ∧
      ∀ r ∈ Subgroup.normalizer (X : Set Y) ⊓ Subgroup.normalizer (U : Set Y),
        ∃ j : ℕ, ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y), r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U

theorem three_dvd_card_isPSU3 {X : Type} [Group X] {n : ℕ} (h : IsPSU 3 2 n X) :
    3 ∣ Nat.card X := by
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu (by norm_num) h]
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  simp only [show 3 * (3 - 1) / 2 = 3 by norm_num]
  set q : ℕ := 2 ^ n with hq
  have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by
    have : ∀ m : ℕ, 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
      intro m
      induction m with
      | zero => norm_num
      | succ k ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> norm_num
    exact this n
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have e2 : (((q : ℤ) ^ 2 - (-1) ^ 2).toNat) = q ^ 2 - 1 := by
    have h1 : (1 : ℕ) ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [this, Int.toNat_natCast]
  have e3 : (((q : ℤ) ^ 3 - (-1) ^ 3).toNat) = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [e2, e3]
  rcases hq3 with h1 | h1
  · have hg : Nat.gcd 3 (q + 1) = 1 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)).gcd_eq_one
    rw [hg, Nat.div_one]
    have h3 : 3 ∣ q ^ 2 - 1 := by
      obtain ⟨a, ha⟩ : ∃ a, q = 3 * a + 1 := ⟨q / 3, by omega⟩
      rw [ha]
      have : (3 * a + 1) ^ 2 - 1 = 3 * (3 * a ^ 2 + 2 * a) := by
        have : 1 ≤ (3 * a + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        zify [this]; ring
      rw [this]; exact Dvd.intro _ rfl
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) _
  · obtain ⟨a, ha⟩ : ∃ a, q = 3 * a + 2 := ⟨q / 3, by omega⟩
    have hg : Nat.gcd 3 (q + 1) = 3 := by
      rw [ha]; exact Nat.gcd_eq_left ⟨a + 1, by ring⟩
    rw [hg]
    have h3 : 3 ∣ q ^ 2 - 1 := by
      rw [ha]
      have : (3 * a + 2) ^ 2 - 1 = 3 * (3 * a ^ 2 + 4 * a + 1) := by
        have : 1 ≤ (3 * a + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
        zify [this]; ring
      rw [this]; exact Dvd.intro _ rfl
    have h9 : 9 ∣ q ^ 3 + 1 := by
      rw [ha]
      exact ⟨3 * a ^ 3 + 6 * a ^ 2 + 4 * a + 1, by ring⟩
    have h27 : 3 * 9 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
      Dvd.dvd.mul_left (mul_dvd_mul h3 h9) _
    have := Nat.dvd_div_of_mul_dvd (show 3 * 9 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) from h27)
    exact (show 3 ∣ 9 from by norm_num).trans this

section Y

variable {Y : Type} [Group Y] [Finite Y]

theorem isCyclic_quotient_of_cyc {B U : Subgroup Y} [hN : (U.subgroupOf B).Normal]
    (hcyc : ∃ g ∈ B, ∀ b ∈ B, ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ U) :
    IsCyclic (↥B ⧸ U.subgroupOf B) := by
  classical
  obtain ⟨g, hg, hgen⟩ := hcyc
  refine ⟨⟨QuotientGroup.mk ⟨g, hg⟩, fun x => ?_⟩⟩
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, hk⟩ := hgen b b.2
  refine ⟨(k : ℤ), ?_⟩
  show (QuotientGroup.mk ⟨g, hg⟩ : ↥B ⧸ U.subgroupOf B) ^ (k : ℤ) = QuotientGroup.mk b
  rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using hk

theorem habel_of_cyc {B U : Subgroup Y} (hUB : U ≤ B) (hBU : B ≤ Subgroup.normalizer (U : Set Y))
    (hcyc : ∃ g ∈ B, ∀ b ∈ B, ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ U) :
    ∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ U := by
  classical
  haveI hN : (U.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).2 hBU
  haveI := isCyclic_quotient_of_cyc (U := U) (B := B) hcyc
  intro a ha b hb
  have h1 : (QuotientGroup.mk ⟨a, ha⟩ : ↥B ⧸ U.subgroupOf B) * QuotientGroup.mk ⟨b, hb⟩ =
      QuotientGroup.mk ⟨b, hb⟩ * QuotientGroup.mk ⟨a, ha⟩ :=
    (IsCyclic.commGroup (α := ↥B ⧸ U.subgroupOf B)).mul_comm _ _
  have h2 : (QuotientGroup.mk (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ : ↥B) :
      ↥B ⧸ U.subgroupOf B) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h1]
    group
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem prime_dvd_index_of_orders {B U : Subgroup Y} (hUB : U ≤ B) {n z p : ℕ} {g : ℕ}
    (hg : g ∣ 3) (heq : Nat.card B * g = Nat.card U * (4 ^ n - 1) * z) (hz : z ≠ 0)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) : p ∣ (U.subgroupOf B).index := by
  have hUcard : Nat.card (U.subgroupOf B) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv
  have h1 := Subgroup.index_mul_card (U.subgroupOf B)
  rw [hUcard] at h1
  have hpos : 0 < Nat.card U := Nat.card_pos
  have h2 : (U.subgroupOf B).index * g = (4 ^ n - 1) * z := by
    have : Nat.card U * ((U.subgroupOf B).index * g) = Nat.card U * ((4 ^ n - 1) * z) := by
      calc Nat.card U * ((U.subgroupOf B).index * g)
          = ((U.subgroupOf B).index * Nat.card U) * g := by ring
        _ = Nat.card B * g := by rw [h1]
        _ = Nat.card U * (4 ^ n - 1) * z := heq
        _ = Nat.card U * ((4 ^ n - 1) * z) := by ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hp4 : p ∣ 4 ^ n - 1 := by
    have h4 : 4 ^ n - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      have h2n : 4 ^ n = 2 ^ n * 2 ^ n := by rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
      have hk1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      obtain ⟨b, hb⟩ : ∃ b, 2 ^ n = b + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel hk1).symm⟩
      rw [h2n, hb, Nat.add_sub_cancel]
      have hsq : (b + 1) * (b + 1) = (b + 1 + 1) * b + 1 := by ring
      rw [hsq, Nat.add_sub_cancel]
    rw [h4]
    exact Dvd.dvd.mul_right hpn _
  have hdvd : p ∣ (U.subgroupOf B).index * g := by
    rw [h2]
    exact Dvd.dvd.mul_right hp4 _
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact h
  · exfalso
    have := Nat.le_of_dvd (by norm_num) (h.trans hg)
    omega

theorem permData_of_single_U3 (hU : U3BorelFacts) {n : ℕ} (hn : 2 ≤ n)
    {Ts Ms Ls Tls X : Subgroup Y} (h : SingleData' Y Ts Ms Ls Tls X) (hperf : Group.IsPerfect ↥X)
    (hX : IsPSU 3 2 n (↥X ⧸ Subgroup.center ↥X)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpn : p ∣ 2 ^ n + 1) : PermData Ts Ms Tls := by
  have hSylX : IsSylowTwoOf (Ts ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal h.sylow le_top (by
      haveI := h.normal
      exact Subgroup.le_normalizer_of_normal)
  obtain ⟨hZ, hcard, hcoat, hcyc, hfrob⟩ := hU n hn Y X (Ts ⊓ X) hperf hX hSylX
  have hUB : Ts ⊓ X ≤ borel X Ts := le_inf inf_le_right Subgroup.le_normalizer
  have hBN : borel X Ts ≤ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := inf_le_right
  have hz : Nat.card ↥(Subgroup.center ↥X) ≠ 0 := Nat.card_pos.ne'
  have hpN : p ∣ ((Ts ⊓ X).subgroupOf (borel X Ts)).index :=
    prime_dvd_index_of_orders hUB (Nat.gcd_dvd_left 3 _) hcard hz hp hp5 hpn
  exact permData_of_single' h hcoat hcyc (habel_of_cyc hUB hBN hcyc) hfrob hp hp5 hpn hpN

theorem false_of_single_U3_three_center (hU : U3BorelFacts) {Ts Ms Ls Tls X : Subgroup Y}
    (h : SingleData' Y Ts Ms Ls Tls X) (hperf : Group.IsPerfect ↥X)
    (hX : IsPSU 3 2 3 (↥X ⧸ Subgroup.center ↥X)) (hZ : Subgroup.center ↥X ≠ ⊥)
    (h27 : ¬ 27 ∣ Nat.card ↥Ms) : False := by
  have hSylX : IsSylowTwoOf (Ts ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal h.sylow le_top (by
      haveI := h.normal
      exact Subgroup.le_normalizer_of_normal)
  obtain ⟨hZ3, hcard, hcoat, hcyc, hfrob⟩ := hU 3 (by norm_num) Y X (Ts ⊓ X) hperf hX hSylX
  have hg : Nat.gcd 3 (2 ^ 3 + 1) = 3 := by norm_num
  rw [hg] at hZ3 hcard
  have hZc : Nat.card ↥(Subgroup.center ↥X) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hZ3 with h1 | h1
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hZ
    · exact h1
  rw [hZc] at hcard
  obtain ⟨r, j, c, -, -, -, -, -, -, hcount⟩ := single_prep' h hcoat hcyc hfrob
  have h9 : 9 ∣ Nat.card ↥(borel X Ts) := by
    have : Nat.card ↥(borel X Ts) = Nat.card ↥(Ts ⊓ X) * 63 := by
      have h3 : Nat.card ↥(borel X Ts) * 3 = Nat.card ↥(Ts ⊓ X) * 63 * 3 := by
        rw [show (borel X Ts) = X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) from rfl]
        simpa using hcard
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3
    rw [this]
    exact Dvd.dvd.mul_left (by norm_num) _
  exact h27 (hcount h9)

end Y

end CFSG.Quasithin.H13.P31X
