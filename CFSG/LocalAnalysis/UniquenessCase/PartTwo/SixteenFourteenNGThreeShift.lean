module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGThreeCentral
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6GrpB
public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCountP27

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

private theorem s1614_sh_swap {G : Type*} [Group G] {a b c : G} (h : a * b = b * a * c) :
    b * a = a * b * c⁻¹ := by
  rw [h]
  group

private theorem s1614_sh_mul_inv_right {G : Type*} [Group G] {a b c : G}
    (hbc : b * c = c * b) (h : a * b = b * a * c) : a * b⁻¹ = b⁻¹ * a * c⁻¹ := by
  have hcb : c⁻¹ * b = b * c⁻¹ := ((show Commute b c from hbc).inv_right).eq.symm
  have h1 : b⁻¹ * a * b = a * c := by
    calc b⁻¹ * a * b = b⁻¹ * (a * b) := by group
      _ = b⁻¹ * (b * a * c) := by rw [h]
      _ = a * c := by group
  have h2 : (b⁻¹ * a * c⁻¹) * b = a := by
    calc (b⁻¹ * a * c⁻¹) * b = b⁻¹ * a * (c⁻¹ * b) := by group
      _ = b⁻¹ * a * (b * c⁻¹) := by rw [hcb]
      _ = b⁻¹ * a * b * c⁻¹ := by group
      _ = (a * c) * c⁻¹ := by rw [h1]
      _ = a := by group
  calc a * b⁻¹ = ((b⁻¹ * a * c⁻¹) * b) * b⁻¹ := by rw [h2]
    _ = b⁻¹ * a * c⁻¹ := by group

private theorem s1614_sh_conj_nat {G : Type*} [Group G] {a b c : G}
    (hc : ∀ g : G, g * c = c * g) (h : a * b * a⁻¹ = b * c) :
    ∀ n : ℕ, a ^ n * b * (a ^ n)⁻¹ = b * c ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hac : a * c * a⁻¹ = c := by rw [hc a]; group
      have hcan : a * c ^ n * a⁻¹ = c ^ n := by rw [← conj_pow, hac]
      calc a ^ (n + 1) * b * (a ^ (n + 1))⁻¹
          = a * (a ^ n * b * (a ^ n)⁻¹) * a⁻¹ := by group
        _ = a * (b * c ^ n) * a⁻¹ := by rw [ih]
        _ = (a * b * a⁻¹) * (a * c ^ n * a⁻¹) := by group
        _ = (b * c) * c ^ n := by rw [h, hcan]
        _ = b * c ^ (n + 1) := by group

private theorem s1614_sh_zpowers_three {G : Type*} [Group G] {c : G} (hc3 : c ^ 3 = 1) {z : G}
    (hz : z ∈ Subgroup.zpowers c) : z = 1 ∨ z = c ∨ z = c ^ 2 := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h3 : c ^ m = c ^ (m % 3) := zpow_eq_zpow_emod' m hc3
  have h0 : 0 ≤ m % 3 := Int.emod_nonneg (a := m) (b := 3) (by norm_num)
  have hlt : m % 3 < 3 := Int.emod_lt_of_pos (a := m) (b := 3) (by norm_num)
  have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rw [← hm, h3]
  rcases hcases with h | h | h
  · exact Or.inl (by rw [h]; simp)
  · exact Or.inr (Or.inl (by rw [h]; simp))
  · exact Or.inr (Or.inr (by rw [h]; simp))

theorem s1614_shift {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x * x = 1)
    (hcard : Nat.card W = 2 ^ 6) {L : Subgroup (MulAut W)} (hL : IsPOnePlusTwo 3 ↥L) {ℓ : ↥L}
    (hℓ : ℓ ∈ Subgroup.center ↥L) (hℓ1 : ℓ ≠ 1) {x₀ x₁ : ↥L} (hx : x₀ * x₁ ≠ x₁ * x₀)
    {u : MulAut W} (hu3 : u * u * u = 1) (huL : ∀ y ∈ L, u * y * u⁻¹ ∈ L) (hu : u ∉ L)
    (hux₁ : u * (x₁ : MulAut W) = (x₁ : MulAut W) * u)
    (huℓ : u * (ℓ : MulAut W) = (ℓ : MulAut W) * u) :
    ∃ c e : ℕ, ¬ 3 ∣ c ∧ u * (x₀ : MulAut W) * u⁻¹ =
      (x₀ : MulAut W) * (x₁ : MulAut W) ^ c * (ℓ : MulAut W) ^ e := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hExtra : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hLcard : Nat.card ↥L = 27 := by rw [hL.2.1]; norm_num
  have hnc : ∃ a b : ↥L, a * b ≠ b * a := ⟨x₀, x₁, hx⟩
  have hZcard : Nat.card (Subgroup.center ↥L) = 3 :=
    CFSG.IsExtraspecial.center_order_p 3 ↥L
  have hℓ3 : ℓ ^ 3 = 1 := hL.2.2 ℓ
  have hx₁3 : x₁ ^ 3 = 1 := hL.2.2 x₁
  have hx₁1 : x₁ ≠ 1 := by
    intro h
    exact hx (by rw [h, mul_one, one_mul])
  have hℓord : orderOf ℓ = 3 := orderOf_eq_prime hℓ3 hℓ1
  have hx₁ord : orderOf x₁ = 3 := orderOf_eq_prime hx₁3 hx₁1
  have hℓcard : Nat.card (Subgroup.zpowers ℓ) = 3 := by rw [Nat.card_zpowers, hℓord]
  have hx₁card : Nat.card (Subgroup.zpowers x₁) = 3 := by rw [Nat.card_zpowers, hx₁ord]
  have hZeq : Subgroup.center ↥L = Subgroup.zpowers ℓ := by
    have hle : Subgroup.zpowers ℓ ≤ Subgroup.center ↥L := Subgroup.zpowers_le.mpr hℓ
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hZcard, hℓcard]
  have hx₁Z : x₁ ∉ Subgroup.center ↥L := fun h =>
    hx (Subgroup.mem_center_iff.mp h x₀)
  have hℓnotz : ℓ ∉ Subgroup.zpowers x₁ := by
    intro hmem
    have hle : Subgroup.zpowers ℓ ≤ Subgroup.zpowers x₁ := Subgroup.zpowers_le.mpr hmem
    have heq : Subgroup.zpowers ℓ = Subgroup.zpowers x₁ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hℓcard, hx₁card])
    refine hx₁Z ?_
    rw [hZeq]
    exact heq.symm ▸ Subgroup.mem_zpowers x₁
  obtain ⟨c₀, hc₀cent, hc₀3, hrel⟩ :=
    CFSG.RankThree.PartTwo.Sec4.RonanK432.exists_commutator_data hLcard hnc x₀ x₁
  have hc₀mem : c₀ ∈ Subgroup.center ↥L := Subgroup.mem_center_iff.mpr hc₀cent
  have hc₀1 : c₀ ≠ 1 := by
    intro h
    exact hx ((by rw [h, mul_one] : x₀ * x₁ = x₀ * x₁ * c₀).trans hrel.symm)
  let C : Subgroup ↥L := Subgroup.centralizer ({x₁} : Set ↥L)
  have hCcard : Nat.card C = 9 :=
    CFSG.Quasithin.SzN31.SmD6GrpB.card_centralizer_eq_nine hLcard hnc hx₁Z
  have hZC : Subgroup.center ↥L ≤ C := Subgroup.center_le_centralizer _
  have hx₁C : x₁ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let H : Subgroup ↥L := Subgroup.zpowers x₁ ⊔ Subgroup.center ↥L
  have hHle : H ≤ C := sup_le (Subgroup.zpowers_le.mpr hx₁C) hZC
  have h3dvdH : 3 ∣ Nat.card H := by
    have h := Subgroup.card_dvd_of_le (show Subgroup.zpowers x₁ ≤ H from le_sup_left)
    rwa [hx₁card] at h
  have hdvdH9 : Nat.card H ∣ 3 ^ 2 := by
    have h := Subgroup.card_dvd_of_le hHle
    rw [hCcard] at h
    simpa using h
  have hHne3 : Nat.card H ≠ 3 := by
    intro h3
    have heq : Subgroup.zpowers x₁ = H :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hx₁card])
    have hℓH : ℓ ∈ H := Subgroup.mem_sup_right (hZeq ▸ Subgroup.mem_zpowers ℓ)
    exact hℓnotz (heq.symm ▸ hℓH)
  have hHcard : Nat.card H = 9 := by
    obtain ⟨m, hm, hmcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvdH9
    have hm0 : m ≠ 0 := by
      intro h0
      rw [hmcard, h0] at h3dvdH
      norm_num at h3dvdH
    have hm1 : m ≠ 1 := by
      intro h1
      apply hHne3
      rw [hmcard, h1]
      norm_num
    have hm2 : m = 2 := by omega
    rw [hmcard, hm2]
    norm_num
  have hHC : H = C := Subgroup.eq_of_le_of_card_ge hHle (by rw [hCcard, hHcard])
  let x₀' : ↥L := ⟨u * (x₀ : MulAut W) * u⁻¹, huL x₀ x₀.2⟩
  have hrelval : (x₁ : MulAut W) * (x₀ : MulAut W) =
      (x₀ : MulAut W) * (x₁ : MulAut W) * (c₀ : MulAut W) := by
    simpa [Subgroup.coe_mul] using congrArg Subtype.val hrel
  have hc₀x₀ : (x₀ : MulAut W) * (c₀ : MulAut W) = (c₀ : MulAut W) * (x₀ : MulAut W) := by
    simpa [Subgroup.coe_mul] using congrArg Subtype.val (hc₀cent x₀)
  have hc₀x₀' : (x₀' : MulAut W) * (c₀ : MulAut W) = (c₀ : MulAut W) * (x₀' : MulAut W) := by
    simpa [Subgroup.coe_mul] using congrArg Subtype.val (hc₀cent x₀')
  have hc₀zpow : c₀ ∈ Subgroup.zpowers ℓ := hZeq ▸ hc₀mem
  obtain ⟨m₀, hm₀⟩ := Subgroup.mem_zpowers_iff.mp hc₀zpow
  have hc₀val : (c₀ : MulAut W) = (ℓ : MulAut W) ^ m₀ := by
    rw [← hm₀, Subgroup.coe_zpow]
  have huc₀ : u * (c₀ : MulAut W) = (c₀ : MulAut W) * u := by
    rw [hc₀val]
    exact ((show Commute u (ℓ : MulAut W) from huℓ).zpow_right m₀).eq
  have hux₁'' : MulAut.conj u (x₁ : MulAut W) = (x₁ : MulAut W) := by
    rw [MulAut.conj_apply, hux₁]
    group
  have huc₀'' : MulAut.conj u (c₀ : MulAut W) = (c₀ : MulAut W) := by
    rw [MulAut.conj_apply, huc₀]
    group
  have hconj_rel : (x₁ : MulAut W) * (x₀' : MulAut W) =
      (x₀' : MulAut W) * (x₁ : MulAut W) * (c₀ : MulAut W) := by
    have h := congrArg (MulAut.conj u) hrelval
    rw [map_mul, map_mul, map_mul, hux₁'', huc₀''] at h
    simpa [x₀', MulAut.conj_apply] using h
  let y : ↥L := x₀⁻¹ * x₀'
  have hx₀inv : (x₁ : MulAut W) * (x₀ : MulAut W)⁻¹ =
      (x₀ : MulAut W)⁻¹ * (x₁ : MulAut W) * (c₀ : MulAut W)⁻¹ :=
    s1614_sh_mul_inv_right hc₀x₀ hrelval
  have hyC : y ∈ C := by
    dsimp only [C]
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (x₀ : MulAut W)⁻¹ * (x₀' : MulAut W) * (x₁ : MulAut W)
       = (x₁ : MulAut W) * ((x₀ : MulAut W)⁻¹ * (x₀' : MulAut W))
    have hx₀inv' : (x₀ : MulAut W)⁻¹ * (x₁ : MulAut W) =
        (x₁ : MulAut W) * (x₀ : MulAut W)⁻¹ * (c₀ : MulAut W) := by
      simpa using s1614_sh_swap hx₀inv
    have hx₀'x₁ : (x₀' : MulAut W) * (x₁ : MulAut W) =
        (x₁ : MulAut W) * (x₀' : MulAut W) * (c₀ : MulAut W)⁻¹ :=
      s1614_sh_swap hconj_rel
    have hc₀x₀'v : (x₀' : MulAut W) * (c₀ : MulAut W)⁻¹ =
        (c₀ : MulAut W)⁻¹ * (x₀' : MulAut W) :=
      ((show Commute (x₀' : MulAut W) (c₀ : MulAut W) from hc₀x₀').inv_right).eq
    calc (x₀ : MulAut W)⁻¹ * (x₀' : MulAut W) * (x₁ : MulAut W)
        = (x₀ : MulAut W)⁻¹ * ((x₀' : MulAut W) * (x₁ : MulAut W)) := by group
      _ = (x₀ : MulAut W)⁻¹ * ((x₁ : MulAut W) * (x₀' : MulAut W) *
            (c₀ : MulAut W)⁻¹) := by rw [hx₀'x₁]
      _ = ((x₀ : MulAut W)⁻¹ * (x₁ : MulAut W)) *
            ((x₀' : MulAut W) * (c₀ : MulAut W)⁻¹) := by group
      _ = ((x₀ : MulAut W)⁻¹ * (x₁ : MulAut W)) *
            ((c₀ : MulAut W)⁻¹ * (x₀' : MulAut W)) := by rw [hc₀x₀'v]
      _ = (((x₀ : MulAut W)⁻¹ * (x₁ : MulAut W)) * (c₀ : MulAut W)⁻¹) *
            (x₀' : MulAut W) := by group
      _ = ((x₁ : MulAut W) * (x₀ : MulAut W)⁻¹ * (c₀ : MulAut W)) *
            (c₀ : MulAut W)⁻¹ * (x₀' : MulAut W) := by rw [hx₀inv']
      _ = (x₁ : MulAut W) * ((x₀ : MulAut W)⁻¹ * (x₀' : MulAut W)) := by group
  have hyH : y ∈ H := hHC.symm ▸ hyC
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hyH
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hbz : b ∈ Subgroup.zpowers ℓ := hZeq ▸ hb
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hbz
  set c : ℕ := (i % ((3 : ℕ) : ℤ)).toNat
  set e : ℕ := (j % ((3 : ℕ) : ℤ)).toNat
  have hci : ((i % ((3 : ℕ) : ℤ)).toNat : ℤ) = i % ((3 : ℕ) : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg (a := i) (b := ((3 : ℕ) : ℤ)) (by norm_num))
  have hej : ((j % ((3 : ℕ) : ℤ)).toNat : ℤ) = j % ((3 : ℕ) : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg (a := j) (b := ((3 : ℕ) : ℤ)) (by norm_num))
  have hx₁c : x₁ ^ i = x₁ ^ c := by
    rw [zpow_eq_zpow_emod' i hx₁3, ← hci, zpow_natCast]
  have hℓe : ℓ ^ j = ℓ ^ e := by
    rw [zpow_eq_zpow_emod' j hℓ3, ← hej, zpow_natCast]
  have hx₀'eq : x₀' = x₀ * x₁ ^ c * ℓ ^ e := by
    have h : x₀' = x₀ * y := by
      apply Subtype.ext
      simp only [x₀', y, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hy : y = x₁ ^ i * ℓ ^ j := by rw [← hab, ← hi, ← hj]
    rw [h, hy, hx₁c, hℓe]
    group
  refine ⟨c, e, ?_, ?_⟩
  ·
    intro h3
    have hx₁c1 : x₁ ^ c = 1 := by
      obtain ⟨t, ht⟩ := h3
      rw [ht, pow_mul, hx₁3, one_pow]
    have hx₀'step3 : x₀' = x₀ * ℓ ^ e := by
      rw [hx₀'eq, hx₁c1, mul_one]
    have he3 : e ≤ 3 := by
      have h2 : j % ((3 : ℕ) : ℤ) < 3 :=
        Int.emod_lt_of_pos (a := j) (b := ((3 : ℕ) : ℤ)) (by norm_num)
      have h4 : (e : ℤ) = j % ((3 : ℕ) : ℤ) := hej
      have h5 : (e : ℤ) < 3 := by rw [h4]; exact h2
      omega
    have hℓinv : (ℓ : ↥L) ^ (3 - e) = (ℓ ^ e)⁻¹ := by
      have h1 : (ℓ : ↥L) ^ (3 - e) * ℓ ^ e = 1 := by
        rw [← pow_add, show 3 - e + e = 3 by omega, hℓ3]
      exact eq_inv_of_mul_eq_one_left h1
    have hkcases : ∃ k : ℕ, (c₀ : ↥L) ^ k = (ℓ ^ e)⁻¹ := by
      rcases s1614_sh_zpowers_three (c := ℓ) hℓ3 hc₀zpow with h | h | h
      · exact absurd h hc₀1
      · exact ⟨3 - e, by rw [h]; exact hℓinv⟩
      · refine ⟨e, ?_⟩
        rw [h, ← pow_mul]
        have h1 : ℓ ^ (2 * e) * ℓ ^ e = 1 := by
          rw [← pow_add, show 2 * e + e = 3 * e by ring, pow_mul, hℓ3, one_pow]
        exact eq_inv_of_mul_eq_one_left h1
    obtain ⟨k, hk⟩ := hkcases
    let w : ↥L := x₁ ^ k
    have hconj_x₀ : (x₁ : ↥L) * x₀ * x₁⁻¹ = x₀ * c₀ := by
      calc (x₁ : ↥L) * x₀ * x₁⁻¹ = (x₀ * x₁ * c₀) * x₁⁻¹ := by rw [hrel]
        _ = x₀ * (x₁ * c₀) * x₁⁻¹ := by group
        _ = x₀ * (c₀ * x₁) * x₁⁻¹ := by rw [hc₀cent x₁]
        _ = x₀ * c₀ := by group
    have hcomp : w * x₀ * w⁻¹ = x₀ * c₀ ^ k :=
      s1614_sh_conj_nat (a := (x₁ : ↥L)) (b := x₀) (c := c₀) hc₀cent hconj_x₀ k
    have hℓpow : w * ℓ ^ e * w⁻¹ = ℓ ^ e := by
      have hcomm : Commute w (ℓ ^ e) :=
        ((show Commute (x₁ : ↥L) ℓ from (Subgroup.mem_center_iff.mp hℓ x₁)).pow_left
          k).pow_right e
      rw [hcomm.eq]
      group
    have hz : w * x₀ * ℓ ^ e * w⁻¹ = x₀ := by
      calc w * x₀ * ℓ ^ e * w⁻¹
          = (w * x₀ * w⁻¹) * (w * ℓ ^ e * w⁻¹) := by group
        _ = (x₀ * c₀ ^ k) * ℓ ^ e := by rw [hcomp, hℓpow]
        _ = x₀ * (c₀ ^ k * ℓ ^ e) := by group
        _ = x₀ * ((ℓ ^ e)⁻¹ * ℓ ^ e) := by rw [hk]
        _ = x₀ := by group
    let v : MulAut W := (w : MulAut W) * u
    have hv_def : v = (w : MulAut W) * u := rfl
    have hzM : (w : MulAut W) * (x₀ : MulAut W) * (ℓ : MulAut W) ^ e *
        (w : MulAut W)⁻¹ = (x₀ : MulAut W) := by
      have h := congrArg Subtype.val hz
      simpa [Subgroup.coe_mul, Subgroup.coe_pow] using h
    have hvx₀ : v * (x₀ : MulAut W) * v⁻¹ = (x₀ : MulAut W) := by
      have hx₀'val' : (x₀' : MulAut W) = (x₀ : MulAut W) * (ℓ : MulAut W) ^ e := by
        rw [hx₀'step3]
        simp [Subgroup.coe_mul, Subgroup.coe_pow]
      calc v * (x₀ : MulAut W) * v⁻¹
          = (w : MulAut W) * (x₀' : MulAut W) * (w : MulAut W)⁻¹ := by
              rw [hv_def]
              simp only [x₀']
              group
        _ = (w : MulAut W) * ((x₀ : MulAut W) * (ℓ : MulAut W) ^ e) *
              (w : MulAut W)⁻¹ := by rw [hx₀'val']
        _ = (x₀ : MulAut W) := by
              rw [show (w : MulAut W) * ((x₀ : MulAut W) * (ℓ : MulAut W) ^ e) *
                  (w : MulAut W)⁻¹ = (w : MulAut W) * (x₀ : MulAut W) *
                  (ℓ : MulAut W) ^ e * (w : MulAut W)⁻¹ from by group]
              exact hzM
    have hvx₁ : v * (x₁ : MulAut W) = (x₁ : MulAut W) * v := by
      have hw : (w : MulAut W) * (x₁ : MulAut W) = (x₁ : MulAut W) * (w : MulAut W) := by
        have hc : Commute ((x₁ : ↥L) ^ k) x₁ := (Commute.refl x₁).pow_left k
        have h := congrArg Subtype.val hc.eq
        simpa [w, Subgroup.coe_pow, Subgroup.coe_mul] using h
      calc v * (x₁ : MulAut W) = ((w : MulAut W) * u) * (x₁ : MulAut W) := by rw [hv_def]
        _ = (w : MulAut W) * (u * (x₁ : MulAut W)) := by group
        _ = (w : MulAut W) * ((x₁ : MulAut W) * u) := by rw [hux₁]
        _ = ((w : MulAut W) * (x₁ : MulAut W)) * u := by group
        _ = ((x₁ : MulAut W) * (w : MulAut W)) * u := by rw [hw]
        _ = (x₁ : MulAut W) * ((w : MulAut W) * u) := by group
        _ = (x₁ : MulAut W) * v := by rw [hv_def]
    have hvℓ : v * (ℓ : MulAut W) = (ℓ : MulAut W) * v := by
      have hw : (w : MulAut W) * (ℓ : MulAut W) = (ℓ : MulAut W) * (w : MulAut W) := by
        have hc : Commute ((x₁ : ↥L) ^ k) ℓ :=
          (show Commute (x₁ : ↥L) ℓ from (Subgroup.mem_center_iff.mp hℓ x₁)).pow_left k
        have h := congrArg Subtype.val hc.eq
        simpa [w, Subgroup.coe_pow, Subgroup.coe_mul] using h
      calc v * (ℓ : MulAut W) = ((w : MulAut W) * u) * (ℓ : MulAut W) := by rw [hv_def]
        _ = (w : MulAut W) * (u * (ℓ : MulAut W)) := by group
        _ = (w : MulAut W) * ((ℓ : MulAut W) * u) := by rw [huℓ]
        _ = ((w : MulAut W) * (ℓ : MulAut W)) * u := by group
        _ = ((ℓ : MulAut W) * (w : MulAut W)) * u := by rw [hw]
        _ = (ℓ : MulAut W) * ((w : MulAut W) * u) := by group
        _ = (ℓ : MulAut W) * v := by rw [hv_def]
    have hv3 : v * v * v = 1 := by
      have hcomm : Commute (w : MulAut W) u := by
        have hc : Commute (x₁ : MulAut W) u := hux₁.symm
        have h2 : Commute ((x₁ : MulAut W) ^ k) u := hc.pow_left k
        simpa [w, Subgroup.coe_pow] using h2
      have hw3 : (w : MulAut W) ^ 3 = 1 := by
        have h3 : w ^ 3 = 1 := by
          show (x₁ ^ k) ^ 3 = 1
          rw [← pow_mul, mul_comm k 3, pow_mul, hx₁3, one_pow]
        have h := congrArg Subtype.val h3
        simpa [Subgroup.coe_pow] using h
      have hu3' : u ^ 3 = 1 := by rw [pow_three']; exact hu3
      rw [← pow_three', hv_def, hcomm.mul_pow 3, hw3, hu3', mul_one]
    let Cv : Subgroup ↥L :=
      Subgroup.comap (Subgroup.subtype L) (Subgroup.centralizer ({v} : Set (MulAut W)))
    have hx₁Cv : x₁ ∈ Cv := by
      dsimp only [Cv]
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact hvx₁.symm
    have hZCv : Subgroup.center ↥L ≤ Cv := by
      intro z hz
      have hzmem : z ∈ Subgroup.zpowers ℓ := hZeq ▸ hz
      obtain ⟨j', hj'⟩ := Subgroup.mem_zpowers_iff.mp hzmem
      dsimp only [Cv]
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      have hzv : (z : MulAut W) = (ℓ : MulAut W) ^ j' := by
        rw [← hj', Subgroup.coe_zpow]
      change (z : MulAut W) * v = v * (z : MulAut W)
      rw [hzv]
      have hcomm : Commute v ((ℓ : MulAut W) ^ j') :=
        (show Commute v (ℓ : MulAut W) from hvℓ).zpow_right j'
      exact hcomm.eq.symm
    have hHCv : H ≤ Cv := sup_le (Subgroup.zpowers_le.mpr hx₁Cv) hZCv
    have hCCv : C ≤ Cv := hHC ▸ hHCv
    have hx₀Cv : x₀ ∈ Cv := by
      dsimp only [Cv]
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      calc (x₀ : MulAut W) * v = (v * (x₀ : MulAut W) * v⁻¹) * v := by rw [hvx₀]
        _ = v * (x₀ : MulAut W) := by group
    have hx₀C : x₀ ∉ C := by
      intro h
      dsimp only [C] at h
      rw [Subgroup.mem_centralizer_singleton_iff] at h
      exact hx h
    have h9dvdCv : 3 ^ 2 ∣ Nat.card Cv := by
      have h := Subgroup.card_dvd_of_le hCCv
      rw [hCcard] at h
      simpa using h
    have hdvdCv : Nat.card Cv ∣ 3 ^ 3 := by
      have h := Subgroup.card_subgroup_dvd_card Cv
      rw [hLcard] at h
      simpa using h
    have hCvcard : Nat.card Cv = 27 := by
      obtain ⟨m, hm, hmcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvdCv
      have hm2 : 2 ≤ m := by
        have h : 3 ^ 2 ∣ 3 ^ m := by rw [← hmcard]; exact h9dvdCv
        exact (Nat.pow_dvd_pow_iff_le_right (x := 3) (k := 2) (l := m) (by norm_num)).mp h
      have hm3 : m = 3 := by
        rcases Nat.lt_or_eq_of_le hm2 with h | h
        · exact le_antisymm hm (Nat.succ_le_of_lt h)
        · exfalso
          have hcard9 : Nat.card Cv = 9 := by rw [hmcard, ← h]; norm_num
          have heq : C = Cv := Subgroup.eq_of_le_of_card_ge hCCv (by rw [hCcard, hcard9])
          exact hx₀C (heq.symm ▸ hx₀Cv)
      rw [hmcard, hm3]
      norm_num
    have hCvtop : Cv = ⊤ :=
      Subgroup.eq_top_of_card_eq Cv (by rw [hCvcard, hLcard])
    have hvL' : ∀ y : MulAut W, y ∈ L → v * y = y * v := by
      intro y hy
      have hyCv : (⟨y, hy⟩ : ↥L) ∈ Cv := by
        rw [hCvtop]
        exact Subgroup.mem_top _
      have hyCv' : (⟨y, hy⟩ : ↥L) ∈ Subgroup.comap (Subgroup.subtype L)
          (Subgroup.centralizer ({v} : Set (MulAut W))) := hyCv
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hyCv'
      exact hyCv'.symm
    have hvzp : v ∈ Subgroup.zpowers (ℓ : MulAut W) :=
      s1614_central_eq hW hcard hL hℓ hℓ1 hv3 hvL'
    have hzple : Subgroup.zpowers (ℓ : MulAut W) ≤ L := Subgroup.zpowers_le.mpr ℓ.2
    have hvLmem : v ∈ L := hzple hvzp
    have huLmem : u ∈ L := by
      have hkey : u = ((w : MulAut W))⁻¹ * v := by
        rw [hv_def]
        group
      rw [hkey]
      refine L.mul_mem (L.inv_mem ?_) hvLmem
      simpa [w, Subgroup.coe_pow] using L.pow_mem x₁.2 k
    exact hu huLmem
  · have hfin : (x₀' : MulAut W) = (x₀ : MulAut W) * (x₁ : MulAut W) ^ c *
        (ℓ : MulAut W) ^ e := by
      rw [hx₀'eq]
      simp [Subgroup.coe_mul, Subgroup.coe_pow]
    simpa [x₀'] using hfin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
