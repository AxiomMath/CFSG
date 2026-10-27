module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Fpf
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def s16h_BlockBound {W : Type} [CommGroup W] (A L : Subgroup (MulAut W)) (q c : ℕ) :
    Prop :=
  ∀ E : Subgroup (MulAut W), E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
    Nat.card ↥E ≤ q ^ c * Nat.card ↥(E ⊓ centSub (commSub (⊤ : Subgroup W) L))

@[expose] noncomputable def s16h_cTable (p m q : ℕ) : ℕ :=
  m / Nat.lcm (orderOf (2 : ZMod p)) (orderOf (2 : ZMod q)) + if q ∣ p - 1 then 1 else 0

@[expose] def s16h_ZpRow (p m : ℕ) : Prop :=
  (p = 3 ∧ (m = 2 ∨ m = 4 ∨ m = 6)) ∨ (p = 5 ∧ m = 4) ∨ (p = 7 ∧ (m = 3 ∨ m = 6))

theorem s16h_blockBound_mono {W : Type} [CommGroup W] {A A' L : Subgroup (MulAut W)}
    {q c c' : ℕ} (hq : 0 < q) (hA : A' ≤ A) (hc : c ≤ c') (h : s16h_BlockBound A L q c) :
    s16h_BlockBound A' L q c' := by
  intro E hE hEab
  exact (h E (hE.trans (inf_le_inf_right _ hA)) hEab).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hq hc))

theorem s16h_card_le_mul_cent_of_normalizes {X : Type*} [Group X] [Finite X] {e : X} {p q : ℕ}
    (hp : p.Prime) (he : orderOf e = p) (hq : q.Prime) {E : Subgroup X}
    (hEn : E ≤ normalizer ((Subgroup.zpowers e : Subgroup X) : Set X))
    (hEq : ∀ x ∈ E, x ^ q = 1) :
    Nat.card ↥E ≤ (if q ∣ p - 1 then q else 1) * Nat.card ↥(E ⊓ centralizer {e}) := by
  classical
  let H : Subgroup X := Subgroup.zpowers e
  have hHcard : Nat.card ↥H = p := by
    change Nat.card ↥(Subgroup.zpowers e) = p
    rw [Nat.card_zpowers, he]
  have hHcyc : IsCyclic ↥H := by
    change IsCyclic ↥(Subgroup.zpowers e)
    infer_instance
  let ψ : ↥E →* MulAut ↥H := H.normalizerMonoidHom.comp (Subgroup.inclusion hEn)
  have hcent : Subgroup.centralizer (H : Set X) = Subgroup.centralizer ({e} : Set X) := by
    change Subgroup.centralizer ((Subgroup.zpowers e : Subgroup X) : Set X) = _
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hψ1 : ∀ y : ↥E, ψ y = 1 ↔ (y : X) ∈ Subgroup.centralizer ({e} : Set X) := by
    intro y
    have h1 : ψ y = 1 ↔ Subgroup.inclusion hEn y ∈ H.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      rfl
    rw [h1, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion,
      hcent]
  have hkermap : ψ.ker.map E.subtype = E ⊓ Subgroup.centralizer ({e} : Set X) := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hψ1 y).mp hy⟩
    · rintro ⟨hxE, hxc⟩
      exact ⟨⟨x, hxE⟩, (hψ1 ⟨x, hxE⟩).mpr hxc, rfl⟩
  have hkercard : Nat.card ↥ψ.ker = Nat.card ↥(E ⊓ Subgroup.centralizer ({e} : Set X)) := by
    have h := Subgroup.card_map_of_injective (K := ψ.ker) (f := E.subtype) E.subtype_injective
    rw [hkermap] at h
    exact h.symm
  haveI : IsCyclic ↥H := hHcyc
  have hMulAut : Nat.card (MulAut ↥H) = p - 1 := by
    rw [IsCyclic.card_mulAut ↥H, hHcard, Nat.totient_prime hp]
  haveI : IsCyclic (MulAut ↥H) := by
    have h := (IsCyclic.mulAutMulEquiv ↥H).isCyclic
    rw [hHcard] at h
    exact h.mpr (ZMod.isCyclic_units_prime hp)
  haveI : IsCyclic ↥ψ.range :=
    isCyclic_of_injective (Subgroup.subtype ψ.range) (Subgroup.subtype_injective ψ.range)
  have hdivp : Nat.card ↥ψ.range ∣ p - 1 := by
    have h := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [hMulAut] at h
  have hexp : Monoid.exponent ↥ψ.range ∣ q := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp g.2
    have hyq : y ^ q = 1 := Subtype.ext (by simpa using hEq (y : X) y.2)
    apply Subtype.ext
    change ((g : MulAut ↥H)) ^ q = 1
    rw [← hy, ← map_pow, hyq, map_one]
  have hdivq : Nat.card ↥ψ.range ∣ q := by
    rw [← IsCyclic.exponent_eq_card (α := ↥ψ.range)]
    exact hexp
  have hle : Nat.card ↥ψ.range ≤ (if q ∣ p - 1 then q else 1) := by
    by_cases hqp : q ∣ p - 1
    · rw [if_pos hqp]
      exact Nat.le_of_dvd hq.pos hdivq
    · rw [if_neg hqp]
      rcases (Nat.dvd_prime hq).mp hdivq with h | h
      · omega
      · exact absurd (h ▸ hdivp) hqp
  calc Nat.card ↥E
      = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := (card_ker_mul_card_range ψ).symm
    _ = Nat.card ↥(E ⊓ Subgroup.centralizer ({e} : Set X)) * Nat.card ↥ψ.range := by
        rw [hkercard]
    _ ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({e} : Set X)) *
          (if q ∣ p - 1 then q else 1) := Nat.mul_le_mul_left _ hle
    _ = (if q ∣ p - 1 then q else 1) *
          Nat.card ↥(E ⊓ Subgroup.centralizer ({e} : Set X)) := by ring

private lemma s16h_commute_zpowers_of {W : Type*} [CommGroup W] {x b : MulAut W}
    (hxb : x * b = b * x) {y : MulAut W} (hy : y ∈ Subgroup.zpowers b) : y * x = x * y := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (show Commute b x from hxb.symm).zpow_left n

theorem s16h_blockBound_of_cyclic {W : Type} [CommGroup W] [Finite W]
    (hV : ∀ v : W, v ^ 2 = 1) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) {A L : Subgroup (MulAut W)} (hLc : IsCyclic ↥L) (hLp : Nat.card ↥L = p)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥) :
    s16h_BlockBound A L q (s16h_cTable p (rk ↥(commSub (⊤ : Subgroup W) L)) q) := by
  intro E hE hEab
  have hEn : E ≤ normalizer (L : Set (MulAut W)) := hE.trans inf_le_right
  obtain ⟨e, he⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top L).mp hLc
  have heord : orderOf e = p := by
    rw [← Nat.card_zpowers, he]
    exact hLp
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hEn' : E ≤ normalizer ((Subgroup.zpowers e : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [he]; exact hEn
  set U : Subgroup W := commSub (⊤ : Subgroup W) L with hU
  set E' : Subgroup (MulAut W) := E ⊓ Subgroup.centralizer ({e} : Set (MulAut W)) with hE'
  have hcard1 : Nat.card ↥E ≤ (if q ∣ p - 1 then q else 1) * Nat.card ↥E' :=
    s16h_card_le_mul_cent_of_normalizes hp heord hq hEn' (fun x hx => hEab.2 x hx)
  have hE'ab : IsElemAbelian q E' := hEab.mono inf_le_left
  have hB : IsPGroup p ↥L := IsPGroup.of_card (n := 1) (by rw [hLp, pow_one])
  have hBE : ∀ b ∈ L, ∀ x ∈ E', b * x = x * b := by
    intro b hb x hx
    have hb' : b ∈ Subgroup.zpowers e := by rw [he]; exact hb
    have hxcent : x * e = e * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    exact s16h_commute_zpowers_of hxcent hb'
  have hUB : ∀ b ∈ L, ∀ u ∈ U, b u ∈ U := by
    intro b hb u hu
    exact commSub_top_stable151b (X := L) (g := b)
      (fun x hx => L.mul_mem (L.mul_mem hb hx) (L.inv_mem hb)) u hu
  have hUE : ∀ x ∈ E', ∀ u ∈ U, x u ∈ U := by
    intro x hx u hu
    have hxE : x ∈ E := (Subgroup.mem_inf.mp hx).1
    have hxN : x ∈ normalizer (L : Set (MulAut W)) := hEn hxE
    exact commSub_top_stable151b (X := L) (g := x)
      (fun y hy => (Subgroup.mem_normalizer_iff.mp hxN y).mp hy) u hu
  have hcard2 : Nat.card ↥E' ≤
      q ^ (rk ↥U / Nat.lcm (orderOf (2 : ZMod p)) (orderOf (2 : ZMod q))) *
        Nat.card ↥(E' ⊓ centSub U) :=
    s16h_card_le_pow_mul_cent hV hp hq hp2 hq2 hB hE'ab hBE hUB hUE hfix
  have hcardle : Nat.card ↥(E' ⊓ centSub U) ≤ Nat.card ↥(E ⊓ centSub U) :=
    Subgroup.card_le_of_le (inf_le_inf_right (centSub U) inf_le_left)
  have hmain : Nat.card ↥E ≤ (if q ∣ p - 1 then q else 1) *
      (q ^ (rk ↥U / Nat.lcm (orderOf (2 : ZMod p)) (orderOf (2 : ZMod q))) *
        Nat.card ↥(E ⊓ centSub U)) := by
    calc Nat.card ↥E ≤ (if q ∣ p - 1 then q else 1) * Nat.card ↥E' := hcard1
      _ ≤ (if q ∣ p - 1 then q else 1) *
          (q ^ (rk ↥U / Nat.lcm (orderOf (2 : ZMod p)) (orderOf (2 : ZMod q))) *
            Nat.card ↥(E' ⊓ centSub U)) := Nat.mul_le_mul_left _ hcard2
      _ ≤ (if q ∣ p - 1 then q else 1) *
          (q ^ (rk ↥U / Nat.lcm (orderOf (2 : ZMod p)) (orderOf (2 : ZMod q))) *
            Nat.card ↥(E ⊓ centSub U)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcardle)
  have hpow : (if q ∣ p - 1 then q else 1) *
        (q ^ (rk ↥U / Nat.lcm (orderOf (2 : ZMod p)) (orderOf (2 : ZMod q))) *
          Nat.card ↥(E ⊓ centSub U)) =
      q ^ (s16h_cTable p (rk ↥U) q) * Nat.card ↥(E ⊓ centSub U) := by
    rw [s16h_cTable]
    by_cases h : q ∣ p - 1
    · rw [if_pos h, if_pos h, pow_succ]; ring
    · rw [if_neg h, if_neg h, one_mul, add_zero]
  rw [hpow] at hmain
  exact hmain

private lemma s16h_orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

private lemma s16h_orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

private lemma s16h_orderOf_two_zmod_seven : orderOf (2 : ZMod 7) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

private lemma s16h_prime_dvd_two_pow_orderOf_sub_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∣ 2 ^ orderOf (2 : ZMod q) - 1 := by
  have h1 : ((2 ^ orderOf (2 : ZMod q) : ℕ) : ZMod q) = 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_orderOf_eq_one]
  have h2 : ((2 ^ orderOf (2 : ZMod q) - 1 : ℕ) : ZMod q) = 0 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, h1, Nat.cast_one, sub_self]
  exact (ZMod.natCast_eq_zero_iff _ q).mp h2

private lemma s16h_orderOf_two_zmod_pos {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    0 < orderOf (2 : ZMod q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hne : (2 : ZMod q) ≠ 0 := by
    intro h0
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 q).mp h0))
  exact orderOf_pos_iff.mpr (isUnit_iff_ne_zero.mpr hne).isOfFinOrder

private lemma s16h_two_le_orderOf_two_zmod {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    2 ≤ orderOf (2 : ZMod q) := by
  have hdvd := s16h_prime_dvd_two_pow_orderOf_sub_one hq hq2
  have hne1 : orderOf (2 : ZMod q) ≠ 1 := by
    intro h1
    rw [h1] at hdvd
    norm_num at hdvd
    have hq2le : 2 ≤ q := hq.two_le
    omega
  have hpos := s16h_orderOf_two_zmod_pos hq hq2
  omega

private lemma s16h_orderOf_two_zmod_eq_two {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : orderOf (2 : ZMod q) = 2) : q = 3 := by
  have hdvd := s16h_prime_dvd_two_pow_orderOf_sub_one hq hq2
  rw [h] at hdvd
  norm_num at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · have hq2le : 2 ≤ q := hq.two_le
    omega
  · exact h3

private lemma s16h_orderOf_two_zmod_eq_three {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : orderOf (2 : ZMod q) = 3) : q = 7 := by
  have hdvd := s16h_prime_dvd_two_pow_orderOf_sub_one hq hq2
  rw [h] at hdvd
  norm_num at hdvd
  rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h1 | h7
  · have hq2le : 2 ≤ q := hq.two_le
    omega
  · exact h7

private lemma s16h_div_le_of_lt_mul {m ℓ k : ℕ} (hℓ : 0 < ℓ) (h : m < (k + 1) * ℓ) :
    m / ℓ ≤ k := by
  have := (Nat.div_lt_iff_lt_mul hℓ).mpr h
  omega

private lemma s16h_not_dvd_two_of_odd_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ¬ q ∣ 2 :=
  fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)

private lemma s16h_not_dvd_four_of_odd_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ∣ 4 := by
  intro h
  have h2 : q ∣ 2 ^ 2 := by simpa using h
  exact s16h_not_dvd_two_of_odd_prime hq hq2 (hq.dvd_of_dvd_pow h2)

private lemma s16h_dvd_six_iff {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : q ∣ 6 ↔ q = 3 := by
  constructor
  · intro h
    have h23 : q ∣ 2 * 3 := by simpa using h
    rcases (hq.dvd_mul).mp h23 with h2 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2) hq2
    · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
  · rintro rfl; norm_num

theorem s16h_cTable_le_two {p m q : ℕ} (hrow : s16h_ZpRow p m) (hq : q.Prime) (hq2 : q ≠ 2)
    (hex : ¬ (p = 3 ∧ m = 6 ∧ q = 3)) : s16h_cTable p m q ≤ 2 := by
  rcases hrow with ⟨rfl, hm⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hm⟩
  · rcases hm with rfl | rfl | rfl
    · rw [s16h_cTable, s16h_orderOf_two_zmod_three, show (3:ℕ) - 1 = 2 by norm_num,
        if_neg (s16h_not_dvd_two_of_odd_prime hq hq2)]
      have hd := s16h_orderOf_two_zmod_pos hq hq2
      have hle : 2 / Nat.lcm 2 (orderOf (2 : ZMod q)) ≤ 1 := by
        apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2)
          (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 2 hd))
        have := Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 2 hd
        nlinarith
      omega
    · rw [s16h_cTable, s16h_orderOf_two_zmod_three, show (3:ℕ) - 1 = 2 by norm_num,
        if_neg (s16h_not_dvd_two_of_odd_prime hq hq2)]
      have hd := s16h_orderOf_two_zmod_pos hq hq2
      have hle : 4 / Nat.lcm 2 (orderOf (2 : ZMod q)) ≤ 2 := by
        apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2)
          (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 2 hd))
        have := Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 2 hd
        nlinarith
      omega
    · have hq3 : q ≠ 3 := fun h => hex ⟨rfl, rfl, h⟩
      rw [s16h_cTable, s16h_orderOf_two_zmod_three, show (3:ℕ) - 1 = 2 by norm_num,
        if_neg (s16h_not_dvd_two_of_odd_prime hq hq2)]
      have hd := s16h_orderOf_two_zmod_pos hq hq2
      have hd3 : 3 ≤ orderOf (2 : ZMod q) := by
        have h2 := s16h_two_le_orderOf_two_zmod hq hq2
        have hne : orderOf (2 : ZMod q) ≠ 2 :=
          fun h => hq3 (s16h_orderOf_two_zmod_eq_two hq hq2 h)
        omega
      have hle : 6 / Nat.lcm 2 (orderOf (2 : ZMod q)) ≤ 2 := by
        apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2)
          (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 2 hd))
        have := Nat.le_lcm_right (m := 2) (orderOf (2 : ZMod q)) (by norm_num)
        nlinarith
      omega
  · rw [s16h_cTable, s16h_orderOf_two_zmod_five, show (5:ℕ) - 1 = 4 by norm_num,
      if_neg (s16h_not_dvd_four_of_odd_prime hq hq2)]
    have hd := s16h_orderOf_two_zmod_pos hq hq2
    have hle : 4 / Nat.lcm 4 (orderOf (2 : ZMod q)) ≤ 1 := by
      apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 4)
        (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 4 hd))
      have := Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 4 hd
      nlinarith
    omega
  · rcases hm with rfl | rfl
    · rw [s16h_cTable, s16h_orderOf_two_zmod_seven, show (7:ℕ) - 1 = 6 by norm_num]
      by_cases hq3 : q = 3
      · subst hq3
        rw [s16h_orderOf_two_zmod_three]
        norm_num
      · rw [if_neg (fun h => hq3 ((s16h_dvd_six_iff hq hq2).mp h))]
        have hd := s16h_orderOf_two_zmod_pos hq hq2
        have hd3 : 3 ≤ orderOf (2 : ZMod q) := by
          have h2 := s16h_two_le_orderOf_two_zmod hq hq2
          have hne : orderOf (2 : ZMod q) ≠ 2 :=
            fun h => hq3 (s16h_orderOf_two_zmod_eq_two hq hq2 h)
          omega
        have hle : 3 / Nat.lcm 3 (orderOf (2 : ZMod q)) ≤ 1 := by
          apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 3)
            (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 3 hd))
          have := Nat.le_lcm_right (m := 3) (orderOf (2 : ZMod q)) (by norm_num)
          nlinarith
        omega
    · rw [s16h_cTable, s16h_orderOf_two_zmod_seven, show (7:ℕ) - 1 = 6 by norm_num]
      by_cases hq3 : q = 3
      · subst hq3
        rw [s16h_orderOf_two_zmod_three]
        norm_num
      · rw [if_neg (fun h => hq3 ((s16h_dvd_six_iff hq hq2).mp h))]
        have hd := s16h_orderOf_two_zmod_pos hq hq2
        have hd3 : 3 ≤ orderOf (2 : ZMod q) := by
          have h2 := s16h_two_le_orderOf_two_zmod hq hq2
          have hne : orderOf (2 : ZMod q) ≠ 2 :=
            fun h => hq3 (s16h_orderOf_two_zmod_eq_two hq hq2 h)
          omega
        have hle : 6 / Nat.lcm 3 (orderOf (2 : ZMod q)) ≤ 2 := by
          apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 3)
            (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 3 hd))
          have := Nat.le_lcm_right (m := 3) (orderOf (2 : ZMod q)) (by norm_num)
          nlinarith
        omega

theorem s16h_cTable_le_one {p m q : ℕ} (hrow : s16h_ZpRow p m) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqp : q ≠ p) (hex : ¬ (p = 7 ∧ m = 6 ∧ q = 3)) : s16h_cTable p m q ≤ 1 := by
  rcases hrow with ⟨rfl, hm⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hm⟩
  · rcases hm with rfl | rfl | rfl
    · rw [s16h_cTable, s16h_orderOf_two_zmod_three, show (3:ℕ) - 1 = 2 by norm_num,
        if_neg (s16h_not_dvd_two_of_odd_prime hq hq2)]
      have hd := s16h_orderOf_two_zmod_pos hq hq2
      have hd3 : 3 ≤ orderOf (2 : ZMod q) := by
        have h2 := s16h_two_le_orderOf_two_zmod hq hq2
        have hne : orderOf (2 : ZMod q) ≠ 2 :=
          fun h => hqp (s16h_orderOf_two_zmod_eq_two hq hq2 h)
        omega
      have hle : 2 / Nat.lcm 2 (orderOf (2 : ZMod q)) ≤ 1 := by
        apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2)
          (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 2 hd))
        have := Nat.le_lcm_right (m := 2) (orderOf (2 : ZMod q)) (by norm_num)
        nlinarith
      omega
    · rw [s16h_cTable, s16h_orderOf_two_zmod_three, show (3:ℕ) - 1 = 2 by norm_num,
        if_neg (s16h_not_dvd_two_of_odd_prime hq hq2)]
      have hd := s16h_orderOf_two_zmod_pos hq hq2
      have hd3 : 3 ≤ orderOf (2 : ZMod q) := by
        have h2 := s16h_two_le_orderOf_two_zmod hq hq2
        have hne : orderOf (2 : ZMod q) ≠ 2 :=
          fun h => hqp (s16h_orderOf_two_zmod_eq_two hq hq2 h)
        omega
      have hle : 4 / Nat.lcm 2 (orderOf (2 : ZMod q)) ≤ 1 := by
        apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2)
          (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 2 hd))
        have := Nat.le_lcm_right (m := 2) (orderOf (2 : ZMod q)) (by norm_num)
        nlinarith
      omega
    · rw [s16h_cTable, s16h_orderOf_two_zmod_three, show (3:ℕ) - 1 = 2 by norm_num,
        if_neg (s16h_not_dvd_two_of_odd_prime hq hq2)]
      have hd := s16h_orderOf_two_zmod_pos hq hq2
      have hd3 : 3 ≤ orderOf (2 : ZMod q) := by
        have h2 := s16h_two_le_orderOf_two_zmod hq hq2
        have hne : orderOf (2 : ZMod q) ≠ 2 :=
          fun h => hqp (s16h_orderOf_two_zmod_eq_two hq hq2 h)
        omega
      have h4 : 4 ≤ Nat.lcm 2 (orderOf (2 : ZMod q)) := by
        have hdvd : 2 ∣ Nat.lcm 2 (orderOf (2 : ZMod q)) := Nat.dvd_lcm_left 2 _
        have h3 : 3 ≤ Nat.lcm 2 (orderOf (2 : ZMod q)) :=
          le_trans hd3 (Nat.le_lcm_right (m := 2) (orderOf (2 : ZMod q)) (by norm_num))
        obtain ⟨k, hk⟩ := hdvd
        omega
      have hle : 6 / Nat.lcm 2 (orderOf (2 : ZMod q)) ≤ 1 := by
        apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 2)
          (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 2 hd))
        nlinarith
      omega
  · rw [s16h_cTable, s16h_orderOf_two_zmod_five, show (5:ℕ) - 1 = 4 by norm_num,
      if_neg (s16h_not_dvd_four_of_odd_prime hq hq2)]
    have hd := s16h_orderOf_two_zmod_pos hq hq2
    have hle : 4 / Nat.lcm 4 (orderOf (2 : ZMod q)) ≤ 1 := by
      apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 4)
        (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 4 hd))
      have := Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 4 hd
      nlinarith
    omega
  · rcases hm with rfl | rfl
    · rw [s16h_cTable, s16h_orderOf_two_zmod_seven, show (7:ℕ) - 1 = 6 by norm_num]
      by_cases hq3 : q = 3
      · subst hq3
        rw [s16h_orderOf_two_zmod_three]
        norm_num
      · rw [if_neg (fun h => hq3 ((s16h_dvd_six_iff hq hq2).mp h))]
        have hd := s16h_orderOf_two_zmod_pos hq hq2
        have hd3 : 3 ≤ orderOf (2 : ZMod q) := by
          have h2 := s16h_two_le_orderOf_two_zmod hq hq2
          have hne : orderOf (2 : ZMod q) ≠ 2 :=
            fun h => hq3 (s16h_orderOf_two_zmod_eq_two hq hq2 h)
          omega
        have hle : 3 / Nat.lcm 3 (orderOf (2 : ZMod q)) ≤ 1 := by
          apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 3)
            (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 3 hd))
          have := Nat.le_lcm_right (m := 3) (orderOf (2 : ZMod q)) (by norm_num)
          nlinarith
        omega
    · have hq3 : q ≠ 3 := fun h => hex ⟨rfl, rfl, h⟩
      rw [s16h_cTable, s16h_orderOf_two_zmod_seven, show (7:ℕ) - 1 = 6 by norm_num,
        if_neg (fun h => hq3 ((s16h_dvd_six_iff hq hq2).mp h))]
      have hd := s16h_orderOf_two_zmod_pos hq hq2
      have hd4 : 4 ≤ orderOf (2 : ZMod q) := by
        have h2 := s16h_two_le_orderOf_two_zmod hq hq2
        have hne2 : orderOf (2 : ZMod q) ≠ 2 :=
          fun h => hq3 (s16h_orderOf_two_zmod_eq_two hq hq2 h)
        have hne3 : orderOf (2 : ZMod q) ≠ 3 :=
          fun h => hqp (s16h_orderOf_two_zmod_eq_three hq hq2 h)
        omega
      have h4 : 4 ≤ Nat.lcm 3 (orderOf (2 : ZMod q)) :=
        le_trans hd4 (Nat.le_lcm_right (m := 3) (orderOf (2 : ZMod q)) (by norm_num))
      have hle : 6 / Nat.lcm 3 (orderOf (2 : ZMod q)) ≤ 1 := by
        apply s16h_div_le_of_lt_mul (lt_of_lt_of_le (by norm_num : (0:ℕ) < 3)
          (Nat.le_lcm_left (n := orderOf (2 : ZMod q)) 3 hd))
        nlinarith
      omega

theorem s16h_blockBound_two_of_cyclic {W : Type} [CommGroup W] [Finite W]
    (hV : ∀ v : W, v ^ 2 = 1) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) {A L : Subgroup (MulAut W)} (hLc : IsCyclic ↥L) (hLp : Nat.card ↥L = p)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥)
    (hrow : s16h_ZpRow p (rk ↥(commSub (⊤ : Subgroup W) L)))
    (hex : ¬ (p = 3 ∧ rk ↥(commSub (⊤ : Subgroup W) L) = 6 ∧ q = 3)) :
    s16h_BlockBound A L q 2 :=
  s16h_blockBound_mono hq.pos le_rfl (s16h_cTable_le_two hrow hq hq2 hex)
    (s16h_blockBound_of_cyclic hV hp hq hp2 hq2 hLc hLp hfix)

theorem s16h_blockBound_one_of_cyclic {W : Type} [CommGroup W] [Finite W]
    (hV : ∀ v : W, v ^ 2 = 1) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hqp : q ≠ p) {A L : Subgroup (MulAut W)} (hLc : IsCyclic ↥L)
    (hLp : Nat.card ↥L = p) (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥)
    (hrow : s16h_ZpRow p (rk ↥(commSub (⊤ : Subgroup W) L)))
    (hex : ¬ (p = 7 ∧ rk ↥(commSub (⊤ : Subgroup W) L) = 6 ∧ q = 3)) :
    s16h_BlockBound A L q 1 :=
  s16h_blockBound_mono hq.pos le_rfl (s16h_cTable_le_one hrow hq hq2 hqp hex)
    (s16h_blockBound_of_cyclic hV hp hq hp2 hq2 hLc hLp hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
