module

public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PGroups

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem eq_one_of_pow_prime_pow_eq_one {x : G} {n m : ℕ} (hx : x ^ (p ^ n) = 1)
    (hm : x ^ m = 1) (hmp : Nat.Coprime m p) : x = 1 := by
  rw [← orderOf_eq_one_iff]
  have hcop : Nat.Coprime (orderOf x) m :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hx) (Nat.Coprime.pow_left n hmp.symm)
  exact Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hm)

theorem orderOf_inv_mul_mul (h x : G) : orderOf (h⁻¹ * x * h) = orderOf x := by
  have h' := MulEquiv.orderOf_eq (MulAut.conj h⁻¹) x
  rwa [MulAut.conj_apply, inv_inv] at h'

theorem mem_zpowers_of_primary {g a b : G} (hab : a * b = g) (hba : b * a = g)
    (ha : ∃ n : ℕ, orderOf a = p ^ n) (hbp : Nat.Coprime (orderOf b) p) :
    a ∈ zpowers g ∧ b ∈ zpowers g := by
  obtain ⟨n, hn⟩ := ha
  have hcop : Nat.Coprime (orderOf a) (orderOf b) := by
    rw [hn]
    exact Nat.Coprime.pow_left n hbp.symm
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hcomm : Commute a b := hab.trans hba.symm
  have hga : g ^ (y * (orderOf b : ℤ)) = a := by
    have hb1 : b ^ (y * (orderOf b : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    have ha1 : a ^ (y * (orderOf b : ℤ)) = a := by
      rw [show y * (orderOf b : ℤ) = 1 + (-x) * (orderOf a : ℤ) by linear_combination hxy,
        zpow_add, zpow_one, mul_comm (-x), zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow,
        mul_one]
    rw [← hab, hcomm.mul_zpow, ha1, hb1, mul_one]
  have haz : a ∈ zpowers g := ⟨_, hga⟩
  refine ⟨haz, ?_⟩
  have hb' : b = a⁻¹ * g := by rw [← hab, inv_mul_cancel_left]
  rw [hb']
  exact mul_mem (inv_mem haz) (mem_zpowers g)

theorem primary_unique {g a b c d : G} (hab : a * b = g) (hba : b * a = g)
    (ha : ∃ n : ℕ, orderOf a = p ^ n) (hbp : Nat.Coprime (orderOf b) p)
    (hcd : c * d = g) (hdc : d * c = g) (hc : ∃ n : ℕ, orderOf c = p ^ n)
    (hdp : Nat.Coprime (orderOf d) p) : a = c ∧ b = d := by
  obtain ⟨haz, hbz⟩ := mem_zpowers_of_primary hab hba ha hbp
  obtain ⟨hcz, hdz⟩ := mem_zpowers_of_primary hcd hdc hc hdp
  have hcomm : ∀ x ∈ zpowers g, ∀ y ∈ zpowers g, Commute x y := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.refl g).zpow_zpow i j
  have hx : c⁻¹ * a = d * b⁻¹ := by
    calc c⁻¹ * a = c⁻¹ * (a * b) * b⁻¹ := by group
      _ = c⁻¹ * (c * d) * b⁻¹ := by rw [hab, hcd]
      _ = d * b⁻¹ := by group
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hc
  have hpow : (c⁻¹ * a) ^ (p ^ (s + t)) = 1 := by
    have hc1 : c ^ (p ^ (s + t)) = 1 := by
      rw [pow_add, mul_comm, pow_mul, ← ht, pow_orderOf_eq_one, one_pow]
    have ha1 : a ^ (p ^ (s + t)) = 1 := by
      rw [pow_add, pow_mul, ← hs, pow_orderOf_eq_one, one_pow]
    rw [((hcomm _ hcz _ haz).inv_left).mul_pow, inv_pow, hc1, ha1, inv_one, one_mul]
  have hm : (c⁻¹ * a) ^ (orderOf d * orderOf b) = 1 := by
    have hd1 : d ^ (orderOf d * orderOf b) = 1 := by
      rw [pow_mul, pow_orderOf_eq_one, one_pow]
    have hb1 : b ^ (orderOf d * orderOf b) = 1 := by
      rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    rw [hx, ((hcomm _ hdz _ hbz).inv_right).mul_pow, inv_pow, hd1, hb1, inv_one, one_mul]
  have h1 := eq_one_of_pow_prime_pow_eq_one hpow hm (Nat.coprime_mul_iff_left.2 ⟨hdp, hbp⟩)
  have hac : a = c := (inv_mul_eq_one.1 h1).symm
  refine ⟨hac, ?_⟩
  rw [hac] at hab
  exact mul_left_cancel (hab.trans hcd.symm)

theorem prime_primary_factorization {g : G} (hg : IsOfFinOrder g) (hp : p.Prime) :
    (∃! ab : G × G, ab.1 * ab.2 = g ∧ ab.2 * ab.1 = g ∧ (∃ n : ℕ, orderOf ab.1 = p ^ n) ∧
      IsOfFinOrder ab.2 ∧ Nat.Coprime (orderOf ab.2) p) ∧
    ∀ a b : G, a * b = g → b * a = g → (∃ n : ℕ, orderOf a = p ^ n) → IsOfFinOrder b →
      Nat.Coprime (orderOf b) p →
      a ∈ zpowers g ∧ b ∈ zpowers g ∧
      ∀ h : G, ((h⁻¹ * a * h) * (h⁻¹ * b * h) = h⁻¹ * g * h ∧
          (h⁻¹ * b * h) * (h⁻¹ * a * h) = h⁻¹ * g * h ∧
          (∃ n : ℕ, orderOf (h⁻¹ * a * h) = p ^ n) ∧ IsOfFinOrder (h⁻¹ * b * h) ∧
          Nat.Coprime (orderOf (h⁻¹ * b * h)) p) ∧
        ∀ c d : G, c * d = h⁻¹ * g * h → d * c = h⁻¹ * g * h → (∃ n : ℕ, orderOf c = p ^ n) →
          IsOfFinOrder d → Nat.Coprime (orderOf d) p → c = h⁻¹ * a * h ∧ d = h⁻¹ * b * h := by
  refine ⟨?_, fun a b hab hba ha hb hbp => ⟨(mem_zpowers_of_primary hab hba ha hbp).1,
    (mem_zpowers_of_primary hab hba ha hbp).2, fun h => ?_⟩⟩
  ·
    have hn := hg.orderOf_pos
    set n := orderOf g with hndef
    set q := p ^ n.factorization p with hqdef
    set m := n / q with hmdef
    have hqm : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hpm : Nat.Coprime p m := Nat.coprime_ordCompl hp hn.ne'
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hqm; omega
    obtain ⟨u, v, huv⟩ :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left (n.factorization p) hpm)
    have hq : (q : ℤ) * m = n := by exact_mod_cast hqm
    have h1 : g ^ (v * (m : ℤ)) * g ^ (u * (q : ℤ)) = g := by
      rw [← zpow_add, show v * (m : ℤ) + u * q = 1 by linear_combination huv, zpow_one]
    have h2 : g ^ (u * (q : ℤ)) * g ^ (v * (m : ℤ)) = g := by
      rw [← zpow_add, show u * (q : ℤ) + v * m = 1 by linear_combination huv, zpow_one]
    have hapow : (g ^ (v * (m : ℤ))) ^ q = 1 := by
      rw [← zpow_natCast, ← zpow_mul, show v * (m : ℤ) * q = v * n by rw [← hq]; ring,
        mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    have hbpow : (g ^ (u * (q : ℤ))) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, show u * (q : ℤ) * m = u * n by rw [← hq]; ring,
        mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    have h3 : ∃ k : ℕ, orderOf (g ^ (v * (m : ℤ))) = p ^ k := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hapow)
      exact ⟨k, hk⟩
    have h4 : IsOfFinOrder (g ^ (u * (q : ℤ))) := isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm0, hbpow⟩
    have h5 : Nat.Coprime (orderOf (g ^ (u * (q : ℤ)))) p :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hbpow) hpm.symm
    refine ⟨(g ^ (v * (m : ℤ)), g ^ (u * (q : ℤ))), ⟨h1, h2, h3, h4, h5⟩, ?_⟩
    rintro ⟨c, d⟩ ⟨hcd, hdc, hc, -, hdp⟩
    dsimp only at hcd hdc hc hdp
    obtain ⟨hc', hd'⟩ := primary_unique hcd hdc hc hdp h1 h2 h3 h5
    exact Prod.ext hc' hd'
  ·
    have hab' : (h⁻¹ * a * h) * (h⁻¹ * b * h) = h⁻¹ * g * h := by rw [← hab]; group
    have hba' : (h⁻¹ * b * h) * (h⁻¹ * a * h) = h⁻¹ * g * h := by rw [← hba]; group
    have ha' : ∃ n : ℕ, orderOf (h⁻¹ * a * h) = p ^ n := by
      rw [orderOf_inv_mul_mul]
      exact ha
    have hb' : IsOfFinOrder (h⁻¹ * b * h) := by
      rw [← orderOf_pos_iff, orderOf_inv_mul_mul]
      exact hb.orderOf_pos
    have hbp' : Nat.Coprime (orderOf (h⁻¹ * b * h)) p := by
      rw [orderOf_inv_mul_mul]
      exact hbp
    exact ⟨⟨hab', hba', ha', hb', hbp'⟩, fun c d hcd hdc hc _ hdp =>
      primary_unique hcd hdc hc hdp hab' hba' ha' hbp'⟩

theorem existsUnique_blocksIsPPart {g : G} (hg : IsOfFinOrder g) (hp : p.Prime) :
    ∃! a : G, CFSG.BlocksIsPPart p g a := by
  obtain ⟨⟨⟨a, b⟩, ⟨hab, hba, ha, hb, hbp⟩, -⟩, -⟩ := prime_primary_factorization hg hp
  refine ⟨a, ⟨b, hab, hba, ha, hb.orderOf_pos, hbp⟩, ?_⟩
  rintro c ⟨d, hcd, hdc, hc, -, hdp⟩
  exact (primary_unique hcd hdc hc hdp hab hba ha hbp).1

end CFSG.RankThree.PGroups
