module

public import CFSG.RankThree.PartOne.S11c.Sec66Glue

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartOne.Sec66T

section Outer

variable {G : Type} [Group G]

theorem mem_center_of_centerQuotientConj_eq_one {L : Subgroup G} (hL : Group.IsPerfect ↥L) (l : L)
    (h : centerQuotientConj L ⟨(l : G), Subgroup.le_normalizer l.2⟩ = 1) :
    l ∈ Subgroup.center L := by
  have : Group.IsPerfect ↥L := hL
  have hAL : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have := commute_of_centerQuotientAction_eq_one (A := L) (L := L) hAL l h
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (this g).symm

theorem exists_pow_mul_eq {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    {l : G} (hl : l ∈ L) (n : ℕ) : ∃ l' ∈ L, (l * g) ^ n = l' * g ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', h⟩ := ih
    refine ⟨l' * (g ^ n * l * (g ^ n)⁻¹), L.mul_mem hl' ?_, ?_⟩
    · have hgn : g ^ n ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hg n
      exact (Subgroup.mem_normalizer_iff.mp hgn l).mp hl
    · rw [pow_succ, h]
      group

theorem pow_apply_eq_of_fix {T : Type} [Group T] {β : MulAut T} {r : T} (h : β r = r) (k : ℕ) :
    (β ^ k) r = r := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, h, ih]

theorem pow_apply_mem_of_inv {T : Type} [Group T] {β : MulAut T} {U : Subgroup T}
    (h : ∀ u ∈ U, β u ∈ U) (k : ℕ) : ∀ u ∈ U, (β ^ k) u ∈ U := by
  induction k with
  | zero => intro u hu; simpa using hu
  | succ k ih =>
    intro u hu
    rw [pow_succ, MulAut.mul_apply]
    exact ih _ (h u hu)

variable [Finite G]

theorem exists_lift_pElement {p : ℕ} (hp : p.Prime) {L : Subgroup G} (hL : Group.IsPerfect ↥L)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hxp : x ^ p = 1) (l : L) (j : ℕ)
    (hβp : (MulAut.conj (l : ↥L ⧸ Subgroup.center ↥L) * centerQuotientConj L ⟨x, hx⟩ ^ j) ^ p = 1)
    (hβ1 : MulAut.conj (l : ↥L ⧸ Subgroup.center ↥L) * centerQuotientConj L ⟨x, hx⟩ ^ j ≠ 1) :
    ∃ (x' : G) (hx' : x' ∈ Subgroup.normalizer (L : Set G)),
      x' ∈ L ⊔ Subgroup.zpowers x ∧ x' ^ p = 1 ∧ ∃ k : ℕ, ¬ p ∣ k ∧
        centerQuotientConj L ⟨x', hx'⟩ =
          (MulAut.conj (l : ↥L ⧸ Subgroup.center ↥L) * centerQuotientConj L ⟨x, hx⟩ ^ j) ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set α := centerQuotientConj L ⟨x, hx⟩ with hα
  set β := MulAut.conj (l : ↥L ⧸ Subgroup.center ↥L) * α ^ j with hβ
  set y : G := (l : G) * x ^ j with hy
  have hlN : (l : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l.2
  have hyN : y ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ hlN (Subgroup.pow_mem _ hx j)
  have hΦy : centerQuotientConj L ⟨y, hyN⟩ = β := by
    have : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set G)) = ⟨(l : G), hlN⟩ * ⟨x, hx⟩ ^ j :=
      Subtype.ext (by simp [hy])
    rw [this, map_mul, map_pow, centerQuotientConj_of_mem l]
  have hymem : y ∈ L ⊔ Subgroup.zpowers x :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2)
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j))
  obtain ⟨l', hl', hl'y⟩ := exists_pow_mul_eq (L := L) (Subgroup.pow_mem _ hx j) l.2 p
  have hypL : y ^ p ∈ L := by
    have h1 : (x ^ j) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxp, one_pow]
    rw [hy, hl'y, h1, mul_one]
    exact hl'
  set z : L := ⟨y ^ p, hypL⟩ with hz
  have hΦz : centerQuotientConj L ⟨(z : G), Subgroup.le_normalizer z.2⟩ = 1 := by
    have : (⟨(z : G), Subgroup.le_normalizer z.2⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨y, hyN⟩ ^ p := Subtype.ext (by simp [hz])
    rw [this, map_pow, hΦy, hβp]
  have hzc : z ∈ Subgroup.center L := mem_center_of_centerQuotientConj_eq_one hL z hΦz
  have hordz : orderOf (y ^ p) ∣ Nat.card (Subgroup.center L) := by
    have h1 : orderOf (y ^ p) = orderOf z := Subgroup.orderOf_coe z
    rw [h1]
    exact Subgroup.orderOf_dvd_natCard (Subgroup.center L) hzc
  have hn0 : 0 < orderOf y := orderOf_pos y
  by_cases hdiv : p ∣ orderOf y
  · set m := orderOf y / p with hm
    have hn : orderOf y = p * m := (Nat.mul_div_cancel' hdiv).symm
    have hord_yp : orderOf (y ^ p) = m := orderOf_pow_of_dvd hp.ne_zero hdiv
    have hpm : ¬ p ∣ m := fun h => hZ (h.trans (hord_yp ▸ hordz))
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hn
      omega
    have hmdvd : m ∣ orderOf y := ⟨p, by rw [hn, mul_comm]⟩
    have hord_x' : orderOf (y ^ m) = p := by
      rw [orderOf_pow_of_dvd hm0 hmdvd, hn, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
    refine ⟨y ^ m, Subgroup.pow_mem _ hyN m, Subgroup.pow_mem _ hymem m, ?_, m, hpm, ?_⟩
    · have := pow_orderOf_eq_one (y ^ m)
      rwa [hord_x'] at this
    · have : (⟨y ^ m, Subgroup.pow_mem _ hyN m⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨y, hyN⟩ ^ m := Subtype.ext (by simp)
      rw [this, map_pow, hΦy]
  · exfalso
    have h1 : β ^ orderOf y = 1 := by
      have : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set G)) ^ orderOf y = 1 :=
        Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [← hΦy, ← map_pow, this, map_one]
    have h2 := pow_gcd_eq_one.2 ⟨h1, hβp⟩
    have hcop : Nat.gcd (orderOf y) p = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdiv)
    rw [hcop, pow_one] at h2
    exact hβ1 h2

end Outer

end CFSG.RankThree.PartOne
