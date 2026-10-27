module

public import CFSG.Timmesfeld.RankOne.Points
public import CFSG.Timmesfeld.Basic
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Timmesfeld

variable {X : Type*} [Group X]

open RankOne

@[expose] def weylSet (A B : Subgroup X) : Set X :=
  {m | m ≠ 1 ∧ (∃ g : X, m ∈ A.map (MulAut.conj g).toMonoidHom) ∧
    A.map (MulAut.conj m).toMonoidHom = B}

@[expose] def hua (A B : Subgroup X) : Subgroup X :=
  Subgroup.closure {x | ∃ m ∈ weylSet A B, ∃ m' ∈ weylSet A B, x = m * m'}

namespace IsElemAbRankOne

variable {A B : Subgroup X} (h : IsElemAbRankOne A B)
include h

theorem eq_of_commute {x g u w : X} (hu : u ∈ A.map (MulAut.conj x).toMonoidHom)
    (hu1 : u ≠ 1) (hw : w ∈ A.map (MulAut.conj g).toMonoidHom) (hw1 : w ≠ 1)
    (hc : Commute u w) :
    A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj x).toMonoidHom := by
  have hfixu : (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj u).toMonoidHom =
      A.map (MulAut.conj x).toMonoidHom := map_conj_of_mem hu
  have h1 : (A.map (MulAut.conj (w * x)).toMonoidHom).map (MulAut.conj u).toMonoidHom =
      A.map (MulAut.conj (w * x)).toMonoidHom :=
    calc (A.map (MulAut.conj (w * x)).toMonoidHom).map (MulAut.conj u).toMonoidHom
        = A.map (MulAut.conj (u * (w * x))).toMonoidHom := (map_conj_mul _ _ _).symm
      _ = A.map (MulAut.conj (w * (u * x))).toMonoidHom := by
          rw [← mul_assoc, ← mul_assoc, hc.eq]
      _ = ((A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj u).toMonoidHom).map
            (MulAut.conj w).toMonoidHom := by rw [map_conj_mul, map_conj_mul A u x]
      _ = A.map (MulAut.conj (w * x)).toMonoidHom := by rw [hfixu, ← map_conj_mul]
  have h2 := h.eq_of_mem_of_map_conj_eq hu hu1 h1
  rw [map_conj_mul] at h2
  exact (h.eq_of_mem_of_map_conj_eq hw hw1 h2).symm

omit h in
theorem _root_.CFSG.Timmesfeld.RankOne.zpow_mul_mul_inv_of_inverts {u r : X}
    (hur : ∀ i : ℤ, u * r ^ i = r ^ (-i) * u) (i : ℤ) :
    r ^ i * u * (r ^ i)⁻¹ = r ^ (2 * i) * u := by
  rw [mul_assoc, ← zpow_neg, hur, neg_neg, ← mul_assoc, ← zpow_add, two_mul]

theorem pow_half_mem {x g u w : X} (hu : u ∈ A.map (MulAut.conj x).toMonoidHom)
    (hu1 : u ≠ 1) (hw : w ∈ A.map (MulAut.conj g).toMonoidHom) {k : ℕ}
    (hk : orderOf (u * w) = k + k) : (u * w) ^ k ∈ A.map (MulAut.conj x).toMonoidHom := by
  have huu : u * u = 1 := h.mul_self_of_mem_map_conj hu
  have hww : w * w = 1 := h.mul_self_of_mem_map_conj hw
  set r := u * w with hr
  set z := r ^ k with hz
  have hzz : z * z = 1 := by
    rw [hz, ← pow_add, ← hk, pow_orderOf_eq_one]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hur : ∀ i : ℤ, u * r ^ i = r ^ (-i) * u := mul_zpow_mul_eq_zpow_neg_mul huu hww
  have huz : u * z = z * u := by
    have := hur k
    rw [zpow_neg, zpow_natCast, ← hz, hzinv] at this
    exact this
  have hconj : ∃ y : X, u * z ∈ A.map (MulAut.conj y).toMonoidHom := by
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
    · refine ⟨r ^ (-(j : ℤ)) * x, ?_⟩
      rw [map_conj_mul]
      have heq : u * z = r ^ (-(j : ℤ)) * u * (r ^ (-(j : ℤ)))⁻¹ := by
        rw [hz, hj, RankOne.zpow_mul_mul_inv_of_inverts hur, ← zpow_natCast, hur]
        congr 2
        push_cast
        ring
      rw [heq]
      exact conj_mem_map_conj _ hu
    · refine ⟨r ^ (-(j : ℤ)) * g, ?_⟩
      rw [map_conj_mul]
      have hw' : w = u * r := by rw [hr, ← mul_assoc, huu, one_mul]
      have heq : u * z = r ^ (-(j : ℤ)) * w * (r ^ (-(j : ℤ)))⁻¹ := by
        rw [hz, hj, hw']
        symm
        calc r ^ (-(j:ℤ)) * (u * r) * (r ^ (-(j:ℤ)))⁻¹
            = r ^ (-(j:ℤ)) * (u * r ^ ((j:ℤ) + 1)) := by
              rw [← zpow_neg, neg_neg, zpow_add_one]; group
          _ = r ^ (-(j:ℤ)) * (r ^ (-((j:ℤ) + 1)) * u) := by rw [hur]
          _ = r ^ (-(((2 * j + 1 : ℕ)) : ℤ)) * u := by
              rw [← mul_assoc, ← zpow_add]; congr 2; push_cast; ring
          _ = u * r ^ (2 * j + 1) := by rw [← hur, zpow_natCast]
      rw [heq]
      exact conj_mem_map_conj _ hw
  obtain ⟨y, hy⟩ := hconj
  by_cases huz1 : u * z = 1
  · have : z = u := by
      calc z = u * (u * z) := by rw [← mul_assoc, huu, one_mul]
        _ = u := by rw [huz1, mul_one]
    rw [this]
    exact hu
  · have hc : Commute u (u * z) := by
      change u * (u * z) = u * z * u
      rw [mul_assoc u z u, ← huz]
    have hyx := h.eq_of_commute hu hu1 hy huz1 hc
    have : z = u * (u * z) := by rw [← mul_assoc, huu, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ hu (hyx ▸ hy)

theorem odd_orderOf_mul [Finite X] {x g u w : X} (hu : u ∈ A.map (MulAut.conj x).toMonoidHom)
    (hu1 : u ≠ 1) (hw : w ∈ A.map (MulAut.conj g).toMonoidHom) (hw1 : w ≠ 1)
    (hne : A.map (MulAut.conj x).toMonoidHom ≠ A.map (MulAut.conj g).toMonoidHom) :
    Odd (orderOf (u * w)) := by
  rcases Nat.even_or_odd (orderOf (u * w)) with ⟨k, hk⟩ | hodd
  · exfalso
    have huu : u * u = 1 := h.mul_self_of_mem_map_conj hu
    have hww : w * w = 1 := h.mul_self_of_mem_map_conj hw
    have hwu : w * u = (u * w)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right huu, inv_eq_of_mul_eq_one_right hww]
    have hk' : orderOf (w * u) = k + k := by rw [hwu, orderOf_inv, hk]
    have h1 := h.pow_half_mem hu hu1 hw hk
    have h2 := h.pow_half_mem hw hw1 hu hk'
    have hzz : ((u * w) ^ k)⁻¹ = (u * w) ^ k := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_add, ← hk, pow_orderOf_eq_one]
    rw [hwu, inv_pow, hzz] at h2
    have hbot := h.map_conj_inf_eq_bot hne
    have hz1 : (u * w) ^ k = 1 := by
      have : (u * w) ^ k ∈ A.map (MulAut.conj x).toMonoidHom ⊓
          A.map (MulAut.conj g).toMonoidHom := ⟨h1, h2⟩
      rwa [hbot, Subgroup.mem_bot] at this
    have hpos : 0 < orderOf (u * w) := orderOf_pos _
    have hlt : k < orderOf (u * w) := by omega
    exact pow_ne_one_of_lt_orderOf (by omega) hlt hz1
  · exact hodd

omit h in
theorem mem_map_conj_one {a : X} (ha : a ∈ A) : a ∈ A.map (MulAut.conj (1 : X)).toMonoidHom := by
  rwa [map_conj_one]

omit h in
theorem _root_.CFSG.Timmesfeld.RankOne.mul_mul_cancel_of_mul_self {x : X} (hx : x * x = 1)
    (y : X) : x * (x * y) = y := by
  rw [← mul_assoc, hx, one_mul]

omit h in
theorem map_conj_mul_of {H K : Subgroup X} {g g' : X}
    (h' : H.map (MulAut.conj g').toMonoidHom = K) :
    H.map (MulAut.conj (g * g')).toMonoidHom = K.map (MulAut.conj g).toMonoidHom := by
  rw [map_conj_mul, h']

theorem mul_pow_three [Finite X] {a b : X} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ B)
    (hab : A.map (MulAut.conj b).toMonoidHom = B.map (MulAut.conj a).toMonoidHom) :
    (a * b) ^ 3 = 1 := by
  have haa : a * a = 1 := h.sq a ha
  have hbb : b * b = 1 := h.symm.sq b hb
  have haa' := RankOne.mul_mul_cancel_of_mul_self haa
  have hbb' := RankOne.mul_mul_cancel_of_mul_self hbb
  have hab' : B.map (MulAut.conj a).toMonoidHom = A.map (MulAut.conj b).toMonoidHom := hab.symm
  have e1 : A.map (MulAut.conj (b * a * b)).toMonoidHom = B := by
    rw [map_conj_mul_of hab, ← map_conj_mul, mul_assoc, haa, mul_one, map_conj_of_mem hb]
  have e2 : B.map (MulAut.conj (b * a * b)).toMonoidHom = A := by
    rw [map_conj_mul_of (map_conj_of_mem hb), map_conj_mul, hab', ← map_conj_mul, hbb,
      map_conj_one]
  have e3 : A.map (MulAut.conj (a * b * a)).toMonoidHom = B := by
    rw [map_conj_mul_of (map_conj_of_mem ha), map_conj_mul, hab, ← map_conj_mul, haa,
      map_conj_one]
  have e4 : B.map (MulAut.conj (a * b * a)).toMonoidHom = A := by
    rw [map_conj_mul_of hab', ← map_conj_mul, mul_assoc, hbb, mul_one, map_conj_of_mem ha]
  set w := b * a * b * (a * b * a) with hw
  have hwA : A.map (MulAut.conj w).toMonoidHom = A := by rw [map_conj_mul_of e3, e2]
  have hwB : B.map (MulAut.conj w).toMonoidHom = B := by rw [map_conj_mul_of e4, e1]
  have hwinv : w⁻¹ = a * w * a := by
    rw [hw]
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb,
      mul_assoc, haa, mul_one]
  have hwaw : w * a * w⁻¹ ∈ A := by
    have := conj_mem_map_conj w ha
    rwa [hwA] at this
  have hww : w * w ∈ A := by
    have heq : w * w = w * a * w⁻¹ * a := by
      rw [hwinv]
      simp only [mul_assoc, haa, haa', mul_one]
    rw [heq]
    exact A.mul_mem hwaw ha
  have hwwB : B.map (MulAut.conj (w * w)).toMonoidHom = B := by
    rw [map_conj_mul, hwB, hwB]
  have hw2 : w * w = 1 := h.eq_one_of_map_conj_eq hww hwwB
  have hab3 : (a * b) ^ 3 = w⁻¹ := by
    rw [hwinv, hw]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc, haa, mul_one]
  have h6 : (a * b) ^ 6 = 1 := by
    rw [show 6 = 3 + 3 from rfl, pow_add, hab3, ← mul_inv_rev, hw2, inv_one]
  have hdvd : orderOf (a * b) ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  obtain ⟨g₀, hg₀⟩ := h.exists_eq_map_conj
  have hne : A.map (MulAut.conj (1 : X)).toMonoidHom ≠ A.map (MulAut.conj g₀).toMonoidHom := by
    rw [map_conj_one, ← hg₀]
    exact h.ne
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [map_conj_one] at hab
    exact h.map_conj_ne ha hab.symm
  have hodd := h.odd_orderOf_mul (mem_map_conj_one ha) ha1 (hg₀ ▸ hb) hb1 hne
  have hne1 : orderOf (a * b) ≠ 1 := by
    intro h1
    rw [orderOf_eq_one_iff, mul_eq_one_iff_eq_inv] at h1
    have : a ∈ A ⊓ B := ⟨ha, h1 ▸ B.inv_mem hb⟩
    rw [h.inf_eq_bot, Subgroup.mem_bot] at this
    exact ha1 this
  have h3 : orderOf (a * b) = 3 := by
    have hle : orderOf (a * b) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hn : orderOf (a * b) <;> simp_all (config := { decide := true })
  rw [← h3, pow_orderOf_eq_one]

theorem mul_mul_eq [Finite X] {a b : X} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ B)
    (hab : A.map (MulAut.conj b).toMonoidHom = B.map (MulAut.conj a).toMonoidHom) :
    a * b * a = b * a * b := by
  have haa : a * a = 1 := h.sq a ha
  have hbb : b * b = 1 := h.symm.sq b hb
  have haa' := RankOne.mul_mul_cancel_of_mul_self haa
  have hbb' := RankOne.mul_mul_cancel_of_mul_self hbb
  have h3 := h.mul_pow_three ha ha1 hb hab
  calc a * b * a = (a * b) ^ 3 * (b * a * b) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc, hbb, hbb', haa', mul_one]
    _ = b * a * b := by rw [h3, one_mul]

theorem mul_self_of_mem_weylSet {m : X} (hm : m ∈ weylSet A B) : m * m = 1 := by
  obtain ⟨-, ⟨g, hg⟩, -⟩ := hm
  exact h.mul_self_of_mem_map_conj hg

theorem map_conj_B_of_mem_weylSet {m : X} (hm : m ∈ weylSet A B) :
    B.map (MulAut.conj m).toMonoidHom = A := by
  rw [← hm.2.2, ← map_conj_mul, h.mul_self_of_mem_weylSet hm, map_conj_one]

theorem mul_mul_mem_weylSet [Finite X] {a b : X} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ B)
    (hab : A.map (MulAut.conj b).toMonoidHom = B.map (MulAut.conj a).toMonoidHom) :
    a * b * a ∈ weylSet A B := by
  have haa : a * a = 1 := h.sq a ha
  have hbb : b * b = 1 := h.symm.sq b hb
  have haa' := RankOne.mul_mul_cancel_of_mul_self haa
  refine ⟨?_, ⟨b, ?_⟩, ?_⟩
  · intro h1
    have hb1 : b = 1 := by
      calc b = a * (a * b * a) * a := by simp only [mul_assoc, haa, haa', mul_one]
        _ = 1 := by rw [h1, mul_one, haa]
    rw [hb1, map_conj_one] at hab
    exact h.map_conj_ne ha hab.symm
  · rw [h.mul_mul_eq ha ha1 hb hab]
    have := conj_mem_map_conj b ha
    rwa [inv_eq_of_mul_eq_one_right hbb] at this
  · rw [map_conj_mul_of (map_conj_of_mem ha), map_conj_mul, hab, ← map_conj_mul, haa,
      map_conj_one]

theorem weylSet_nonempty [Finite X] : (weylSet A B).Nonempty := by
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  obtain ⟨b, hb, -, hab⟩ := h.moufang a ha ha1
  exact ⟨_, h.mul_mul_mem_weylSet ha ha1 hb hab⟩

theorem exists_eq_mul_weyl_mul [Finite X] {b : X} (hb : b ∈ B) (hb1 : b ≠ 1) :
    ∃ a ∈ A, ∃ m ∈ weylSet A B, b = a * m * a := by
  obtain ⟨a, ha, ha1, hab⟩ := h.moufang' b hb hb1
  refine ⟨a, ha, a * b * a, h.mul_mul_mem_weylSet ha ha1 hb hab.symm, ?_⟩
  have haa : a * a = 1 := h.sq a ha
  have haa' := RankOne.mul_mul_cancel_of_mul_self haa
  simp only [mul_assoc, haa, haa', mul_one]

theorem mul_mul_mem_weylSet_of_mem {n m : X} (hn : n ∈ weylSet A B) (hm : m ∈ weylSet A B) :
    n * m * n⁻¹ ∈ weylSet A B := by
  obtain ⟨hm1, ⟨g, hg⟩, hmA⟩ := hm
  refine ⟨?_, ⟨n * g, ?_⟩, ?_⟩
  · intro h1
    apply hm1
    calc m = n⁻¹ * (n * m * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  · rw [map_conj_mul]
    exact conj_mem_map_conj n hg
  · rw [map_conj_mul, map_conj_mul, inv_eq_of_mul_eq_one_right (h.mul_self_of_mem_weylSet hn),
      hn.2.2, h.map_conj_B_of_mem_weylSet ⟨hm1, ⟨g, hg⟩, hmA⟩, hn.2.2]

theorem eq_of_mem_weylSet {m m' g : X} (hm : m ∈ weylSet A B) (hm' : m' ∈ weylSet A B)
    (hmg : m ∈ A.map (MulAut.conj g).toMonoidHom)
    (hm'g : m' ∈ A.map (MulAut.conj g).toMonoidHom) : m = m' := by
  by_contra hne
  have hx : m⁻¹ * m' ∈ A.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hmg) hm'g
  have hx1 : m⁻¹ * m' ≠ 1 := fun h1 => hne (inv_mul_eq_one.1 h1)
  have hfix : (A.map (MulAut.conj (1 : X)).toMonoidHom).map
      (MulAut.conj (m⁻¹ * m')).toMonoidHom = A.map (MulAut.conj (1 : X)).toMonoidHom := by
    rw [map_conj_one, map_conj_mul, hm'.2.2,
      inv_eq_of_mul_eq_one_right (h.mul_self_of_mem_weylSet hm),
      h.map_conj_B_of_mem_weylSet hm]
  have hg := h.eq_of_mem_of_map_conj_eq hx hx1 hfix
  rw [map_conj_one] at hg
  have : A.map (MulAut.conj m).toMonoidHom = A := map_conj_of_mem (hg ▸ hmg)
  exact h.ne (this.symm.trans hm.2.2)

theorem exists_mem_pt_of_mem_weylSet {m : X} (hm : m ∈ weylSet A B) :
    ∃ a ∈ A, a ≠ 1 ∧ m ∈ B.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨hm1, ⟨g, hg⟩, hmA⟩ := hm
  have hgA : A.map (MulAut.conj g).toMonoidHom ≠ A := by
    intro hgA
    rw [hgA] at hg
    exact h.ne ((map_conj_of_mem hg).symm.trans hmA)
  obtain ⟨a, ha, haeq⟩ := h.exists_eq_of_map_conj_ne hgA
  refine ⟨a, ha, ?_, haeq ▸ hg⟩
  rintro rfl
  rw [map_conj_one] at haeq
  rw [haeq] at hg
  have := h.map_conj_B_of_mem_weylSet ⟨hm1, ⟨g, haeq ▸ hg⟩, hmA⟩
  rw [map_conj_of_mem hg] at this
  exact h.ne this.symm

theorem hua_le : hua A B ≤ Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) := by
  rw [hua, Subgroup.closure_le]
  rintro _ ⟨m, hm, m', hm', rfl⟩
  refine ⟨map_conj_eq_self_iff.1 ?_, map_conj_eq_self_iff.1 ?_⟩
  · rw [map_conj_mul, hm'.2.2, h.map_conj_B_of_mem_weylSet hm]
  · rw [map_conj_mul, h.map_conj_B_of_mem_weylSet hm', hm.2.2]

theorem conj_mem_hua {n k : X} (hn : n ∈ weylSet A B) (hk : k ∈ hua A B) :
    n * k * n⁻¹ ∈ hua A B := by
  have hle : (hua A B).map (MulAut.conj n).toMonoidHom ≤ hua A B := by
    rw [hua, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨m, hm, m', hm', rfl⟩, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨n * m * n⁻¹, h.mul_mul_mem_weylSet_of_mem hn hm,
      n * m' * n⁻¹, h.mul_mul_mem_weylSet_of_mem hn hm', ?_⟩
    simp [mul_assoc]
  exact hle (conj_mem_map_conj n hk)

theorem normalizer_inf_eq_hua [Finite X] :
    Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) = hua A B := by
  obtain ⟨n, hn⟩ := h.weylSet_nonempty
  have hnn : n * n = 1 := h.mul_self_of_mem_weylSet hn
  have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnn
  have hnn' := RankOne.mul_mul_cancel_of_mul_self hnn
  have hHN := h.hua_le
  have hkA : ∀ k ∈ hua A B, ∀ a ∈ A, k * a * k⁻¹ ∈ A := fun k hk a ha => by
    have := conj_mem_map_conj k ha
    rwa [map_conj_eq_self_iff.2 (Subgroup.mem_inf.1 (hHN hk)).1] at this
  let Y : Set X := {y | (∃ a ∈ A, ∃ k ∈ hua A B, y = a * k) ∨
    (∃ a ∈ A, ∃ a' ∈ A, ∃ k ∈ hua A B, y = a * n * a' * k)}
  have hY1 : (1 : X) ∈ Y := Or.inl ⟨1, A.one_mem, 1, Subgroup.one_mem _, by simp⟩
  have hgenA : ∀ x ∈ A, ∀ y ∈ Y, y * x ∈ Y := by
    rintro x hx y (⟨a, ha, k, hk, rfl⟩ | ⟨a, ha, a', ha', k, hk, rfl⟩)
    · exact Or.inl ⟨a * (k * x * k⁻¹), A.mul_mem ha (hkA k hk x hx), k, hk, by group⟩
    · exact Or.inr ⟨a, ha, a' * (k * x * k⁻¹), A.mul_mem ha' (hkA k hk x hx), k, hk, by group⟩
  have hgenn : ∀ y ∈ Y, y * n ∈ Y := by
    have hkn : ∀ k ∈ hua A B, n * k * n ∈ hua A B := fun k hk => by
      have := h.conj_mem_hua hn hk
      rwa [hninv] at this
    rintro y (⟨a, ha, k, hk, rfl⟩ | ⟨a, ha, a', ha', k, hk, rfl⟩)
    · refine Or.inr ⟨a, ha, 1, A.one_mem, n * k * n, hkn k hk, ?_⟩
      simp only [mul_one, mul_assoc, hnn']
    · by_cases ha'1 : a' = 1
      · subst ha'1
        refine Or.inl ⟨a, ha, n * k * n, hkn k hk, ?_⟩
        simp only [mul_one, mul_assoc]
      have hb : n * a' * n ∈ B := by
        have := conj_mem_map_conj n ha'
        rwa [hn.2.2, hninv] at this
      have hb1 : n * a' * n ≠ 1 := by
        intro h1
        apply ha'1
        calc a' = n * (n * a' * n) * n := by simp only [mul_assoc, hnn, hnn', mul_one]
          _ = 1 := by rw [h1, mul_one, hnn]
      obtain ⟨a₁, ha₁, m, hm, hbeq⟩ := h.exists_eq_mul_weyl_mul hb hb1
      have hmm : m * m = 1 := h.mul_self_of_mem_weylSet hm
      have hmm' := RankOne.mul_mul_cancel_of_mul_self hmm
      have hminv : m⁻¹ = m := inv_eq_of_mul_eq_one_right hmm
      have hnm : n * m ∈ hua A B := Subgroup.subset_closure ⟨n, hn, m, hm, rfl⟩
      refine Or.inr ⟨a * a₁, A.mul_mem ha ha₁, (n * m) * a₁ * (n * m)⁻¹,
        hkA _ hnm _ ha₁, (n * m) * (n * k * n), Subgroup.mul_mem _ hnm (hkn k hk), ?_⟩
      calc a * n * a' * k * n = a * (n * a' * n) * (n * k * n) := by
            simp only [mul_assoc, hnn']
        _ = a * (a₁ * m * a₁) * (n * k * n) := by rw [hbeq]
        _ = a * a₁ * n * (n * m * a₁ * (n * m)⁻¹) * (n * m * (n * k * n)) := by
            simp only [mul_inv_rev, hninv, hminv, mul_assoc, hnn', hmm']
  have hall : ∀ x : X, ∀ y ∈ Y, y * x ∈ Y := by
    intro x
    have hx : x ∈ Subgroup.closure ((A : Set X) ∪ {n}) := by
      have hB : B ≤ Subgroup.closure ((A : Set X) ∪ {n}) := by
        intro b hb
        have hb' : b ∈ A.map (MulAut.conj n).toMonoidHom := by rwa [hn.2.2]
        rw [mem_map_conj] at hb'
        have hnmem : n ∈ Subgroup.closure ((A : Set X) ∪ {n}) :=
          Subgroup.subset_closure (Or.inr rfl)
        have hbmem : n⁻¹ * b * n ∈ Subgroup.closure ((A : Set X) ∪ {n}) :=
          Subgroup.subset_closure (Or.inl hb')
        have : b = n * (n⁻¹ * b * n) * n⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnmem hbmem) (Subgroup.inv_mem _ hnmem)
      have hA : A ≤ Subgroup.closure ((A : Set X) ∪ {n}) := fun a ha =>
        Subgroup.subset_closure (Or.inl ha)
      have := sup_le hA hB
      rw [h.gen] at this
      exact this trivial
    induction hx using Subgroup.closure_induction'' with
    | mem x hx =>
      rcases hx with hx | rfl
      · exact hgenA x hx
      · exact hgenn
    | inv_mem x hx =>
      rcases hx with hx | rfl
      · exact hgenA _ (A.inv_mem hx)
      · rw [hninv]
        exact hgenn
    | one => intro y hy; rwa [mul_one]
    | mul x y _ _ hx hy =>
      intro z hz
      rw [← mul_assoc]
      exact hy _ (hx z hz)
  refine le_antisymm (fun x hx => ?_) hHN
  have hxY : x ∈ Y := by simpa using hall x 1 hY1
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.1 hx
  rcases hxY with ⟨a, ha, k, hk, rfl⟩ | ⟨a, ha, a', ha', k, hk, rfl⟩
  · have hkB := (Subgroup.mem_inf.1 (hHN hk)).2
    have hBa : B.map (MulAut.conj a).toMonoidHom = B := by
      have := map_conj_eq_self_iff.2 hxB
      rwa [map_conj_mul, map_conj_eq_self_iff.2 hkB] at this
    rw [h.eq_one_of_map_conj_eq ha hBa, one_mul]
    exact hk
  · exfalso
    have hkA' := (Subgroup.mem_inf.1 (hHN hk)).1
    have := map_conj_eq_self_iff.2 hxA
    rw [map_conj_mul, map_conj_eq_self_iff.2 hkA', map_conj_mul, map_conj_of_mem ha',
      map_conj_mul, hn.2.2] at this
    exact h.map_conj_ne ha this

theorem hua_eq_bot_of_card_eq_two [Finite X] (hA : Nat.card A = 2) : hua A B = ⊥ := by
  have hsub : ∀ m ∈ weylSet A B, ∀ m' ∈ weylSet A B, m = m' := by
    intro m hm m' hm'
    obtain ⟨a, ha, ha1, hma⟩ := h.exists_mem_pt_of_mem_weylSet hm
    obtain ⟨a', ha', ha'1, hm'a⟩ := h.exists_mem_pt_of_mem_weylSet hm'
    have haa : a = a' := by
      have h1 : (⟨a, ha⟩ : A) ≠ 1 := fun h1 => ha1 (congrArg Subtype.val h1)
      have h2 : (⟨a', ha'⟩ : A) ≠ 1 := fun h2 => ha'1 (congrArg Subtype.val h2)
      have := Nat.card_eq_two_iff' (1 : A) |>.1 hA
      obtain ⟨y, -, hy⟩ := this
      exact congrArg Subtype.val ((hy _ h1).trans (hy _ h2).symm)
    obtain ⟨g₀, hg₀⟩ := h.exists_eq_map_conj
    rw [hg₀, ← map_conj_mul] at hma hm'a
    rw [← haa] at hm'a
    exact h.eq_of_mem_weylSet hm hm' hma hm'a
  rw [hua, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨m, hm, m', hm', rfl⟩
  rw [hsub m hm m' hm', h.mul_self_of_mem_weylSet hm', Set.mem_singleton_iff]

theorem card_eq_six [Finite X] (hA : Nat.card A = 2) : Nat.card X = 6 := by
  rw [h.card_eq, h.normalizer_inf_eq_hua, h.hua_eq_bot_of_card_eq_two hA, Subgroup.card_bot,
    hA]

end IsElemAbRankOne

end CFSG.Timmesfeld
