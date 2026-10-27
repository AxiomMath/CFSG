module

public import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G} {a b c : G}

@[expose] def qdCore (a b c : G) : Subgroup G :=
  Subgroup.closure {x | ∃ g ∈ Subgroup.closure ({a, b} : Set G), x = g * c * g⁻¹}

theorem conj_self_mem_qdCore {g : G} (hg : g ∈ Subgroup.closure ({a, b} : Set G)) :
    g * c * g⁻¹ ∈ qdCore a b c :=
  Subgroup.subset_closure ⟨g, hg, rfl⟩

theorem self_mem_qdCore : c ∈ qdCore a b c := by
  simpa using conj_self_mem_qdCore (a := a) (b := b) (c := c) (Subgroup.one_mem _)

theorem conj_mem_qdCore {g x : G} (hg : g ∈ Subgroup.closure ({a, b} : Set G))
    (hx : x ∈ qdCore a b c) : g * x * g⁻¹ ∈ qdCore a b c := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    rw [show g * (h * c * h⁻¹) * g⁻¹ = g * h * c * (g * h)⁻¹ by group]
    exact conj_self_mem_qdCore (Subgroup.mul_mem _ hg hh)
  | one => simp
  | mul x y _ _ ihx ihy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ihx

namespace QD

private theorem eq_one_of_odd_of_dvd_four {m : ℕ} (hm : Odd m) (h : m ∣ 4) : m = 1 :=
  Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hm)) h

private theorem reflection_mem (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (ha : a ∈ D)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hodd : Odd (orderOf (a * b))) (i : ℤ) :
    (a * b) ^ i * a ∈ D ∧ (a * b) ^ i * a * ((a * b) ^ i * a) = 1 := by
  have hk := mul_zpow_mul_eq_zpow_neg_mul ha2 hb2 i
  have haz : a * ((a * b) ^ i * a) = (a * b) ^ (-i) := by
    rw [← mul_assoc, hk, mul_assoc, ha2, mul_one]
  have hz2 : (a * b) ^ i * a * ((a * b) ^ i * a) = 1 := by
    rw [mul_assoc, haz, ← zpow_add, add_neg_cancel, zpow_zero]
  refine ⟨?_, hz2⟩
  have hodd' : Odd (orderOf (a * ((a * b) ^ i * a))) := by
    rw [haz]
    exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one zpow_pow_orderOf)
  obtain ⟨g, -, hg⟩ := exists_conj_of_odd_orderOf_mul ha2 hz2 hodd'
  rw [← hg]
  exact hN g a ha

private theorem exists_reflection_conj (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (ha : a ∈ D)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hodd : Odd (orderOf (a * b))) (hac : Commute a c)
    {g : G} (hg : g ∈ Subgroup.closure ({a, b} : Set G)) :
    ∃ z ∈ D, z * z = 1 ∧ g * c * g⁻¹ = z * c * z := by
  obtain ⟨i, hgi⟩ := exists_zpow_of_mem_closure_pair ha2 hb2 hg
  obtain ⟨hzD, hz2⟩ := reflection_mem hN ha ha2 hb2 hodd i
  refine ⟨_, hzD, hz2, ?_⟩
  have hzinv : ((a * b) ^ i * a)⁻¹ = (a * b) ^ i * a := inv_eq_of_mul_eq_one_right hz2
  have haca : a * c * a⁻¹ = c := by rw [hac.eq, mul_inv_cancel_right]
  have key : g * c * g⁻¹ = (a * b) ^ i * a * c * ((a * b) ^ i * a)⁻¹ := by
    rcases hgi with rfl | rfl
    · rw [show (a * b) ^ i * a * c * ((a * b) ^ i * a)⁻¹ =
        (a * b) ^ i * (a * c * a⁻¹) * ((a * b) ^ i)⁻¹ by group, haca]
    · rfl
  rw [key, hzinv]

private theorem commute_of_conj_eq (hD : IsRootInvolutionSet D) (hb : b ∈ D) (hc : c ∈ D)
    (h4 : orderOf (b * c) = 4) {u z : G} (hu : u ∈ D) (hz : z ∈ D) (hcu : Commute c u)
    (hv : b * u * b = z * c * z) : Commute c (z * c * z) := by
  have hb2 := hD.mul_self_eq_one hb
  have hc2 := hD.mul_self_eq_one hc
  have hz2 := hD.mul_self_eq_one hz
  have hbb : ∀ y : G, b * (b * y) = y := fun y => by rw [← mul_assoc, hb2, one_mul]
  have hcc : ∀ y : G, c * (c * y) = y := fun y => by rw [← mul_assoc, hc2, one_mul]
  have hzz : ∀ y : G, z * (z * y) = y := fun y => by rw [← mul_assoc, hz2, one_mul]
  have hw : c * (z * c * z) = (c * z) ^ 2 := by rw [sq]; simp only [mul_assoc]
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hc hz with hcz | hcz | ⟨hcz, -⟩
  ·
    rw [← hcz.eq, mul_assoc, hz2, mul_one]
  ·
    refine (commute_iff_mul_sq_eq_one hc2 (by simp only [mul_assoc, hzz, hcc, hz2])).2 ?_
    rw [hw, ← pow_mul, show 2 * 2 = orderOf (c * z) by rw [hcz], pow_orderOf_eq_one]
  ·
    have hu' : u = b * (z * c * z) * b := by rw [← hv]; simp only [mul_assoc, hbb, hb2, mul_one]
    have hpw : b * c * b * u = b * (c * (z * c * z)) * b⁻¹ := by
      rw [hu', hD.inv_eq hb]; simp only [mul_assoc, hbb]
    have hpodd : Odd (orderOf (b * c * b * u)) := by
      rw [hpw, orderOf_conj_eq, hw]
      exact Odd.of_dvd_nat hcz (orderOf_pow_dvd 2)
    have hcb4 : orderOf (c * b) = 4 := by rw [orderOf_mul_comm_eq]; exact h4
    obtain ⟨hsqD, hcsq, -, hbcb⟩ := sq_mem_of_orderOf_eq_four hD hc hb hcb4
    have hcp : Commute c (b * c * b * u) :=
      (by rw [hbcb]; exact (Commute.refl c).mul_right hcsq : Commute c (b * c * b)).mul_right hcu
    have h2p : orderOf ((c * b) ^ 2 * u) = 2 * orderOf (b * c * b * u) := by
      rw [show (c * b) ^ 2 * u = b * c * b * u * c by
        rw [← hcp.eq, sq]; simp only [mul_assoc]]
      exact orderOf_mul_eq_two_mul_of_odd hcp.symm hpodd (hD.orderOf_eq_two hc)
    obtain ⟨k, hk⟩ := hpodd
    have hp1 : orderOf (b * c * b * u) = 1 := by
      rcases hD.orderOf_mul hsqD hu with h | h | h <;> rw [h2p] at h
      · omega
      · omega
      · exact absurd h (Nat.not_odd_iff_even.2 (even_two_mul _))
    rw [hpw, orderOf_conj_eq] at hp1
    rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 hp1)]
    exact (Commute.refl c).inv_right

private theorem commute_conj_self (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (hodd : Odd (orderOf (a * b))) (h4 : orderOf (b * c) = 4) (hac : Commute a c) {g : G}
    (hg : g ∈ Subgroup.closure ({a, b} : Set G)) : Commute c (g * c * g⁻¹) := by
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb
  have hamem : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hbmem : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have haca : a * c * a⁻¹ = c := by rw [hac.eq, mul_inv_cancel_right]
  obtain ⟨r, hr⟩ : ∃ r, a * b = r := ⟨_, rfl⟩
  have hrmem : r ∈ Subgroup.closure ({a, b} : Set G) := hr ▸ Subgroup.mul_mem _ hamem hbmem
  have hnat : ∀ j : ℕ, Commute c (r ^ (j : ℤ) * c * (r ^ (j : ℤ))⁻¹) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      set u := r ^ (j : ℤ) * c * (r ^ (j : ℤ))⁻¹ with hu
      obtain ⟨z, hz, -, hzc⟩ := exists_reflection_conj hN ha ha2 hb2 hodd hac
        (Subgroup.mul_mem _ hbmem (Subgroup.zpow_mem _ hrmem j))
      have hbub : b * u * b = z * c * z := by
        calc b * u * b = b * u * b⁻¹ := by rw [hD.inv_eq hb]
          _ = b * r ^ (j : ℤ) * c * (b * r ^ (j : ℤ))⁻¹ := by rw [hu]; group
          _ = z * c * z := hzc
      have h1 : Commute c (b * u * b) := by
        rw [hbub]
        exact commute_of_conj_eq hD hb hc h4 (hN _ c hc) hz ih hbub
      have h2 : r ^ ((j + 1 : ℕ) : ℤ) * c * (r ^ ((j + 1 : ℕ) : ℤ))⁻¹ =
          a * (b * u * b) * a⁻¹ := by
        calc r ^ ((j + 1 : ℕ) : ℤ) * c * (r ^ ((j + 1 : ℕ) : ℤ))⁻¹ = r * u * r⁻¹ := by
              rw [hu]; push_cast; group
          _ = a * (b * u * b⁻¹) * a⁻¹ := by rw [← hr]; group
          _ = a * (b * u * b) * a⁻¹ := by rw [hD.inv_eq hb]
      rw [h2]
      have := (Commute.conj_iff a).2 h1
      rwa [haca] at this
  obtain ⟨i, hgi⟩ := exists_zpow_of_mem_closure_pair ha2 hb2 hg
  rw [hr] at hgi
  have hgc : g * c * g⁻¹ = r ^ i * c * (r ^ i)⁻¹ := by
    rcases hgi with rfl | rfl
    · rfl
    · rw [show r ^ i * a * c * (r ^ i * a)⁻¹ = r ^ i * (a * c * a⁻¹) * (r ^ i)⁻¹ by group, haca]
  rw [hgc]
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · exact hnat j
  ·
    have := (Commute.conj_iff (r ^ (-(j : ℤ)))).2 (hnat j).symm
    rwa [show r ^ (-(j : ℤ)) * (r ^ (j : ℤ) * c * (r ^ (j : ℤ))⁻¹) * (r ^ (-(j : ℤ)))⁻¹ = c by
      group] at this

private theorem not_commute_of_collinear (hD : IsRootInvolutionSet D) (ha : a ∈ D)
    (hab : ¬ Commute a b) (hodd : Odd (orderOf (a * b))) {x : G} (hx : x ∈ D)
    (hbx : Commute b x) (hbxD : b * x ∈ D) : ¬ Commute a x := by
  intro hax
  have h2 := orderOf_mul_eq_two_mul_of_odd (hax.mul_left hbx) hodd (hD.orderOf_eq_two hx)
  rw [mul_assoc] at h2
  obtain ⟨k, hk⟩ := hodd
  have h1 : orderOf (a * b) = 1 := by
    rcases hD.orderOf_mul ha hbxD with h | h | h <;> rw [h2] at h
    · omega
    · omega
    · exact absurd h (Nat.not_odd_iff_even.2 (even_two_mul _))
  apply hab
  rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 h1)]
  exact (Commute.refl a).inv_right

private theorem orderOf_dvd_orderOf_mul {Q : Subgroup G} {r x : G} (hQ2 : ∀ y ∈ Q, y * y = 1)
    (hrQ : ∀ y ∈ Q, r⁻¹ * y * r ∈ Q) (hodd : Odd (orderOf r)) (hx : x ∈ Q) :
    orderOf r ∣ orderOf (r * x) := by
  have key : ∀ k : ℕ, ∃ q ∈ Q, (r * x) ^ k = r ^ k * q := by
    intro k
    induction k with
    | zero => exact ⟨1, Q.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨q, hq, hk⟩ := ih
      refine ⟨r⁻¹ * q * r * x, Q.mul_mem (hrQ q hq) hx, ?_⟩
      rw [pow_succ, hk, pow_succ]
      group
  obtain ⟨q, hq, hk⟩ := key (orderOf (r * x))
  rw [pow_orderOf_eq_one] at hk
  have hrq : r ^ orderOf (r * x) ∈ Q := by
    rw [eq_inv_of_mul_eq_one_left hk.symm]
    exact Q.inv_mem hq
  have h2 : r ^ (orderOf (r * x) * 2) = 1 := by
    rw [pow_mul, sq]
    exact hQ2 _ hrq
  exact (Nat.coprime_two_right.2 hodd).dvd_of_dvd_mul_right (orderOf_dvd_of_pow_eq_one h2)

private def colPts (D : Set G) (Q : Subgroup G) (d : G) : Set G :=
  {x | x ∈ D ∧ x ∈ Q ∧ Commute d x ∧ d * x ∈ D}

end QD

open QD

theorem not_commute_conj_of_odd_special (hD : IsRootInvolutionSet D) (ha : a ∈ D) (hb : b ∈ D)
    (hc : c ∈ D) (_hab : ¬ Commute a b) (hodd : Odd (orderOf (a * b)))
    (h4 : orderOf (b * c) = 4) (hac : Commute a c) : ¬ Commute a (b * c * b) := by
  intro h
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb
  have hc2 := hD.mul_self_eq_one hc
  have h1 : Commute (b * a * b) c := by
    have := (Commute.conj_iff b).2 h
    rwa [hD.inv_eq hb, show b * (b * c * b) * b = b * b * c * (b * b) by group, hb2, one_mul,
      mul_one] at this
  have h2 : Commute ((a * b) ^ 2) c := by
    rw [show (a * b) ^ 2 = a * (b * a * b) by rw [sq]; simp only [mul_assoc]]
    exact hac.mul_left h1
  obtain ⟨k, hk⟩ := hodd
  have h3 : Commute (a * b) c := by
    have := h2.pow_left (k + 1)
    rwa [← pow_mul, show 2 * (k + 1) = orderOf (a * b) + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul] at this
  have h5 : Commute b c := by
    have := hac.mul_left h3
    rwa [← mul_assoc, ha2, one_mul] at this
  have h6 := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one hb2 hc2).1 h5)
  rw [h4] at h6
  norm_num at h6

theorem commute_conj_of_odd_special (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (_hab : ¬ Commute a b) (hodd : Odd (orderOf (a * b))) (h4 : orderOf (b * c) = 4)
    (hac : Commute a c) {g h : G} (hg : g ∈ Subgroup.closure ({a, b} : Set G))
    (hh : h ∈ Subgroup.closure ({a, b} : Set G)) :
    Commute (g * c * g⁻¹) (h * c * h⁻¹) := by
  have := commute_conj_self hD hN ha hb hc hodd h4 hac
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hh)
  rw [← Commute.conj_iff g] at this
  rwa [show g * (g⁻¹ * h * c * (g⁻¹ * h)⁻¹) * g⁻¹ = h * c * h⁻¹ by group] at this

theorem mul_conj_mem_of_odd_special (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (_hab : ¬ Commute a b) (hodd : Odd (orderOf (a * b))) (h4 : orderOf (b * c) = 4)
    (hac : Commute a c) {g : G} (hg : g ∈ Subgroup.closure ({a, b} : Set G))
    (hne : g * c * g⁻¹ ≠ c) : c * (g * c * g⁻¹) ∈ D := by
  have hcomm := commute_conj_self hD hN ha hb hc hodd h4 hac hg
  obtain ⟨z, hz, hz2, hgz⟩ := exists_reflection_conj hN ha (hD.mul_self_eq_one ha)
    (hD.mul_self_eq_one hb) hodd hac hg
  rw [hgz] at hne hcomm ⊢
  have hc2 := hD.mul_self_eq_one hc
  have hcc : ∀ y : G, c * (c * y) = y := fun y => by rw [← mul_assoc, hc2, one_mul]
  have hzz : ∀ y : G, z * (z * y) = y := fun y => by rw [← mul_assoc, hz2, one_mul]
  have hw : c * (z * c * z) = (c * z) ^ 2 := by rw [sq]; simp only [mul_assoc]
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hc hz with hcz | hcz | ⟨hcz, -⟩
  · exact absurd (by rw [← hcz.eq, mul_assoc, hz2, mul_one]) hne
  · rw [hw]
    exact hD.sq_mem hc hz hcz
  ·
    refine absurd ?_ hne
    have hw2 : (c * (z * c * z)) ^ 2 = 1 :=
      (commute_iff_mul_sq_eq_one hc2 (by simp only [mul_assoc, hzz, hcc, hz2])).1 hcomm
    have hwodd : Odd (orderOf (c * (z * c * z))) := by
      rw [hw]
      exact Odd.of_dvd_nat hcz (orderOf_pow_dvd 2)
    have h1 : orderOf (c * (z * c * z)) = 1 :=
      eq_one_of_odd_of_dvd_four hwodd ((orderOf_dvd_of_pow_eq_one hw2).trans (by norm_num))
    rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 h1), hD.inv_eq hc]

theorem qdCore_commute (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (hab : ¬ Commute a b) (hodd : Odd (orderOf (a * b))) (h4 : orderOf (b * c) = 4)
    (hac : Commute a c) : ∀ x ∈ qdCore a b c, ∀ y ∈ qdCore a b c, Commute x y := by
  intro x hx y hy
  refine commute_of_mem_closure ?_ hx hy
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
  exact commute_conj_of_odd_special hD hN ha hb hc hab hodd h4 hac hg hh

theorem qdCore_mul_self (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (hab : ¬ Commute a b) (hodd : Odd (orderOf (a * b))) (h4 : orderOf (b * c) = 4)
    (hac : Commute a c) : ∀ x ∈ qdCore a b c, x * x = 1 := by
  have hc2 := hD.mul_self_eq_one hc
  have hQ := qdCore_commute hD hN ha hb hc hab hodd h4 hac
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, -, rfl⟩ := hx
    rw [show g * c * g⁻¹ * (g * c * g⁻¹) = g * (c * c) * g⁻¹ by group, hc2, mul_one,
      mul_inv_cancel]
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    rw [show x * y * (x * y) = x * (y * x) * y by group, ← (hQ x hx y hy).eq,
      show x * (x * y) * y = x * x * (y * y) by group, ihx, ihy, mul_one]
  | inv x _ ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem pow_four_of_mem_qdCore (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (hab : ¬ Commute a b) (hodd : Odd (orderOf (a * b))) (h4 : orderOf (b * c) = 4)
    (hac : Commute a c) {x : G} (hx : x ∈ qdCore a b c) : (a * x) ^ 4 = 1 := by
  have hamem : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have h2 : (a * x) ^ 2 ∈ qdCore a b c := by
    rw [show (a * x) ^ 2 = a * x * a⁻¹ * x by rw [sq, hD.inv_eq ha]; simp only [mul_assoc]]
    exact Subgroup.mul_mem _ (conj_mem_qdCore hamem hx) hx
  rw [show 4 = 2 * 2 from rfl, pow_mul, sq]
  exact qdCore_mul_self hD hN ha hb hc hab hodd h4 hac _ h2

theorem exists_conj_eq_mul_of_odd_special [Finite G] (hD : IsRootInvolutionSet D)
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (hab : ¬ Commute a b) (hodd : Odd (orderOf (a * b))) (h4 : orderOf (b * c) = 4)
    (hac : Commute a c) (hacD : a * c ∈ D) :
    ∃ x ∈ D, x ∈ qdCore a b c ∧ Commute b x ∧ b * x ∈ D ∧ x * a * x = a * c := by
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb
  have hQc := qdCore_commute hD hN ha hb hc hab hodd h4 hac
  have hQ2 := qdCore_mul_self hD hN ha hb hc hab hodd h4 hac
  have hamem : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hbmem : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hrmem : (a * b)⁻¹ ∈ Subgroup.closure ({a, b} : Set G) :=
    Subgroup.inv_mem _ (Subgroup.mul_mem _ hamem hbmem)
  have hn1 : orderOf (a * b) ≠ 1 := fun h => hab (by
    rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 h)]
    exact (Commute.refl a).inv_right)
  have h4x : ∀ x ∈ colPts D (qdCore a b c) b, orderOf (a * x) = 4 := by
    rintro x ⟨hxD, hxQ, hbx, hbxD⟩
    have hax := not_commute_of_collinear hD ha hab hodd hxD hbx hbxD
    rcases commute_or_orderOf_mul_eq_four_or_odd hD ha hxD with h | h | ⟨h, -⟩
    · exact absurd h hax
    · exact h
    · refine absurd ?_ hax
      have h1 := eq_one_of_odd_of_dvd_four h (orderOf_dvd_of_pow_eq_one
        (pow_four_of_mem_qdCore hD hN ha hb hc hab hodd h4 hac hxQ))
      rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 h1)]
      exact (Commute.refl a).inv_right
  have hmaps : Set.MapsTo (fun x => (a * x) ^ 2) (colPts D (qdCore a b c) b)
      (colPts D (qdCore a b c) a) := by
    intro x hx
    have hx4 := h4x x hx
    obtain ⟨hxD, hxQ, -, -⟩ := hx
    obtain ⟨hsqD, hasq, -, hxax⟩ := sq_mem_of_orderOf_eq_four hD ha hxD hx4
    refine ⟨hsqD, ?_, hasq, ?_⟩
    · show (a * x) ^ 2 ∈ qdCore a b c
      rw [show (a * x) ^ 2 = a * x * a⁻¹ * x by rw [sq, hD.inv_eq ha]; simp only [mul_assoc]]
      exact Subgroup.mul_mem _ (conj_mem_qdCore hamem hxQ) hxQ
    · have := hN x a ha
      rwa [hD.inv_eq hxD, hxax] at this
  have hinj : Set.InjOn (fun x => (a * x) ^ 2) (colPts D (qdCore a b c) b) := by
    intro x hx y hy hxy
    simp only at hxy
    by_contra hne
    have hx4 := h4x x hx
    have hy4 := h4x y hy
    obtain ⟨hxD, hxQ, hbx, hbxD⟩ := hx
    obtain ⟨hyD, hyQ, hby, hbyD⟩ := hy
    have hx2 := hD.mul_self_eq_one hxD
    have hy2 := hD.mul_self_eq_one hyD
    have hxx : ∀ w : G, x * (x * w) = w := fun w => by rw [← mul_assoc, hx2, one_mul]
    have hxay : x * a * x = y * a * y := by
      rw [(sq_mem_of_orderOf_eq_four hD ha hxD hx4).2.2.2,
        (sq_mem_of_orderOf_eq_four hD ha hyD hy4).2.2.2, hxy]
    have ht2 : orderOf (x * y) = 2 := by
      refine orderOf_eq_prime (by rw [sq]; exact hQ2 _ (Subgroup.mul_mem _ hxQ hyQ)) fun h => ?_
      exact hne (by rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hy2])
    have hta : Commute a (x * y) := by
      calc a * (x * y) = x * (x * a * x) * y := by simp only [mul_assoc, hxx]
        _ = x * (y * a * y) * y := by rw [hxay]
        _ = x * y * a := by simp only [mul_assoc, hy2, mul_one]
    have htb : Commute b (x * y) := hbx.mul_right hby
    have htx : Commute x (x * y) := (Commute.refl x).mul_right (hQc x hxQ y hyQ)
    have hdvd : orderOf (a * b) ∣ orderOf (a * (b * x)) := by
      rw [← mul_assoc]
      refine orderOf_dvd_orderOf_mul hQ2 (fun q hq => ?_) hodd hxQ
      have := conj_mem_qdCore hrmem hq
      rwa [inv_inv] at this
    have hmodd : Odd (orderOf (a * (b * x))) := by
      rcases hD.orderOf_mul ha hbxD with h | h | h
      · exact absurd (eq_one_of_odd_of_dvd_four hodd ((h ▸ hdvd).trans (by norm_num))) hn1
      · exact absurd (eq_one_of_odd_of_dvd_four hodd (h ▸ hdvd)) hn1
      · exact h
    have h2m : orderOf (a * (b * y)) = 2 * orderOf (a * (b * x)) := by
      rw [show a * (b * y) = a * (b * x) * (x * y) by simp only [mul_assoc, hxx]]
      exact orderOf_mul_eq_two_mul_of_odd (hta.mul_left (htb.mul_left htx)) hmodd ht2
    obtain ⟨k, hk⟩ := hmodd
    rcases hD.orderOf_mul ha hbyD with h | h | h <;> rw [h2m] at h
    · have h1 : orderOf (a * (b * x)) = 1 := by omega
      rw [h1] at hdvd
      exact hn1 (Nat.dvd_one.1 hdvd)
    · omega
    · exact absurd h (Nat.not_odd_iff_even.2 (even_two_mul _))
  obtain ⟨h, hh, hhab⟩ := exists_conj_of_odd_orderOf_mul ha2 hb2 hodd
  have hle : (colPts D (qdCore a b c) a).ncard ≤ (colPts D (qdCore a b c) b).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun x => h * x * h⁻¹) ?_ ?_
    · rintro x ⟨hxD, hxQ, hax, haxD⟩
      refine ⟨hN h x hxD, conj_mem_qdCore hh hxQ, ?_, ?_⟩
      · rw [← hhab]
        exact (Commute.conj_iff h).2 hax
      · rw [← hhab, show h * a * h⁻¹ * (h * x * h⁻¹) = h * (a * x) * h⁻¹ by group]
        exact hN h _ haxD
    · intro x _ y _ hxy
      simpa using hxy
  have heq : (fun x => (a * x) ^ 2) '' colPts D (qdCore a b c) b = colPts D (qdCore a b c) a :=
    Set.eq_of_subset_of_ncard_le hmaps.image_subset (by rw [hinj.ncard_image]; exact hle)
  have hcX : c ∈ colPts D (qdCore a b c) a := ⟨hc, self_mem_qdCore, hac, hacD⟩
  rw [← heq] at hcX
  obtain ⟨x, hx, hxc⟩ := hcX
  have hx4 := h4x x hx
  obtain ⟨hxD, hxQ, hbx, hbxD⟩ := hx
  refine ⟨x, hxD, hxQ, hbx, hbxD, ?_⟩
  rw [(sq_mem_of_orderOf_eq_four hD ha hxD hx4).2.2.2]
  simp only at hxc
  rw [hxc]

end CFSG.Timmesfeld.Bridge
