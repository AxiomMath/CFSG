module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

section Descent

variable {L : Type} [Group L]

theorem mem_normalizer_zpowers_of_commute {z w : L} (h : w * z = z * w) :
    w ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup L) : Set L) := by
  have hc : Commute w z := h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ y ∈ Subgroup.zpowers z, w * y * w⁻¹ = y := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hc.zpow_right k).mul_inv_cancel
  have key' : ∀ y ∈ Subgroup.zpowers z, w⁻¹ * y * w = y := by
    intro y hy
    have h1 : w * y * w⁻¹ = y := key y hy
    calc w⁻¹ * y * w = w⁻¹ * (w * y * w⁻¹) * w := by rw [h1]
      _ = y := by group
  constructor
  · intro hx
    rw [key x hx]
    exact hx
  · intro hx
    have h1 := key' _ hx
    have e : w⁻¹ * (w * x * w⁻¹) * w = x := by group
    rw [e] at h1
    have h2 : x = w * x * w⁻¹ := h1
    rw [h2]
    exact hx

theorem eq_one_of_mem_zpowers_of_mem_center {z c : L} (hz : orderOf z = 3)
    (hzc : z ∉ Subgroup.center L) (hcz : c ∈ Subgroup.zpowers z)
    (hcc : c ∈ Subgroup.center L) : c = 1 := by
  by_contra hne
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcz
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have h3 : ¬ (3 : ℤ) ∣ j := by
    intro hj
    obtain ⟨m, rfl⟩ := hj
    apply hne
    rw [zpow_mul]
    have : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
    rw [this, one_zpow]
  have hcop : IsCoprime (3 : ℤ) j := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hp : Prime (3 : ℤ) := Int.prime_three
    exact (Int.isCoprime_iff_gcd_eq_one.mp ((Prime.coprime_iff_not_dvd hp).mpr h3))
  obtain ⟨u, v, huv⟩ := hcop
  apply hzc
  have : z = (z ^ j) ^ v * (z ^ (3 : ℤ)) ^ u := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add]
    have : j * v + 3 * u = 1 := by linarith
    rw [this, zpow_one]
  have h3z : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
  rw [h3z, one_zpow, mul_one] at this
  rw [this]
  exact Subgroup.zpow_mem _ hcc v

theorem weaklyClosed_mk_zpowers {z : L} (hz : orderOf z = 3) (hzc : z ∉ Subgroup.center L)
    (h : WeaklyClosed (Subgroup.zpowers z)) :
    WeaklyClosed (Subgroup.zpowers (QuotientGroup.mk z : L ⧸ Subgroup.center L)) := by
  classical
  intro gb hle
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  set w : L := g * z * g⁻¹ with hw
  have hw3 : w ^ 3 = 1 := by rw [hw, conj_pow, hz3]; group
  have hwN : (QuotientGroup.mk w : L ⧸ Subgroup.center L) ∈
      Subgroup.normalizer ((Subgroup.zpowers (QuotientGroup.mk z : L ⧸ Subgroup.center L) :
        Subgroup (L ⧸ Subgroup.center L)) : Set (L ⧸ Subgroup.center L)) := by
    apply hle
    refine ⟨QuotientGroup.mk z, Subgroup.mem_zpowers _, ?_⟩
    simp [hw]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hwN (QuotientGroup.mk z)).mp (Subgroup.mem_zpowers _))
  have hzbar3 : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hz3, QuotientGroup.mk_one]
  have hzbar1 : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ≠ 1 := by
    intro h1
    exact hzc ((QuotientGroup.eq_one_iff z).mp h1)
  have hzbarord : orderOf (QuotientGroup.mk z : L ⧸ Subgroup.center L) = 3 :=
    orderOf_eq_prime hzbar3 hzbar1
  have hφ3 : (MulAut.conj (QuotientGroup.mk w : L ⧸ Subgroup.center L)) ^ 3 = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow, hw3, QuotientGroup.mk_one, map_one]
  have hφz : (MulAut.conj (QuotientGroup.mk w : L ⧸ Subgroup.center L)) (QuotientGroup.mk z) =
      (QuotientGroup.mk z : L ⧸ Subgroup.center L) ^ k := by
    rw [MulAut.conj_apply]; exact hk.symm
  have hcube : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ^ (k ^ 3) =
      (QuotientGroup.mk z : L ⧸ Subgroup.center L) := by
    have h1 : ((MulAut.conj (QuotientGroup.mk w : L ⧸ Subgroup.center L)) ^ 3)
        (QuotientGroup.mk z) = QuotientGroup.mk z := by rw [hφ3]; rfl
    have h2 : ((MulAut.conj (QuotientGroup.mk w : L ⧸ Subgroup.center L)) ^ 3)
        (QuotientGroup.mk z) = (QuotientGroup.mk z : L ⧸ Subgroup.center L) ^ (k ^ 3) := by
      have e1 : ∀ n : ℕ, ((MulAut.conj (QuotientGroup.mk w : L ⧸ Subgroup.center L)) ^ n)
          (QuotientGroup.mk z) = (QuotientGroup.mk z : L ⧸ Subgroup.center L) ^ (k ^ n) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, MulAut.mul_apply, hφz, map_zpow, ih, ← zpow_mul, pow_succ]
      exact e1 3
    rw [← h2, h1]
  have hdvd : (3 : ℤ) ∣ k ^ 3 - 1 := by
    have h1 : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ^ (k ^ 3 - 1) = 1 := by
      rw [zpow_sub, hcube, zpow_one, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hzbarord] at this
    exact_mod_cast this
  have hk3 : (k : ZMod 3) = 1 := by
    have h' : ((k ^ 3 - 1 : ℤ) : ZMod 3) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hdvd
    push_cast at h'
    generalize (k : ZMod 3) = r at h' ⊢
    revert r; decide
  have hk1' : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ^ k = QuotientGroup.mk z := by
    have : (3 : ℤ) ∣ k - 1 := by
      have h0 : ((k - 1 : ℤ) : ZMod 3) = 0 := by push_cast; rw [hk3]; simp
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 3).mp h0
    obtain ⟨m, hm⟩ := this
    have : k = 1 + 3 * m := by linarith
    rw [this, zpow_add, zpow_one, zpow_mul]
    have h3 : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ^ (3 : ℤ) = 1 := by
      exact_mod_cast hzbar3
    rw [h3, one_zpow, mul_one]
  have hcomm : (QuotientGroup.mk w : L ⧸ Subgroup.center L) * QuotientGroup.mk z *
      (QuotientGroup.mk w)⁻¹ = QuotientGroup.mk z := by rw [← hk, hk1']
  set c : L := z⁻¹ * (w * z * w⁻¹) with hc
  have hcC : c ∈ Subgroup.center L := by
    have : (QuotientGroup.mk (w * z * w⁻¹) : L ⧸ Subgroup.center L) = QuotientGroup.mk z := by
      simpa using hcomm
    exact QuotientGroup.eq.mp this.symm
  have hwzw : w * z * w⁻¹ = z * c := by rw [hc]; group
  have hzc_comm : (z * c) * z = z * (z * c) := by
    have hcc := Subgroup.mem_center_iff.mp hcC z
    calc z * c * z = z * (c * z) := by group
      _ = z * (z * c) := by rw [hcc]
  have hmap : (Subgroup.zpowers z).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers (z * c) := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hwzw
  have hle1 : (Subgroup.zpowers z).map (MulAut.conj w).toMonoidHom ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup L) : Set L) := by
    rw [hmap, Subgroup.zpowers_le]
    exact mem_normalizer_zpowers_of_commute hzc_comm
  have heq1 := h w hle1
  rw [hmap] at heq1
  have hzcmem : z * c ∈ Subgroup.zpowers z := by rw [← heq1]; exact Subgroup.mem_zpowers _
  have hcmem : c ∈ Subgroup.zpowers z := by
    have := (Subgroup.zpowers z).mul_mem ((Subgroup.zpowers z).inv_mem (Subgroup.mem_zpowers z))
      hzcmem
    simpa using this
  have hc1 : c = 1 := eq_one_of_mem_zpowers_of_mem_center hz hzc hcmem hcC
  have hwz : w * z = z * w := by
    rw [hc1, mul_one] at hwzw
    calc w * z = w * z * w⁻¹ * w := by group
      _ = z * w := by rw [hwzw]
  have hmapg : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers w := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hle2 : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup L) : Set L) := by
    rw [hmapg, Subgroup.zpowers_le]
    exact mem_normalizer_zpowers_of_commute hwz
  have heq2 := h g hle2
  rw [hmapg] at heq2
  rw [MonoidHom.map_zpowers]
  have e : (MulAut.conj (g : L ⧸ Subgroup.center L)).toMonoidHom (QuotientGroup.mk z) =
      QuotientGroup.mk w := by
    simp [hw]
  rw [e]
  have := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center L))) heq2
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
  exact this

end Descent

end CFSG.RankThree.PartTwo.Sec4.RonanK432
