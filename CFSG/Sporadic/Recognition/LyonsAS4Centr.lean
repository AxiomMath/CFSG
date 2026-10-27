module

public import CFSG.Sporadic.Recognition.LyonsAS4Subgroup
public import CFSG.Sporadic.Recognition.LyonsAS4Local
public import CFSG.GH74.GLS.Stage12.McLCover

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage12.McLRec

instance normal_zpowers_self_centralizer {G : Type*} [Group G] (x : G) :
    (zpowers (⟨x, self_mem_centralizer_singleton x⟩ : ↥(centralizer ({x} : Set G)))).Normal :=
  normal_of_le_center <| zpowers_le.2 <| Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2)

abbrev CentQuot {G : Type*} [Group G] (x : G) : Type _ :=
  ↥(centralizer ({x} : Set G)) ⧸
    zpowers (⟨x, self_mem_centralizer_singleton x⟩ : ↥(centralizer ({x} : Set G)))

theorem zpow_cases {K : Type*} [Group K] {x : K} (hx : x ^ 3 = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x ∨ x ^ k = x ^ 2 := by
  have h3 : x ^ (3 : ℤ) = 1 := by simpa using hx
  rw [zpow_eq_zpow_emod k h3]
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h] <;> simp

theorem zpow_eq_one_of_zpow_two_mul {K : Type*} [Group K] {x : K} (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    {k : ℤ} (h : x ^ (2 * k) = 1) : x ^ k = 1 := by
  have hx2 : x ^ 2 ≠ 1 := by
    intro h2
    apply hx1
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx, h2]; group
  rcases zpow_cases hx k with h1 | h1 | h1
  · exact h1
  · exfalso
    apply hx2
    rw [mul_comm, zpow_mul, h1] at h
    simpa using h
  · exfalso
    apply hx1
    rw [mul_comm, zpow_mul, h1] at h
    have h4 : x ^ 4 = 1 := by simpa [← pow_mul] using h
    calc x = x ^ 4 * (x ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hx]; group

namespace LyData

variable {G : Type} [Group G] {t : G} {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x : ↥(centralizer ({t} : Set G))}

theorem Lsub_le_centralizer (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    IsCover11.Lsub ρ ≤ centralizer ({x} : Set ↥(centralizer ({t} : Set G))) := by
  intro l hl
  obtain ⟨h0, h1, h2⟩ := hl
  have : ρ l * ρ x = ρ x * ρ l := by rw [hx]; exact commute_x1p_of_fix h0 h1 h2
  exact mem_centralizer_singleton_iff.2 (D.cover.commute_of_rho_commute_pow_three hx3 this)

@[expose] def toCent (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    ↥(IsCover11.Lsub ρ) →* ↥(centralizer ({(x : G)} : Set G)) :=
  ((centralizer ({t} : Set G)).subtype.comp (IsCover11.Lsub ρ).subtype).codRestrict
    (centralizer ({(x : G)} : Set G)) fun l =>
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val
        (mem_centralizer_singleton_iff.1 (D.Lsub_le_centralizer hx3 hx l.2)))

@[expose] def toQuot (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    ↥(IsCover11.Lsub ρ) →* CentQuot (x : G) :=
  (QuotientGroup.mk' _).comp (D.toCent hx3 hx)

theorem toQuot_apply (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p)
    (l : ↥(IsCover11.Lsub ρ)) :
    D.toQuot hx3 hx l = QuotientGroup.mk (⟨((l : ↥(centralizer ({t} : Set G))) : G), by
      exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val
        (mem_centralizer_singleton_iff.1 (D.Lsub_le_centralizer hx3 hx l.2)))⟩ :
        ↥(centralizer ({(x : G)} : Set G))) :=
  rfl

@[expose] def tQuot (x : ↥(centralizer ({t} : Set G))) : CentQuot (x : G) :=
  QuotientGroup.mk ⟨t, mem_centralizer_singleton_iff.2
    (mem_centralizer_singleton_iff.1 x.2).symm⟩

theorem zpow_eq_one_of_mem_Lsub (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) {k : ℤ}
    (h : x ^ k ∈ IsCover11.Lsub ρ) : x ^ k = 1 := by
  have hl0 : ρ (x ^ k) 0 = 0 := (mem_fix012.1 (IsCover11.mem_Lsub.1 h)).1
  rcases zpow_cases hx3 k with h1 | h1 | h1
  · exact h1
  · rw [h1, hx] at hl0
    exact absurd hl0 (by decide)
  · rw [h1, map_pow, hx] at hl0
    exact absurd hl0 (by decide)

theorem toQuot_injective (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    Function.Injective (D.toQuot hx3 hx) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have hl' : D.toCent hx3 hx l ∈
      zpowers (⟨(x : G), self_mem_centralizer_singleton _⟩ :
        ↥(centralizer ({(x : G)} : Set G))) :=
    (QuotientGroup.eq_one_iff _).1 hl
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hl'
  have hk' : (l : ↥(centralizer ({t} : Set G))) = x ^ k := by
    apply Subtype.ext
    have h2 := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at h2
    exact h2.symm
  have h1 : x ^ k = 1 := zpow_eq_one_of_mem_Lsub hx3 hx (hk' ▸ l.2)
  apply Subtype.ext
  rw [hk', h1]
  rfl

theorem comm_of_commutator_zpow {K : Type*} [Group K] {x t m : K} (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (ht : t ^ 2 = 1) (htx : t * x = x * t) {k : ℤ} (hk : x ^ k = (m * t)⁻¹ * (t * m)) :
    m * t = t * m := by
  have htk : t * x ^ k = x ^ k * t := (Commute.zpow_right (show Commute t x from htx) k)
  have hc : m⁻¹ * t * m = t * x ^ k := by rw [hk]; group
  have hsq : (t * x ^ k) * (t * x ^ k) = 1 := by
    rw [← hc]
    calc m⁻¹ * t * m * (m⁻¹ * t * m) = m⁻¹ * (t * t) * m := by group
      _ = 1 := by rw [← pow_two, ht]; group
  have hxk2 : (x ^ k) ^ 2 = 1 := by
    calc (x ^ k) ^ 2 = (t * x ^ k) * (t * x ^ k) := by
          rw [mul_assoc, ← mul_assoc (x ^ k), ← htk, mul_assoc, ← mul_assoc t t, ← pow_two, ht,
            one_mul, pow_two]
      _ = 1 := hsq
  have hxk : x ^ k = 1 := by
    apply zpow_eq_one_of_zpow_two_mul hx hx1
    rw [mul_comm, zpow_mul]
    simpa using hxk2
  rw [hxk, mul_one] at hc
  calc m * t = m * (m⁻¹ * t * m) := by rw [hc]
    _ = t * m := by group

theorem range_toQuot (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    (D.toQuot hx3 hx).range = centralizer ({tQuot x} : Set (CentQuot (x : G))) := by
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hx
    exact (by decide : (1 : Perm (Fin 11)) ≠ x1p) hx
  have hxt : t * (x : G) = (x : G) * t := (mem_centralizer_singleton_iff.1 x.2).symm
  have ht2 : t ^ 2 = 1 := by rw [← D.order_t]; exact pow_orderOf_eq_one t
  have hxG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  ext q
  constructor
  · rintro ⟨l, rfl⟩
    rw [mem_centralizer_singleton_iff, toQuot_apply, tQuot, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (l : ↥(centralizer ({t} : Set G))).2)
  · intro hq
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [mem_centralizer_singleton_iff, tQuot, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq] at hq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hq
    have hkG : (x : G) ^ k = ((m : G) * t)⁻¹ * (t * (m : G)) := by
      have := congrArg Subtype.val hk
      simpa using this
    have hmt : (m : G) * t = t * (m : G) := comm_of_commutator_zpow hxG3 hx1 ht2 hxt hkG
    have hmH : (m : G) ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hmt
    have hmx : (m : G) * (x : G) = (x : G) * (m : G) := mem_centralizer_singleton_iff.1 m.2
    let h : ↥(centralizer ({t} : Set G)) := ⟨(m : G), hmH⟩
    have hhx : h * x = x * h := Subtype.ext hmx
    have hρ : ρ h * x1p = x1p * ρ h := by
      rw [← hx, ← map_mul, ← map_mul, hhx]
    obtain ⟨n, hn0, hn1, hn2⟩ := exists_pow_fix_of_commute hρ
    have hl₀ : (x ^ n)⁻¹ * h ∈ IsCover11.Lsub ρ := by
      show ρ ((x ^ n)⁻¹ * h) ∈ fix012
      rw [map_mul, map_inv, map_pow, hx]
      exact ⟨hn0, hn1, hn2⟩
    refine ⟨⟨(x ^ n)⁻¹ * h, hl₀⟩, ?_⟩
    rw [toQuot_apply, QuotientGroup.eq]
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    apply Subtype.ext
    have hcomm : (m : G) * (x : G) ^ n = (x : G) ^ n * (m : G) :=
      (Commute.pow_right (show Commute (m : G) (x : G) from hmx) n).eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, zpow_natCast, Subgroup.coe_pow, mul_inv_rev,
      inv_inv]
    show (x : G) ^ n = (m : G)⁻¹ * (x : G) ^ n * (m : G)
    calc (x : G) ^ n = (m : G)⁻¹ * ((m : G) * (x : G) ^ n) := by group
      _ = (m : G)⁻¹ * ((x : G) ^ n * (m : G)) := by rw [hcomm]
      _ = (m : G)⁻¹ * (x : G) ^ n * (m : G) := by group

theorem isDoubleCoverOfAlt_centralizer_quot (D : LyData G t ρ) (hx3 : x ^ 3 = 1)
    (hx : ρ x = x1p) :
    IsDoubleCoverOfAlt ↥(centralizer ({tQuot x} : Set (CentQuot (x : G)))) 8 := by
  have h1 : IsDoubleCoverOfAlt ↥(IsCover11.Lsub ρ) 8 := D.cover.isDoubleCoverOfAlt_Lsub
  exact isDoubleCoverOfAlt_congr
    ((MonoidHom.ofInjective (D.toQuot_injective hx3 hx)).trans
      (MulEquiv.subgroupCongr (D.range_toQuot hx3 hx))) h1

theorem orderOf_tQuot (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    orderOf (tQuot x) = 2 := by
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hx
    exact (by decide : (1 : Perm (Fin 11)) ≠ x1p) hx
  have hxG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have ht2 : t ^ 2 = 1 := by rw [← D.order_t]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    have := D.order_t
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hsq : tQuot x ^ 2 = 1 := by
    rw [tQuot, ← QuotientGroup.mk_pow, show (1 : CentQuot (x : G)) = QuotientGroup.mk 1 from rfl]
    congr 1
    exact Subtype.ext ht2
  have hne : tQuot x ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((QuotientGroup.eq_one_iff _).1 h)
    have hkG : (x : G) ^ k = t := by
      have := congrArg Subtype.val hk
      simpa using this
    apply ht1
    rw [← hkG]
    apply zpow_eq_one_of_zpow_two_mul hxG3 hx1
    rw [mul_comm, zpow_mul, hkG]
    simpa using ht2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime hsq hne

end LyData

end CFSG.Sporadic.Recognition.LyonsSims
