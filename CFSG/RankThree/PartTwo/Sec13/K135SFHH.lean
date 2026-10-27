module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

open CFSG
open scoped commutatorElement

private theorem sf_hh_normal_pCore3 {Y : Type*} [Group Y] (Rb : Subgroup Y) [Rb.Normal] :
    ((CFSG.pCore 3 Rb).map Rb.subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨r, hr, rfl⟩ g
  refine ⟨MulAut.conjNormal g r, ?_, ?_⟩
  · have hchar : (CFSG.pCore 3 Rb).Characteristic := inferInstance
    exact (Subgroup.characteristic_iff_le_comap.mp hchar (MulAut.conjNormal g)) hr
  · simp [MulAut.conjNormal_apply]

private theorem sf_hh_mem_pCore_map {Y : Type*} [Group Y] [Finite Y]
    (Rb : Subgroup Y) (hsolv : Group.IsSolvable Rb) (hcore : CFSG.pPrimeCore 3 Rb = ⊥)
    {x : Y} (hxR : x ∈ Rb)
    (hx : x ∈ Subgroup.centralizer (((CFSG.pCore 3 Rb).map Rb.subtype : Subgroup Y) : Set Y)) :
    x ∈ (CFSG.pCore 3 Rb).map Rb.subtype := by
  have hcent : (⟨x, hxR⟩ : Rb) ∈
      Subgroup.centralizer (((CFSG.pCore 3 Rb : Subgroup Rb)) : Set Rb) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ : (y : Y) ∈ (CFSG.pCore 3 Rb).map Rb.subtype := ⟨y, hy, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (y : Y) hyQ)
  have hle := (CFSG.centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot (G := ↥Rb) hsolv hcore)
  exact ⟨⟨x, hxR⟩, hle hcent, rfl⟩

private theorem sf_hh_centralizer_coprime {Y : Type*} [Group Y] (R Q : Subgroup Y) [R.Normal]
    [Q.Normal] (hQ3 : IsPGroup 3 Q)
    (hQR : ∀ x ∈ R, x ∈ Subgroup.centralizer (Q : Set Y) → x ∈ Q)
    {a : Y} (ha : a ∈ Subgroup.centralizer (Q : Set Y)) (hcop : Nat.Coprime 3 (orderOf a)) :
    a ∈ Subgroup.centralizer (R : Set Y) := by
  have hQa : ∀ q ∈ Q, q * a = a * q := fun q hq => Subgroup.mem_centralizer_iff.mp ha q hq
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  obtain ⟨c, hc⟩ : ∃ c : Y, c = r⁻¹ * (a * r * a⁻¹) := ⟨_, rfl⟩
  have hcR : c ∈ R := by
    rw [hc]
    exact R.mul_mem (R.inv_mem hr) ((inferInstance : R.Normal).conj_mem r hr a)
  have hcq : ∀ q ∈ Q, c * q = q * c := by
    intro q hq
    have hq1 : a⁻¹ * q * a = q := by
      calc a⁻¹ * q * a = a⁻¹ * (q * a) := by group
        _ = a⁻¹ * (a * q) := by rw [hQa q hq]
        _ = q := by group
    have hq₁ : r * q * r⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem q hq r
    have hq3 : a * (r * q * r⁻¹) * a⁻¹ = r * q * r⁻¹ := by
      rw [← hQa _ hq₁]; group
    calc c * q = r⁻¹ * (a * r * a⁻¹) * q := by rw [hc]
      _ = r⁻¹ * (a * r * (a⁻¹ * q * a) * a⁻¹) := by group
      _ = r⁻¹ * (a * r * q * a⁻¹) := by rw [hq1]
      _ = r⁻¹ * ((a * (r * q * r⁻¹) * a⁻¹) * (a * r * a⁻¹)) := by group
      _ = r⁻¹ * ((r * q * r⁻¹) * (a * r * a⁻¹)) := by rw [hq3]
      _ = q * (r⁻¹ * (a * r * a⁻¹)) := by group
      _ = q * c := by rw [hc]
  have hcC : c ∈ Subgroup.centralizer (Q : Set Y) :=
    Subgroup.mem_centralizer_iff.mpr (fun q hq => (hcq q hq).symm)
  have hcQ : c ∈ Q := hQR c hcR hcC
  obtain ⟨k, hk⟩ := hQ3 ⟨c, hcQ⟩
  have hck : c ^ 3 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hac : ∀ j : ℕ, a * c ^ j = c ^ j * a := fun j =>
    (Subgroup.mem_centralizer_iff.mp ha (c ^ j) (pow_mem hcQ j)).symm
  have hrel : a * r = r * c * a := by
    rw [hc]; group
  have hpow : ∀ j : ℕ, a ^ j * r = r * c ^ j * a ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc a ^ (j + 1) * r = a * (a ^ j * r) := by rw [pow_succ', mul_assoc]
        _ = a * (r * c ^ j * a ^ j) := by rw [ih]
        _ = (a * r) * c ^ j * a ^ j := by simp only [mul_assoc]
        _ = (r * c * a) * c ^ j * a ^ j := by rw [hrel]
        _ = r * c * (a * c ^ j) * a ^ j := by simp only [mul_assoc]
        _ = r * c * (c ^ j * a) * a ^ j := by rw [hac j]
        _ = r * c ^ (j + 1) * a ^ (j + 1) := by
          rw [pow_succ' c j, pow_succ' a j]; simp only [mul_assoc]
  have hd : a ^ 3 ^ k * r = r * a ^ 3 ^ k := by
    rw [hpow (3 ^ k), hck, mul_one]
  have hcd : Commute (a ^ 3 ^ k) r := hd
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left k hcop)
  have hbez : a = (a ^ 3 ^ k) ^ u := by
    calc a = a ^ (u * ((3 ^ k : ℕ) : ℤ) + v * ((orderOf a : ℕ) : ℤ)) := by
          rw [huv, zpow_one]
      _ = a ^ (u * ((3 ^ k : ℕ) : ℤ)) * a ^ (v * ((orderOf a : ℕ) : ℤ)) := zpow_add a _ _
      _ = (a ^ 3 ^ k) ^ u := by
        have h2 : a ^ (v * ((orderOf a : ℕ) : ℤ)) = 1 := by
          rw [mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
        have h3 : a ^ (u * ((3 ^ k : ℕ) : ℤ)) = (a ^ 3 ^ k) ^ u := by
          rw [mul_comm, zpow_mul, zpow_natCast]
        rw [h2, mul_one, h3]
  have hcz : Commute ((a ^ 3 ^ k) ^ u) r := hcd.zpow_left u
  rw [← hbez] at hcz
  exact hcz.symm.eq

private theorem sf_hh_exists_pow_three {Y : Type*} [Group Y] [Finite Y]
    (R Q : Subgroup Y) [R.Normal] [Q.Normal] (hQ3 : IsPGroup 3 Q)
    (hQR : ∀ x ∈ R, x ∈ Subgroup.centralizer (Q : Set Y) → x ∈ Q)
    (X : Subgroup Y) (hX : X ≤ Subgroup.centralizer (Q : Set Y)) :
    ∀ x ∈ X, ∃ e : ℕ, x ^ 3 ^ e ∈ Subgroup.centralizer (R : Set Y) := by
  intro x hx
  obtain ⟨e, m, hm, hxm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  refine ⟨e, sf_hh_centralizer_coprime R Q hQ3 hQR (pow_mem (hX hx) (3 ^ e)) ?_⟩
  have hpm : (x ^ 3 ^ e) ^ m = 1 := by
    rw [← pow_mul, ← hxm, pow_orderOf_eq_one]
  have hdvd : orderOf (x ^ 3 ^ e) ∣ m := orderOf_dvd_of_pow_eq_one hpm
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (fun h => hm (h.trans hdvd))

private theorem sf_hh_isPGroup_quotient {Y : Type*} [Group Y] (X C : Subgroup Y) [C.Normal]
    (h : ∀ x ∈ X, ∃ e : ℕ, x ^ 3 ^ e ∈ C) :
    IsPGroup 3 (X ⧸ C.subgroupOf X) := by
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨e, he⟩ := h x.1 x.2
  refine ⟨e, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow]
  exact he

theorem commutator_eq_bot_of_centralizes_pCore {Y : Type*} [Group Y] [Finite Y]
    (Rb : Subgroup Y) [Rb.Normal] (hsolv : Group.IsSolvable Rb) (hcore : CFSG.pPrimeCore 3 Rb = ⊥)
    (Xb : Subgroup Y) [Group.IsPerfect Xb]
    (hQ : Xb ≤ Subgroup.centralizer (((CFSG.pCore 3 Rb).map Rb.subtype : Subgroup Y) : Set Y)) :
    ⁅Rb, Xb⁆ = ⊥ := by
  haveI hQn : ((CFSG.pCore 3 Rb).map Rb.subtype).Normal := sf_hh_normal_pCore3 Rb
  have hQ3 : IsPGroup 3 ↥((CFSG.pCore 3 Rb).map Rb.subtype) :=
    (CFSG.pCore_isPGroup (p := 3) (G := ↥Rb)).map Rb.subtype
  have hQR : ∀ x ∈ Rb,
      x ∈ Subgroup.centralizer (((CFSG.pCore 3 Rb).map Rb.subtype : Subgroup Y) : Set Y) →
      x ∈ (CFSG.pCore 3 Rb).map Rb.subtype :=
    fun x hx hxC => sf_hh_mem_pCore_map Rb hsolv hcore hx hxC
  have hpow := sf_hh_exists_pow_three Rb ((CFSG.pCore 3 Rb).map Rb.subtype) hQ3 hQR Xb hQ
  have hXC : Xb ≤ Subgroup.centralizer (Rb : Set Y) := by
    have hPG := sf_hh_isPGroup_quotient Xb (Subgroup.centralizer (Rb : Set Y)) hpow
    have hsub : Subsingleton (Xb ⧸ (Subgroup.centralizer (Rb : Set Y)).subgroupOf Xb) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isNilpotent
        (Xb ⧸ (Subgroup.centralizer (Rb : Set Y)).subgroupOf Xb) (IsPGroup.isNilpotent hPG)
    have htop : (Subgroup.centralizer (Rb : Set Y)).subgroupOf Xb = ⊤ :=
      QuotientGroup.subgroup_eq_top_of_subsingleton _ hsub
    intro x hx
    have hxK : (⟨x, hx⟩ : Xb) ∈ (Subgroup.centralizer (Rb : Set Y)).subgroupOf Xb := by
      rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hxK
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact ((Subgroup.mem_centralizer_iff.mp (hXC hx)) r hr).symm

end CFSG.RankThree.PartTwo.Sec13.K135SF
