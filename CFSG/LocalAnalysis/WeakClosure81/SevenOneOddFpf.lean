module

public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.RankThree.GF2n.Tim77Prop24TwoSz
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_of_odd_of_mem_or_mul_mem_normalizer {X D : Subgroup G} {a : G} (ha2 : a * a = 1)
    (haD : a ∈ normalizer (D : Set G)) (hX : ∀ x ∈ X, x ∈ D ∨ a * x ∈ D)
    {x : G} (hx : x ∈ X) (hodd : Odd (orderOf x)) : x ∈ D := by
  rcases hX x hx with hxD | haxD
  · exact hxD
  · have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hxeq : x = a * (a * x) := by rw [← mul_assoc, ha2, one_mul]
    have hconj : a * (a * x) * a⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp haD (a * x)).mp haxD
    have hx2eq : x ^ 2 = (a * (a * x) * a⁻¹) * (a * x) := by
      rw [pow_two]
      conv_lhs => rw [hxeq]
      rw [hainv]
      group
    have hx2 : x ^ 2 ∈ D := by
      rw [hx2eq]
      exact D.mul_mem hconj haxD
    exact CFSG.Quasithin.B2F.mem_of_odd_orderOf_of_pow_mem hodd (k := 1) (by simpa using hx2)

theorem eq_one_of_commute_of_odd_of_mQuot_eq_one {A : Subgroup G} (hAel : IsElemAbelian 2 A)
    (hTI : IsTI A) {h : G} (hU : nVSub A h ≠ ⊥) (hU1 : E3.mQuot A (nVSub A h) = 1)
    (hodd : ∀ x ∈ A ⊔ conjSubgroup A h, Odd (orderOf x) → x = 1 ∨ (orderOf x).Prime)
    {x : G} (hx : x ∈ A ⊔ conjSubgroup A h) (hxo : Odd (orderOf x)) (hx1 : x ≠ 1)
    {b : G} (hb : b ∈ nVSub A h ⊔ bSub A h) (hxb : x * b = b * x) : b = 1 := by
  classical
  have hA2 : IsPGroup 2 A := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hAel
  have hne : nVSub A h ≠ A := by
    intro hEq
    rw [hEq, E3.mQuot_self] at hU1
    omega
  have hUidx : (nVSub A h).relIndex A = 2 := by
    rw [E3.relIndex_eq_two_pow hA2 (nVSub A h), hU1, pow_one]
  let M : Subgroup G := nVSub A h ⊔ bSub A h
  have hMdef : M = nVSub A h ⊔ bSub A h := rfl
  let S : CFSG.RankThree.GF2n.Tim77.Prop24Setup A (conjSubgroup A h)
      (nVSub A h) (bSub A h) M := prop24Setup hAel hTI hU hne
  have hBidx : (bSub A h).relIndex (conjSubgroup A h) = 2 := by
    rw [S.relIndex_Lb, hUidx]
  obtain ⟨a, haA, haU⟩ := SetLike.exists_of_lt (lt_of_le_of_ne inf_le_left hne)
  obtain ⟨a', ha'Ah, ha'B⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have hrX : a * a' ∈ A ⊔ conjSubgroup A h :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left haA) (Subgroup.mem_sup_right ha'Ah)
  have hrodd : Odd (orderOf (a * a')) := S.odd_orderOf_mul haA haU ha'Ah ha'B
  have hr1 : a * a' ≠ 1 := by
    intro hr
    have ha'inv : a' = a⁻¹ := by
      calc a' = a⁻¹ * (a * a') := by group
        _ = a⁻¹ := by rw [hr, mul_one]
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (S.sq_A haA)
    have ha'eq : a' = a := by rw [ha'inv, hainv]
    have hbot : a ∈ (⊥ : Subgroup G) := by
      rw [← S.inf_eq_bot]
      exact Subgroup.mem_inf.mpr ⟨haA, ha'eq ▸ ha'Ah⟩
    exact haU (by rw [Subgroup.mem_bot.mp hbot]; exact (nVSub A h).one_mem)
  have hrprime : (orderOf (a * a')).Prime := by
    rcases hodd (a * a') hrX hrodd with h1 | hp
    · exact absurd h1 hr1
    · exact hp
  set r : G := a * a' with hrdef
  have hrX' : r ∈ A ⊔ conjSubgroup A h := hrX
  have hrodd' : Odd (orderOf r) := hrodd
  have hrprime' : (orderOf r).Prime := hrprime
  have hrN : r ∈ normalizer (M : Set G) := by
    rw [hMdef]
    exact S.sup_le_normalizer_M hrX'
  have haN : a ∈ normalizer (M : Set G) := by
    rw [hMdef]
    exact S.A_le_normalizer_M haA
  have har : a * r * a⁻¹ = r⁻¹ := by
    have haa : a * a = 1 := S.sq_A haA
    have ha'a' : a' * a' = 1 := S.sq_Ab ha'Ah
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    have ha'inv : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha'a'
    rw [hrdef]
    calc a * (a * a') * a⁻¹ = (a * a) * a' * a := by rw [hainv]; group
      _ = a' * a := by rw [haa, one_mul]
      _ = (a * a')⁻¹ := by rw [mul_inv_rev, ha'inv, hainv]
  set D : Subgroup G := Subgroup.zpowers r ⊔ M with hD
  have hDcoe : (D : Set G) = (Subgroup.zpowers r : Set G) * (M : Set G) := by
    rw [hD]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Subgroup.zpowers_le.mpr hrN)
  have haD : a ∈ normalizer (D : Set G) := by
    have hconjD : ∀ d ∈ D, a * d * a⁻¹ ∈ D := by
      intro d hd
      change d ∈ (D : Set G) at hd
      rw [hDcoe] at hd
      obtain ⟨u, hu, m, hm, rfl⟩ := hd
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have harz : a * r ^ k * a⁻¹ = r ^ (-k) := by
        rw [show a * r ^ k * a⁻¹ = (a * r * a⁻¹) ^ k by rw [conj_zpow]]
        rw [har, inv_zpow, zpow_neg]
      have hm' : a * m * a⁻¹ ∈ M :=
        (Subgroup.mem_normalizer_iff.mp haN m).mp hm
      rw [show a * (r ^ k * m) * a⁻¹ = (a * r ^ k * a⁻¹) * (a * m * a⁻¹) by group]
      rw [harz]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.zpow_mem (Subgroup.zpowers r)
          (Subgroup.mem_zpowers r) (-k)))
        (Subgroup.mem_sup_right hm')
    have haa : a * a = 1 := S.sq_A haA
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    refine Subgroup.mem_normalizer_iff.mpr fun d => ⟨fun hd => hconjD d hd, fun hd => ?_⟩
    have h := hconjD (a * d * a⁻¹) hd
    have hd' : a * (a * d * a⁻¹) * a⁻¹ = d := by
      rw [hainv]
      calc a * (a * d * a) * a = (a * a) * d * (a * a) := by group
        _ = d := by rw [haa, one_mul, mul_one]
    rwa [hd'] at h
  have hzpow_a : ∀ u : G, u ∈ Subgroup.zpowers a → u = 1 ∨ u = a := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have ha1 : a ≠ 1 := fun h1 => haU (h1 ▸ (nVSub A h).one_mem)
    have haord : orderOf a = 2 := by
      have h2 : a ^ 2 = 1 := by rw [pow_two]; exact S.sq_A haA
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr h2) with h1 | h2'
      · exact absurd (orderOf_eq_one_iff.mp h1) ha1
      · exact h2'
    have hk := zpow_mod_orderOf a k
    rw [haord] at hk
    push_cast at hk
    rw [← hk]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  have hA_le : A ≤ Subgroup.zpowers a ⊔ D := by
    intro u huA
    by_cases huU : u ∈ nVSub A h
    · exact Subgroup.mem_sup_right (by
        rw [hD]
        exact Subgroup.mem_sup_right (Subgroup.mem_sup_left huU))
    · have hauU : a * u ∈ nVSub A h := by
        have hkey := (Subgroup.mul_mem_iff_of_index_two (H := (nVSub A h).subgroupOf A)
          hUidx (a := (⟨a, haA⟩ : ↥A)) (b := (⟨u, huA⟩ : ↥A)))
        have ha' : (⟨a, haA⟩ : ↥A) ∉ (nVSub A h).subgroupOf A := by
          rw [Subgroup.mem_subgroupOf]; exact haU
        have hu' : (⟨u, huA⟩ : ↥A) ∉ (nVSub A h).subgroupOf A := by
          rw [Subgroup.mem_subgroupOf]; exact huU
        exact hkey.mpr (iff_of_false ha' hu')
      have hauD : a * u ∈ D := by
        rw [hD]
        exact Subgroup.mem_sup_right (Subgroup.mem_sup_left hauU)
      have hueq : u = a * (a * u) := by rw [← mul_assoc, S.sq_A haA, one_mul]
      rw [hueq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
        (Subgroup.mem_sup_right hauD)
  have ha'eq : a' = a * r := by
    rw [hrdef]
    rw [← mul_assoc, S.sq_A haA, one_mul]
  have hAh_le : conjSubgroup A h ≤ Subgroup.zpowers a ⊔ D := by
    intro u hu
    by_cases huB : u ∈ bSub A h
    · exact Subgroup.mem_sup_right (by
        rw [hD]
        exact Subgroup.mem_sup_right (Subgroup.mem_sup_right huB))
    · have ha'uB : a' * u ∈ bSub A h := by
        have hkey := (Subgroup.mul_mem_iff_of_index_two
          (H := (bSub A h).subgroupOf (conjSubgroup A h)) hBidx
          (a := (⟨a', ha'Ah⟩ : ↥(conjSubgroup A h)))
          (b := (⟨u, hu⟩ : ↥(conjSubgroup A h))))
        have ha'' : (⟨a', ha'Ah⟩ : ↥(conjSubgroup A h)) ∉
            (bSub A h).subgroupOf (conjSubgroup A h) := by
          rw [Subgroup.mem_subgroupOf]; exact ha'B
        have hu' : (⟨u, hu⟩ : ↥(conjSubgroup A h)) ∉
            (bSub A h).subgroupOf (conjSubgroup A h) := by
          rw [Subgroup.mem_subgroupOf]; exact huB
        exact hkey.mpr (iff_of_false ha'' hu')
      have ha'uD : a' * u ∈ D := by
        rw [hD]
        exact Subgroup.mem_sup_right (Subgroup.mem_sup_right ha'uB)
      have ha'sup : a' ∈ Subgroup.zpowers a ⊔ D := by
        rw [ha'eq]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
          (by rw [hD]; exact Subgroup.mem_sup_right (Subgroup.mem_sup_left
            (Subgroup.mem_zpowers r)))
      have hueq : u = a' * (a' * u) := by rw [← mul_assoc, S.sq_Ab ha'Ah, one_mul]
      rw [hueq]
      exact Subgroup.mul_mem _ ha'sup (Subgroup.mem_sup_right ha'uD)
  have hX_le : A ⊔ conjSubgroup A h ≤ Subgroup.zpowers a ⊔ D := sup_le hA_le hAh_le
  have hXprop : ∀ y ∈ A ⊔ conjSubgroup A h, y ∈ D ∨ a * y ∈ D := by
    intro y hy
    have hysup : y ∈ Subgroup.zpowers a ⊔ D := hX_le hy
    have hcoe : ((Subgroup.zpowers a ⊔ D : Subgroup G) : Set G) =
        (Subgroup.zpowers a : Set G) * (D : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Subgroup.zpowers_le.mpr haD)
    change y ∈ ((Subgroup.zpowers a ⊔ D : Subgroup G) : Set G) at hysup
    rw [hcoe] at hysup
    obtain ⟨u, hu, d, hd, rfl⟩ := hysup
    rcases hzpow_a u hu with h1 | h2
    · left
      simpa [h1] using hd
    · right
      have haa : a * a = 1 := S.sq_A haA
      have haad : a * (a * d) = d := by rw [← mul_assoc, haa, one_mul]
      simpa [h2, haad] using hd
  have haa : a * a = 1 := S.sq_A haA
  have hxD : x ∈ D :=
    mem_of_odd_of_mem_or_mul_mem_normalizer haa haD hXprop hx hxo
  change x ∈ (D : Set G) at hxD
  rw [hDcoe] at hxD
  obtain ⟨u, hu, y, hy, hxy⟩ := hxD
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [← hk] at hxy
  have hq0 : (orderOf r : ℤ) ≠ 0 := by exact_mod_cast hrprime'.ne_zero
  have hknonneg : 0 ≤ k % (orderOf r : ℤ) := Int.emod_nonneg k hq0
  let j : ℕ := (k % (orderOf r : ℤ)).toNat
  have hjk : (j : ℤ) = k % (orderOf r : ℤ) := Int.toNat_of_nonneg hknonneg
  have hrj : r ^ j = r ^ k := by
    rw [← zpow_natCast, hjk, zpow_mod_orderOf]
  have hxj : x = r ^ j * y := by
    rw [← hxy, ← hrj]
  have hxM : x ∉ M := by
    intro hxM
    have hx2 : x * x = 1 := S.mem_M_sq hxM
    have hord : orderOf x ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hx2
    have hcop : Nat.Coprime (orderOf x) 2 := (Nat.coprime_two_left.mpr hxo).symm
    have h1 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd hcop hord
    exact hx1 (orderOf_eq_one_iff.mp h1)
  have hqj : ¬ orderOf r ∣ j := by
    intro hdvd
    have hrj1 : r ^ j = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
    have hxy1 : x = y := by rw [hxj, hrj1, one_mul]
    exact hxM (hxy1.symm ▸ hy)
  have hcopj : Nat.Coprime j (orderOf r) :=
    (hrprime'.coprime_iff_not_dvd.mpr hqj).symm
  obtain ⟨e, -, he⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopj hrprime'.one_lt
  have hrjN : r ^ j ∈ normalizer (M : Set G) :=
    Subgroup.pow_mem (Subgroup.normalizer (M : Set G)) hrN j
  have hy0 : r ^ j * y * (r ^ j)⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.mp hrjN y).mp hy
  obtain ⟨y', hy', hpow⟩ :=
    CFSG.Quasithin.B2F.exists_pow_mul_mem (I := M) hy0 hrjN e
  have hrie : (r ^ j) ^ e = r := by
    rw [← pow_mul, pow_eq_pow_mod (j * e) (pow_orderOf_eq_one r), he, pow_one]
  have hxe : x ^ e = r * (r⁻¹ * y' * r) := by
    have hxeq : x = (r ^ j * y * (r ^ j)⁻¹) * r ^ j := by
      rw [hxj]
      rw [show r ^ j * y * (r ^ j)⁻¹ * r ^ j = r ^ j * y by group]
    calc x ^ e = ((r ^ j * y * (r ^ j)⁻¹) * r ^ j) ^ e := by rw [← hxeq]
      _ = y' * (r ^ j) ^ e := hpow
      _ = y' * r := by rw [hrie]
      _ = r * (r⁻¹ * y' * r) := by group
  have hy'' : r⁻¹ * y' * r ∈ M := by
    have hrInvN : r⁻¹ ∈ normalizer (M : Set G) :=
      Subgroup.inv_mem (Subgroup.normalizer (M : Set G)) hrN
    simpa using (Subgroup.mem_normalizer_iff.mp hrInvN y').mp hy'
  have hbeq : b * (r * (r⁻¹ * y' * r)) = (r * (r⁻¹ * y' * r)) * b := by
    have hcxb : Commute x b := hxb
    have hxe_b : b * x ^ e = x ^ e * b := (hcxb.pow_left e).eq.symm
    rw [← hxe]
    exact hxe_b
  have hbM : b ∈ M := by rw [hMdef]; exact hb
  have hbY : b * (r⁻¹ * y' * r) = (r⁻¹ * y' * r) * b :=
    S.comm_M hbM hy''
  have hbr : b * r = r * b := by
    calc b * r = b * r * (r⁻¹ * y' * r) * (r⁻¹ * y' * r)⁻¹ := by group
      _ = b * (r * (r⁻¹ * y' * r)) * (r⁻¹ * y' * r)⁻¹ := by group
      _ = (r * (r⁻¹ * y' * r)) * b * (r⁻¹ * y' * r)⁻¹ := by rw [hbeq]
      _ = r * ((r⁻¹ * y' * r) * b) * (r⁻¹ * y' * r)⁻¹ := by group
      _ = r * (b * (r⁻¹ * y' * r)) * (r⁻¹ * y' * r)⁻¹ := by rw [hbY]
      _ = r * b := by group
  exact S.eq_one_of_commute_mul haA haU ha'Ah ha'B hbM (by simpa [hrdef] using hbr.symm)

end CFSG.LocalAnalysis.WeakClosure81