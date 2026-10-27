module

public import CFSG.RankThree.PartOne.KLAY.D4Outer
public import CFSG.RankThree.PartOne.KLAY.RootLayer
public import CFSG.RankThree.PartOne.KF.G2Dih

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley

theorem eq_one_of_sq_eq_one_of_pow_eq_one {G : Type*} [Group G] {x : G} {p : ℕ} (hp : Odd p)
    (h2 : x ^ 2 = 1) (hp1 : x ^ p = 1) : x = 1 := by
  obtain ⟨m, rfl⟩ := hp
  have : x ^ (2 * m + 1) = x := by rw [pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← this]
  exact hp1

theorem rootLayer_row3_s0
    {p f : ℕ} {K : Type} [Field K] {σ : K →+* K} (hP : D4Param p f K σ) (v : G2V p K)
    (hv1 : v ≠ 1) (hv : g2s0 p K v = v) :
    RootLayer (graphFixedRootGroup TwistTag.D4 K σ) p (tp3M hP v)
      (2 ^ f * ((2 ^ f) ^ 2 - 1)) := by
  classical
  have : Finite K := hP.finite
  have hchar : CharP K 2 := ringChar.of_eq hP.ringChar_eq_two
  have hp := hP.prime
  have h5 := hP.five_le
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hv0 : v 0 = 1 := by
    have h := congrFun hv 0
    rw [g2s0_apply_zero] at h
    have h2 : v 0 ^ 2 = 1 := by
      rw [sq]
      exact mul_eq_one_iff_inv_eq.2 h
    have hp1 : v 0 ^ p = 1 := Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 (v 0).2)
    exact eq_one_of_sq_eq_one_of_pow_eq_one hodd h2 hp1
  have hvz : v = ![1, v 1] := by
    funext i
    fin_cases i
    · exact hv0
    · rfl
  have hz1 : v 1 ≠ 1 := fun h => hv1 (by
    rw [hvz, h]
    funext i
    fin_cases i <;> rfl)
  have hzp : ((v 1 : rootsOfUnity p K) : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).1 (v 1).2
  have hz1' : ((v 1 : rootsOfUnity p K) : Kˣ) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have : Fact p.Prime := ⟨hp⟩
  have hzprim : IsPrimitiveRoot ((v 1 : rootsOfUnity p K) : Kˣ) p := by
    have := IsPrimitiveRoot.orderOf ((v 1 : rootsOfUnity p K) : Kˣ)
    rwa [orderOf_eq_prime hzp hz1'] at this
  obtain ⟨k, hkmem, hkcard⟩ := exists_fixedField hP
  have hkchar : CharP ↥k 2 := inferInstance
  have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
    have := Nat.one_lt_two_pow (n := f) (by have := hP.one_le; omega)
    omega) hP.dvd
  have h4 : 4 ≤ Nat.card ↥k := by
    rw [hkcard]
    omega
  have hSL := d4_SL2Torus_two hP hzprim k hkmem
  have hD := d4_layerD_two hP hzprim k hkmem hkcard
  rw [hvz]
  exact RootLayer.of_SL2Torus hSL hp h4 (by rw [hkcard]; exact hP.dvd) hD (by rw [hkcard])

theorem rootLayer_row3_s1
    {p f : ℕ} {K : Type} [Field K] {σ : K →+* K} (hP : D4Param p f K σ) (v : G2V p K)
    (hv1 : v ≠ 1) (hv : g2s1 p K v = v) :
    RootLayer (graphFixedRootGroup TwistTag.D4 K σ) p (tp3M hP v)
      ((2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1)) := by
  classical
  have : Finite K := hP.finite
  have hchar : CharP K 2 := ringChar.of_eq hP.ringChar_eq_two
  have hp := hP.prime
  have h5 := hP.five_le
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hv1' : v 1 = 1 := by
    have h := congrFun hv 1
    rw [g2s1_apply_one] at h
    have h2 : v 1 ^ 2 = 1 := by
      rw [sq]
      exact mul_eq_one_iff_inv_eq.2 h
    have hp1 : v 1 ^ p = 1 := Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 (v 1).2)
    exact eq_one_of_sq_eq_one_of_pow_eq_one hodd h2 hp1
  have hvz : v = ![v 0, 1] := by
    funext i
    fin_cases i
    · rfl
    · exact hv1'
  have hz1 : v 0 ≠ 1 := fun h => hv1 (by
    rw [hvz, h]
    funext i
    fin_cases i <;> rfl)
  have hzp : ((v 0 : rootsOfUnity p K) : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).1 (v 0).2
  have hz1' : ((v 0 : rootsOfUnity p K) : Kˣ) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have : Fact p.Prime := ⟨hp⟩
  have hzprim : IsPrimitiveRoot ((v 0 : rootsOfUnity p K) : Kˣ) p := by
    have := IsPrimitiveRoot.orderOf ((v 0 : rootsOfUnity p K) : Kˣ)
    rwa [orderOf_eq_prime hzp hz1'] at this
  have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
    have := Nat.one_lt_two_pow (n := f) (by have := hP.one_le; omega)
    omega) hP.dvd
  have h4 : 4 ≤ Nat.card K := by
    have h6 : 6 ^ 3 ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    rw [hP.card]
    omega
  have hpq : p ∣ Nat.card K - 1 := by
    have h1 : 2 ^ f - 1 ∣ (2 ^ f) ^ 3 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 3
    rw [hP.card]
    exact hP.dvd.trans h1
  have hSL := d4_SL2Torus_three hP hzprim
  have hD := d4_layerD_three hP hzprim
  rw [hvz]
  exact RootLayer.of_SL2Torus hSL hp h4 hpq hD (by rw [hP.card])

end CFSG.RankThree.PartOne.KLAY
