module

public import CFSG.Sporadic.Th.Max3.Involutions
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieConj
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.TwoBLocalBound

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

theorem orderOf_kap_of_orderOf_eq_prime {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {x : ↥Max3.M}
    (hx : orderOf x = p) : orderOf (Max3.InvRep.kap x) = p := by
  have hpow : Max3.InvRep.kap x ^ p = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hne : Max3.InvRep.kap x ≠ 1 := by
    intro h1
    have hxQ : (x : J) ∈ Max3.Q := Max3.InvRep.kap_eq_one_iff.1 h1
    have hxJ : orderOf (x : J) = p := (Subgroup.orderOf_mk (x : J) x.2).symm.trans hx
    have hdvdQ : p ∣ Nat.card Max3.Q := by
      have h := orderOf_dvd_natCard (⟨(x : J), hxQ⟩ : ↥Max3.Q)
      rwa [Subgroup.orderOf_mk, hxJ] at h
    have hp2 : p ∣ 2 ^ 9 := by rw [Max3.card_Q] at hdvdQ; simpa using hdvdQ
    exact hp (Nat.prime_eq_prime_of_dvd_pow Fact.out Nat.prime_two hp2)
  exact orderOf_eq_prime hpow hne

theorem card_centralizer_le_mul (g : ↥Max3.M) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set ↥Max3.M)) ≤
      Nat.card ↥(Max3.Q.subgroupOf Max3.M ⊓ Subgroup.centralizer ({g} : Set ↥Max3.M)) *
        Nat.card ↥(Subgroup.centralizer ({Max3.InvRep.kap g} :
          Set (alternatingGroup (Fin 9)))) := by
  have h := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_le_mul
    (K := Max3.Q.subgroupOf Max3.M) (e := Max3.kappa) g
  simpa [Max3.InvRep.kap, Max3.AltQuot.proj] using h

theorem exists_conj_of_isConj_kap {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {x y : ↥Max3.M}
    (hx : orderOf x = p) (hy : orderOf y = p)
    (hxy : IsConj (Max3.InvRep.kap x) (Max3.InvRep.kap y)) :
    ∃ m : ↥Max3.M, m * x * m⁻¹ = y := by
  have hO : ¬ p ∣ Nat.card ↥(Max3.Q.subgroupOf Max3.M) := by
    have hcard : Nat.card ↥(Max3.Q.subgroupOf Max3.M) = 512 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Max3.Q_le_M).toEquiv).trans
        Max3.card_Q
    rw [hcard, show (512 : ℕ) = 2 ^ 9 by norm_num]
    intro h
    exact hp (Nat.prime_eq_prime_of_dvd_pow Fact.out Nat.prime_two h)
  have hconjproj : IsConj (AltQuot.proj x) (AltQuot.proj y) := by
    obtain ⟨a, ha⟩ := isConj_iff.mp hxy
    obtain ⟨m, hm⟩ := Max3.InvRep.kap_surjective a
    refine isConj_iff.mpr ⟨AltQuot.proj m, ?_⟩
    have hkap : Max3.InvRep.kap (m * x * m⁻¹) = Max3.InvRep.kap y := by
      rw [map_mul, map_mul, map_inv, hm, ha]
    have hproj : AltQuot.proj (m * x * m⁻¹) = AltQuot.proj y :=
      AltQuot.proj_eq_proj_iff.mpr (Max3.InvRep.kap_eq_iff.1 hkap)
    calc AltQuot.proj m * AltQuot.proj x * (AltQuot.proj m)⁻¹
        = AltQuot.proj (m * x * m⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = AltQuot.proj y := hproj
  have hconjM : IsConj x y :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L.isConj_of_mk_isConj
      (Y := ↥Max3.M) (Max3.Q.subgroupOf Max3.M) hO hx hy (by
        simpa [AltQuot.proj] using hconjproj)
  obtain ⟨c, hc⟩ := hconjM
  refine ⟨(c : ↥Max3.M), ?_⟩
  have hc' : (c : ↥Max3.M) * x = y * (c : ↥Max3.M) := hc
  calc (c : ↥Max3.M) * x * (c : ↥Max3.M)⁻¹
      = y * (c : ↥Max3.M) * (c : ↥Max3.M)⁻¹ := by rw [hc']
    _ = y := by group

end CFSG.Sporadic.Th.Recog
