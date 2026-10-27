module

public import CFSG.Assembly.LargeEvenDefs
import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportCore
import CFSG.Fischer.Classification.Recognition.Basic
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FixedFreeRank

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem bmPComponent_of_conj_pow {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {t s m : K} (ht : orderOf t = p) {k : ℕ} (hk : k % p ≠ 0) (h : m * s * m⁻¹ = t ^ k)
    (hC : ∃ C : Subgroup K, LargeEvenPComponent p (Subgroup.centralizer ({t} : Set K)) C) :
    ∃ C : Subgroup K, LargeEvenPComponent p (Subgroup.centralizer ({s} : Set K)) C := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hC⟩ := hC
  have hk1 : t ^ k ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ht] at this
    exact hk (Nat.mod_eq_zero_of_dvd this)
  have hcen := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_prime
    (G := K) ht hk1
  rw [← hcen] at hC
  have h1 := (largeEvenPComponent_map_mulEquiv p (MulAut.conj m⁻¹)
    (Subgroup.centralizer ({t ^ k} : Set K)) C).mpr hC
  have hs : (MulAut.conj m⁻¹) (t ^ k) = s := by
    rw [← h]
    simp [MulAut.conj_apply, mul_assoc]
  rw [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton, hs] at h1
  exact ⟨_, h1⟩

end CFSG.StandardType.SporadicShape
