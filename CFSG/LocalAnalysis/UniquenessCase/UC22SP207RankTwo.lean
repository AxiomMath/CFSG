module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
public import CFSG.GH74.BNPair.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Tits
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Central
import CFSG.Quasithin.Vol2.GoldschmidtF431BNRad

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GH74.BNPair
open CFSG.GroupTheory.TitsSystem (IsBNPair)
open scoped Pointwise

theorem uc22sp207_noStrongParabolic_of_rankTwo {X : Type} [Group X] [Finite X] {n : ℕ}
    (D : RankTwoSystem X n) (hn : Even n) (hU2 : IsPGroup 2 D.U) (hUi : ¬ 2 ∣ D.U.index) :
    NoStrongParabolic X := by
  have h : IsBNPair D.B D.N ({D.w₁, D.w₂} : Set (WeylGroup D.B D.N)) := by
    have := uc22sp207_isBNPair_of_isTitsSystem D.isTits
    rwa [D.rank2.gens] at this
  have hdih := D.rank2.dih
  obtain ⟨n₀, hn₀⟩ := QuotientGroup.mk_surjective (altWord D.w₁ D.w₂ n)
  have hmax : ∀ w, wordLength {D.w₁, D.w₂} w ≤
      wordLength {D.w₁, D.w₂} (n₀ : WeylGroup D.B D.N) := by
    intro w
    rw [hn₀, hdih.wordLength_altWord le_rfl]
    exact hdih.wordLength_le w
  have hgen : ∀ s ∈ ({D.w₁, D.w₂} : Set (WeylGroup D.B D.N)),
      altWord D.w₁ D.w₂ n * s = s * altWord D.w₁ D.w₂ n := by
    rintro s (rfl | rfl)
    · rw [mul_altWord_even n hn, altWord_succ, ← hdih.altWord_eq]
    · rw [hdih.altWord_eq, mul_altWord_even n hn, altWord_succ, ← hdih.altWord_eq]
  have hcomm : ∀ w : WeylGroup D.B D.N,
      (n₀ : WeylGroup D.B D.N) * w = w * (n₀ : WeylGroup D.B D.N) := by
    intro w
    have hw : w ∈ Subgroup.closure ({D.w₁, D.w₂} : Set (WeylGroup D.B D.N)) := by
      rw [hdih.closure_eq]
      trivial
    have key : Commute (altWord D.w₁ D.w₂ n) w := by
      induction hw using Subgroup.closure_induction with
      | mem s hs => exact hgen s hs
      | one => exact Commute.one_right _
      | mul u v _ _ hu hv => exact hu.mul_right hv
      | inv u _ hu => exact hu.inv_right
    rw [hn₀]
    exact key.eq
  have hcen : ∀ x ∈ D.N, (n₀ : X) * x * (n₀ : X)⁻¹ * x⁻¹ ∈ D.B := by
    intro x hx
    have h1 : ((n₀ * ⟨x, hx⟩ * n₀⁻¹ * (⟨x, hx⟩ : D.N)⁻¹ : D.N) : WeylGroup D.B D.N) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hcomm]
      group
    simpa using mk_eq_one_iff.1 h1
  have hBUH : D.B ≤ D.U ⊔ (D.B ⊓ D.N) := by
    intro b hb
    have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
    obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.1 hb'
    exact mul_mem (mem_sup_right (show t ∈ D.B ⊓ D.N from ht)) (mem_sup_left (show u ∈ D.U from hu))
  exact uc22sp207_noStrongParabolic_of_isBNPair h hU2 hUi D.U_le_B
    (CFSG.Quasithin.H13.F431.BN.B_le_normalizer_U D) hBUH n₀.2 (uc22sp207_sup_conj_eq_top h hmax)
    hcen

end CFSG.LocalAnalysis.UniquenessCase.UC22
