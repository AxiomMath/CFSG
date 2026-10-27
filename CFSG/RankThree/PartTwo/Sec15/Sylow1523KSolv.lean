module

import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Sylow1523K

variable {G : Type} [Group G] [Finite G]

theorem le_thetaQuotCentralizer_of_isPerfect {K J : Subgroup G} (hK : K = oPrimeResidualOf 3 K)
    (hKp : Group.IsPerfect ↥K) (hKJ : K ≤ Subgroup.normalizer (J : Set G))
    (hJ3 : ¬ 3 ∣ Nat.card J)
    (hout : commutator (MulAut (↥J ⧸ aschbacherSolvableCore 3 ↥J)) ≤
      (MulAut.conj : (↥J ⧸ aschbacherSolvableCore 3 ↥J) →*
        MulAut (↥J ⧸ aschbacherSolvableCore 3 ↥J)).range) :
    K ≤ Sec4.thetaQuotCentralizer J := by
  set Q := ↥J ⧸ aschbacherSolvableCore 3 ↥J with hQ
  set ρ : Subgroup.normalizer (J : Set G) →* MulAut Q :=
    (Sec4.thetaQuotMulAut ↥J).comp J.normalizerMonoidHom with hρ
  set φ : ↥K →* MulAut Q := ρ.comp (Subgroup.inclusion hKJ) with hφ
  have hrange : φ.range ≤ (MulAut.conj : Q →* MulAut Q).range := by
    refine le_trans ?_ hout
    have h1 : (commutator ↥K).map φ ≤ commutator (MulAut Q) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    rwa [Group.isPerfect_def.mp hKp, ← MonoidHom.range_eq_map] at h1
  have hI3 : Nat.Coprime 3 (Nat.card (MulAut.conj : Q →* MulAut Q).range) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hJ3 ?_
    exact h3.trans ((Subgroup.card_range_dvd _).trans (Subgroup.card_quotient_dvd_card _))
  have hφ3 : ∀ (y : G) (hy : y ∈ K) (k : ℕ), y ^ 3 ^ k = 1 → φ ⟨y, hy⟩ = 1 := by
    intro y hy k hk
    have hmem : φ ⟨y, hy⟩ ∈ (MulAut.conj : Q →* MulAut Q).range := hrange ⟨⟨y, hy⟩, rfl⟩
    have hyk : (⟨y, hy⟩ : ↥K) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    have hpow : φ ⟨y, hy⟩ ^ 3 ^ k = 1 := by rw [← map_pow, hyk, map_one]
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hI3)
      (orderOf_dvd_of_pow_eq_one hpow) (Subgroup.orderOf_dvd_natCard _ hmem))
  refine hK.le.trans ?_
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro y ⟨hyK, k, hk⟩
  exact ⟨⟨y, hKJ hyK⟩, MonoidHom.mem_ker.mpr (hφ3 y hyK k hk), rfl⟩

end Sylow1523K

end CFSG.RankThree.PartTwo.Sec15
