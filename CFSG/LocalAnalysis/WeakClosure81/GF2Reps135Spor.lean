module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs
public import CFSG.LocalAnalysis.WeakClosure81.W115WeakDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowMGe
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeSmall
import CFSG.GH74.E2.ComponentsShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

private theorem w135_not_sq_dvd_443520 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) :
    ¬ r ^ 2 ∣ 443520 := by
  intro h
  have hcop : Nat.Coprime (r ^ 2) (2 ^ 7 * 3 ^ 2) := by
    refine Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right ?_ ?_)
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_three).2 hr3)
  have h385 : r ^ 2 ∣ 385 := by
    apply hcop.dvd_of_dvd_mul_left
    rwa [show (2 : ℕ) ^ 7 * 3 ^ 2 * 385 = 443520 by norm_num]
  have hr20 : r < 20 := by
    have hle : r ^ 2 ≤ 385 := Nat.le_of_dvd (by norm_num) h385
    by_contra hge
    have h20 : 20 ≤ r := not_lt.1 hge
    have hsq : 20 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left h20 2
    omega
  interval_cases r <;> norm_num at h385
  all_goals norm_num at hr

theorem w135_isSpor_of_center_bot {X : Type} [Group X] {s : TauCeti.SporadicName}
    (hz : Subgroup.center X = ⊥) (h : IsSpor (X ⧸ Subgroup.center X) s) : IsSpor X s :=
  CFSG.GH74.E2.isSporadic_of_center_bot hz h

theorem w135_card_center_eq_three_of_m22 {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    (hz : Subgroup.center X ≠ ⊥) (h : IsSpor (X ⧸ Subgroup.center X) .M22) :
    Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card (X ⧸ Subgroup.center X) = 443520 :=
    (Nat.card_congr e.toEquiv).trans CFSG.RankThree.PartTwo.Sec4.Census.card_m22_eq
  have : Group.IsPerfect X := hq.1
  have hprime : ∀ {r : ℕ}, r.Prime → r ∣ Nat.card (Subgroup.center X) → r = 3 := by
    intro r hr hrZ
    by_contra hr3
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrZ)
    have : Fact r.Prime := ⟨hr⟩
    have hnotsq : ¬ r ^ 2 ∣ 443520 := w135_not_sq_dvd_443520 hr hr2 hr3
    let f : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' _
    have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
    have hker : f.ker = Subgroup.center X := QuotientGroup.ker_mk' _
    have hcent : f.ker ≤ Subgroup.center X := le_of_eq hker
    have : Finite (X ⧸ Subgroup.center X) := Finite.of_surjective f hsurj
    obtain ⟨C⟩ : Nonempty (Sylow r f.ker) := inferInstance
    obtain ⟨Q⟩ : Nonempty (Sylow r (X ⧸ Subgroup.center X)) := inferInstance
    have hcyc : IsCyclic (Q : Subgroup (X ⧸ Subgroup.center X)) := by
      have hQcard : Nat.card (Q : Subgroup (X ⧸ Subgroup.center X)) =
          r ^ (Nat.card (X ⧸ Subgroup.center X)).factorization r := Q.card_eq_multiplicity
      rw [hcard] at hQcard
      have hfac : (443520).factorization r ≤ 1 := by
        by_contra hlt
        have h2 : 2 ≤ (443520).factorization r := Nat.succ_le_of_lt (not_le.1 hlt)
        exact hnotsq ((hr.pow_dvd_iff_le_factorization (by norm_num)).mpr h2)
      refine isCyclic_of_card_dvd_prime (p := r) ?_
      rw [hQcard]
      simpa using (Nat.pow_dvd_pow_iff_le_right hr.one_lt).mpr hfac
    have hCbot := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot
      f hsurj hcent C Q hcyc
    exact (Sylow.ne_bot_of_dvd_card C (by rw [hker]; exact hrZ)) hCbot
  have hpos : Nat.card (Subgroup.center X) ≠ 0 := Nat.card_pos.ne'
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hpos
    (fun {d} hd hdZ => hprime hd hdZ)
  have hZ3 : IsPGroup 3 (Subgroup.center X) := IsPGroup.of_card hpow
  have hdvd : Nat.card (Subgroup.center X) ∣ 3 :=
    CFSG.RankThree.PartTwo.Sec4.Census.card_center_dvd_three_of_M22 hq hZ3 e
  have hgt : 1 < Nat.card (Subgroup.center X) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hz
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · omega
  · exact h3

theorem w135_spor_case
    (h111 : ∀ s : TauCeti.SporadicName, s ≠ .M22 → W4Thm11_1RowM4 s)
    (h115 : W4Lem11_5Weak) (h116 : W4Lem11_6Weak)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    (hS : CFSG.Blueprint.NativeSporadic.SporadicRep (↥L ⧸ Subgroup.center ↥L)) :
    W4Lem13_5Concl W Y L t := by
  obtain ⟨s, hs⟩ := hS
  have hctx' := hctx
  obtain ⟨hK, hO, hLY, hF, hq, hirr⟩ := hctx
  have hnorm : (L.subgroupOf Y).Normal := w135_normal_of_ctx hctx'
  have hO2 : O2Trivial L := w135_o2Trivial_of_ctx hctx'
  have m3 : E3.mParam Y ≤ 3 := w135_mParam_le_three htY ht2 hm
  by_cases hs22 : s = .M22
  · rw [hs22] at hs
    by_cases hz : Subgroup.center ↥L = ⊥
    · have hM : IsSpor ↥L .M22 := w135_isSpor_of_center_bot hz hs
      rcases h115 W hW Y L hLY hnorm hF hq hO2 hM hirr with h8 | hrk
      · omega
      · exact W4Lem13_5Concl.of_m22 ⟨hM, by rw [w135_card_eq_two_pow_rk hW, hrk]⟩
    · have hcard : Nat.card (Subgroup.center ↥L) = 3 :=
        w135_card_center_eq_three_of_m22 hq (w135_odd_card_center hctx') hz hs
      have h4 := h116 W hW Y L hLY hnorm hF hq hO2 hcard hs hirr
      omega
  · have h4 := h111 s hs22 W hW Y L hLY hnorm hF hq hO2 hs
    omega

end CFSG.LocalAnalysis.WeakClosure81
