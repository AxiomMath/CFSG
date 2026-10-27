module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Low
public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Four
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588D4
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588D1
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588D2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.RepresentationTheory
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)

namespace K318

theorem five_dvd_and_le_ordA {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) :
    5 ∣ ordA 1 (r ^ 2) ∧ 7800 ≤ ordA 1 (r ^ 2) := by
  have hodd : Odd (r ^ 2) := (hr.odd_of_ne_two (by omega)).pow
  have h2 := N588.two_mul_ordA_one hodd
  have hx : 25 ≤ r ^ 2 := by nlinarith
  have hx4 : 1 ≤ (r ^ 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨?_, ?_⟩
  · have h5 : 5 ∣ 2 * ordA 1 (r ^ 2) := by
      rw [h2]
      by_cases hr5' : r = 5
      · subst hr5'
        exact Dvd.dvd.mul_right (by norm_num) _
      · apply Dvd.dvd.mul_left
        have hcop : Nat.Coprime r 5 :=
          (Nat.coprime_primes hr Nat.prime_five).2 hr5'
        have h4 := Nat.ModEq.pow_totient hcop
        rw [Nat.totient_prime Nat.prime_five] at h4
        have h4' : (r ^ 2) ^ 2 ≡ 1 [MOD 5] := by
          rw [← pow_mul]
          exact h4
        exact (Nat.modEq_iff_dvd' hx4).1 h4'.symm
    exact (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 5 2)).1 h5
  · have h3 : 25 * 624 ≤ r ^ 2 * ((r ^ 2) ^ 2 - 1) := by
      apply Nat.mul_le_mul hx
      have : 625 ≤ (r ^ 2) ^ 2 := by nlinarith
      omega
    omega

theorem simple_card_of_list620
    {r : ℕ} {X : Type} [Group X] (hX : List620' r X) :
    IsSimpleGroup X ∧ ((r ≠ 3 ∧ Nat.card X = ordA 1 (r ^ 2)) ∨ Nat.card X = 7920 ∨
      Nat.card X = 20160 ∨ Nat.card X = 17971200 ∨ Nat.card X = 1814400) := by
  rcases hX with ⟨hr3, h⟩ | ⟨-, h | h⟩ | ⟨-, h | h⟩
  · exact ⟨LieModel.isSimpleGroup_psl_two h, Or.inl ⟨hr3, N588.card_of_psl_two h⟩⟩
  · obtain ⟨hs, hc⟩ := N588.simple_card_of_isSpor_M11 h
    exact ⟨hs, Or.inr (Or.inl hc)⟩
  · exact ⟨LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h,
      Or.inr (Or.inr (Or.inl (LieModel.card_psl_three_four h)))⟩
  · obtain ⟨hs, hc⟩ := N588.simple_card_of_tits h
    exact ⟨hs, Or.inr (Or.inr (Or.inr (Or.inl hc)))⟩
  · obtain ⟨hs, hc⟩ := N588.simple_card_of_isAlt_ten h
    exact ⟨hs, Or.inr (Or.inr (Or.inr (Or.inr hc)))⟩

theorem big_five_of_orders {r n : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : (r ≠ 3 ∧ n = ordA 1 (r ^ 2)) ∨ n = 7920 ∨ n = 20160 ∨ n = 17971200 ∨ n = 1814400) :
    1081 ≤ n ∧ 5 ∣ n := by
  rcases h with ⟨hr3, rfl⟩ | rfl | rfl | rfl | rfl
  · have hr5 : 5 ≤ r := by
      have := hr.two_le
      have h4 : r ≠ 4 := by
        rintro rfl
        norm_num at hr
      omega
    obtain ⟨h5, h78⟩ := five_dvd_and_le_ordA hr hr5
    exact ⟨by omega, h5⟩
  all_goals exact ⟨by norm_num, by norm_num⟩

theorem false_of_linear_section {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqr : q ≠ r) {X : Type} [Group X] (hX : List620' r X) {L : Type} [Group L]
    [Finite L] [Group.IsPerfect L] (Y : Subgroup L) [Y.Normal] (hYs : Group.IsSolvable Y)
    (hYodd : Odd (Nat.card Y)) (eX : L ⧸ Y ≃* X) {d : ℕ} (hd : d ≤ 4)
    (φ : L →* GL (Fin d) (ZMod q)) (hφ : φ.ker ≤ Y) : False := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hsX, horder⟩ := simple_card_of_list620 hX
  have hs : IsSimpleGroup (L ⧸ Y) := (MulEquiv.isSimpleGroup_congr eX).2 hsX
  have hnL : Nat.card (L ⧸ Y) = Nat.card X := Nat.card_congr eX.toEquiv
  obtain ⟨hbig, h5⟩ := big_five_of_orders hr hr2 horder
  have h318 : ¬ N588.List318 r (Nat.card X) := N588.false_of_orders hr hr2 horder
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  by_cases hirr : IsIrreducibleMatrixRep φ
  · obtain ⟨hRn, ⟨e⟩⟩ := exists_range_quotient_equiv φ Y hφ
    haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have hRs : Group.IsSolvable (Y.map φ.rangeRestrict) := by
      haveI := hYs
      exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective φ.rangeRestrict Y)
    have hRodd : Odd (Nat.card (Y.map φ.rangeRestrict)) :=
      Odd.of_dvd_nat hYodd (Subgroup.card_map_dvd Y _)
    have hsP : IsSimpleGroup (φ.range ⧸ Y.map φ.rangeRestrict) :=
      (MulEquiv.isSimpleGroup_congr e).2 hs
    have hcard : Nat.card (φ.range ⧸ Y.map φ.rangeRestrict) = Nat.card X :=
      (Nat.card_congr e.toEquiv).trans hnL
    have hirrP : IsIrreducibleMatrixRep φ.range.subtype := fun W hW =>
      hirr W fun g w hw => hW ⟨φ g, g, rfl⟩ w hw
    rcases (show d ≤ 3 ∨ d = 4 by omega) with hd3 | rfl
    · exact false_of_dim_le_three hq2 hd3 hirrP _ hRs hsP (hcard ▸ hbig) (hcard ▸ h5)
        (hcard ▸ h318)
    · exact false_of_dim_four hq2 hirrP _ hRs hRodd hsP hr hr2 hqr hX (e.trans eX)
  · simp only [IsIrreducibleMatrixRep, not_forall] at hirr
    obtain ⟨W, hW, hWne⟩ := hirr
    push Not at hWne
    obtain ⟨d', hd', ψ, hψ⟩ := exists_lower_of_reducible hYs hs φ hφ W hW hWne.1 hWne.2
    exact ih d' hd' (by omega) ψ hψ

end K318

namespace Mz614

variable {G : Type} [Group G] [Finite G]

open N588


theorem c622_direct (m : Mz614 G) (_h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h619 : m.C619)
    (hL : m.L620) : m.C622 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hX : m.r = 3 ∧ IsAlt m.Lbar 6 ∨ K318.List620' m.r m.Lbar := by
    rcases hL.2 with h | h | h
    · by_cases hr3 : m.r = 3
      · exact Or.inl ⟨hr3, isAlt_six_of_psl_two h hr3⟩
      · exact Or.inr (Or.inl ⟨hr3, h⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  rcases hX with ⟨hr3, hA⟩ | hX
  · exact Or.inr ⟨hr3, hA⟩
  have hs : IsSimpleGroup m.Lbar := (K318.simple_card_of_list620 hX).1
  have hnc := m.Lbar_not_comm hL.1 hs
  obtain ⟨-, hperf, hdich⟩ := quasisimple_or_centralizer_le (r := m.r)
    (P := CFSG.pPrimeCore m.r ↥m.L) m.isSolvable_pPrimeCore_L CFSG.pPrimeCore_coprime_card hs hnc
    m.gen_L
  rcases hdich with hq | hcent
  · exact Or.inl hq
  exfalso
  haveI : Group.IsPerfect ↥m.L := ⟨hperf⟩
  obtain ⟨q, hq, hqY, d, hd, φ, hφ⟩ := K318.exists_linear_section (CFSG.pPrimeCore m.r ↥m.L)
    m.isSolvable_pPrimeCore_L m.odd_card_pPrimeCore_L
    (fun p hp hp2 => m.pRank_pPrimeCore_L_le_three h619 hp hp2) hcent hs
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 m.odd_card_pPrimeCore_L) (even_iff_two_dvd.2 hqY)
  have hqr : q ≠ m.r := by
    rintro rfl
    have hcop := CFSG.pPrimeCore_coprime_card (p := m.r) (G := ↥m.L)
    exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hqY)
  exact K318.false_of_linear_section m.hr m.d.odd hq hq2 hqr hX (CFSG.pPrimeCore m.r ↥m.L)
    m.isSolvable_pPrimeCore_L m.odd_card_pPrimeCore_L (MulEquiv.refl _) hd φ hφ

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
