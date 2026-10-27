module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeKNeOneFamilies
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpOmegaThreeNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCentralizerRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_not_sq_dvd_336_card_of_isSLn_six_seven
    {B : Type} [Group B] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hSL : IsSLn B n 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hp7 : p ≠ 7) :
    ¬ p ^ 2 ∣ 336 * Nat.card B := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hSL
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  intro hsq
  have hcard : Nat.card B = Nat.card (StatedSL n K) := Nat.card_congr e.toEquiv
  have hsq' : p ^ 2 ∣ 336 * Nat.card (StatedSL n K) := by
    rwa [hcard] at hsq
  have hbound : 336 * Nat.card (StatedSL n K) ∣ 935911159612047360 :=
    s168e3_card_statedSL_six_seven_dvd hK2 hn
  rcases s168e3_prime_eq_three_or_seven_of_sq_dvd_336_mul hp hp2 hsq' hbound with h3 | h7
  · exact hp3 h3
  · exact hp7 h7

theorem s168e3_false_of_sum_three_sl_six_seven
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1) :
    False := by
  have hT := s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  have h7 := s168e3_irrSet_seven_of_sum_three c hcomp hsum htrans hs
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hLn : IsLn ↥(lBar V₀ V hV L) n 1 := s16k_isLn_of_isSLn hn3 hSL
  have hClass : StatedClassicalModel ↥(lBar V₀ V hV L) .PSL n 2 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hLn (by decide)
  have hcard6 : n = 6 → Nat.card ↥(lBar V₀ V hV L) = 20158709760 := by
    intro h6
    have hc6 : StatedClassicalModel ↥(lBar V₀ V hV L) .PSL 6 2 1 := h6 ▸ hClass
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hc6]
    decide
  have hcard7 : n = 7 → Nat.card ↥(lBar V₀ V hV L) = 163849992929280 := by
    intro h7
    have hc7 : StatedClassicalModel ↥(lBar V₀ V hV L) .PSL 7 2 1 := h7 ▸ hClass
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hc7]
    decide
  have h3K := s168e3_three_not_dvd_kBar_of_sl_six_seven c hcomp hn hSL
  have h3 : 3 ∈ D.sig := by
    have hsig : D.sig = {3} := by
      refine s168e3_sig_eq_three_of_three_not_dvd_kBar c hT h7 h3K ?_
      intro p hp hp2 hp3 hp7
      rcases hn with rfl | rfl
      · simpa [hcard6 rfl] using
          s168e3_not_sq_dvd_336_card_of_isSLn_six_seven (Or.inl rfl) hSL hp hp2 hp3 hp7
      · simpa [hcard7 rfl] using
          s168e3_not_sq_dvd_336_card_of_isSLn_six_seven (Or.inr rfl) hSL hp hp2 hp3 hp7
    rw [hsig]
    exact Set.mem_singleton 3
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c167_cfg2_simple_ln hLn
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
    have hZ := s168e3_card_center_eq_one_of_isSLn_two_of_five_le
      (Q := Q) (B := ↥(lBar V₀ V hV L)) (n := n) hn5 hSL ⟨hQ.1⟩ eQ
    rw [hZ]
    norm_num
  have hE : T3EngineBranch (lBar V₀ V hV L) ⊤ (fixV (lBar V₀ V hV L)) 3 := by
    rcases hn with rfl | rfl
    · exact hT.t3EngineBranch_of_card (by rw [hcard6 rfl]; decide +kernel)
    · exact hT.t3EngineBranch_of_card (by rw [hcard7 rfl]; decide +kernel)
  exact s168e3_false_of_t3EngineBranch c hcomp hT h3 hsimple hcover hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
