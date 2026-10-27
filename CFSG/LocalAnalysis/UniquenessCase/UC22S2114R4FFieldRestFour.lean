module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FLowerLinearSetup
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)



theorem s21_14R4FFieldRest_dataOfSetup4 {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    ∀ (_ : UC6S846.SigmaStd (UC6.dataOfSetup4 hS hU S)) (_ : F07.R76Sig (UC6.dataOfSetup4 hS hU S)) (_ : F07.R74Card (UC6.dataOfSetup4 hS hU S)),
    H1930 (UC6.dataOfSetup4 hS hU S) → ∀ c : Ctx21 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True), ∀ L ∈ calC S.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ∀ l f : ℕ, 4 ≤ l → PartTwo.S17.CHasLieRank (BarInf L) l f → 3 ≤ c.n →
    c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    (Odd c.n ∨ (LieModel (BarInf L) .PSL 5 2 f ∧ Odd f ∧ 3 ≤ f)) →
    (∀ r : ℕ, r.Prime → 5 ≤ r → r ∣ 2 ^ c.n - 1 → r ∣ f) →
    ∀ (b : G), b ∈ c.B0 → ∀ (hbL : b ∈ normalizer (L : Set G)) (r : ℕ),
      r.Prime → 5 ≤ r → orderOf b = r → r ∣ 2 ^ c.n - 1 → r ∣ f →
      inducedBarInfAutHom L ⟨b, hbL⟩ ∉
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range →
      (¬ ∃ m : ℕ, 8 ≤ m ∧ LieModel (BarInf L) .PSU m 2 f ∧ Odd c.n) →
      (¬ ∃ m : ℕ, 8 ≤ m ∧ LieModel (BarInf L) .PSL m 2 f) →
      (¬ ∃ m : ℕ, 5 ≤ m ∧ LieModel (BarInf L) .PSL m 2 f ∧ (Even f ∨ 2 ≤ f / r)) →
      (¬ ∃ m : ℕ, 6 ≤ m ∧ LieModel (BarInf L) .PSL m 2 f) →
      (¬ ∃ n : ℕ, 4 ≤ n ∧ LieModel (BarInf L) .PSp n 2 f) →
      (¬ ∃ n : ℕ, 4 ≤ n ∧ LieModel (BarInf L) .POmegaPlus n 2 f) →
      (¬ ∃ n : ℕ, 5 ≤ n ∧ LieModel (BarInf L) .POmegaMinus n 2 f) →
      ¬ LieModel (BarInf L) .F4 0 2 f → ¬ LieModel (BarInf L) .E6 0 2 f →
      ¬ LieModel (BarInf L) .E7 0 2 f →
      ¬ LieModel (BarInf L) .E8 0 2 f →
      ¬ LieModel (BarInf L) .twistedE6 0 2 f →
      (¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) ∧
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∈ (UC6.dataOfSetup4 hS hU S).sig ∧
        ∃ X : Subgroup (BarInf L), IsPGroup p ↥X ∧ ¬ IsCyclic ↥X ∧
          ∀ x ∈ X, inducedBarInfAutHom L ⟨b, hbL⟩ x = x) ∧
      (∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ≠ r ∧
        ¬ q ∣ Nat.card (CFSG.solvableRadical ↥L) ∧
        ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
          ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* BarInf L, Function.Injective ι ∧
            ∀ a, inducedBarInfAutHom L ⟨b, hbL⟩ (ι a) = ι (κ a)) := by
  intro hSg h76 h74 hH c L hL hX hpow l f hl hlr hn3 hBL hfaith hcase hall
    b hbB hbL r hr hr5 hbr hrn hrf hin hu hlin hlow hsix hsp hplus hminus hf4 he6 he7 he8 htw
  rcases hcase with hodd | ⟨h5, _, _⟩
  · obtain ⟨t, m, hadm, hmodel, hrank⟩ := hlr
    have hbig : 4 ≤ PartTwo.S17.CS17LieRank t m := hrank.symm ▸ hl
    cases t with
    | PSL =>
      have hm : 5 ≤ m := by simp only [PartTwo.S17.CS17LieRank] at hbig; omega
      by_cases hm5 : m = 5
      · subst m
        exact (uc22s2114r4f_false_of_psl_five_dataOfSetup4 hS hU S hMS hPart
          h74 hH c hL hmodel hbB hbL hr hr5 hbr hrn hrf (Or.inl hodd) hin).elim
      · exact (hsix ⟨m, by omega, hmodel⟩).elim
    | PSU => exact (hu ⟨m, by simp only [PartTwo.S17.CS17LieRank] at hbig; omega,
        hmodel, hodd⟩).elim
    | PSp => exact (hsp ⟨m, by simpa only [PartTwo.S17.CS17LieRank] using hbig, hmodel⟩).elim
    | POmegaOdd => exact (hadm.2.2.2 rfl).elim
    | POmegaPlus => exact (hplus ⟨m, by simpa only [PartTwo.S17.CS17LieRank] using hbig, hmodel⟩).elim
    | POmegaMinus => exact (hminus ⟨m, by simp only [PartTwo.S17.CS17LieRank] at hbig; omega, hmodel⟩).elim
    | F4 => have hm : m = 0 := hadm.2.2; subst m; exact (hf4 hmodel).elim
    | E6 => have hm : m = 0 := hadm.2.2; subst m; exact (he6 hmodel).elim
    | E7 => have hm : m = 0 := hadm.2.2; subst m; exact (he7 hmodel).elim
    | E8 => have hm : m = 0 := hadm.2.2; subst m; exact (he8 hmodel).elim
    | twistedE6 => have hm : m = 0 := hadm.2.2; subst m; exact (htw hmodel).elim
    | G2 => simp [PartTwo.S17.CS17LieRank] at hbig
    | trialityD4 => simp [PartTwo.S17.CS17LieRank] at hbig
    | twistedB2 => simp [PartTwo.S17.CS17LieRank] at hbig
    | twistedG2 => simp [PartTwo.S17.CS17LieRank] at hbig
    | twistedF4 => simp [PartTwo.S17.CS17LieRank] at hbig
    | Tits => simp [PartTwo.S17.CS17LieRank] at hbig
  · exact (uc22s2114r4f_false_of_psl_five_dataOfSetup4 hS hU S hMS hPart
      h74 hH c hL h5 hbB hbL hr hr5 hbr hrn hrf
      (Or.inr ⟨h5, by assumption, by assumption⟩) hin).elim


end CFSG.LocalAnalysis.UniquenessCase.UC22
