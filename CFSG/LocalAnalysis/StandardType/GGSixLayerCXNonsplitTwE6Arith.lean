module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Order
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion
public import CFSG.RankThree.PartOne.KLC.Degenerate
public import CFSG.Foundations
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Close
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.PartOne.N143X.RankHelpers
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley

namespace TwE6Nonsplit

section Row

private def rowTwistedE6 : Finset ℕ := {1, 2, 3, 4, 6, 8, 10, 12, 18}

private theorem mem_rowTwistedE6 {m : ℕ} (hm : m ∈ rowTwistedE6) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12 ∨ m = 18 := by
  simpa [rowTwistedE6] using hm

end Row

section Card


theorem exists_dvd_phi_of_dvd_card_twE6 {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpC : p ∣ Nat.card (twistedE6RootGroup K σ)) :
    ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12 ∨ m = 18) ∧
      (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi m).eval ((2 ^ f : ℕ) : ℤ) := by
  set q := 2 ^ f with hqdef
  have hq1 : 1 ≤ q := by rw [hqdef]; exact Nat.one_le_two_pow
  have hpq : ¬ p ∣ q := by
    rw [hqdef]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hcard : Nat.card (twistedE6RootGroup K σ) = ordTwistedE6 q := by
    rw [hqdef]
    exact CFSG.LieType.SeitzGeneration.ExcHighThree.card_twistedE6RootGroup_eq
      Nat.prime_two hf σ hK hσ
  have hord : p ∣ ordTwistedE6 q := by rw [← hcard]; exact hpC
  have hnum : p ∣ CFSG.SeitzReduction.E6Pilot.numTwistedE6 q := by
    have h1 : ordTwistedE6 q ∣ CFSG.SeitzReduction.E6Pilot.numTwistedE6 q :=
      ⟨Nat.gcd 3 (q + 1), (CFSG.SeitzReduction.E6Pilot.ordTwistedE6_mul_gcd q).symm⟩
    exact hord.trans h1
  obtain ⟨h9, h5, -⟩ := plus_factors_eq_prod_exhaustionPhi (q : ℤ)
  have hplus : ∀ M : List ℕ, (∀ m ∈ M, m ∈ rowTwistedE6) →
      ∀ n : ℕ, (n : ℤ) = (M.map fun m => (exhaustionPhi m).eval (q : ℤ)).prod → p ∣ n →
      ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12 ∨ m = 18) ∧
        (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) := by
    intro M hM n hn hpn
    have h1 : (p : ℤ) ∣ (M.map fun m => (exhaustionPhi m).eval (q : ℤ)).prod := by
      rw [← hn]
      exact Int.natCast_dvd_natCast.mpr hpn
    obtain ⟨m, hm, hpm⟩ := exists_dvd_exhaustionPhi_of_dvd_prod hp h1
    exact ⟨m, mem_rowTwistedE6 (hM m hm), hpm⟩
  have hminus : ∀ d ∈ ([12, 8, 6, 2] : List ℕ), p ∣ q ^ d - 1 →
      ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12 ∨ m = 18) ∧
        (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ) := by
    intro d hd h
    obtain ⟨m, hm, hpm⟩ := exists_mem_row_of_dvd_pow_sub_one hp hq1
      (D := [12, 8, 6, 2]) (by decide) (row := rowTwistedE6) (by decide) ⟨d, hd, h⟩
    exact ⟨m, mem_rowTwistedE6 hm, hpm⟩
  unfold CFSG.SeitzReduction.E6Pilot.numTwistedE6 at hnum
  rcases (Nat.Prime.dvd_mul hp).1 hnum with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
            · exact absurd (hp.dvd_of_dvd_pow h) hpq
            · exact hminus 12 (by simp) h
          · exact hplus [2, 6, 18] (by decide) _ (by push_cast; exact h9) h
        · exact hminus 8 (by simp) h
      · exact hminus 6 (by simp) h
    · exact hplus [2, 10] (by decide) _ (by push_cast; exact h5) h
  · exact hminus 2 (by simp) h

end Card

section Ten

theorem five_lt_of_dvd_phiTen {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hq : 1 ≤ q)
    (hq2 : ¬ p ∣ q + 1)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 10).eval (q : ℤ)) :
    5 < p := by
  by_contra hlt
  have hp5 : p = 5 := by
    have h2 := hp.two_le
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  subst hp5
  apply hq2
  have h : (5 : ℤ) ∣ ((q + 1 : ℕ) : ℤ) := by
    have := CFSG.RankThree.PartOne.KLC.dvd_add_one_of_dvd_phi_ten hpf
    push_cast
    exact this
  exact Int.natCast_dvd_natCast.mp h

end Ten

end TwE6Nonsplit

end CFSG.StandardType
