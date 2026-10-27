module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanPlus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RootLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientBridge
public import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
public import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

theorem k_U4CartanPlus_of_center :
    ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .PSU 4 2 n → 2 < 2 ^ n →
      Subgroup.center Y = ⊥ →
      ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ → ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 →
        p ∣ Nat.card (normalizerQuotient S) := by
  intro Y _ _ n hY hq hZ S hS p hp hpd
  have : IsSimpleGroup Y :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hY
  have hQ : CFSG.Open.IsQuasisimple Y :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.P22y.isQuasisimple_of_isSimpleGroup hZ
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_equiv_quot_of_center_eq_bot hZ
  have hL : LieModel (Y ⧸ Subgroup.center Y) .PSU (2 * 2 + 0) 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hY
  have hn : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp at hq
    · exact h
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have h4 : ¬ p ∣ 2 * 2 + 0 := by
    intro h
    have h' : p ∣ 2 ^ 2 := by simpa using h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h'))
  have hW := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_borelWit_of_lieModel (r := 2)
    (ε := 0) hQ (by norm_num) (by norm_num) (by norm_num) hn hL hp hpd h4
  have h := (le_pRank_normalizerQuotient_of_borelWit hp hp2 hW S hS).2
  simpa using h

section Certificates


theorem k_U4CartanPlus_holds : K_U4CartanPlus := by
  intro Y _ _ n hY hq S hS p hp hpd
  exact k_U4CartanPlus_of_center Y n hY hq
    (center_eq_bot_of_rootLineShape hq (Or.inl hY)) S hS p hp hpd

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
