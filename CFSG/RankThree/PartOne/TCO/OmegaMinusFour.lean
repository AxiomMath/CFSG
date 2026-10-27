module

public import CFSG.RankThree.PartOne.S11d.LowRank
public import CFSG.RankThree.PartOne.KF.ClsOmegaMinusQPlus
public import CFSG.RankThree.PartOne.TCO.WeirFour
public import CFSG.RankThree.PartOne.TCO.ModelMinus

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.RankThree.PartOne.TCO

theorem false_of_pOmegaMinus_four {T : Type} [Group T] [Finite T] {p n f₀ : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hLR2 : LocalRankLeTwo p T) (h2 : 2 ≤ CFSG.pRank p T)
    (hM : LieModel T .POmegaMinus n 2 (p * f₀)) (hn : n ≤ 4) : False := by
  classical
  obtain ⟨hadm, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.statedClassicalModel_of_lieModel_classical (by decide) hM
  have hch : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hcard
  have hn4 : n = 4 := le_antisymm hn hadm.2.2
  subst hn4
  have hp2 : p ≠ 2 := by omega
  by_cases h1 : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1
  · have h3 : 3 ≤ localRank p
        (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) := by
      rcases h1 with h1 | h1
      · exact CFSG.RankThree.PartTwo.KFacts.KS21LocalRank.le_localRank_statedOmegaMinus_torus hp hp2
          (by rw [Nat.card_units]; exact h1) b c
      · exact CFSG.RankThree.PartOne.omegaEightMinusQPlus K b c hirr p hp hp2 h1
    have h3T : 3 ≤ localRank p T := by
      rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
      exact h3
    exact CFSG.RankThree.PartOne.false_of_three_le_localRank hp hLR2 h3T
  · push Not at h1
    have : Fact p.Prime := ⟨hp⟩
    have hpK : ¬ p ∣ Nat.card K := by
      intro hd
      rw [hcard] at hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
    have hQ1 : 1 ≤ Nat.card K := Nat.card_pos
    have hr : (Nat.card K : ZMod p) ^ 2 ≠ 1 := by
      intro hsq
      have hmul : ((Nat.card K : ZMod p) - 1) * ((Nat.card K : ZMod p) + 1) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.1 hmul with h | h
      · apply h1.1
        have h' : ((Nat.card K : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          rw [Nat.cast_one]; exact sub_eq_zero.1 h
        exact (Nat.modEq_iff_dvd' hQ1).1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h').symm
      · apply h1.2
        have h' : (((Nat.card K + 1 : ℕ)) : ZMod p) = 0 := by
          rw [Nat.cast_add, Nat.cast_one]; exact h
        exact (ZMod.natCast_eq_zero_iff _ _).1 h'
    obtain ⟨iso⟩ := nonempty_statedProj_mulEquiv_orthDerived (K := K) (n := 4) le_rfl hirr
    have hle : CFSG.RankThree.Classical2.orthDerived (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) ≤
        TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) := by
      refine Subgroup.commutator_le.mpr fun a ha a' ha' => ?_
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha ha')
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ ha')
    let ι : T →* TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) :=
      (Subgroup.inclusion hle).comp (e.trans iso).toMonoidHom
    have hι : Function.Injective ι :=
      (Subgroup.inclusion_injective hle).comp (e.trans iso).injective
    have := pRank_le_one_orthMinusFour hirr hp hp2 hpK hr ι hι
    omega

theorem threeCompBL_POmegaMinus : ThreeCompBL .POmegaMinus := by
  intro T _ _ p hp hp5 hLR2 h2 n f₀ _ hM hlow
  exact (false_of_pOmegaMinus_four hp hp5 hLR2 h2 hM hlow).elim

theorem fixedRankTL_POmegaMinus : FixedRankTL .POmegaMinus := by
  intro T _ _ p hp hp5 hLR2 h2 n f₀ _ hM hlow
  exact (false_of_pOmegaMinus_four hp hp5 hLR2 h2 hM hlow).elim

end CFSG.RankThree.PartOne.TCX
