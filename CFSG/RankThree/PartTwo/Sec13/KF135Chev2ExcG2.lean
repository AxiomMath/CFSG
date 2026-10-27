module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodG2
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellG2
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcG2
public import CFSG.RankThree.PartOne.KF.F122G2
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneSmall

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.RankThree.PartTwo.Sec13.KF135Proof CFSG.LieType.SeitzGeneration


theorem false_of_kF135Hyp_G2_of_not_E2 {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)}
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) {hv : (TauCeti.LieTypeIndex.G2 q).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) (h : KF135Hyp S p P x u V)
    (hres : ¬ (p ∣ q.exponent ∧ p ∣ q.card + 1)) : False := by
  have hp := h.prime
  have hp7 := h.seven_le
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by omega
  have hpq : p ≠ q.p := by
    rw [hq2]
    exact hp2
  have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have hq1 : 1 ≤ q.card := by
    rw [hcard]
    exact Nat.one_le_two_pow
  obtain ⟨K, _, _, hK, hKc, ⟨e₁⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  have f : S ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := e.trans e₁
  by_cases h1 : p ∣ q.card - 1
  ·
    have : CharP K 2 := hq2 ▸ hKc
    have : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := Finite.of_equiv _ f.toEquiv
    have hl := CFSG.RankThree.PartOne.two_le_localRank_adjoint_G2 (k := K) hp hp2
      (by rwa [hK])
    rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv f hp] at hl
    exact false_of_two_le_localRank h hl
  by_cases h2 : p ∣ q.card ^ 2 - 1
  ·
    have hplus : p ∣ q.card + 1 := by
      rw [sq_sub_one_eq_mul hq1] at h2
      exact ((Nat.Prime.dvd_mul hp).mp h2).resolve_left h1
    have hn : ¬ p ∣ q.exponent := fun hn => hres ⟨hn, hplus⟩
    have hn2 : 2 ≤ q.exponent := by
      by_contra hlt
      have h3 : 3 ≤ q.card :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      have hle : q.exponent ≤ 1 := by omega
      have : q.card ≤ 2 := by
        rw [hcard]
        calc 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
          _ = 2 := by norm_num
      omega
    have hK2 : Nat.card K = 2 ^ q.exponent := hK.trans hcard
    have hinn : P ≤ (MulAut.conj : S →* MulAut S).range := by
      refine le_inn_of_forall_not_outer f hp (fun α hα => ?_) h.exponent
      obtain ⟨-, σ, hσ, -⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.stdDescent_G2_even hn2 hK2 hp
          α hα
      obtain ⟨-, -, -, -, hcardAut, -⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
          Nat.prime_two (by omega) hK2
      apply hn
      rw [← hσ, ← hcardAut]
      exact orderOf_dvd_natCard σ
    have hr : RankLE2 p S := RankLE2.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Curtis.Coordinator.rankLE2_cat_G2 q hv hq2 hp hp2)
    have hab : ∀ Q : Sylow p S, IsMulCommutative (Q : Subgroup S) := fun Q =>
      CFSG.LocalAnalysis.RankFourTheoremC.crossSylowAbelianAt_G2 hv p hp hp5
        (by
          show (TauCeti.LieTypeIndex.G2 q).characteristic ≠ p
          rw [TauCeti.LieTypeIndex.characteristic_G2, hq2]
          exact hp2.symm) S h.simple ⟨e⟩ Q
    exact false_of_rankLE2_inner h hinn hr hab
  ·
    have hr : RankLE1 p S := RankLE1.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE1_cat_G2 q hv hp hp5 hpq h2)
    exact false_of_rankLE1 h (CFSG.RankThree.PartOne.OutStructure.OutPNice.of_mulEquiv e
      (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.outPNice_cat_G2 q hv hp)).toChain hr

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
