module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcBasic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousReeF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.RankThree.PartOne.KF.F122F4
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneRee
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.RankThree.PartTwo.Sec13.KF135Proof CFSG.LieType.SeitzGeneration CFSG.LieType.Ree

theorem pow_four_sub_one_eq {Q : ℕ} (hQ : 1 ≤ Q) : Q ^ 4 - 1 = (Q - 1) * (Q + 1) * (Q ^ 2 + 1) := by
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  rw [show Q ^ 4 = (Q ^ 2) ^ 2 by ring, sq_sub_one_eq_mul h2, sq_sub_one_eq_mul hQ]


theorem false_of_kF135Hyp_F4_of_not_E2 {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)} {m : ℕ}
    {hv : (TauCeti.LieTypeIndex.reeF4 m).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) (h : KF135Hyp S p P x u V)
    (hres : ¬ (p ∣ 2 * m + 1 ∧ p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 ∧ ¬ p ∣ 2 ^ (2 * m + 1) - 1)) :
    False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp7 := h.seven_le
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by omega
  have hout : CFSG.RankThree.PartOne.OutStructure.OutPChain p S :=
    (CFSG.RankThree.PartOne.OutStructure.outPNice_twistedF4 hp
      (CFSG.StandardType.ChevTwo.reeTitsModel_of_reeF4 m hv e)).toChain
  obtain ⟨X, _, _, _, hm1, hX, -, ⟨e₁⟩⟩ := CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  have f : S ≃* ↥(ReeTag.F4.reeGamma X m) := e.trans e₁
  have : Finite ↥(ReeTag.F4.reeGamma X m) := Finite.of_equiv _ f.toEquiv
  have hq1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  by_cases h1 : p ∣ 2 ^ (2 * m + 1) - 1
  ·
    have hl := CFSG.RankThree.PartOne.two_le_localRank_reeFixed_F4 (K := X) (a := m) hX hp h1
    have g : ↥(reeFixed ReeTag.F4 X m) ≃* ↥(ReeTag.F4.reeGamma X m) :=
      ((reeFixed ReeTag.F4 X m).equivMapOfInjective
        (CFSG.Blueprint.Chevalley.adjointGroup ReeTag.F4.tag X).subtype
        Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (CFSG.LieType.Ree.LargeReeInvolution.map_reeFixed_eq_reeGamma))
    have : Finite ↥(reeFixed ReeTag.F4 X m) := Finite.of_equiv _ g.symm.toEquiv
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv g hp,
      ← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv f hp] at hl
    exact false_of_two_le_localRank h hl
  by_cases h4 : p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1
  ·
    have hn : ¬ p ∣ 2 * m + 1 := fun hn => hres ⟨hn, h4, h1⟩
    have hinn : P ≤ (MulAut.conj : S →* MulAut S).range := by
      refine le_inn_of_forall_not_outer f hp (fun α hα => ?_) h.exponent
      obtain ⟨-, β, hβ, -⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeF4_stdDescent_odd hm1 hX hp
          α hα
      obtain ⟨-, -, -, -, hcardAut, -⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
          Nat.prime_two (by omega) hX
      apply hn
      rw [← hβ, ← hcardAut]
      exact orderOf_dvd_natCard β
    obtain ⟨d, hd, hpd⟩ : ∃ d, (d = 1 ∨ d = 2 ∨ d = 4) ∧
        p ∣ CFSG.RankThree.PartOne.K128.phiF4 d (2 ^ (2 * m + 1)) := by
      rw [pow_four_sub_one_eq hq1] at h4
      rcases (Nat.Prime.dvd_mul hp).mp h4 with h4 | h4
      · rcases (Nat.Prime.dvd_mul hp).mp h4 with h4 | h4
        · exact absurd h4 h1
        · exact ⟨2, Or.inr (Or.inl rfl), h4⟩
      · exact ⟨4, Or.inr (Or.inr rfl), h4⟩
    have hshape := CFSG.RankThree.PartOne.K1214.SylowShape.of_mulEquiv f
      (CFSG.RankThree.PartOne.K128.sylowShape_ree (K := X) (a := m) hX hd hp hp5 hpd)
    exact false_of_rankLE2_inner h hinn
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_of_sylowShape hp hshape)
      (isMulCommutative_of_sylowShape hshape)
  ·
    have hr : RankLE1 p S := RankLE1.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE1_cat_reeF4 hv hp hp2 h4)
    exact false_of_rankLE1 h hout hr

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
