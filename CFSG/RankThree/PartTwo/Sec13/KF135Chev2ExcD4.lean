module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcBasic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.RankThree.PartOne.KF.F122D4
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneTw
public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.Adapters.TauCetiExceptional.EvenB1

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.RankThree.PartTwo.Sec13.KF135Proof CFSG.LieType.SeitzGeneration

theorem pow_six_sub_one_eq {Q : ℕ} (hQ : 1 ≤ Q) :
    Q ^ 6 - 1 = (Q - 1) * (Q + 1) * ((Q ^ 2 + Q + 1) * (Q ^ 2 - Q + 1)) := by
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ
  rw [show Q ^ 6 = (Q ^ 3) ^ 2 by ring, sq_sub_one_eq_mul h3,
    CFSG.RankThree.PartOne.K128.pow3_sub_one Q hQ,
    CFSG.RankThree.PartOne.K128.cube_add_one_eq Q hQ]
  ring


theorem false_of_kF135Hyp_D4_of_not_E2 {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)}
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) {hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) (h : KF135Hyp S p P x u V)
    (hres : ¬ (p ∣ q.exponent ∧ p ∣ q.card ^ 6 - 1 ∧ ¬ p ∣ q.card - 1)) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
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
  have hout : CFSG.RankThree.PartOne.OutStructure.OutPChain p S := by
    have hce : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
          CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hq2 (by decide) e⟩
    rw [hq2] at hce
    exact (CFSG.RankThree.PartOne.OutStructure.outPNice_trialityD4 hp hce).toChain
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e₁⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have f : S ≃* ↥(CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) := e.trans e₁
  have : Finite ↥(CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) := Finite.of_equiv _ f.toEquiv
  by_cases h1 : p ∣ q.card - 1
  ·
    have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hq2]
    have hσ' : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, hq2]
    have hl := CFSG.RankThree.PartOne.two_le_localRank_graphFixedD4 q.exponent_pos hK' σ
      (Or.inl hσ') hp hp2 (by rwa [← hcard])
    rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv f hp] at hl
    exact false_of_two_le_localRank h hl
  by_cases h6 : p ∣ q.card ^ 6 - 1
  ·
    have hn : ¬ p ∣ q.exponent := fun hn => hres ⟨hn, h6, h1⟩
    have hinn : P ≤ (MulAut.conj : S →* MulAut S).range := by
      refine le_inn_of_forall_not_outer f hp (fun α hα => ?_) h.exponent
      obtain ⟨-, η, hη, -⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.trialityD4_stdDescent
          q.prime_p q.exponent_pos hK σ hσ hp hp5 α hα
      have hK3 : Nat.card K = 2 ^ (3 * q.exponent) := by rw [hK, hq2, ← pow_mul, mul_comm]
      obtain ⟨-, -, -, -, hcardAut, -⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
          Nat.prime_two (by have := q.exponent_pos; omega) hK3
      have h3n : p ∣ 3 * q.exponent := by
        rw [← hη, ← hcardAut]
        exact orderOf_dvd_natCard η
      rcases (Nat.Prime.dvd_mul hp).mp h3n with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
      · exact hn h3
    have hcard3 : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
    obtain ⟨m, hm, hpm⟩ : ∃ m, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6) ∧
        p ∣ CFSG.RankThree.PartOne.K128.phiNat m (q.p ^ q.exponent) := by
      rw [← hcard3]
      rw [pow_six_sub_one_eq hq1] at h6
      rcases (Nat.Prime.dvd_mul hp).mp h6 with h6 | h6
      · rcases (Nat.Prime.dvd_mul hp).mp h6 with h6 | h6
        · exact ⟨1, Or.inl rfl, h6⟩
        · exact ⟨2, Or.inr (Or.inl rfl), h6⟩
      · rcases (Nat.Prime.dvd_mul hp).mp h6 with h6 | h6
        · exact ⟨3, Or.inr (Or.inr (Or.inl rfl)), h6⟩
        · exact ⟨6, Or.inr (Or.inr (Or.inr rfl)), h6⟩
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hshape := CFSG.RankThree.PartOne.K1214.SylowShape.of_mulEquiv f
      (CFSG.RankThree.PartOne.K128.sylowShape_D4 q.exponent_pos K hK σ hσ hm hp hp5 hpm)
    exact false_of_rankLE2_inner h hinn
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_of_sylowShape hp hshape)
      (isMulCommutative_of_sylowShape hshape)
  ·
    have hr : RankLE1 p S := RankLE1.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE1_cat_trialityD4 q hv hp hp2 hpq h6)
    exact false_of_rankLE1 h hout hr

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
