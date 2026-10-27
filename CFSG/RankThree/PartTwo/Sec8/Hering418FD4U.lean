module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FLin
public import CFSG.RankThree.PartTwo.Sec8.Hering418FU

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (ordTwistedA)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

section Fixed


theorem exists_fixed_order_four_lThree {G : Type} [Group G]
    [Finite G] {K : Subgroup G} {a : G} {m : ℕ} (hmE : Even m) (hm1 : 1 ≤ m)
    (eKP : K ⧸ aschbacherSolvableCore 3 K ≃* projSL 3 (GaloisField 2 m))
    (hKa : KFacts.InducesStdKind K a .field) (haK : a ∈ Subgroup.normalizer (K : Set G)) :
    ∃ y : K ⧸ aschbacherSolvableCore 3 K,
      Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) y = y ∧ y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eK : K ⧸ aschbacherSolvableCore 3 K ≃* projectiveSL 3 (GaloisField 2 m) :=
    eKP.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 m))
  obtain ⟨haK', hkindK⟩ := hasKind_of_inducesStdKind_lThree hmE hm1 eKP hKa
  obtain ⟨uK, huKfix, huK4, huK2⟩ := exists_fixed_order_four_of_hasKind_field hkindK
  refine ⟨eK.symm uK, ?_, ?_, ?_⟩
  · apply eK.injective
    have h1 : KFacts.inducedAutHom K eK ⟨a, haK⟩ (eK (eK.symm uK)) =
        eK (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) (eK.symm uK)) := by
      change MulAut.congr eK _ (eK (eK.symm uK)) = _
      simp [MulAut.congr_apply]
    rw [← h1, MulEquiv.apply_symm_apply]
    exact huKfix
  · apply eK.injective
    rw [map_pow, map_one, MulEquiv.apply_symm_apply]
    exact huK4
  · intro h
    apply huK2
    rw [← MulEquiv.apply_symm_apply eK uK, ← map_pow, h, map_one]

theorem exists_fixed_order_four_uThree {G : Type} [Group G] [Finite G] {K : Subgroup G} {a : G}
    {m : ℕ} (hmo : Odd m) (hm2 : 2 ≤ m)
    (eKP : K ⧸ aschbacherSolvableCore 3 K ≃* projSU 3 2 m)
    (hKa : KFacts.InducesStdKind K a .field) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (ha3 : a ^ 3 = 1) :
    ∃ y : K ⧸ aschbacherSolvableCore 3 K,
      Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) y = y ∧ y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm1 : 1 ≤ m := by omega
  have hGF := Sec4.unitaryFieldData_galoisField 2 m hm1
  have hq : 2 < 2 ^ m :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm2)
  have hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd (eKP.trans (Sec4.projSUEquivUnitaryPSU 2 m hGF)).symm
      (KFacts.center_unitaryPSU_three_eq_bot hGF hq)
  have hcardK : Nat.card (K ⧸ aschbacherSolvableCore 3 K) = ordTwistedA 2 (2 ^ m) :=
    (Nat.card_congr eKP.toEquiv).trans (KFacts.card_projSU_three_two hm1)
  have hoddK := KFacts.not_oddCharStdModel_of_mulEquiv_projSU hm2 eKP
  obtain ⟨K'', _, hK'', hq'', eK, haK', hkindK⟩ :
      ∃ (K'' : Type) (_ : Field K'') (hK'' : UnitaryFieldData 2 m K'') (_ : 2 < 2 ^ m)
        (eK : K ⧸ aschbacherSolvableCore 3 K ≃* unitaryPSU hK'' 3)
        (haK' : a ∈ Subgroup.normalizer (K : Set G)),
        (KFacts.stdPinnedPSU3 hK'').HasKind (KFacts.inducedAutHom K eK ⟨a, haK'⟩) .field := by
    rcases KFacts.inducesKindPSU3_or_oddCharStdModel (m := m) hmo hcardK hZK hKa with
      ⟨K'', _, hK'', hq'', eK, hx', hkind⟩ | hO
    · exact ⟨K'', inferInstance, hK'', hq'', eK, hx', hkind⟩
    · exact (hoddK hO).elim
  obtain ⟨uK, huKfix, huK4, huK2⟩ := exists_fixed_order_four_psu hK'' hq'' hmo hkindK
    (KFacts.inducedAutHom_pow_eq_one K eK haK' ha3)
  refine ⟨eK.symm uK, ?_, ?_, ?_⟩
  · apply eK.injective
    have h1 : KFacts.inducedAutHom K eK ⟨a, haK⟩ (eK (eK.symm uK)) =
        eK (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) (eK.symm uK)) := by
      change MulAut.congr eK _ (eK (eK.symm uK)) = _
      simp [MulAut.congr_apply]
    rw [← h1, MulEquiv.apply_symm_apply]
    exact huKfix
  · apply eK.injective
    rw [map_pow, map_one, MulEquiv.apply_symm_apply]
    exact huK4
  · intro h
    apply huK2
    rw [← MulEquiv.apply_symm_apply eK uK, ← map_pow, h, map_one]

end Fixed

end CFSG.RankThree.PartTwo.Sec8.Hering418
