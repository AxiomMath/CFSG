module

public import CFSG.RankThree.PartOne.N143.O7Rank
public import CFSG.RankThree.PartOne.N143.SectionListLie
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG TauCeti CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr)
open CFSG.ClassicalInvolution.Upgrade (map_statedOmega statedQuadOdd_comp)

namespace O7

theorem det_eq_one_of_mem_om {A : GL Idx (ZMod 3)} (hA : A ∈ Om) :
    Matrix.GeneralLinearGroup.det A = 1 := by
  have h : Om ≤ (Matrix.GeneralLinearGroup.det (n := Idx) (R := ZMod 3)).ker := by
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  exact h hA

theorem scalars_subgroupOf_om : (StatedScalars Idx (ZMod 3)).subgroupOf Om = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.1 hA : (A : GL Idx (ZMod 3)) ∈ StatedScalars Idx (ZMod 3))
  have h1 : c ^ Fintype.card Idx = 1 := by
    rw [← Matrix.GeneralLinearGroup.det_scalar, hc]
    exact det_eq_one_of_mem_om A.2
  have hcard : Fintype.card Idx = 7 := by simp [Idx]
  have hc1 : c = 1 := by
    have key : ∀ c : (ZMod 3)ˣ, c ^ 7 = 1 → c = 1 := by decide
    exact key c (hcard ▸ h1)
  subst hc1
  exact Subtype.ext (hc.symm.trans (map_one _))

noncomputable def projEquivOm : StatedProj Om ≃* ↥Om :=
  (QuotientGroup.quotientMulEquivOfEq scalars_subgroupOf_om).trans QuotientGroup.quotientBot

noncomputable def modelEquiv {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    StatedProj (StatedOmega (StatedQuadOdd 3 K)) ≃* ↥Om := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  let σ : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  have hH : (StatedOmega (StatedQuadOdd 3 K)).map (glCongr (ι := Idx) σ).toMonoidHom = Om := by
    rw [om_eq_stated]
    exact map_statedOmega σ (statedQuadOdd_comp σ)
  exact (statedProjCongr (glCongr σ) hH (glCongr_statedScalars σ)).trans projEquivOm

end O7

theorem noOddCentralCoverFor_o7 : NoOddCentralCoverFor IsLieO7Index := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | B r q =>
      obtain ⟨rfl, hq3⟩ : r = 3 ∧ q.card = 3 := hi
      obtain ⟨hp3, -⟩ := primePower_eq_three hq3
      have hp2 : q.p ≠ 2 := by omega
      have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv hp2 le_rfl
        (G := (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group) (MulEquiv.refl _)
      obtain ⟨-, K, _, _, hK3, ⟨eK⟩⟩ := hmodel
      have hK : Nat.card K = 3 := by rw [hK3, ← PrimePower.card_def]; exact hq3
      let e' : S ≃* ↥O7.Om := e.trans (eK.trans (O7.modelEquiv hK))
      let φ' : Y →* ↥O7.Om := e'.toMonoidHom.comp φ
      have hφ' : Function.Surjective φ' := e'.surjective.comp hφ
      have hkerφ : φ'.ker = φ.ker := by
        ext x
        simp [φ', MonoidHom.mem_ker]
      have h4 := O7.four_le_localRank_of_cover φ' hφ' (hkerφ ▸ hcent) (hkerφ ▸ h3dvd)
      have := h4.trans (CFSG.RankThree.OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num))
      omega
    | A r q => exact hi.elim
    | twistedA r q => exact hi.elim
    | C r q => exact hi.elim
    | D r q => exact hi.elim
    | twistedD r q => exact hi.elim
    | E6 q => exact hi.elim
    | E7 q => exact hi.elim
    | E8 q => exact hi.elim
    | F4 q => exact hi.elim
    | G2 q => exact hi.elim
    | twistedE6 q => exact hi.elim
    | trialityD4 q => exact hi.elim
    | suzuki m => exact hi.elim
    | reeG2 m => exact hi.elim
    | reeF4 m => exact hi.elim
    | tits => exact hi.elim

end CFSG.RankThree.PartOne.N143
