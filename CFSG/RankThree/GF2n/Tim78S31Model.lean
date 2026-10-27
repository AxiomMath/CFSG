module

public import CFSG.RankThree.GF2n.Tim78S31Count
public import CFSG.RankThree.GF2n.DecompSetupFive

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Data31

variable {U : Subgroup G} {g α x : G} (D : Data31 U g α x) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include D hCen hU

theorem linear : ∃ f : ℕ, 2 ≤ f ∧ (PartTwo.omegaOneSub U).relIndex U = 2 ^ f ∧
    ∃ _ : ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf
      (U ⊔ conjSubgroup α U)).Normal,
      Nonempty (↥(U ⊔ conjSubgroup α U) ⧸
        (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf
          (U ⊔ conjSubgroup α U) ≃* PSL(2, GaloisField 2 f)) := by
  have K := D.core
  have P := D.pair
  have Q := P.qdata hCen hU
  have hN := Q.normal_Q
  have QP := Q.quotPair
  obtain ⟨-, hmod⟩ := QP.models hCen hU
  have hrel : (PartTwo.omegaOneSub U).relIndex U =
      Nat.card ((U.subgroupOf (U ⊔ conjSubgroup α U)).map (QuotientGroup.mk'
        ((nrm U (conjSubgroup α U) ⊔ nrm (conjSubgroup α U) U).subgroupOf
          (U ⊔ conjSubgroup α U)))) := by
    rw [← P.nrm_eq hCen hU]
    exact Q.relIndex_eq_card_image
  have hce := D.card_eq hCen hU
  have hNq : (nrm U (conjSubgroup α U) ⊔ nrm (conjSubgroup α U) U).subgroupOf
      (U ⊔ conjSubgroup α U) = (PartTwo.omegaOneSub U ⊔
        PartTwo.omegaOneSub (conjSubgroup α U)).subgroupOf (U ⊔ conjSubgroup α U) := by
    rw [P.N_eq hCen hU]
  rcases hmod with ⟨f, hf, hT, ⟨e⟩⟩ | ⟨a, ha, hT, ⟨e⟩⟩ | ⟨m, hm, h3, hT, ⟨e⟩⟩
  · have hN' := P.normal hCen hU
    exact ⟨f, hf, by rw [hrel, hT], hN',
      ⟨(QuotientGroup.quotientMulEquivOfEq hNq).symm.trans e⟩⟩
  ·
    exfalso
    have h5 := Q.decompSetup.card_modEq_one_of_sz QP ha e
    rw [P.N_eq hCen hU, P.card_N hCen hU, K.card_omega_conj α, hce, hrel, hT] at h5
    have key : (2 ^ (2 * a + 1) * 2 ^ (2 * a + 1)) % 5 = 4 := by
      have h16 : 16 ^ a % 5 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have e : 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) = 4 * 16 ^ a := by
        rw [← pow_add, show 2 * a + 1 + (2 * a + 1) = 2 + 4 * a by ring, pow_add, pow_mul]
        norm_num
      rw [e]
      omega
    unfold Nat.ModEq at h5
    rw [key] at h5
    norm_num at h5
  ·
    exfalso
    have h4 := K.card4
    rw [hce, hrel, hT] at h4
    omega

end Data31

end CFSG.RankThree.GF2n.Tim78
