module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofField
import CFSG.RankThree.PartTwo.Sec4.Item424ProofBasic
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Ree

@[expose] def K424FieldCentLinear : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (c : G) (n : ℕ) (F : Type) [Field F]
    [Finite F], 3 ≤ n →
    (KFacts.InducesKindPSL n F L c .field ∨ KFacts.InducesKindSL n F L c .field) → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)) →
    Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
      IsFieldCent424 (L ⧸ aschbacherSolvableCore 3 L)

@[expose] def K424FieldCentUnitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (c : G) {p f : ℕ} {F : Type} [Field F]
    (hF : UnitaryFieldData p f F) (hq : 2 < p ^ f),
    (KFacts.InducesKindPSU3 hF L c .field ∨ KFacts.InducesKindSU3 hF L hq c .field) →
    c ^ 3 = 1 → K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)) →
    Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
      IsFieldCent424 (L ⧸ aschbacherSolvableCore 3 L)

@[expose] def K424FieldCentSymplectic :
    Prop :=
  (∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (c : G) (r : ℕ) (F : Type) [Field F]
    [Finite F], (3 ≤ r ∨ (r = 2 ∧ ringChar F ≠ 2)) → KFacts.InducesKindPSp r F L c .field →
    c ^ 3 = 1 → K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)) →
      ¬ Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K)) ∧
  (∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (c : G) (F : Type) [Field F]
    [Finite F] [CharP F 2], KFacts.InducesKindPSp4Even F L c .field →
    c ^ 3 = 1 → K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)) →
      ¬ Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K))

@[expose] def K424FieldCentLargeRee :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (c : G) (a : ℕ) (F : Type) [Field F]
    [Finite F] [CharP F ReeTag.F4.prime], 1 ≤ a → Nat.card F = 2 ^ (2 * a + 1) →
    KFacts.InducesKindLargeRee a F L c .field → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)) →
      ¬ Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K)

namespace Item424Res2

variable {G : Type} [Group G] [Finite G]

theorem hasType424_fixSub_of_mem {L K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K)) :
    Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub (Item426.thetaAut L hcN)) := by
  have hKL : K ≤ L := (mem_thetaComponentsIn_iff.mp hK).1.trans inf_le_left
  have hJα := Item426.map_mem_thetaComponentsIn_fixSub L hcN hc3 hK
  obtain ⟨eK⟩ := Item426.nonempty_quotTheta_map_equiv L hKL
  exact Sec11.KS11Lie2Proof.hasType424_of_mem hJα (Sec11.isType424_of_mulEquiv eK.symm hT)

theorem three_dvd_card_quot_of_config {L K : Subgroup G} {c : G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K)) :
    3 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L) := by
  have hKL : K ≤ L := (mem_thetaComponentsIn_iff.mp hK).1.trans inf_le_left
  obtain ⟨eK⟩ := Item426.nonempty_quotTheta_map_equiv L hKL
  have hJT := Sec11.isType424_of_mulEquiv eK.symm hT
  exact ((Item424Proof.three_dvd_card_of_isType424 hJT).trans
    (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card _)

end Item424Res2

open Item424Res2

theorem k424FieldCentNotL2_of
    (hLin : K424FieldCentLinear) (hU : K424FieldCentUnitary) (hSp : K424FieldCentSymplectic)
    (hR : K424FieldCentLargeRee) : K424FieldCentNotL2 := by
  intro G _ _ L K c hf hc3 hK hT hL2
  have hout := hf.inducesOuterTheta L (by intro h; cases h)
  cases hf with
  | psl2 F h =>
    obtain ⟨e, -⟩ := h
    exact (hL2 ⟨F, inferInstance, inferInstance, ⟨e⟩⟩).elim
  | psl n F hn h => exact hLin G L K c n F hn (Or.inl h) hc3 hK hT
  | sl n F hn h => exact hLin G L K c n F hn (Or.inr h) hc3 hK hT
  | psu3 hF hq h => exact hU G L K c hF hq (Or.inl h) hc3 hK hT
  | su3 hF hq h => exact hU G L K c hF hq (Or.inr h) hc3 hK hT
  | psp r F hr h => exact (hSp.1 G L K c r F hr h hc3 hK hT).elim
  | psp4even F h => exact (hSp.2 G L K c F h hc3 hK hT).elim
  | g2 F hF3 hF4 h =>
    exfalso
    obtain ⟨e, -⟩ := h
    obtain ⟨hcN, hα⟩ := hout
    have hα3 := Item426.thetaAut_pow_eq_one L hcN hc3
    have hHas := (hasType424_fixSub_of_mem hcN hc3 hK hT).of_mulEquiv
      (Sec11.KS11Lie2Proof.fixSubCongr e (Item426.thetaAut L hcN))
    have hβ3 : MulAut.congr e (Item426.thetaAut L hcN) ^ 3 = 1 := by
      rw [← map_pow, hα3, map_one]
    have hβout : ¬ KFacts.IsInnerAut (MulAut.congr e (Item426.thetaAut L hcN)) := by
      rwa [KFacts.isInnerAut_congr]
    by_cases h8 : Nat.card F = 8
    · exact Sec11.KS11Lie3Proof.not_hasType424_outer_g2_eight h8 hβ3 hβout hHas
    · exact Sec11.KS11Lie2Proof.not_hasType424_outer_g2 hF3 hF4 h8 hβ3 hβout hHas
  | sz a F ha hF h =>
    exfalso
    obtain ⟨e, -⟩ := h
    have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
    have h3 := three_dvd_card_quot_of_config hK hT
    rw [Nat.card_congr e.toEquiv] at h3
    exact KFacts.not_three_dvd_card_suzukiGroup hF h3
  | triality f hf F hF σ hσ h =>
    exact (Sec11.not_inducesKindTriality_field_of_pow_three hf hF hσ L hc3 h).elim
  | largeRee a ha F hF h => exact (hR G L K c a F ha hF h hc3 hK).elim hT

end CFSG.RankThree.PartTwo.Sec4
