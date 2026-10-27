module

public import CFSG.RankThree.PartTwo.Sec8.Item87Proof
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofLink
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)

@[expose] def KF87UnitaryJ : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (n : ℕ), 1 ≤ n →
    (IsoGTwoEven H n ∨ Nonempty (H ≃* projSp 2 (GaloisField 2 n))) → perfectResidual H ≠ ⊥

@[expose] def KFG2TwoNonsolv : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    perfectResidual (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) ≠ ⊥

namespace Item87Res2Proof

theorem le_perfectResidual_of_isPerfect {H : Type} [Group H] {P : Subgroup H}
    (hP : Group.IsPerfect P) : P ≤ perfectResidual H := by
  refine le_iInf fun n => ?_
  induction n with
  | zero => rw [derivedSeries_zero]; exact le_top
  | succ n ih =>
    rw [derivedSeries_succ, ← commutator_self_eq_of_isPerfect hP]
    exact Subgroup.commutator_mono ih ih

theorem perfectResidual_ne_bot_of_isPerfect {H : Type*} [Group H] [Nontrivial H]
    (hH : Group.IsPerfect H) : perfectResidual H ≠ ⊥ := by
  rw [KFacts.perfectResidual_eq_top_of_isPerfect hH]
  exact top_ne_bot

end Item87Res2Proof

theorem kF87UnitaryJ_of
    (hG2 : KFG2TwoNonsolv) :
    KF87UnitaryJ := by
  intro H _ _ n hn hH
  rcases hH with ⟨K, _, _, hK, ⟨e⟩⟩ | he
  ·
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      intro h0
      apply hG2 K (by rw [hK, pow_one])
      rw [← KFacts.perfectResidual_map_mulEquiv e, h0, Subgroup.map_bot]
    · have hK3 : 3 ≤ Nat.card K := by
        rw [hK]
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      have hp := CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card (K := K) hK3
      have := CFSG.LieType.Steinberg.Adjoint.nontrivial_g2 (K := K)
      have hpH : Group.IsPerfect H := hp.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      have : Nontrivial H := e.toEquiv.nontrivial
      exact Item87Res2Proof.perfectResidual_ne_bot_of_isPerfect hpH
  ·
    obtain ⟨e⟩ := he
    have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    set ψ : H ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 n)) :=
      e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm with hψ
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      have hF2 : Nat.card (GaloisField 2 1) = 2 := by rw [hF, pow_one]
      obtain ⟨hq, -⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour
        (ψ.trans (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hF2))
      intro h0
      have hle : commutator H ≤ perfectResidual H :=
        Item87Res2Proof.le_perfectResidual_of_isPerfect hq.1
      rw [h0, le_bot_iff] at hle
      have : Nontrivial (commutator H) := LocalCores.isQuasisimple_nontrivial hq
      exact (Subgroup.nontrivial_iff_ne_bot _).mp this hle
    · have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      have hs := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
        (GaloisField 2 n) 2 (by norm_num) (Or.inl (Or.inr h4))
      have h4' : ∃ s : Finset (GaloisField 2 n), s.card = 4 := by
        have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
        obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
          Finset (GaloisField 2 n))) (n := 4) (by
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
            exact h4)
        exact ⟨s, hs⟩
      have hp := CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2
        (GaloisField 2 n) (Or.inl h4')
      have hpH : Group.IsPerfect H := hp.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
      have : Nontrivial H := ψ.toEquiv.nontrivial
      exact Item87Res2Proof.perfectResidual_ne_bot_of_isPerfect hpH


@[expose] def Pair87UnitaryY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 →
      ∀ Y ∈ thetaComponentsAt 3 a, sec8J X a ≤ Y → sec8I L a ≤ Y

theorem pair87Unitary_of (h45 : Sec4.Item4_5) (hJ : KF87UnitaryJ) (hY : Pair87UnitaryY) :
    Pair87Unitary := by
  intro G _ _ A c L a b X n h hU
  refine ⟨?_, hY G A c L a b X n h hU⟩
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  obtain ⟨hbA, hb1, hn, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hAel := h.mem_partTwoF.1
  have ha3 : a ^ 3 = 1 := hAel.2 a h.a_mem
  have haX : a ∈ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45
      (hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hb1))
      (Item87Proof.le_centralizer_of_isElemAbelian hAel hbA) hAel
      ⟨4, by norm_num, by rw [h.card_eq]; norm_num⟩ X h.pairRel.2.2.1 h.a_mem
  set C := barCentralizer (Subgroup.zpowers a) X with hC
  have hCtype := h.centralizer_of_unitary ⟨3, hU⟩
  have hres : perfectResidual C ≠ ⊥ := hJ C n hn hCtype
  intro hJ0
  apply hres
  have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq haX ⟨1, by rwa [pow_one]⟩
  have hJdef : sec8J X a = inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({a} : Set G)) :=
    rfl
  rw [← hJdef, hJ0, imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot] at himg
  rw [inSubgroup] at himg
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp himg.symm

end CFSG.RankThree.PartTwo.Sec8
