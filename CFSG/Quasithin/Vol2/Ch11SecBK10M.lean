module

public import CFSG.Quasithin.Vol2.Ch11SecBK10J
public import CFSG.Quasithin.Vol2.Ch11SecBK10K
public import CFSG.Quasithin.Vol2.Ch11SecBK10L
public import CFSG.Quasithin.Vol2.Ch11SecBK10P
public import CFSG.Quasithin.Vol2.Ch11SecBK10S
public import CFSG.Quasithin.Vol2.Ch11SecBK10U
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Quasithin.EmptyFaithful.R3c3Spor
public import CFSG.Quasithin.EmptyFaithful.R3c3Lie

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
open CFSG.GorensteinWalter

@[expose] noncomputable def psl2EquivOfModel {X K : Type} [Group X] [Field K]
    (e : X ≃* StatedProj (StatedSL 2 K)) : X ≃* PSL2 K :=
  e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm

@[expose] noncomputable def projSL3EquivOfModel {X K : Type} [Group X] [Field K]
    (e : X ≃* StatedProj (StatedSL 3 K)) : X ≃* projectiveSL 3 K :=
  (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])

theorem torusRigid_or_rank
    (X : Type) [Group X] [Finite X] (hX : Milestones.SQTKSimpleList X) :
    TorusRigid X ∨ 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rcases hX with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, h2⟩ | (⟨f, h3⟩ | h3) | ⟨n, hn, h4⟩ |
    ⟨s, hs, ⟨e⟩⟩
  ·
    rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | hn6
    · left
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
        (ZMod 5) (Or.inr (Nat.card_zmod 5))
      have hT := L2.torusRigid_psl2_small (K := ZMod 5) (p := 5) (f := 1) (by norm_num)
        (by norm_num) (by rw [Nat.card_zmod, pow_one])
      exact hT.of_mulEquiv (psl2EquivOfModel (e.trans e5.symm)).symm
    · exact Or.inr (R3c3.two_le_pRank_three_alt hn6 e)
  ·
    rcases h2 with ⟨f, hf, hm⟩ | hm | hm
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
      left
      exact (L2.torusRigid_psl2_small hp (by omega) hK).of_mulEquiv (psl2EquivOfModel e).symm
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
      left
      exact (L3.torusRigid_prime hp hp2 (by rw [hK, pow_one])).of_mulEquiv
        (projSL3EquivOfModel e).symm
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
      left
      have hU : UnitaryFieldData p 1 K := ⟨hp, le_rfl, by rw [hK, pow_one, mul_one, sq]⟩
      exact (U3.torusRigid_prime hU hp2).of_mulEquiv
        (e.trans (unitaryPSUEquiv hU (by omega)).symm).symm
  ·
    rcases h3 with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
      ⟨hfo, hf3, hm⟩ | ⟨hfo, hf3, hm⟩
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
      have := charP_two_of_card hK
      exact Or.inl (L2.torusRigid_psl2.of_mulEquiv (psl2EquivOfModel e).symm)
    · rcases Nat.even_or_odd f with hfe | hfo
      · exact Or.inr (R3c3.two_le_pRank_three_isPSL_three_two_even hfe hm)
      · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
        have := charP_two_of_card hK
        exact Or.inl ((L3.torusRigid_L3 hfo hK).of_mulEquiv (projSL3EquivOfModel e).symm)
    · rcases Nat.even_or_odd f with hfe | hfo
      · obtain ⟨⟨hℓ, hm1, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
        have hU : UnitaryFieldData 2 f K := ⟨hℓ, hm1, by rw [hK, ← pow_mul, mul_comm]⟩
        exact Or.inl ((U3.torusRigid_even hU hfe).of_mulEquiv
          (e.trans (unitaryPSUEquiv hU (by omega)).symm).symm)
      · exact Or.inr (R3c3.two_le_pRank_three_isPSU_two_odd hfo hm)
    · exact Or.inr (R3c3.two_le_pRank_three_isPSp_two hm)
    · exact Or.inr (R3c3.two_le_pRank_three_isG2 hm)
    · exact Or.inr (R3c3.two_le_pRank_three_is3D4 hm)
    · exact Or.inr (R3c3.two_le_pRank_three_is2F4 hm)
    · obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := hm
      exact Or.inl ((Sz.torusRigid_sz ha (by rw [hK, hfa])).of_mulEquiv e.symm)
  · exact Or.inr (R3c3.two_le_pRank_three_isTits h3)
  · exact Or.inr (R3c3.two_le_pRank_three_isPSL_two_one hn h4)
  ·
    by_cases hJ1 : s = .J1
    · subst hJ1
      left
      have : Finite NativeSporadic.J1 := CFSG.Sporadic.J1.fam_j1_simplicity.1
      have : Finite (NativeSporadic.Carrier .J1) := CFSG.Sporadic.J1.fam_j1_simplicity.1
      obtain ⟨-, hinn, -⟩ := CFSG.Sporadic.Schreier.at_j1_schreier
      refine (torusRigid_of_forall_eq_one fun β hβ => ?_).of_mulEquiv e.symm
      obtain ⟨g, hg⟩ := hinn β
      exact eq_one_of_mem_inner hβ ⟨g, hg.symm⟩
    · right
      have hs' : CFSG.QuasithinUnique.Ch1.IsLemma115SporadicName s := by
        rcases hs with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
          first | exact absurd rfl hJ1 | simp [CFSG.QuasithinUnique.Ch1.IsLemma115SporadicName]
      exact R3c3.two_le_pRank_three_of_lemma115SporadicName hs' e

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD
