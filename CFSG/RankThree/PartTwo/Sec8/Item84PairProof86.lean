module

public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof84
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof86
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof84Items
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint.Chevalley (adjointGroup)


@[expose] def Pair84GammaNL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → (∀ m : ℕ, ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) →
    Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n))) →
    ∀ (b : G) (X : Subgroup G), b ∈ Subgroup.closure ({c, d} : Set G) → PairRel A c L b X →
      (∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) → IsGammaIndex A X c n

@[expose] def Pair84GammaRee : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n →
    IsoSUThree (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G)))) (2 ^ (3 * n)) →
    ∀ (b : G) (X : Subgroup G), b ∈ Subgroup.closure ({c, d} : Set G) → PairRel A c L b X →
      (∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) → (gammaSet A X).Nonempty

@[expose] def Pair86NonUnitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * n) →
      ∃ b ∈ Subgroup.closure ({c, d} : Set G), b ∉ Subgroup.zpowers c ∧ ∃ X : Subgroup G,
        PairRel A c L b X ∧ ∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m

theorem pair84GammaNonempty_of (hUL : Pair84GammaUL) (hNL : Pair84GammaNL)
    (hR : Pair84GammaRee) : Pair84GammaNonempty := by
  intro G _ _ A c L a d n h b X hb hrel hXU
  have hn1 : 1 ≤ n := h.data83.odd.pos
  rcases h.data83.cases with ⟨hDG, hK, -⟩ | ⟨-, -, hKSU⟩ | ⟨hS, -, -⟩ | ⟨hP, -, -⟩ | ⟨hSp, -, hK⟩
  · have hLU : ∀ m : ℕ, ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m :=
      not_isUnitaryTwo_of_isList86 hn1 (hDG.elim Or.inl fun hG => Or.inr (Or.inl hG))
    exact ⟨c, n, hNL G A c L a d n h hLU hK b X hb hrel hXU⟩
  · exact hR G A c L a d n h hKSU b X hb hrel hXU
  · exact ⟨c, n, hUL G A c L a d n h b X hb hrel ⟨3 * n, Or.inr hS⟩ hXU⟩
  · exact ⟨c, n, hUL G A c L a d n h b X hb hrel ⟨3 * n, Or.inl hP⟩ hXU⟩
  · have hLU : ∀ m : ℕ, ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m :=
      not_isUnitaryTwo_of_isList86 hn1 (Or.inr (Or.inr hSp))
    exact ⟨c, n, hNL G A c L a d n h hLU hK b X hb hrel hXU⟩


theorem pair86One_of (hT : Pair86NonUnitary) (hUL : Pair84GammaUL) : Pair86One := by
  intro G _ _ A c L a d n h hLU3
  have hd := h.data83
  have hn1 : 1 ≤ n := hd.odd.pos
  have hK : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n))) := by
    rcases hd.cases with ⟨hDG, -, -⟩ | ⟨hR, -, -⟩ | ⟨-, -, hK⟩ | ⟨-, -, hK⟩ | ⟨hSp, -, -⟩
    · exact (not_isUnitaryTwo_of_isList86 hn1 (hDG.elim Or.inl fun hG => Or.inr (Or.inl hG))
        (3 * n) hLU3).elim
    · obtain ⟨k, hk, hkn, he⟩ := reeF4_of_isoReeF4 (by omega) hR
      exact ((sigF4_of_reeF4 hn1 ⟨k, hk, hkn, he⟩).not_isUnitaryTwo hn1 (3 * n) hLU3).elim
    · exact hK
    · exact hK
    · exact (not_isUnitaryTwo_of_isList86 hn1 (Or.inr (Or.inr hSp)) (3 * n) hLU3).elim
  obtain ⟨b, hb, hbc, X, hrel, hXU⟩ := hT G A c L a d n h hLU3
  have hcΓ := hUL G A c L a d n h b X hb hrel ⟨3 * n, hLU3⟩ hXU
  refine ⟨b, hb, hbc, X, hrel, ?_⟩
  obtain ⟨-, -, -, hcases⟩ := Item87Proof.isGammaIndex_cases hcΓ
  rcases hcases with ⟨-, hSU⟩ | ⟨htype, -⟩
  ·
    exfalso
    obtain ⟨hbΓ, -, hLb⟩ := partner_data h hb hrel
    have hX : X ∈ thetaComponentsAt 3 b := hrel.2.2.1
    have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
      (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
    obtain ⟨hKe, -, hKe1⟩ := Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
    obtain ⟨hKb, -, -⟩ := Item87Proof.residual_of_isGammaIndex hX hcΓ
    set Ke := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hKedef
    set Kb := inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) with hKbdef
    have hKeL : Ke ≤ L := (Item87Proof.residual_le _).trans inf_le_left
    have hKeKb : Ke ≤ Kb :=
      KFacts.le_inSubgroup_perfectResidual (Item87Proof.isPerfect_residual _)
        (le_inf hrel.2.2.2.1 (hKeL.trans hLc))
    have hKb' : Kb ∈ thetaComponentsIn
        (Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b}) := by
      rwa [inf_comm] at hKb
    have heq : Ke = Kb := Sec6.eq_of_mem_thetaComponentsIn_of_le hKe hKb'
      (Item87Proof.isPerfect_residual _) hKe1 le_rfl hKeKb
    have hKbL : Kb ≤ L := heq ▸ hKeL
    have hKbX : Kb ≤ X := (Item87Proof.residual_le _).trans inf_le_left
    have hL2 : Nonempty (imageModTheta L Kb ≃* projSL 2 (GaloisField 2 (3 * n))) := by
      rw [← heq, hKedef, hLb]
      exact hK
    exact false_of_isoSUThree_le_projSL (L := X) (X := L) (K := Kb) (M := Kb) hKbX le_rfl hKbL
      hd.odd hSU hL2
  · rcases htype with hD | ⟨q, hp, hq, hG⟩ | hU | hS | hSp
    · exact Or.inl hD
    · refine Or.inr (Or.inl ?_)
      exact Item8KFactsProof.isoGTwoEven_of_isoGTwo hp hq hG
    · exact (hXU (3 * n) (Or.inl hU)).elim
    · exact (hXU (3 * n) (Or.inr hS)).elim
    · exact Or.inr (Or.inr hSp)

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
