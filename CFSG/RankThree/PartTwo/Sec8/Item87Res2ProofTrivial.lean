module

public import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofUnitary
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofCent
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.RankThree.PartTwo.KFacts.K71Sp4

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KF87INontriv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (m : ℕ), 1 ≤ m →
    IsGammaType (L ⧸ aschbacherSolvableCore 3 L) m →
    ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 → x ^ 3 = 1 →
    (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) →
    Sec8PairGTwo L x m →
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) L) ≠ ⊥

@[expose] def KF87INontrivRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (m : ℕ), 1 ≤ m →
    (IsGammaTypeRee (L ⧸ aschbacherSolvableCore 3 L) m ∨
      IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * m)) →
    ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 → x ^ 3 = 1 →
    (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) →
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) L) ≠ ⊥

theorem kF87INontriv_of (hG2 : KFG2TwoNonsolv) (hR : KF87INontrivRest) : KF87INontriv := by
  intro G _ _ L x m hm htype hU3 hx3 hk hg
  have hG2C : IsoGTwoEven (barCentralizer (Subgroup.zpowers x) L) m →
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) L) ≠ ⊥ := by
    intro hC h0
    apply kF87UnitaryJ_of hG2 _ m hm (Or.inl hC)
    rw [inSubgroup] at h0
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h0
  rcases htype with hRee | hD | ⟨q, hq2, hqe, hGq⟩ | hU | hS | hSp
  · exact hR G L x m hm (Or.inl hRee) hU3 hx3 hk
  · exact hG2C (hg (Or.inl hD))
  · exact hG2C (hg (Or.inr (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hGq)))
  · exact hR G L x m hm (Or.inr (Or.inl hU)) hU3 hx3 hk
  · exact hR G L x m hm (Or.inr (Or.inr hS)) hU3 hx3 hk
  ·
    have hout : Sec4.InducesOuterTheta x L := by
      rcases hk with h | h
      · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
      · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
    obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (by omega) hx3 hout hSp
    have hq := Item87Res2Proof.isQuasisimple_inSubgroup_perfectResidual_of_projSp hm ι
    have : Nontrivial (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) L)) :=
      LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this

theorem pair87TrivialG2_of (hN : KF87INontriv) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
      (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n → Sec8PairGTwo L a n →
      ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 → sec8I L a = ⊥ → sec8J X a = ⊥ →
        (thetaComponentsAt 3 a).Nonempty := by
  intro G _ _ A c L a b X n h hg2 hU hI _
  exfalso
  obtain ⟨-, -, hn, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hne := hN G L a n hn (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex) hU ha3
    h.inducesStdKind hg2
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) :=
    by simp only [sec8I, hU, ↓reduceIte]
  rw [hIdef] at hI
  apply hne
  rw [← KFacts.imageModTheta_perfectResidual_centralizer_eq h.a_mem_normalizer
    ⟨1, by rwa [pow_one]⟩, hI, imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem pair87Trivial_of (hN : KF87INontriv) : Pair87Trivial :=
  fun G _ _ A c L a b X n h => pair87TrivialG2_of hN G A c L a b X n h h.gTwo

end CFSG.RankThree.PartTwo.Sec8
