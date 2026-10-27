module

public import CFSG.RankThree.PartOne.K159.InnLayerFive
public import CFSG.RankThree.PartOne.K159.ThetaChain
public import CFSG.RankThree.PartOne.S13K.KFLiftRows

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def KFCompGenFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ e ∈ E, e ≠ 1 → ∀ Q : Subgroup G,
      Q ≤ lieGenerated p E ⊓ Subgroup.centralizer ({e} : Set G) →
      IsComponent (Q.subgroupOf (lieGenerated p E ⊓ Subgroup.centralizer ({e} : Set G))) →
      Q ≤ Subgroup.closure {x : G | ∃ t ∈ reflectionSet p E, ∃ K : Subgroup G, IsKt p E t K ∧
        K ≤ Subgroup.centralizer ({e} : Set G) ∧ x ∈ K}

theorem kfCompLayerFive_of_gen (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hAt : KFU5At) (hGen : KFCompGenFive) :
    KFCompLayerFive := by
  intro G _ _ p A c L E h15 hF hout e he he1 Q hQH hQc
  refine (hGen G p A c L E h15 hF hout e he he1 Q hQH hQc).trans
    ((Subgroup.closure_le _).2 ?_)
  rintro x ⟨t, ht, K, hK, hKC, hxK⟩
  obtain ⟨f, hf, hpf, ⟨e₀⟩, -⟩ := id hout
  have hAtt := hAt G p A c L E f h15 hF hout hf hpf ⟨e₀⟩ t ht
  have hq : CFSG.IsQuasisimple ↥(kZero p E t) := S13K.isQuasisimple_of_model_psl_two hAtt.2.1
  have hKeq : K = kZero p E t := hK.2 hAtt.1
  have hfix : e ∈ autFixedInG E t := by
    rw [← hAtt.2.2.1]
    refine ⟨he, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    rw [← hKeq] at hk
    exact Subgroup.mem_centralizer_singleton_iff.1 (hKC hk)
  exact isKt_le_thetaLayer hS h82 h15.h12 hK hq hfix he1 hxK

end CFSG.RankThree.PartOne.K159
