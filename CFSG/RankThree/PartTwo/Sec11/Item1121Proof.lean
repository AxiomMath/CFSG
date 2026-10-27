module

public import CFSG.RankThree.PartTwo.Sec11.Item1121ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1123Proof
import CFSG.RankThree.PartTwo.Sec11.Item1121ProofFusion

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


theorem isSylowOf_sec11P_of_normalizer {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf 3 (sec11P R g) ⊤ :=
  isSylowOf_top_of_subset_mul h.isPGroup_sec11P le_sup_left h.isSylowOf
    (subset_mul_normalizer_of_transitive hcdN hNd (Subgroup.subset_closure (by simp))
      h.zpowers_ne (h.htrans hcdN hNd))

theorem item1121N_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113)
    (h117 : Item117) (h1115 : Item1115) (h1120 : Item1120) (hK : KFact1121Lists) :
    Item1121N := by
  intro G _ _ A c L a R Y d x s r g hbig hcdN hNd K _
  refine ⟨fun e => ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hbig.toSec11Data
  set π : sec11P R g →* W33 := e.toMonoidHom.comp (QuotientGroup.mk' K) with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective K)
  by_cases hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}
  · exact Item1121Proof.false_of_closure_eq h45 h1115 h1120 hbig π hπ hrs
  have hra := Item1121Proof.r_mul_a_ne h45 h113 h117 h1115 h1120 hbig π hπ hrs
  have hS := isSylowOf_sec11P_of_normalizer h hcdN hNd
  obtain ⟨hUn, habel, hrU, -, -⟩ := Item1121Proof.preU_facts h45 h1115 h1120 hbig π hπ hrs
  have hP := coe_sylowOfIsSylowOf hS
  refine Sec8.rank3II_transfer_false h.toTheoremFourHyp (sylowOfIsSylowOf hS) (r := r) ?_ ?_ ?_
    hrU ?_
  · rw [hP]
    exact hUn
  · rw [hP]
    exact habel
  · rw [hP]
    exact (Item1121Proof.mem_P_facts h).1
  · rw [hP]
    exact Item1121Proof.fusion_mem_preU h45 h48 h113 h117 h1115 h1120 hK hbig hcdN hNd π hπ hrs
      hra

theorem item1123N_of_steps (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113)
    (h117 : Item117) (h1115 : Item1115) (h1120 : Item1120) (hK : KFact1121Lists) :
    Item1123N :=
  item1123N_of h45 h113 h1120 (item1121N_of h45 h48 h113 h117 h1115 h1120 hK)

end CFSG.RankThree.PartTwo.Sec11
