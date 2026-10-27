module

public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionListBound
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143.Weyl613Small
public import CFSG.RankThree.PartOne.N143.Item613IdxDefs
import CFSG.RankThree.PartOne.N143.CaseB1Theta
import CFSG.RankThree.PartOne.S10.EmbeddingTransport

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

@[expose] def ListEvenQ (X : Type) [Group X] : Prop := ListEvenItem X

@[expose] def Item613ListIdx : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → Census3.TheoremThreeList X → Item613AtIdx X

@[expose] def KF64WSimpleList : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    CFSG.IsKGroup X → ListEvenItem X →
    ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ E : Subgroup X, CFSG.IsElementaryAbelian p E →
      Nat.card E = p ^ 3 → (Nat.card (torusWeyl E)).factorization 3 ≤ 1

theorem kf64wSimpleList_of_small (hS : KF64WSimpleSmall)
    (hB : ∀ (X : Type) [Group X], ListEvenItem X → EvenLieTypeSmall X) : KF64WSimpleList :=
  fun X _ _ hs hnab hK hX p hp hp7 E hE hcard => hS X hs hnab hK (hB X hX) p hp hp7 E hE hcard

theorem thetaQuotient_center_bot_and_list (h : SectionListBound) {L : Type} [Group L] [Finite L]
    (hK : CFSG.IsKGroup L) (he : CFSG.Assembly.evenRank L ≤ 3) (p : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L)) :
    Subgroup.center (L ⧸ aschbacherSolvableCore p L) = ⊥ ∧
      Census3.TheoremThreeList (L ⧸ aschbacherSolvableCore p L) := by
  obtain ⟨hlist, hcen⟩ := h L hK he ⊤ _ hq
    ((QuotientGroup.mk' (aschbacherSolvableCore p L)).comp
      (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp
      (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).surjective)
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore p L) = ⊥ := by
    by_contra hne
    have hc1 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore p L)) ≠ 1 := fun h =>
      hne (Subgroup.card_eq_one.1 h)
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hc1
    by_cases hrp : r = p
    · subst hrp
      exact hcen r hr hp7 hrdvd
    · exact not_dvd_card_center_theta_quotient hp hr hrp hrdvd
  exact ⟨hZ, Census3.TheoremThreeList.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hlist⟩

theorem item613With_listEven (hSLB : SectionListBound) (hI : Item613ListIdx) :
    Item613With ListEvenQ := by
  intro _hSchreier H _ _ hK he p hp hp7 L hL E hE hcard hEL hex
  obtain ⟨S, hS1, hS2, hSL, hSθ, hEN, hSE⟩ := hex
  have hLK : CFSG.IsKGroup ↥L := isKGroup_subgroup hK L
  have hLe : CFSG.Assembly.evenRank ↥L ≤ 3 :=
    (CFSG.RankThree.PartOne.Sec9A.evenRank_subgroup_le L).trans he
  have hq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore p ↥L) := hL.2.2
  obtain ⟨hZ, hlist⟩ := thetaQuotient_center_bot_and_list hSLB hLK hLe p hp hp7 hq
  obtain ⟨⟨eZ⟩, hsimple, hnonab⟩ := simple_of_quasisimple_center_bot hq hZ
  have hQK : CFSG.IsKGroup (↥L ⧸ aschbacherSolvableCore p ↥L) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hLK _
  have : Fact p.Prime := ⟨hp⟩
  have hEL' : IsElementaryAbelian p (E.subgroupOf L) := by
    have := hE
    exact IsElementaryAbelian.subgroupOf hEL
  have hcardE : Nat.card (E.subgroupOf L) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  obtain ⟨hEa, hEc, hS2q, hSbot, hNq, hCq⟩ := section_data
    (QuotientGroup.mk' (aschbacherSolvableCore p ↥L)) hp (not_dvd_card_ker_theta hp)
    hEL' (isPGroup_subgroupOf hSL hS2) (normalizer_subgroupOf_of_le hEN)
    ((commutator_subgroupOf hSL hEL).trans (by rw [hSE]))
    (by rw [QuotientGroup.ker_mk']; exact hSθ)
  have hEcard : p ^ 2 ≤ Nat.card ((E.subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore p ↥L))) := by
    rw [hEc, hcardE]
    exact hcard
  have h := hI _ hsimple hlist p hp hp7 _ hEa hEcard ⟨_, hSbot, hS2q, hNq, hCq⟩
  exact ListEvenItem.of_mulEquiv eZ.symm h

theorem kf64wWith_listEven (hSLB : SectionListBound) (hS : KF64WSimpleList) :
    KF64WWith ListEvenQ := by
  intro H _ _ hK he hperf p hp hp7 hq hEven E hE hcard _hex
  obtain ⟨hZ, -⟩ := thetaQuotient_center_bot_and_list hSLB hK he p hp hp7 hq
  obtain ⟨⟨eZ⟩, hsimple, hnonab⟩ := simple_of_quasisimple_center_bot hq hZ
  have hQK : CFSG.IsKGroup (H ⧸ aschbacherSolvableCore p H) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hK _
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := by
    have := hE
    exact IsElementaryAbelian.isPGroup p E
  have hdis := disjoint_ker_of_isPGroup (QuotientGroup.mk' (aschbacherSolvableCore p H)) hp hEp
    (not_dvd_card_ker_theta hp)
  have hEa : IsElementaryAbelian p (E.map (QuotientGroup.mk' (aschbacherSolvableCore p H))) := by
    have := hE
    exact IsElementaryAbelian.map _
  have hEc : Nat.card (E.map (QuotientGroup.mk' (aschbacherSolvableCore p H))) = p ^ 3 := by
    rw [card_map_of_disjoint_ker _ hdis, hcard]
  have h1 := hS _ hsimple hnonab hQK (ListEvenItem.of_mulEquiv eZ hEven) p hp hp7 _ hEa hEc
  exact (torusWeyl_factorization_le _ hdis 3).trans h1

end CFSG.RankThree.PartOne.N143
