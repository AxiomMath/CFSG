module

public import CFSG.RankThree.PartOne.N143.SectionGroup
public import CFSG.RankThree.PartOne.N143.Statements
import CFSG.RankThree.PartOne.N143.CaseB1Theta
import CFSG.RankThree.PartOne.S10.EmbeddingTransport

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

@[expose] def ThetaQuotientBookkeeping : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsKGroup L → CFSG.Assembly.evenRank L ≤ 3 →
    Group.IsPerfect L → ∀ p : ℕ, p.Prime → 7 ≤ p →
      CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L) →
        Subgroup.center (L ⧸ aschbacherSolvableCore p L) = ⊥ ∧
          CFSG.Assembly.evenRank (L ⧸ aschbacherSolvableCore p L) ≤ 3

@[expose] def Item613Simple : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    CFSG.IsKGroup X → CFSG.Assembly.evenRank X ≤ 3 →
    ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ E : Subgroup X, CFSG.IsElementaryAbelian p E →
      p ^ 2 ≤ Nat.card E →
      (∃ S : Subgroup X, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set X) ∧ ⁅S, E⁆ = S) →
      CFSG.Blueprint.EvenLieType X

@[expose] def KF64WSimple : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    CFSG.IsKGroup X → CFSG.Assembly.evenRank X ≤ 3 → CFSG.Blueprint.EvenLieType X →
    ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ E : Subgroup X, CFSG.IsElementaryAbelian p E →
      Nat.card E = p ^ 3 → (Nat.card (torusWeyl E)).factorization 3 ≤ 1

theorem evenLieType_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.Blueprint.EvenLieType X) : CFSG.Blueprint.EvenLieType Y := by
  obtain ⟨t, n, f, hadm, hm⟩ := h
  exact ⟨t, n, f, hadm, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩

theorem not_dvd_card_ker_theta {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.card (QuotientGroup.mk' (aschbacherSolvableCore p X)).ker := by
  rw [QuotientGroup.ker_mk']
  exact (solvable_prime_complement_core_characterization (H := X) hp).2.2.1

theorem simple_of_quasisimple_center_bot {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (hZ : Subgroup.center Q = ⊥) :
    Nonempty (Q ⧸ Subgroup.center Q ≃* Q) ∧ IsSimpleGroup Q ∧ ∃ a b : Q, a * b ≠ b * a := by
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2.1
  refine ⟨⟨e⟩, e.symm.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hq.2.2
  exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩

theorem item613_of_simple (hB : ThetaQuotientBookkeeping) (hS : Item613Simple) : Item613 := by
  intro _hSchreier H _ _ hK he p hp hp7 L hL E hE hcard hEL hex
  obtain ⟨S, hS1, hS2, hSL, hSθ, hEN, hSE⟩ := hex
  have hLK : CFSG.IsKGroup ↥L := isKGroup_subgroup hK L
  have hLe : CFSG.Assembly.evenRank ↥L ≤ 3 :=
    (CFSG.RankThree.PartOne.Sec9A.evenRank_subgroup_le L).trans he
  have hq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore p ↥L) := hL.2.2
  obtain ⟨hZ, hQe⟩ := hB ↥L hLK hLe hL.1 p hp hp7 hq
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
  have h := hS _ hsimple hnonab hQK hQe p hp hp7 _ hEa hEcard ⟨_, hSbot, hS2q, hNq, hCq⟩
  exact evenLieType_of_mulEquiv eZ.symm h

theorem kf64w_of_simple (hB : ThetaQuotientBookkeeping) (hS : KF64WSimple) : KF64W := by
  intro H _ _ hK he hperf p hp hp7 hq hEven E hE hcard _hex
  obtain ⟨hZ, hQe⟩ := hB H hK he hperf p hp hp7 hq
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
  have h1 := hS _ hsimple hnonab hQK hQe (evenLieType_of_mulEquiv eZ hEven) p hp hp7 _ hEa hEc
  exact (torusWeyl_factorization_le _ hdis 3).trans h1

end CFSG.RankThree.PartOne.N143
