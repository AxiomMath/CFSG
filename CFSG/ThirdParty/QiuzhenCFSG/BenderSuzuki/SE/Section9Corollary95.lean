module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Lemma92
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Lemma94

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9, Corollary 9.5

Lemma 9.2 eliminates the fusion-control alternative of Lemma 9.4 for every
prime occurring in the abelianization of the minimal-supplement intersection.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

public theorem corollary_9_5
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X} {p : ℕ} [Fact p.Prime]
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hp : p ∣ Nat.card
      (((W ⊓ (M ⊓ rightConjugate M t)).subgroupOf W) ⧸
        derivedSubgroup
          ((W ⊓ (M ⊓ rightConjugate M t)).subgroupOf W)))
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (h43 : II1Lemma43bCyclic (X := X)) :
    Lemma94AlternativeB (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t p := by
  let E : Subgroup W :=
    (W ⊓ (M ⊓ rightConjugate M t)).subgroupOf W
  have hpEsub : p ∣ Nat.card E :=
    hp.trans (Subgroup.card_quotient_dvd_card
      (s := derivedSubgroup E))
  have hEcard : Nat.card E = Nat.card
      (W ⊓ (M ⊓ rightConjugate M t) : Subgroup X) := by
    simpa [E] using natCard_subgroupOf_eq
      (W ⊓ (M ⊓ rightConjugate M t)) W inf_le_left
  have hpE : p ∣ Nat.card
      (W ⊓ (M ⊓ rightConjugate M t) : Subgroup X) := by
    rwa [hEcard] at hpEsub
  rcases lemma_9_4 hM ht htM d83 h84 hW.prop hpE hIne h43 with
    hA | hB
  · rcases hA with ⟨Q, hQE, hfusion⟩
    exact False.elim
      (lemma_9_2_of_controlsFusionIn hW Q hQE hfusion hp)
  · exact hB

end CFSG.BenderSuzuki
