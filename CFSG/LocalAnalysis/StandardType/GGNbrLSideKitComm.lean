module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.StandardType.GGNbrLSideKit

private theorem commutator_equiv {G B : Type*} [Group G] [Group B] {A : Subgroup G}
    (φ : ↥A ≃* B) : Nonempty (↥⁅A, A⁆ ≃* ↥(commutator B)) := by
  have e1 : ↥(commutator ↥A) ≃* ↥⁅A, A⁆ :=
    (Subgroup.equivMapOfInjective (commutator ↥A) A.subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator A))
  exact ⟨e1.symm.trans (MulEquiv.commutatorCongr φ)⟩

theorem quasisimple_commutator_iff {G B : Type*} [Group G] [Group B] {A : Subgroup G}
    (φ : ↥A ≃* B) : CFSG.IsQuasisimple ↥⁅A, A⁆ ↔ CFSG.IsQuasisimple ↥(commutator B) := by
  obtain ⟨e⟩ := commutator_equiv φ
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e, CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm⟩

theorem tame_of_mulEquiv {G B : Type*} [Group G] [Group B] {A : Subgroup G} (φ : ↥A ≃* B)
    (h : CFSG.IsQuasisimple ↥(commutator B) ∨ Group.IsSolvable B) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A := by
  rcases h with h | h
  · exact Or.inl ((quasisimple_commutator_iff φ).2 h)
  · exact Or.inr (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)

theorem card_quot_commutator_of_mulEquiv {G B : Type*} [Group G] [Group B] {A : Subgroup G}
    (φ : ↥A ≃* B) :
    Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) =
      Nat.card (↥(commutator B) ⧸ Subgroup.center ↥(commutator B)) := by
  obtain ⟨e⟩ := commutator_equiv φ
  exact Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

theorem lieModel_quot_commutator_of_mulEquiv {G B : Type} [Group G] [Group B] {A : Subgroup G}
    (φ : ↥A ≃* B) {t : CFSG.Open.StatedLieTag} {m p f : ℕ}
    (h : CFSG.Blueprint.LieModel (↥(commutator B) ⧸ Subgroup.center ↥(commutator B)) t m p f) :
    CFSG.Blueprint.LieModel (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) t m p f := by
  obtain ⟨e⟩ := commutator_equiv φ
  exact CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv e.symm h

end CFSG.StandardType.GGNbrLSideKit
