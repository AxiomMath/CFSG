module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.Reconstruction

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII

universe u

/-! # Peterfalvi, Part II, Chapter IV, Section 1 Lemma, first assertion -/

private theorem lemma_a_compatible_copy_closure_iso_obligation
    {L : Type u} {X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    [FaithfulSMul L X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ {L' : Type u} {X' : Type*}
      [Group L'] [Finite L'] [MulAction L' X'] [Finite X'] [FaithfulSMul L' X']
      (M' Q' D' : Subgroup L') (t' : L') (f' g' h' : L' → L'),
      MulAction.IsMultiplyPretransitive L' X' 2 →
        (∃ x' : X', M' = MulAction.stabilizer L' x') →
          IsInvolution t' → t' ∉ M' →
            D' = M' ⊓ rightConjugate M' t' →
              (Q'.subgroupOf M').Normal →
                Disjoint Q' D' → Q' ⊔ D' = M' →
                  (∀ x' : L', x' ∈ Q' → x' ≠ 1 → f' x' ∈ Q' ∧ f' x' ≠ 1) →
                    (∀ x' : L', x' ∈ Q' → x' ≠ 1 → g' x' ∈ Q' ∧ g' x' ≠ 1) →
                      (∀ x' : L', x' ∈ Q' → x' ≠ 1 → h' x' ∈ D') →
                        (∀ x' : L', x' ∈ Q' → x' ≠ 1 →
                          t' * x' * t' = g' x' * h' x' * t' * f' x') →
                          (qIso : Q ≃* Q') →
                            (∀ x : L, ∀ hx : x ∈ Q, ∀ hx1 : x ≠ 1,
                              ((qIso ⟨f x, (hf_mem x hx hx1).1⟩ : Q') : L') =
                                f' ((qIso ⟨x, hx⟩ : Q') : L')) →
                              Nonempty (((⨆ x : L, rightConjugate Q x) : Subgroup L) ≃*
                                ((⨆ x : L', rightConjugate Q' x) : Subgroup L')) := by
  intro L' X' _ _ _ _ _ M' Q' D' t' f' g' h' htwo_transitive'
    hpoint_stabilizer' ht_involution' ht_not_mem_M' hD_eq' hQ_normal_in_M'
    hQ_disjoint_D' hQ_sup_D' hf_mem' hg_mem' hh_mem' hcanonical_eq' qIso hf_compat
  obtain ⟨a, hM⟩ := hpoint_stabilizer
  obtain ⟨a', hM'⟩ := hpoint_stabilizer'
  obtain ⟨e, _he_base, hQ, ht⟩ :=
    exists_rankOnePointEquiv M Q D t f g h a M' Q' D' t' f' g' h' a'
      htwo_transitive hM ht_involution ht_not_mem_M hD_eq hQ_normal_in_M
      hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      htwo_transitive' hM' ht_involution' ht_not_mem_M' hD_eq'
      hQ_normal_in_M' hQ_disjoint_D' hQ_sup_D' hf_mem' hg_mem' hh_mem'
      hcanonical_eq' qIso hf_compat
  obtain ⟨E, hE_Q, _hE_t⟩ :=
    rankOneGeneratedSubgroup_equiv Q t Q' t' qIso e hQ ht
  let A : Subgroup L := Subgroup.closure ((Q : Set L) ∪ ({t} : Set L))
  let A' : Subgroup L' := Subgroup.closure ((Q' : Set L') ∪ ({t'} : Set L'))
  let N : Subgroup L := ⨆ l : L, rightConjugate Q l
  let N' : Subgroup L' := ⨆ l : L', rightConjugate Q' l
  let QA : Subgroup A := Q.subgroupOf A
  let QA' : Subgroup A' := Q'.subgroupOf A'
  have hN_le_A : N ≤ A :=
    rankOneNormalClosure_le_generated M Q D t a htwo_transitive hM
      ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D
  have hN'_le_A' : N' ≤ A' :=
    rankOneNormalClosure_le_generated M' Q' D' t' a' htwo_transitive' hM'
      ht_involution' ht_not_mem_M' hD_eq' hQ_normal_in_M' hQ_disjoint_D'
      hQ_sup_D'
  have hN_sub : N.subgroupOf A = Subgroup.normalClosure (QA : Set A) :=
    rankOneNormalClosure_subgroupOf_generated M Q D t a htwo_transitive hM
      ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D
  have hN'_sub : N'.subgroupOf A' = Subgroup.normalClosure (QA' : Set A') :=
    rankOneNormalClosure_subgroupOf_generated M' Q' D' t' a' htwo_transitive' hM'
      ht_involution' ht_not_mem_M' hD_eq' hQ_normal_in_M' hQ_disjoint_D'
      hQ_sup_D'
  have hQA_map : QA.map E.toMonoidHom = QA' := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      rcases hx with ⟨y, hy, rfl⟩
      let q : Q := ⟨y, hy⟩
      have hy_eq : y = ⟨q, Subgroup.subset_closure (Or.inl q.property)⟩ :=
        Subtype.ext rfl
      change ((E y : A') : L') ∈ Q'
      rw [hy_eq, hE_Q q]
      exact (qIso q).property
    · intro x hx
      let q' : Q' := ⟨x, hx⟩
      let q : Q := qIso.symm q'
      let y : A := ⟨q, Subgroup.subset_closure (Or.inl q.property)⟩
      rw [Subgroup.mem_map]
      refine ⟨y, q.property, ?_⟩
      apply Subtype.ext
      have hspec := hE_Q q
      simpa [y, q, q'] using congrArg Subtype.val hspec
  have hnormal_map :
      (Subgroup.normalClosure (QA : Set A)).map E.toMonoidHom =
        Subgroup.normalClosure (QA' : Set A') := by
    rw [Subgroup.map_normalClosure (QA : Set A) E.toMonoidHom E.surjective]
    congr 1
    rw [← Subgroup.coe_map, hQA_map]
  exact ⟨
    (Subgroup.subgroupOfEquivOfLe hN_le_A).symm |>.trans
      (MulEquiv.subgroupCongr hN_sub) |>.trans
      (E.subgroupMap (Subgroup.normalClosure (QA : Set A))) |>.trans
      (MulEquiv.subgroupCongr hnormal_map) |>.trans
      (MulEquiv.subgroupCongr hN'_sub.symm) |>.trans
      (Subgroup.subgroupOfEquivOfLe hN'_le_A')⟩

public theorem lemma_a
    {L : Type u} {X : Type*}
    [Group L] [Finite L] [MulAction L X] [Finite X] [FaithfulSMul L X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ {L' : Type u} {X' : Type*}
        [Group L'] [Finite L'] [MulAction L' X'] [Finite X'] [FaithfulSMul L' X']
        (M' Q' D' : Subgroup L') (t' : L') (f' g' h' : L' → L'),
        MulAction.IsMultiplyPretransitive L' X' 2 →
          (∃ x' : X', M' = MulAction.stabilizer L' x') →
            IsInvolution t' → t' ∉ M' →
              D' = M' ⊓ rightConjugate M' t' →
                (Q'.subgroupOf M').Normal →
                  Disjoint Q' D' → Q' ⊔ D' = M' →
                    (∀ x' : L', x' ∈ Q' → x' ≠ 1 → f' x' ∈ Q' ∧ f' x' ≠ 1) →
                      (∀ x' : L', x' ∈ Q' → x' ≠ 1 → g' x' ∈ Q' ∧ g' x' ≠ 1) →
                        (∀ x' : L', x' ∈ Q' → x' ≠ 1 → h' x' ∈ D') →
                          (∀ x' : L', x' ∈ Q' → x' ≠ 1 →
                            t' * x' * t' = g' x' * h' x' * t' * f' x') →
                            (qIso : Q ≃* Q') →
                              (∀ x : L, ∀ hx : x ∈ Q, ∀ hx1 : x ≠ 1,
                                ((qIso ⟨f x, (hf_mem x hx hx1).1⟩ : Q') : L') =
                                  f' ((qIso ⟨x, hx⟩ : Q') : L')) →
                                Nonempty (((⨆ x : L, rightConjugate Q x) : Subgroup L) ≃*
                                  ((⨆ x : L', rightConjugate Q' x) : Subgroup L')) := by
  exact lemma_a_compatible_copy_closure_iso_obligation M Q D t f g h
    htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq
    hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
end PFchapter4section1
end CFSG.BenderSuzuki
