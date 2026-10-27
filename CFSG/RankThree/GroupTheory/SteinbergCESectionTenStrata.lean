module

public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction

public section

namespace CFSG.RankThree.GroupTheory

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def sectionTenRel (p : ℕ) (L K : Subgroup G) : Prop :=
  L = (L ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore p) L

@[expose] def sectionTenStar (p : ℕ) (A : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ thetaComponentFamily p A ∧
    ∀ K ∈ thetaComponentFamily p A, sectionTenRel p L K → sectionTenRel p K L}

@[expose] def sectionTenZero (p : ℕ) (A : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ thetaComponentFamily p A ∧ ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
    A ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A⁆}

@[expose] def sectionTenZeroStar (p : ℕ) (A : Subgroup G) : Set (Subgroup G) :=
  sectionTenZero p A ∩ sectionTenStar p A

@[expose] def sectionTenOne (p : ℕ) (A : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ thetaComponentFamily p A ∧ ∃ hA : A ≤ Subgroup.normalizer (L : Set G),
    (thetaQuotientAction p hA).range ≤
      (MulAut.conj : (L ⧸ aschbacherSolvableCore p L) →*
        MulAut (L ⧸ aschbacherSolvableCore p L)).range}

@[expose] def sectionTenTwo (p : ℕ) (A : Subgroup G) : Set (Subgroup G) :=
  thetaComponentFamily p A \ sectionTenOne p A

@[expose] def sectionTenAt (p : ℕ) (X : Set (Subgroup G)) (a : G) : Set (Subgroup G) :=
  X ∩ thetaComponentsAt p a

theorem sectionTen_quotient_action_kernel (p : ℕ) {A L : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (L : Set G)) :
    (thetaQuotientAction p hA).ker.map A.subtype = thetaQuotientCentralizer p A L ∧
      ∀ x : G, x ∈ thetaQuotientCentralizer p A L ↔
        x ∈ A ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L := by
  refine ⟨(thetaQuotientCentralizer_eq_map_ker p hA).symm, fun x => ?_⟩
  rw [mem_thetaQuotientCentralizer_iff]
  exact ⟨fun ⟨hxA, _, h⟩ => ⟨hxA, h⟩, fun ⟨hxA, h⟩ => ⟨hxA, hA hxA, h⟩⟩

theorem sectionTenRel_iff {p : ℕ} {L K : Subgroup G} :
    sectionTenRel p L K ↔
      (L : Set G) = ((L ⊓ K : Subgroup G) : Set G) *
        (inSubgroup (aschbacherSolvableCore p) L : Set G) := by
  have hθL : inSubgroup (aschbacherSolvableCore p) L ≤ L := Subgroup.map_subtype_le _
  have hnormal : ((inSubgroup (aschbacherSolvableCore p) L).subgroupOf L).Normal := by
    have h : (inSubgroup (aschbacherSolvableCore p) L).subgroupOf L = aschbacherSolvableCore p L :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [h]
    infer_instance
  have hLN := (Subgroup.normal_subgroupOf_iff_le_normalizer hθL).mp hnormal
  rw [sectionTenRel, ← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hLN),
    SetLike.coe_set_eq]

theorem sectionTenRel_refl (p : ℕ) (L : Subgroup G) : sectionTenRel p L L := by
  rw [sectionTenRel, inf_idem]
  exact (sup_eq_left.mpr (Subgroup.map_subtype_le _)).symm

theorem mem_sectionTenOne_iff {p : ℕ} {A L : Subgroup G} :
    L ∈ sectionTenOne p A ↔ L ∈ thetaComponentFamily p A ∧
      ∃ hA : A ≤ Subgroup.normalizer (L : Set G), ∀ a : A,
        ∃ q : L ⧸ aschbacherSolvableCore p L, thetaQuotientAction p hA a = MulAut.conj q := by
  refine and_congr_right fun _ => exists_congr fun hA => ⟨fun h a => ?_, fun h => ?_⟩
  · obtain ⟨q, hq⟩ := h ⟨a, rfl⟩
    exact ⟨q, hq.symm⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨q, hq⟩ := h a
    exact ⟨q, hq.symm⟩

theorem sectionTenOne_union_sectionTenTwo (p : ℕ) (A : Subgroup G) :
    sectionTenOne p A ∪ sectionTenTwo p A = thetaComponentFamily p A ∧
      Disjoint (sectionTenOne p A) (sectionTenTwo p A) :=
  ⟨Set.union_sdiff_cancel fun _ hL => hL.1, Set.disjoint_sdiff_right⟩

theorem sectionTenZeroStar_subset (p : ℕ) (A : Subgroup G) :
    sectionTenZeroStar p A ⊆ sectionTenZero p A ∧
      sectionTenZeroStar p A ⊆ sectionTenStar p A ∧
      sectionTenStar p A ⊆ thetaComponentFamily p A ∧
      sectionTenZero p A ⊆ thetaComponentFamily p A :=
  ⟨Set.inter_subset_left, Set.inter_subset_right, fun _ hL => hL.1, fun _ hL => hL.1⟩

end CFSG.RankThree.GroupTheory
