module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Monster.B.CTIB

open Subgroup

variable {E : Type*} [Group E]

theorem commutator_le_of_isQuasisimple {K : Subgroup E} (hK : CFSG.IsQuasisimple K) :
    K ≤ commutator E := by
  have h := congrArg (Subgroup.map K.subtype) (Group.isPerfect_def.1 hK.1)
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  rw [← h, _root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top

theorem not_le_center_of_isQuasisimple {Q : Subgroup E} {K : Subgroup Q}
    (hK : CFSG.IsQuasisimple K) : ¬ K ≤ center Q := by
  intro hle
  obtain ⟨-, -, a, b, hab⟩ := hK
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact mem_center_iff.1 (hle b.2) (a : Q)

theorem subnormal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {H : Subgroup Q} (hH : H.IsSubnormal) : H = ⊤ ∨ H ≤ center Q := by
  induction hH with
  | top => exact .inl rfl
  | step H K hHK _ hHn ih =>
    rcases ih with rfl | hK
    · have hN : H.Normal := by
        constructor
        intro n hn g
        have := hHn.conj_mem ⟨n, Subgroup.mem_top n⟩ hn ⟨g, Subgroup.mem_top g⟩
        exact this
      exact CFSG.LocalCores.quasisimple_normal_subgroups hQ hN
    · exact .inr (hHK.trans hK)

theorem unique_component_of_quasisimple_commutator [Finite E]
    (hq : CFSG.IsQuasisimple (commutator E)) :
    CFSG.IsComponent (commutator E) ∧
      ∀ K : Subgroup E, CFSG.IsComponent K → K = commutator E := by
  refine ⟨⟨hq, (commutator_normal (⊤ : Subgroup E) ⊤).isSubnormal⟩, fun K hK => ?_⟩
  have hle := commutator_le_of_isQuasisimple hK.1
  have hsub : (K.subgroupOf (commutator E)).IsSubnormal := hK.2.subgroupOf
  rcases subnormal_eq_top_or_le_center hq hsub with h | h
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.1 h)
  · exfalso
    have hK' : CFSG.IsQuasisimple (K.subgroupOf (commutator E)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hK.1
    exact not_le_center_of_isQuasisimple hK' h

end CFSG.Monster.B.CTIB
