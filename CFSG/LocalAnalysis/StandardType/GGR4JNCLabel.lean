module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

private theorem ncl_hasLabel_of_subgroupOf {G : Type} [Group G] {L J : Subgroup G} (hJL : J ≤ L)
    {lab : LargeEvenLabel}
    (h : GGHasLabel lab
      (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L))) :
    GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
  let e : ↥(J.subgroupOf L) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJL
  let eQ : (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) ≃*
      (↥J ⧸ Subgroup.center ↥J) :=
    QuotientGroup.congr (Subgroup.center ↥(J.subgroupOf L)) (Subgroup.center ↥J) e
      (Subgroup.map_center_eq e)
  exact largeEvenRawDatum_mono (fun _ _ _ _ hQ => ⟨eQ.symm.trans hQ.some⟩) h

private theorem ncl_label_of_layer {G : Type} [Group G] {L J : Subgroup G} (hJL : J ≤ L) {f : ℕ}
    (h : (3 ∣ 2 ^ f + 1 ∧
        GGHasLabel ⟨.A, 5, f⟩ (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L))) ∨
      (3 ∣ 2 ^ f - 1 ∧
        GGHasLabel ⟨.twA, 5, f⟩ (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L))) ∨
      GGHasLabel ⟨.twD, 4, f⟩
        (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L))) :
    GGR4JLabel (↥J ⧸ Subgroup.center ↥J) := by
  rcases h with ⟨h3, hA⟩ | ⟨h3, hA⟩ | hD
  · exact ⟨f, Or.inr (Or.inr (Or.inl ⟨h3, ncl_hasLabel_of_subgroupOf hJL hA⟩))⟩
  · exact ⟨f, Or.inr (Or.inl ⟨h3, ncl_hasLabel_of_subgroupOf hJL hA⟩)⟩
  · exact ⟨f, Or.inr (Or.inr (Or.inr (ncl_hasLabel_of_subgroupOf hJL hD)))⟩

theorem ggR4J_label_of_row (hM7a : GGF4OrderThreeLayer) (hM7b : GGE6OppOrderThreeLayer)
    {G : Type} [Group G] [Finite G] {L J : Subgroup G} [Group.IsPerfect ↥L] {f : ℕ} (hf : 1 ≤ f)
    (hrow : GGHasLabel ⟨.F4, 0, f⟩ (↥L ⧸ Subgroup.center ↥L) ∨
      (GGHasLabel ⟨.E6, 0, f⟩ (↥L ⧸ Subgroup.center ↥L) ∧ 3 ∣ 2 ^ f + 1) ∨
      (GGHasLabel ⟨.twE6, 0, f⟩ (↥L ⧸ Subgroup.center ↥L) ∧ 3 ∣ 2 ^ f - 1))
    (hJL : J ≤ L) {z : ↥L} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hJlayer : J.subgroupOf L = LargeEvenLayer (Subgroup.centralizer ({z} : Set ↥L)))
    (hJcomp : IsComponentOf (J.subgroupOf L) (Subgroup.centralizer ({z} : Set ↥L)))
    (hno : GGHasLabel ⟨.E6, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L) →
      GGHasLabel ⟨.A, 2, 2⟩ (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) → False) :
    GGR4JLabel (↥J ⧸ Subgroup.center ↥J) := by
  rcases hrow with hF4L | ⟨hE6L, h3E⟩ | ⟨hT6L, h3T⟩
  · exact ⟨f, Or.inl (ncl_hasLabel_of_subgroupOf hJL
      (hM7a ↥L f hf hF4L z hz1 hz3 (J.subgroupOf L) hJlayer hJcomp).1)⟩
  · rcases hM7b ↥L f hf (Or.inl ⟨hE6L, h3E⟩) z hz1 hz3 (J.subgroupOf L) hJlayer hJcomp with
      ⟨hdisj, -⟩ | ⟨-, hE6two, hA22⟩
    · exact ncl_label_of_layer hJL hdisj
    · exact (hno hE6two hA22).elim
  · rcases hM7b ↥L f hf (Or.inr ⟨hT6L, h3T⟩) z hz1 hz3 (J.subgroupOf L) hJlayer hJcomp with
      ⟨hdisj, -⟩ | ⟨-, hE6two, hA22⟩
    · exact ncl_label_of_layer hJL hdisj
    · exact (hno hE6two hA22).elim

end CFSG.StandardType

end
