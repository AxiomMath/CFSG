module

public import CFSG.Sporadic.Schreier.Co3First
public import CFSG.Sporadic.Schreier.Co3Generation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierTwoCentralizersIntrinsic

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers

theorem co3TSylow_mem_iff
    (x : co3P) :
    x ∈ (co3TSylow : Subgroup co3P) ↔ (x : Equiv.Perm (Fin 276)) ∈ co3T := by
  rw [co3TSylow_coe, Subgroup.mem_subgroupOf]

theorem co3TSylow_centerIn
    (x : co3P) :
    x ∈ CFSG.centerIn (co3TSylow : Subgroup co3P) ↔ x = 1 ∨ x = co3ZP := by
  rw [CFSG.centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, co3TSylow_mem_iff]
  have key := co3T_center_iff (x : Equiv.Perm (Fin 276))
  constructor
  · rintro ⟨hx, hc⟩
    have h := key.1 ⟨hx, fun y hy => ?_⟩
    · rcases h with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · have := hc ⟨y, co3T_le_P hy⟩ ((co3TSylow_mem_iff _).2 hy)
      exact (congrArg Subtype.val this).symm
  · intro h
    have hx : (x : Equiv.Perm (Fin 276)) = 1 ∨ (x : Equiv.Perm (Fin 276)) = co3Z := by
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    obtain ⟨hxT, hc⟩ := key.2 hx
    refine ⟨hxT, fun y hy => Subtype.ext ?_⟩
    exact (hc y ((co3TSylow_mem_iff y).1 hy)).symm

theorem co3_intrinsicCentralizer :
    intrinsicCentralizer (co3TSylow : Subgroup co3P) = co3M.subgroupOf co3P := by
  rw [co3M_subgroupOf_eq]
  ext g
  rw [intrinsicCentralizer, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h co3ZP ((co3TSylow_centerIn _).2 (Or.inr rfl))).symm
  · intro h x hx
    rcases (co3TSylow_centerIn x).1 hx with rfl | rfl
    · rw [one_mul, mul_one]
    · exact h.symm

theorem co3_secondCentralizer :
    secondCentralizer co3TtP = co3M1.subgroupOf co3P := by
  rw [co3M1_subgroupOf_eq]
  rfl

theorem mem_co3_intrinsicCentralizer
    {g : co3P} :
    g ∈ intrinsicCentralizer (co3TSylow : Subgroup co3P) ↔ (g : Equiv.Perm (Fin 276)) ∈ co3M := by
  rw [co3_intrinsicCentralizer, Subgroup.mem_subgroupOf]

theorem mem_co3_secondCentralizer
    {g : co3P} :
    g ∈ secondCentralizer co3TtP ↔ (g : Equiv.Perm (Fin 276)) ∈ co3M1 := by
  rw [co3_secondCentralizer, Subgroup.mem_subgroupOf]

theorem co3TtP_mem :
    co3TtP ∈ intrinsicCentralizer (co3TSylow : Subgroup co3P) := by
  rw [co3_intrinsicCentralizer, Subgroup.mem_subgroupOf]
  exact co3Tt_mem_M

theorem co3_generate :
    intrinsicCentralizer (co3TSylow : Subgroup co3P) ⊔ secondCentralizer co3TtP = ⊤ := by
  rw [co3_intrinsicCentralizer, co3_secondCentralizer]
  apply Subgroup.map_injective co3P.subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 co3M_le_P, inf_eq_left.2 co3M1_le_P, co3M_sup_M1, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

@[expose] def co3IntrinsicEquiv :
    intrinsicCentralizer (co3TSylow : Subgroup co3P) ≃* co3M :=
  (MulEquiv.subgroupCongr co3_intrinsicCentralizer).trans (Subgroup.subgroupOfEquivOfLe co3M_le_P)

@[expose] def co3SecondEquiv :
    secondCentralizer co3TtP ≃* co3M1 :=
  (MulEquiv.subgroupCongr co3_secondCentralizer).trans (Subgroup.subgroupOfEquivOfLe co3M1_le_P)

instance co3_intrinsic_outer_solvable :
    Group.IsSolvable (Outer (intrinsicCentralizer (co3TSylow : Subgroup co3P))) :=
  (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism co3IntrinsicEquiv).2.2
    co3M_outer_solvable

instance co3_second_outer_solvable :
    Group.IsSolvable (Outer (secondCentralizer co3TtP)) :=
  (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism co3SecondEquiv).2.2
    co3M1_outer_solvable

theorem card_co3_intersectionCentralizer_le :
    Nat.card (intersectionCentralizer (intrinsicCentralizer (co3TSylow : Subgroup co3P))
      co3TtP) ≤ 4 := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨((x : secondCentralizer co3TtP) : co3P), ?_⟩ : co3CM1)) ?_) card_co3CM1_le
  · refine Subgroup.mem_inf.2 ⟨mem_co3_secondCentralizer.1 (x : secondCentralizer co3TtP).2, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨hgM, hgM1⟩ := Subgroup.mem_inf.1 hg
      have hgP : g ∈ co3P := co3M_le_P hgM
      have hg2 : (⟨g, hgP⟩ : co3P) ∈ secondCentralizer co3TtP := mem_co3_secondCentralizer.2 hgM1
      have hg1 : (⟨⟨g, hgP⟩, hg2⟩ : secondCentralizer co3TtP) ∈
          centralizerIntersection (intrinsicCentralizer (co3TSylow : Subgroup co3P)) co3TtP := by
        rw [centralizerIntersection, Subgroup.mem_subgroupOf]
        exact mem_co3_intrinsicCentralizer.2 hgM
      have := Subgroup.mem_centralizer_iff.1 x.2 _ hg1
      exact congrArg (fun y : secondCentralizer co3TtP => ((y : co3P) : Equiv.Perm (Fin 276)))
        this
  · intro x y h
    have := congrArg (fun z : co3CM1 => (z : Equiv.Perm (Fin 276))) h
    exact Subtype.ext (Subtype.ext (Subtype.ext this))

instance co3_intersection_solvable :
    Group.IsSolvable (intersectionCentralizer (intrinsicCentralizer (co3TSylow : Subgroup co3P))
      co3TtP) :=
  CFSG.ComponentClassification.CatalogueSchreierAlternating.solvable_of_card_le_four
    card_co3_intersectionCentralizer_le

theorem co3P_outer_solvable :
    Group.IsSolvable (Outer co3P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact intrinsic_two_centralizer_schreier co3P 2 co3TSylow co3TtP co3TtP_mem co3_generate

theorem AT_Co3_Schreier :
    Group.IsSolvable (Outer Blueprint.NativeSporadic.Co3) :=
  (@CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism Blueprint.NativeSporadic.Co3 co3P
    Units.instGroup _ co3PermEquiv).2.2 co3P_outer_solvable

end CFSG.Sporadic.Schreier.Co3
