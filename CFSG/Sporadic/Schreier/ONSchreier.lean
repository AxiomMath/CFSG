module

public import CFSG.Sporadic.Schreier.ONTwoCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierTwoCentralizersIntrinsic

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers

theorem onTSylow_mem_iff
    (x : Pv) :
    x ∈ (onTSylow : Subgroup Pv) ↔ (x : Equiv.Perm (Fin N)) ∈ onT := by
  rw [onTSylow_coe, Subgroup.mem_subgroupOf]

theorem onTSylow_centerIn
    (x : Pv) :
    x ∈ CFSG.centerIn (onTSylow : Subgroup Pv) ↔ (x : Equiv.Perm (Fin N)) ∈ CFSG.centerIn onT := by
  rw [CFSG.centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, onTSylow_mem_iff,
    CFSG.centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun y hy => ?_⟩
    have := hc ⟨y, onT_le hy⟩ ((onTSylow_mem_iff _).2 hy)
    exact congrArg Subtype.val this
  · rintro ⟨hx, hc⟩
    exact ⟨hx, fun y hy => Subtype.ext (hc y ((onTSylow_mem_iff y).1 hy))⟩

theorem on_intrinsicCentralizer :
    intrinsicCentralizer (onTSylow : Subgroup Pv) = onM.subgroupOf Pv := by
  ext g
  rw [intrinsicCentralizer, Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf,
    onM_eq_centralizer_z, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨g.2, ?_⟩
    have hz : zP ∈ CFSG.centerIn (onTSylow : Subgroup Pv) := by
      rw [onTSylow_centerIn, onT_centerIn]
      exact Subgroup.mem_zpowers _
    exact (congrArg Subtype.val (h zP hz)).symm
  · rintro ⟨-, hgz⟩ x hx
    rw [SetLike.mem_coe, onTSylow_centerIn, onT_centerIn] at hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hk]
    exact (Commute.zpow_left (Commute.symm hgz) k)

@[expose] def tP :
    Pv := ⟨ont, onM_le ont_mem_M⟩

theorem on_secondCentralizer :
    secondCentralizer tP = onM1.subgroupOf Pv := by
  ext g
  rw [mem_secondCentralizer_iff, Subgroup.mem_subgroupOf, onM1_eq_centralizer_t, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨g.2, (congrArg Subtype.val h).symm⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext h.symm

theorem tP_mem :
    tP ∈ intrinsicCentralizer (onTSylow : Subgroup Pv) := by
  rw [on_intrinsicCentralizer, Subgroup.mem_subgroupOf]
  exact ont_mem_M

theorem on_generate :
    intrinsicCentralizer (onTSylow : Subgroup Pv) ⊔ secondCentralizer tP = ⊤ := by
  rw [on_intrinsicCentralizer, on_secondCentralizer]
  apply Subgroup.map_injective Pv.subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 onM_le, inf_eq_left.2 onM1_le_P, onM_sup_M1, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

@[expose] def onIntrinsicEquiv :
    intrinsicCentralizer (onTSylow : Subgroup Pv) ≃* onM :=
  (MulEquiv.subgroupCongr on_intrinsicCentralizer).trans (Subgroup.subgroupOfEquivOfLe onM_le)

@[expose] def onSecondEquiv :
    secondCentralizer tP ≃* onM1 :=
  (MulEquiv.subgroupCongr on_secondCentralizer).trans (Subgroup.subgroupOfEquivOfLe onM1_le_P)

instance on_intrinsic_outer_solvable :
    Group.IsSolvable (Outer (intrinsicCentralizer (onTSylow : Subgroup Pv))) :=
  (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism onIntrinsicEquiv).2.2
    at_on_first_centralizer_schreier

instance on_second_outer_solvable :
    Group.IsSolvable (Outer (secondCentralizer tP)) :=
  (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism onSecondEquiv).2.2 onM1_outer_solvable

theorem card_on_intersectionCentralizer_le :
    Nat.card (intersectionCentralizer (intrinsicCentralizer (onTSylow : Subgroup Pv)) tP) ≤ 4 := by
  have hb : Nat.card (onM1 ⊓ Subgroup.centralizer ((onM ⊓ onM1 : Subgroup (Equiv.Perm (Fin N))) :
      Set (Equiv.Perm (Fin N))) : Subgroup (Equiv.Perm (Fin N))) ≤ 4 :=
    (Subgroup.card_le_of_le centralizer_inter_le).trans card_cM1D0_le
  refine le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨((x : secondCentralizer tP) : Pv), ?_⟩ :
      (onM1 ⊓ Subgroup.centralizer ((onM ⊓ onM1 : Subgroup (Equiv.Perm (Fin N))) :
        Set (Equiv.Perm (Fin N))) : Subgroup (Equiv.Perm (Fin N))))) ?_) hb
  · refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h := (mem_secondCentralizer_iff tP _).1 (x : secondCentralizer tP).2
      rw [onM1_eq_centralizer_t]
      exact Subgroup.mem_inf.2 ⟨((x : secondCentralizer tP) : Pv).2,
        Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h).symm⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨hgM, hgM1⟩ := Subgroup.mem_inf.1 hg
      have hgP : g ∈ Pv := onM_le hgM
      have hg2 : (⟨g, hgP⟩ : Pv) ∈ secondCentralizer tP := by
        rw [on_secondCentralizer, Subgroup.mem_subgroupOf]
        exact hgM1
      have hg1 : (⟨⟨g, hgP⟩, hg2⟩ : secondCentralizer tP) ∈
          centralizerIntersection (intrinsicCentralizer (onTSylow : Subgroup Pv)) tP := by
        rw [centralizerIntersection, Subgroup.mem_subgroupOf, on_intrinsicCentralizer,
          Subgroup.mem_subgroupOf]
        exact hgM
      have := Subgroup.mem_centralizer_iff.1 x.2 _ hg1
      exact congrArg (fun y : secondCentralizer tP => ((y : Pv) : Equiv.Perm (Fin N))) this
  · intro x y h
    have := congrArg (fun w : (onM1 ⊓ Subgroup.centralizer ((onM ⊓ onM1 :
      Subgroup (Equiv.Perm (Fin N))) : Set (Equiv.Perm (Fin N))) : Subgroup (Equiv.Perm (Fin N))) =>
        (w : Equiv.Perm (Fin N))) h
    exact Subtype.ext (Subtype.ext (Subtype.ext this))

instance on_intersection_solvable :
    Group.IsSolvable (intersectionCentralizer (intrinsicCentralizer (onTSylow : Subgroup Pv))
      tP) :=
  CFSG.ComponentClassification.CatalogueSchreierAlternating.solvable_of_card_le_four
    card_on_intersectionCentralizer_le

theorem onP_outer_solvable :
    Group.IsSolvable (Outer Pv) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact intrinsic_two_centralizer_schreier Pv 2 onTSylow tP tP_mem on_generate

theorem at_on_schreier :
    Group.IsSolvable (Outer Blueprint.NativeSporadic.ON) :=
  (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism (G := Blueprint.NativeSporadic.ON)
    (H := Pv) (by exact onEquivPv)).2.2 onP_outer_solvable

end CFSG.ONSchreier
