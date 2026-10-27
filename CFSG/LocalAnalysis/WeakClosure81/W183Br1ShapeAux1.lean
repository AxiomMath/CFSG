module

public import CFSG.Adapters.LieModelSimple
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Quasithin.Background.P3Sp44Comm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt Bar2 CoverOf)
open CFSG.Blueprint (LieModel)
open scoped IsMulCommutative commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183_finite_lgl : Finite (LGL 2 V) :=
  Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
    (fun e f h => LinearEquiv.ext (congrFun h))

theorem w183_center_eq_bot_of_simple {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center X := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

private theorem w183_open_isQuasisimple_of_simple {X : Type} [Group X]
    (hs : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple X := by
  have hcenter : Subgroup.center X = ⊥ := w183_center_eq_bot_of_simple hs hnab
  refine ⟨?_, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      haveI := (commutator_eq_bot_iff X).mp h
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (mul_comm a b)
    · exact h
  · have e : X ⧸ Subgroup.center X ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup

theorem w183_exists_mul_ne_of_isL3_two {X : Type} [Group X] (h : IsL3 X 2) :
    ∃ a b : X, a * b ≠ b * a := by
  have hst : CFSG.Open.StatedClassicalModel X .PSL 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have hcard : Nat.card X = 20160 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hst
  have hsimple : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  by_contra hnab
  have hcomm : IsMulCommutative X := IsMulCommutative.of_comm (fun a b => by
    by_contra hab
    exact hnab ⟨a, b, hab⟩)
  letI : IsMulCommutative X := hcomm
  have hp : (Nat.card X).Prime := CommGroup.is_simple_iff_prime_card.mp hsimple
  rw [hcard] at hp
  norm_num at hp

theorem w183_map_conjSubgroup_subgroupOf {W : Type} [Group W] {Y P : Subgroup W} (hPY : P ≤ Y)
    {x : W} (hx : x ∈ Y) :
    (conjSubgroup (P.subgroupOf Y) (⟨x, hx⟩ : ↥Y)).map Y.subtype = conjSubgroup P x := by
  ext w
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_conjSubgroup_iff] at hv ⊢
    exact hv
  · intro hw
    rw [mem_conjSubgroup_iff] at hw
    have hxinv : x⁻¹ ∈ Y := Y.inv_mem hx
    have hwY : w ∈ Y := by
      have h : x⁻¹ * (x * w * x⁻¹) * x = w := by group
      rw [← h]
      exact Y.mul_mem (Y.mul_mem hxinv (hPY hw)) hx
    refine ⟨⟨w, hwY⟩, ?_, rfl⟩
    rw [mem_conjSubgroup_iff, Subgroup.mem_subgroupOf]
    exact hw

theorem w183_isSylowIn_of_subgroupOf {W : Type} [Group W] {Y L A : Subgroup W} (hAY : A ≤ Y)
    (hLY : L ≤ Y) (h : IsSylowIn 2 (A.subgroupOf Y) (L.subgroupOf Y)) :
    IsSylowIn 2 A L := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    have ha' : (⟨a, hAY ha⟩ : ↥Y) ∈ L.subgroupOf Y :=
      h.le (Subgroup.mem_subgroupOf.mpr ha)
    exact Subgroup.mem_subgroupOf.mp ha'
  · exact h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hAY)
  · have hrel := Subgroup.relIndex_comap (H := A) (f := Y.subtype) (K := L.subgroupOf Y)
    rw [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLY] at hrel
    rw [← hrel]
    exact h.not_dvd_relIndex

theorem w183_coverOf_and_component_of_isL3 {W : Type} [Group W] {Y L : Subgroup W} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hshape : IsL3 ↥L 2) :
    CFSG.Open.IsComponentOf (L.subgroupOf Y) ⊤ ∧ CoverOf ↥(L.subgroupOf Y) ↥L := by
  have hsimple : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hshape
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := w183_exists_mul_ne_of_isL3_two hshape
  have hqL : CFSG.Open.IsQuasisimple ↥L := w183_open_isQuasisimple_of_simple hsimple hnab
  have hqL' : CFSG.Open.IsQuasisimple ↥(L.subgroupOf Y) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY) hqL
  have hsimpleL' : IsSimpleGroup ↥(L.subgroupOf Y) :=
    (Subgroup.subgroupOfEquivOfLe hLY).isSimpleGroup
  have hnabL' : ∃ a b : ↥(L.subgroupOf Y), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨(Subgroup.subgroupOfEquivOfLe hLY).symm a,
      (Subgroup.subgroupOfEquivOfLe hLY).symm b, ?_⟩
    intro h
    exact hab (by simpa using congrArg (Subgroup.subgroupOfEquivOfLe hLY) h)
  have hcenterL' : Subgroup.center ↥(L.subgroupOf Y) = ⊥ :=
    w183_center_eq_bot_of_simple hsimpleL' hnabL'
  refine ⟨⟨le_top, ?_, hqL'⟩, hqL', ⟨?_⟩⟩
  · exact CFSG.Open.IsSubnormal.step le_top (hLn.subgroupOf ⊤)
      (CFSG.Open.IsSubnormal.refl ⊤)
  exact ((QuotientGroup.quotientMulEquivOfEq hcenterL').trans
    QuotientGroup.quotientBot).trans (Subgroup.subgroupOfEquivOfLe hLY)

end CFSG.LocalAnalysis.WeakClosure81

end
