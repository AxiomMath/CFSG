module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_map_subgroupOf_mk' {L Q : Subgroup G}
    (hQsyl : ∃ P : Sylow 3 ↥L, (P : Subgroup ↥L) = Q.subgroupOf L) :
    ∃ Pb : Sylow 3 (Bar2 L),
      (Pb : Subgroup (Bar2 L)) =
        (Q.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := hQsyl
  refine ⟨Sylow.mapSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)) P, ?_⟩
  rw [Sylow.coe_mapSurjective, hP]

theorem injective_comp_subgroupOf_mk' {L Q : Subgroup G} (hQL : Q ≤ L)
    (hQO2 : Q ⊓ pCoreOf 2 L = ⊥) :
    Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hQL)) := by
  have hf_one : ∀ q : ↥Q,
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hQL)) q = 1 → q = 1 := by
    intro q hq
    have hq' : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (Subgroup.inclusion hQL q) = 1 := hq
    have hqmem : Subgroup.inclusion hQL q ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff _).mp hq'
    have hqG : (q : G) ∈ pCoreOf 2 L := by
      rw [pCoreOf]
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hQL q, hqmem, rfl⟩
    have hbot : (q : G) ∈ Q ⊓ pCoreOf 2 L := ⟨q.2, hqG⟩
    rw [hQO2] at hbot
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  intro q₁ q₂ h
  have h1 : ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
      (Subgroup.inclusion hQL)) (q₁ * q₂⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  exact mul_inv_eq_one.mp (hf_one _ h1)

theorem range_comp_subgroupOf_mk' {L Q : Subgroup G} (hQL : Q ≤ L) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hQL)).range =
      (Q.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion hQL q, Subgroup.mem_subgroupOf.mpr q.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩,
      congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (Subtype.ext rfl)⟩

theorem card_center_map_eq_of_injective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) :
    Nat.card ((Subgroup.center f.range).map (Subgroup.subtype f.range)) =
      Nat.card ((Subgroup.center A).map f) := by
  rw [Subgroup.card_subtype, Subgroup.card_map_of_injective hf]
  exact (Nat.card_congr (Subgroup.centerCongr (MonoidHom.ofInjective hf)).toEquiv).symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
