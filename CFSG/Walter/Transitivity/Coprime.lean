module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs

public section

namespace CFSG.Walter.Transitivity

open CFSG

variable {G : Type*} [Group G] [Finite G]

theorem exists_conjBy_of_coprime_action {A K L₁ L₂ : Subgroup G} {π : Set Nat.Primes}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hsolv : Group.IsSolvable K)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K)) (hL₁K : L₁ ≤ K) (hL₂K : L₂ ≤ K)
    (hL₁ : IsPiSubgroup π L₁) (hL₂ : IsPiSubgroup π L₂)
    (hAL₁ : A ≤ Subgroup.normalizer (L₁ : Set G))
    (hAL₂ : A ≤ Subgroup.normalizer (L₂ : Set G)) :
    ∃ S : Subgroup G, S ≤ K ∧ IsPiSubgroup π S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      L₁ ≤ S ∧ ∃ c ∈ K ⊓ Subgroup.centralizer (A : Set G), L₂ ≤ S.conjBy c := by
  classical
  have : Subgroup.Normalizes A K := ⟨hAK⟩
  obtain ⟨R₁, hR₁Hall, hR₁inv, hL₁R₁⟩ :=
    proposition_1_5_b (G := K) (A := A) hsolv hcop π (L₁.subgroupOf K) (hL₁.subgroupOf hL₁K)
      (isInvariant_subgroupOf_of_le_normalizer hAK hAL₁ hL₁K)
  obtain ⟨R₂, hR₂Hall, hR₂inv, hL₂R₂⟩ :=
    proposition_1_5_b (G := K) (A := A) hsolv hcop π (L₂.subgroupOf K) (hL₂.subgroupOf hL₂K)
      (isInvariant_subgroupOf_of_le_normalizer hAK hAL₂ hL₂K)
  obtain ⟨m, hmfix, hR₂eq⟩ :=
    exists_mem_fixedPointSubgroup_eq_map_conj_of_isHallSubgroup_of_isInvariant (G := K)
      (A := A) hsolv hcop π R₁ R₂ hR₁Hall hR₂Hall hR₁inv hR₂inv
  rw [fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn K A hAK] at hmfix
  have hm : (m : G) ∈ K ⊓ Subgroup.centralizer (A : Set G) := hmfix
  let S : Subgroup G := R₁.map K.subtype
  have hSsub : S.subgroupOf K = R₁ :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective R₁
  have hmapL : ∀ {L : Subgroup G} {R : Subgroup K}, L ≤ K → L.subgroupOf K ≤ R →
      L ≤ R.map K.subtype := by
    intro L R hLK hLR x hx
    exact ⟨⟨x, hLK hx⟩, hLR hx, rfl⟩
  refine ⟨S, Subgroup.map_subtype_le R₁, hR₁Hall.isPiSubgroup.map K.subtype, ?_,
    hmapL hL₁K hL₁R₁, m, hm, ?_⟩
  · refine subgroup_le_normalizer_of_conj_mem S A ?_
    rintro a _ ⟨y, hy, rfl⟩
    exact ⟨a • y, (hR₁inv.invariant a y).1 hy, by
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩
  · have hR₂S : R₂.map K.subtype = S.conjBy (m : G) := by
      rw [hR₂eq, ← hSsub]
      exact map_subgroupOf_map_conj_eq (Subgroup.map_subtype_le R₁) m
    exact hR₂S ▸ hmapL hL₂K hL₂R₂

end CFSG.Walter.Transitivity
