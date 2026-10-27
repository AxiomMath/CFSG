module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Walter.W67.P56Ab

variable {G : Type*} [Group G] [Finite G]

theorem isSolvable_of_odd {K : Subgroup G} (hK : Odd (Nat.card K)) : Group.IsSolvable K :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ hK

theorem exists_hall_invariant {A K L : Subgroup G} {π : Set Nat.Primes}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hsolv : Group.IsSolvable K)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K)) (hLK : L ≤ K) (hL : IsPiSubgroup π L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ S : Subgroup G, S ≤ K ∧ IsHallSubgroup π (S.subgroupOf K) ∧
      A ≤ Subgroup.normalizer (S : Set G) ∧ L ≤ S := by
  classical
  have : Subgroup.Normalizes A K := ⟨hAK⟩
  obtain ⟨R, hRHall, hRinv, hLR⟩ :=
    proposition_1_5_b (G := K) (A := A) hsolv hcop π (L.subgroupOf K) (hL.subgroupOf hLK)
      (isInvariant_subgroupOf_of_le_normalizer hAK hAL hLK)
  let S : Subgroup G := R.map K.subtype
  have hSsub : S.subgroupOf K = R :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective R
  refine ⟨S, Subgroup.map_subtype_le R, hSsub ▸ hRHall, ?_, ?_⟩
  · refine subgroup_le_normalizer_of_conj_mem S A ?_
    rintro a _ ⟨y, hy, rfl⟩
    exact ⟨a • y, (hRinv.invariant a y).1 hy, by
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩
  · intro x hx
    exact ⟨⟨x, hLK hx⟩, hLR hx, rfl⟩

theorem exists_conj_hall_invariant {A K S₁ S₂ : Subgroup G} {π : Set Nat.Primes}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hsolv : Group.IsSolvable K)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card K)) (h₁K : S₁ ≤ K) (h₂K : S₂ ≤ K)
    (h₁ : IsHallSubgroup π (S₁.subgroupOf K)) (h₂ : IsHallSubgroup π (S₂.subgroupOf K))
    (hA₁ : A ≤ Subgroup.normalizer (S₁ : Set G)) (hA₂ : A ≤ Subgroup.normalizer (S₂ : Set G)) :
    ∃ c ∈ K ⊓ Subgroup.centralizer (A : Set G),
      S₂ = S₁.map (MulAut.conj c).toMonoidHom := by
  classical
  have : Subgroup.Normalizes A K := ⟨hAK⟩
  obtain ⟨m, hmfix, hR₂eq⟩ :=
    exists_mem_fixedPointSubgroup_eq_map_conj_of_isHallSubgroup_of_isInvariant (G := K)
      (A := A) hsolv hcop π (S₁.subgroupOf K) (S₂.subgroupOf K) h₁ h₂
      (isInvariant_subgroupOf_of_le_normalizer hAK hA₁ h₁K)
      (isInvariant_subgroupOf_of_le_normalizer hAK hA₂ h₂K)
  rw [fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn K A hAK] at hmfix
  have hm : (m : G) ∈ K ⊓ Subgroup.centralizer (A : Set G) := hmfix
  refine ⟨m, hm, ?_⟩
  have h₂map : (S₂.subgroupOf K).map K.subtype = S₂ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h₂K]
  rw [← h₂map, hR₂eq]
  exact map_subgroupOf_map_conj_eq h₁K m

end CFSG.Walter.W67.P56Ab
