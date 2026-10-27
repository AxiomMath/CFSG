module

public import CFSG.Quasithin.Background.E3ClosedOne
public import CFSG.Quasithin.Background.E3ClosedTwo

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Closed

variable {G : Type u} [Group G] [Finite G] {V H S A K : Subgroup G}

omit [Finite G] in
theorem normal_subgroupOf_inf_pCoreOf {Y : Subgroup G} (hYK : Y ≤ K) :
    ((pCoreOf 2 K ⊓ Y).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.1
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (hYK hy)) x
  have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hy) x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]

theorem e3_12_core (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) (hAV : A ≤ V) (hAS : A ≤ S)
    {j : ℕ} (hK : E1.IsE j H S A K) :
    IsSylowIn 2 (pCoreOf 2 K ⊓ kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K)
        (kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K) ∧
      ¬ A ≤ kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K := by
  set Y := kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K with hY
  have hAab : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAV hV
  obtain ⟨hAK, -⟩ := card_le_of_isE hS hAS hAab hK
  have hYK : Y ≤ K := kerIn_le.trans inf_le_left
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := kerIn_le.trans inf_le_right
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_kerIn _ _
  have hYn : (Y.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).2 hKY
  have hcomm : IsPGroup 2 ↥⁅A.subgroupOf K, Y.subgroupOf K⁆ := by
    have hVK : IsPGroup 2 ↥((V ⊓ K).subgroupOf K) := by
      have h2 : IsPGroup 2 ↥(V ⊓ K) := (B2F.isPGroup_of_isElemAbelian hV).to_le inf_le_left
      exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    refine hVK.to_le (Subgroup.commutator_le.2 fun a ha y hy => ?_)
    have haV : (a : G) ∈ V := hAV ha
    have hyN : (y : G) ∈ Subgroup.normalizer (V : Set G) := hYN hy
    have e : ((⁅a, y⁆ : ↥K) : G) = (a : G) * ((y : G) * (a : G)⁻¹ * (y : G)⁻¹) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hV' : ((⁅a, y⁆ : ↥K) : G) ∈ V := by
      rw [e]
      exact V.mul_mem haV ((Subgroup.mem_normalizer_iff.1 hyN _).1 (V.inv_mem haV))
    have hmem : ((⁅a, y⁆ : ↥K) : G) ∈ V ⊓ K := ⟨hV', (⁅a, y⁆ : ↥K).2⟩
    exact hmem
  have key : IsSylowIn 2 (CFSG.Open.pCore 2 ↥K ⊓ Y.subgroupOf K) (Y.subgroupOf K) ∧
      ¬ A.subgroupOf K ≤ Y.subgroupOf K := by
    rcases hK.2.2.2 with ⟨hE, -⟩ | ⟨hE, -⟩
    · exact eOne_closed hE hcomm
    · exact eTwo_closed hE hcomm
  have hmap : (CFSG.Open.pCore 2 ↥K ⊓ Y.subgroupOf K).map K.subtype = pCoreOf 2 K ⊓ Y := by
    rw [Subgroup.map_inf _ _ _ K.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hYK]
    rfl
  refine ⟨?_, fun hAY => key.2 fun x hx => hAY hx⟩
  have h := (E1.isSylowIn_map_of_injective K.subtype_injective).2 key.1
  rwa [hmap, Subgroup.map_subgroupOf_eq_of_le hYK] at h

theorem e3_12_isTwoClosed (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) (hAV : A ≤ V)
    (hAS : A ≤ S) (hK : E1.IsEAny H S A K) :
    E1.IsTwoClosed (kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K) := by
  obtain ⟨j, hj⟩ := hK
  exact ⟨_, (e3_12_core hV hS hAV hAS hj).1,
    normal_subgroupOf_inf_pCoreOf (kerIn_le.trans inf_le_left)⟩

theorem e3_12_not_le (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) (hAV : A ≤ V) (hAS : A ≤ S)
    (hK : E1.IsEAny H S A K) :
    ¬ A ≤ kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K := by
  obtain ⟨j, hj⟩ := hK
  exact (e3_12_core hV hS hAV hAS hj).2

theorem e3_12_le_pCoreOf (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) (hAV : A ≤ V)
    (hAS : A ≤ S) (hK : E1.IsEAny H S A K) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXY : X ≤ kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K) : X ≤ pCoreOf 2 K := by
  obtain ⟨j, hj⟩ := hK
  have h := E1.le_of_isSylowIn_of_normal (e3_12_core hV hS hAV hAS hj).1
    (normal_subgroupOf_inf_pCoreOf (kerIn_le.trans inf_le_left)) hXY hX
  exact h.trans inf_le_left

end Closed

end E3

end CFSG.Quasithin
