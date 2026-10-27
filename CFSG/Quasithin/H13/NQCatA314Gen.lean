module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem isSylowTwoOf_top_subgroupOf {T L : Subgroup G} (h : IsSylowTwoOf T L) :
    IsSylowTwoOf (T.subgroupOf L) ⊤ := by
  obtain ⟨hTL, hT2, hTi⟩ := h
  refine ⟨le_top, hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm, ?_⟩
  rwa [show ((T.subgroupOf L).subgroupOf ⊤).index = (T.subgroupOf L).index from
    Subgroup.relIndex_top_right _]

theorem sup_ne_of_isSimpleGroup {T B L : Subgroup G} (hB : B ∈ lFamily T) (hBL : B ≤ L)
    (hne : B ≠ L) (hs : IsSimpleGroup ↥L) : B ⊔ T ≠ L := by
  intro hX
  have hBX : B ∈ cComp L := hX ▸ (hB : B ∈ cComp (B ⊔ T))
  have h1 := A4.subnormal_subgroupOf L (subnormal_of_mem_cComp hBX)
  rw [Subgroup.subgroupOf_self] at h1
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hs (A3.subnormal_top_iff.mp h1) with
    h | h
  · apply ne_bot_of_mem_cComp hBX
    have h2 : Disjoint B L := Subgroup.subgroupOf_eq_bot.mp h
    exact h2.eq_bot_of_le hBL
  · exact hne (le_antisymm hBL (Subgroup.subgroupOf_eq_top.mp h))

theorem card_sup_subgroupOf {T B L : Subgroup G} (hBL : B ≤ L) (hTL : T ≤ L) :
    Nat.card ↥((B ⊔ T).subgroupOf L) = Nat.card ↥(B ⊔ T) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hBL hTL)).toEquiv

theorem card_dvd_sup [Finite G] (B T : Subgroup G) : Nat.card B ∣ Nat.card ↥(B ⊔ T) :=
  Subgroup.card_dvd_of_le le_sup_left

theorem conj_mem_center_of_normal {X : Type*} [Group X] {V : Subgroup X} [hV : V.Normal]
    (b : X) {v : V} (hv : v ∈ Subgroup.center V) :
    (⟨b * v * b⁻¹, hV.conj_mem v v.2 b⟩ : V) ∈ Subgroup.center V := by
  rw [Subgroup.mem_center_iff] at hv ⊢
  intro x
  have h1 := congrArg Subtype.val (hv ⟨b⁻¹ * x * b, by
    have := hV.conj_mem x x.2 b⁻¹
    rwa [inv_inv] at this⟩)
  simp only [Subgroup.coe_mul] at h1
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  calc (x : X) * (b * v * b⁻¹) = b * ((b⁻¹ * x * b) * v) * b⁻¹ := by group
    _ = b * (v * (b⁻¹ * x * b)) * b⁻¹ := by rw [h1]
    _ = b * v * b⁻¹ * x := by group

theorem eq_inf_centralizer_of_card [Finite G] {L B : Subgroup G} {z : G}
    (hle : B ≤ L ⊓ Subgroup.centralizer ({z} : Set G))
    (hcard : Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set G)) ≤ Nat.card B) :
    B = L ⊓ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.eq_of_le_of_card_ge hle hcard

end CFSG.Quasithin.H13.NQCat.A314D
