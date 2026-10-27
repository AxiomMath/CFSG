module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN9

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.H13.L829N

theorem nk_liftCase1_three : NKLiftCase1 3 := fun hKc htH hJ hne hs hna h3 hr =>
  not_surv1_of_pRank_three hKc htH hJ hne hs hna h3 hr

theorem nk_liftCase2_three : NKLiftCase2 3 := by
  intro G _ _ H K M hKH hJ hrk hrank
  obtain ⟨E₀, hE₀, hE₀9⟩ := exists_elemAb9_of_two_le_pRank hrk
  set Y : Subgroup H := (kerIn M H).subgroupOf H with hYdef
  set K' : Subgroup H := K.subgroupOf H with hK'def
  set D : Subgroup H := CFSG.pCore 2 H with hDdef
  have hD : IsPGroup 2 D := CFSG.pCore_isPGroup
  have hYK : ∀ y ∈ Y, ∀ k ∈ K', y * k * y⁻¹ * k⁻¹ ∈ D := by
    intro y hy k hk
    have hyJ : (y : G) ∈ kerIn M H := Subgroup.mem_subgroupOf.mp hy
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hmem := ((hJ (y : G)).mp hyJ).2 (k : G) (Subgroup.mem_sup_left hkK)
    have hmem' : ((y * k * y⁻¹ * k⁻¹ : H) : G) ∈ pCoreOf 2 H := by
      simpa using hmem
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hmem'
    have hxe : x = y * k * y⁻¹ * k⁻¹ := Subtype.ext hxg
    rw [← hxe]
    exact hx
  let E : Subgroup (E2.StarQuot M H) := E₀.map (E2.star M H K).subtype
  have hE : IsElemAbelian 3 E := isElemAbelian_map 3 _ hE₀
  have hE9 : Nat.card E = 9 := by
    rw [Subgroup.card_map_of_injective (E2.star M H K).subtype_injective, hE₀9]
  have hEK : ∀ e ∈ E, ∃ k ∈ K', (k : E2.StarQuot M H) = e := by
    intro e he
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp he
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp x.2
    refine ⟨k, hk, ?_⟩
    rw [← hxe]
    exact hkx
  obtain ⟨F, -, hF, hF9⟩ := exists_elemAb9_of_quotient_meet Y K' D hD hYK E hE hE9 hEK
  have hFH : F.map H.subtype ≤ H := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hF' : IsElemAbelian 3 (F.map H.subtype) := isElemAbelian_map 3 H.subtype hF
  have hF'9 : Nat.card (F.map H.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hF9]
  have h2 := two_le_pRank_three_of_elemAb9 hFH hF' hF'9
  omega

end CFSG.Quasithin.H13.L829NK
