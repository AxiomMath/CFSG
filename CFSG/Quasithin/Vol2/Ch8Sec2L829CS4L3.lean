module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4Core
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

theorem not_surv2b_of_pRank {G : Type} [Group G] [Finite G] {H K M : Subgroup G} (hKH : K ≤ H)
    (hJ : ∀ x : G, x ∈ kerIn M H ↔
      x ∈ K ⊔ pCoreOf 2 H ∧ ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hn : ∃ n : ℕ, 1 ≤ n ∧
      ((IsPSL 3 2 n (E2.star M H K) ∧ Even n) ∨ E2.IsSp4Prime n (E2.star M H K)))
    (hrank : CFSG.Open.pRank 3 H ≤ 1) : False := by
  obtain ⟨n, hn1, hcase⟩ := hn
  have hrk : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(E2.star M H K)) := by
    rcases hcase with ⟨hL, hev⟩ | hSp
    · exact R3c3.two_le_pRank_three_isPSL_three_two_even hev hL
    · unfold E2.IsSp4Prime at hSp
      by_cases h1 : n = 1
      · rw [if_pos h1] at hSp
        obtain ⟨e⟩ := hSp
        exact R3c3.two_le_pRank_three_alt (le_refl 6) e
      · rw [if_neg h1] at hSp
        exact R3c3.two_le_pRank_three_isPSp_two hSp
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

end CFSG.Quasithin.H13
