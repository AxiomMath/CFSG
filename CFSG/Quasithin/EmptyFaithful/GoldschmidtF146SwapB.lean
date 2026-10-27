module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146SwapA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace F146Field

variable {G : Type} [Group G] [Finite G]

namespace Swap

theorem bar_swap (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) {T H K : Subgroup G}
    (hsq : SQTKGroup ↥H) (hT : IsSylowTwoOf T H) (hK : K ∈ cComp H) {t : G} (ht : t ∈ T)
    (hne : cjSub t K ≠ K) :
    conjSubgroupsBy ((T.subgroupOf H).map (E2P.barMap H)) (E2P.kbar H K) =
        {E2P.kbar H K, E2P.kbar H (cjSub t K)} ∧
      ⁅E2P.kbar H K, E2P.kbar H (cjSub t K)⁆ = ⊥ ∧
      E2P.kbar H K ⊓ E2P.kbar H (cjSub t K) = ⊥ := by
  have htH : t ∈ H := hT.1 ht
  obtain ⟨-, h2⟩ := h38 _ (E2P.sqtkHypCat_bar hsq) _ (kbar_mem_cComp_top hK)
  have hkb : E2P.kbar H (cjSub t K) = cjSub (E2P.barMap H ⟨t, htH⟩) (E2P.kbar H K) :=
    kbar_cjSub K htH
  have hne' : E2P.kbar H (cjSub t K) ≠ E2P.kbar H K := fun h =>
    hne (kbar_injOn (cjSub_mem_cComp hK htH) hK h)
  have hmem : cjSub (E2P.barMap H ⟨t, htH⟩) (E2P.kbar H K) ∈
      conjSubgroupsBy ((T.subgroupOf H).map (E2P.barMap H)) (E2P.kbar H K) :=
    ⟨_, ⟨⟨t, htH⟩, ht, rfl⟩, rfl⟩
  rcases h2 _ (Swap.isSylowTwoOf_bar hT) with
    ⟨-, hconj, -⟩ | ⟨t', -, -, hconj, -, hcomm, hinf, -, -⟩
  · rw [hconj, Set.mem_singleton_iff] at hmem
    exact absurd (hkb.trans hmem) hne'
  · rw [hconj, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact absurd (hkb.trans h) hne'
    · rw [hkb, h]
      exact ⟨hconj, hcomm, hinf⟩

end Swap

theorem case1_orbit (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) {T H K : Subgroup G}
    (hsq : SQTKGroup ↥H) (hT : IsSylowTwoOf T H) (hK : K ∈ cComp H) {t : G} (ht : t ∈ T)
    (hne : cjSub t K ≠ K) :
    ∀ s ∈ T, cjSub s K = K ∨ cjSub s K = cjSub t K := by
  intro s hs
  obtain ⟨hconj, -, -⟩ := Swap.bar_swap h38 hsq hT hK ht hne
  have hsH : s ∈ H := hT.1 hs
  have hmem : E2P.kbar H (cjSub s K) ∈
      conjSubgroupsBy ((T.subgroupOf H).map (E2P.barMap H)) (E2P.kbar H K) := by
    rw [Swap.kbar_cjSub K hsH]
    exact ⟨_, ⟨⟨s, hsH⟩, hs, rfl⟩, rfl⟩
  rw [hconj, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · exact Or.inl (Swap.kbar_injOn (Swap.cjSub_mem_cComp hK hsH) hK h)
  · exact Or.inr (Swap.kbar_injOn (Swap.cjSub_mem_cComp hK hsH)
      (Swap.cjSub_mem_cComp hK (hT.1 ht)) h)

end F146Field

end CFSG.Quasithin
