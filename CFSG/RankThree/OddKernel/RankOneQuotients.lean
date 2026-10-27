module

public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open CFSG.Assembly.RankThreeEven (localRank)

universe u

theorem localRank_quotient_le_of_surjective {G : Type*} [Group G] [Finite G] {p a b : ℕ}
    (hp : 1 < p) (N : Subgroup G) [N.Normal]
    (hab : ∀ (M : Subgroup G) (L : Subgroup (G ⧸ N)) (ψ : M →* L), Function.Surjective ψ →
      pRank p M ≤ a → pRank p L ≤ b)
    (hloc : localRank p G ≤ a) : localRank p (G ⧸ N) ≤ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine csSup_le' ?_
  rintro k ⟨H, ⟨U, hU0, hU2, rfl⟩, rfl⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 (U.comap (QuotientGroup.mk' N))) := inferInstance
  have hlift := sylow_preimage_map_normalizer N U hU2 T
  obtain ⟨hmapT, hnorm, -⟩ := hlift
  obtain ⟨T', hT'⟩ : ∃ T' : Subgroup G, T' = (T : Subgroup (U.comap (QuotientGroup.mk' N))).map
      (U.comap (QuotientGroup.mk' N)).subtype := ⟨_, rfl⟩
  rw [← hT'] at hmapT hnorm
  have hT'2 : IsPGroup 2 T' := hT' ▸ T.isPGroup'.map _
  have hT'0 : T' ≠ ⊥ := fun h => hU0 (by rw [← hmapT, h, Subgroup.map_bot])
  let ψ := ((QuotientGroup.mk' N).domRestrict (normalizer (T' : Set G))).codRestrict
      (normalizer (U : Set (G ⧸ N))) (fun x => hnorm ▸ mem_map_of_mem _ x.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    rw [← hnorm] at hz
    obtain ⟨m, hm, rfl⟩ := mem_map.1 hz
    exact ⟨⟨m, hm⟩, rfl⟩
  have h := hab _ _ ψ hψ ((pRank_normalizer_le_localRank hp hT'0 hT'2).trans hloc)
  change CFSG.Open.pRank p (normalizer (U : Set (G ⧸ N))) ≤ b
  rwa [pRank_eq_pRank_top_subgroup, ← pRank_eq_open_pRank_top]

theorem pRank_le_one_of_surjective {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L : Type*} [Group M]
    [Group L] [Finite M] [Finite L] (ψ : M →* L) (hψ : Function.Surjective ψ)
    (hM : pRank p M ≤ 1) : pRank p L ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow p M) := inferInstance
  have hP₀ : pRank p (P₀ : Subgroup M) ≤ 1 := (pRank_sylow P₀).2 ▸ hM
  have hcyc : IsCyclic (P₀ : Subgroup M) :=
    ((CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification hp P₀.isPGroup').1
      hP₀).resolve_right fun h => hp2 h.1
  have hQ : IsCyclic ((P₀.mapSurjective hψ : Sylow p L) : Subgroup L) := by
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective (ψ.subgroupMap _) (ψ.subgroupMap_surjective _)
  rw [← (pRank_sylow (P₀.mapSurjective hψ)).2]
  exact (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification hp
    (P₀.mapSurjective hψ).isPGroup').2 (Or.inl hQ)

theorem odd_prime_two_local_rank_one_quotients {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type u} [Group G] [Finite G] (N : Subgroup G) [N.Normal] (hloc : localRank p G ≤ 1) :
    localRank p (G ⧸ N) ≤ 1 :=
  localRank_quotient_le_of_surjective hp.one_lt N
    (fun _ _ ψ hψ hM => pRank_le_one_of_surjective hp hp2 ψ hψ hM) hloc

end CFSG.RankThree.OddKernel
