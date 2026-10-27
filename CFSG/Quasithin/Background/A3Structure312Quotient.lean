module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.A3ComponentsCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace A312

theorem map_mem_cComp {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q] (f : G →* Q)
    {X Y : Subgroup G} (hker : Group.IsSolvable ↥(f.ker ⊓ X)) (hY : Y ∈ cComp X) :
    Y.map f ∈ cComp (X.map f) := by
  have hYX : Y ≤ X := le_of_mem_cComp hY
  have hkerN : Subgroup.normalizer (f.ker : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hNnorm : Y ≤ Subgroup.normalizer ((f.ker ⊓ X : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨by rw [hkerN]; trivial, Subgroup.le_normalizer (hYX hy)⟩
  have h3 := cComp_commutator_perfectCore hY (inf_le_right : f.ker ⊓ X ≤ X) hker hNnorm
  refine ⟨?_, ?_, A3.subnormal_map f (subnormal_of_mem_cComp hY), ?_⟩
  · intro hbot
    have hle : Y ≤ f.ker := (Subgroup.map_eq_bot_iff Y).mp hbot
    have : Group.IsSolvable ↥Y :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_inf hle hYX : Y ≤ f.ker ⊓ X))
        (Subgroup.inclusion_injective _)
    exact not_isSolvable_of_mem_cComp hY this
  · rw [← Subgroup.map_commutator, perfect_of_mem_cComp hY]
  · intro K' hK'lt hK'ne hK'perf hK'sub
    set J : Subgroup G := K'.comap f ⊓ X with hJ
    have hK'le : K' ≤ X.map f := hK'lt.le.trans (Subgroup.map_mono hYX)
    have hJmap : J.map f = K' := by
      refine le_antisymm ((Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le f K')) ?_
      intro k' hk'
      obtain ⟨x, hxX, hx⟩ := hK'le hk'
      exact ⟨x, ⟨show f x ∈ K' from hx ▸ hk', hxX⟩, hx⟩
    have hJsub : IsSubnormal J X := by
      have h1 := A3.subnormal_comap f hK'sub
      exact A3.subnormal_inf_right h1 (Subgroup.le_comap_map f X)
    have hJle : J ≤ Y ⊔ (f.ker ⊓ X) := by
      intro j hj
      have hjf : f j ∈ Y.map f := hK'lt.le (by rw [← hJmap]; exact Subgroup.mem_map_of_mem f hj)
      obtain ⟨y, hy, hyj⟩ := hjf
      have hyj' : y⁻¹ * j ∈ f.ker ⊓ X :=
        ⟨by simp [hyj], X.mul_mem (X.inv_mem (hYX hy)) hj.2⟩
      have : j = y * (y⁻¹ * j) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hy hyj'
    have hcore_le : perfectCore J ≤ Y := (perfectCore_mono hJle).trans h3.2.le
    have hmapcore : (perfectCore J).map f = K' := by
      rw [map_perfectCore, hJmap, perfectCore_eq_self_of_perfect hK'perf]
    have hcore_ne : perfectCore J ≠ ⊥ := by
      intro h
      apply hK'ne
      rw [← hmapcore, h, Subgroup.map_bot]
    have hcore_eq : perfectCore J = Y := by
      by_contra hne
      exact not_subnormal_of_mem_cComp hY (lt_of_le_of_ne hcore_le hne) hcore_ne
        (perfectCore_perfect _) (A3.subnormal_perfectCore hJsub)
    rw [hcore_eq] at hmapcore
    exact hK'lt.ne hmapcore.symm

theorem mem_cComp_subgroupOf {G : Type*} [Group G] [Finite G] {X Y L : Subgroup G}
    (hXL : X ≤ L) (hY : Y ∈ cComp X) : Y.subgroupOf L ∈ cComp (X.subgroupOf L) := by
  have hYX : Y ≤ X := le_of_mem_cComp hY
  have hYL : (Y.subgroupOf L).map L.subtype = Y := Subgroup.map_subgroupOf_eq_of_le (hYX.trans hXL)
  have hXL' : (X.subgroupOf L).map L.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXL
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply ne_bot_of_mem_cComp hY
    rw [← hYL, h, Subgroup.map_bot]
  · apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, hYL, perfect_of_mem_cComp hY]
  · exact A3.subnormal_comap L.subtype (subnormal_of_mem_cComp hY)
  · intro K' hK'lt hK'ne hK'perf hK'sub
    have hKY : K'.map L.subtype < Y := by
      rw [← hYL]
      exact lt_of_le_of_ne (Subgroup.map_mono hK'lt.le) fun h =>
        hK'lt.ne (Subgroup.map_injective L.subtype_injective h)
    have hKne : K'.map L.subtype ≠ ⊥ := fun h =>
      hK'ne ((Subgroup.map_eq_bot_iff_of_injective K' L.subtype_injective).mp h)
    have hKperf : ⁅K'.map L.subtype, K'.map L.subtype⁆ = K'.map L.subtype := by
      rw [← Subgroup.map_commutator, hK'perf]
    have hKsub : IsSubnormal (K'.map L.subtype) X := by
      have := A3.subnormal_map L.subtype hK'sub
      rwa [hXL'] at this
    exact not_subnormal_of_mem_cComp hY hKY hKne hKperf hKsub

theorem isSylowTwoOf_top_map {H K : Type*} [Group H] [Finite H] [Group K] (f : H →* K)
    (hf : Function.Surjective f) {S : Subgroup H} (hS : IsSylowTwoOf S ⊤) :
    IsSylowTwoOf (S.map f) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Finite.of_surjective f hf
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P : Sylow 2 H := hS.2.1.toSylow hidx
  let P' : Sylow 2 K := P.mapSurjective hf
  have hP' : (P' : Subgroup K) = S.map f := Sylow.coe_mapSurjective hf P
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hP']
    exact P'.isPGroup'
  · rw [show ((S.map f).subgroupOf ⊤).index = (S.map f).index from
      Subgroup.relIndex_top_right (S.map f), ← hP']
    exact P'.not_dvd_index

theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(CFSG.oddCore_eq_piCore X).trans (CFSG.pPrimeCore_eq_piCore X 2).symm]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem oddCore_isSolvable (X : Type*) [Group X] [Finite X] :
    Group.IsSolvable ↥(CFSG.oddCore X) :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCore X)

end A312

end CFSG.Quasithin
