module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LieType.TitsSimplicity.Simplicity
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open scoped commutatorElement

private theorem normal_subgroupOf_of_le_normalizer_A04 {G : Type} [Group G] {K N : Subgroup G}
    (hNK : N ≤ K) (hnorm : K ≤ Subgroup.normalizer (N : Set G)) : (N.subgroupOf K).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hNK]
  intro h k hh hk
  exact (Subgroup.mem_normalizer_iff.1 (hnorm hk) h).1 hh

theorem eq_of_map_pCore_eq_top {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hperf : ⁅K, K⁆ = K) {N : Subgroup G} (hNK : N ≤ K)
    (hnorm : K ≤ Subgroup.normalizer (N : Set G))
    (hN : (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) = ⊤) : N = K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hMnorm : (N.subgroupOf K).Normal :=
    normal_subgroupOf_of_le_normalizer_A04 hNK hnorm
  have hperf' : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hperf
  haveI := CFSG.pCore_isNilpotent (p := 2) (G := ↥K)
  have hsup : N.subgroupOf K ⊔ CFSG.pCore 2 ↥K = ⊤ := by
    have h := Subgroup.comap_map_eq (f := QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (N.subgroupOf K)
    rw [hN, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have htop : N.subgroupOf K = ⊤ :=
    CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf' (B := CFSG.pCore 2 ↥K)
      inferInstance hsup
  exact le_antisymm hNK (Subgroup.subgroupOf_eq_top.1 htop)

theorem normal_closure_top {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hperf : ⁅K, K⁆ = K) (hqs : CFSG.Open.IsQuasisimple (Bar2 K)) (X : Subgroup G) (hXK : X ≤ K)
    (hX : ¬ (X.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ≤
      Subgroup.center (Bar2 K)) :
    ∀ N : Subgroup G, N ≤ K → K ≤ Subgroup.normalizer (N : Set G) → X ≤ N → N = K := by
  intro N hNK hnorm hXN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hπker : π.ker = CFSG.pCore 2 ↥K := by
    rw [hπ]; exact QuotientGroup.ker_mk' (CFSG.pCore 2 ↥K)
  set ρ := QuotientGroup.mk' (Subgroup.center (Bar2 K)) with hρ
  have hρker : ρ.ker = Subgroup.center (Bar2 K) := by
    rw [hρ]; exact QuotientGroup.ker_mk' (Subgroup.center (Bar2 K))
  haveI hMnorm : (N.subgroupOf K).Normal :=
    normal_subgroupOf_of_le_normalizer_A04 hNK hnorm
  haveI hMbar_normal : ((N.subgroupOf K).map π).Normal :=
    hMnorm.map π (by rw [hπ]; exact QuotientGroup.mk'_surjective _)
  haveI hQperf : Group.IsPerfect (Bar2 K) := ⟨hqs.1⟩
  haveI hsimple : IsSimpleGroup (Bar2 K ⧸ Subgroup.center (Bar2 K)) := hqs.2
  haveI hMbarRho_normal : (((N.subgroupOf K).map π).map ρ).Normal :=
    hMbar_normal.map ρ (by rw [hρ]; exact QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((N.subgroupOf K).map π).map ρ) with hbot | htop
  · exfalso
    apply hX
    have hcenter : (N.subgroupOf K).map π ≤ Subgroup.center (Bar2 K) := by
      have h : (N.subgroupOf K).map π ≤ ρ.ker :=
        (Subgroup.map_eq_bot_iff ((N.subgroupOf K).map π)).1 hbot
      rwa [hρker] at h
    have hXle : X.subgroupOf K ≤ N.subgroupOf K := fun _ hx => hXN hx
    exact (Subgroup.map_mono (f := π) hXle).trans hcenter
  · have hsup : (N.subgroupOf K).map π ⊔ Subgroup.center (Bar2 K) = ⊤ := by
      have h := Subgroup.comap_map_eq (f := ρ) ((N.subgroupOf K).map π)
      rw [htop, Subgroup.comap_top ρ, hρker] at h
      exact h.symm
    have hMtop : (N.subgroupOf K).map π = ⊤ :=
      CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hQperf
        (B := Subgroup.center (Bar2 K)) inferInstance hsup
    exact eq_of_map_pCore_eq_top hperf hNK hnorm hMtop

theorem normal_closure_top_of_perfect {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hperf : ⁅K, K⁆ = K) (hqs : CFSG.Open.IsQuasisimple (Bar2 K)) (X : Subgroup G) (hXK : X ≤ K)
    (hXperf : ⁅X, X⁆ = X) (hX2 : ¬ IsPGroup 2 ↥X) :
    ∀ N : Subgroup G, N ≤ K → K ≤ Subgroup.normalizer (N : Set G) → X ≤ N → N = K := by
  refine normal_closure_top K hperf hqs X hXK ?_
  intro hle
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hπker : π.ker = CFSG.pCore 2 ↥K := by
    rw [hπ]; exact QuotientGroup.ker_mk' (CFSG.pCore 2 ↥K)
  have hX'perf : ⁅X.subgroupOf K, X.subgroupOf K⁆ = X.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXK, hXperf]
  have hcomm : ⁅(X.subgroupOf K).map π, (X.subgroupOf K).map π⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (hle.trans (Subgroup.center_le_centralizer _))
  have hbot : (X.subgroupOf K).map π = ⊥ := by
    rw [← hX'perf, Subgroup.map_commutator]
    exact hcomm
  have hker : X.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
    have h : X.subgroupOf K ≤ π.ker := (Subgroup.map_eq_bot_iff (X.subgroupOf K)).1 hbot
    rwa [hπker] at h
  have hp : IsPGroup 2 ↥(X.subgroupOf K) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).to_le hker
  exact hX2 (hp.of_equiv (Subgroup.subgroupOfEquivOfLe hXK))

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
