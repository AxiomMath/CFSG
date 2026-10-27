module

public import CFSG.Quasithin.Background.SimsE215KF1Defs

public import CFSG.Quasithin.Vol2.Ch3E213MSp4
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv

public section

namespace CFSG.Quasithin.SimsE2.KF1

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch3E213M
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiUnipotent antiUnipotentCenter antiUnipotentCenter_comm)

theorem barIn_le_centralizer_of_sp4Data {G : Type} [Group G] {H T M V K : Subgroup G}
    {k : Type} [Field k] [Finite k] [CharP k 2] (D : Sp4Data H T M V K k) :
    barIn M H V ≤ Subgroup.centralizer
      ((barIn M H T ⊓ barIn M H K : Subgroup _) : Set _) := by
  intro v hvV
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hvK : v ∈ kZero H M := D.V_le hvV
  have hxK : x ∈ kZero H M := by
    rw [D.kZero_eq]
    exact hx.2
  have hxT : x ∈ barIn M H T := hx.1
  have hzv : D.θ ⟨v, hvK⟩ ∈ antiUnipotentCenter k :=
    D.V_le_center (Subgroup.mem_map.mpr
      ⟨⟨v, hvK⟩, Subgroup.mem_subgroupOf.mpr hvV, rfl⟩)
  have hzu : D.θ ⟨x, hxK⟩ ∈ antiUnipotent k := by
    rw [← D.sylow]
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr hxT, rfl⟩
  have hcomm := antiUnipotentCenter_comm hzv hzu
  have hkvx : (⟨v, hvK⟩ : ↥(kZero H M)) * ⟨x, hxK⟩ =
      ⟨x, hxK⟩ * ⟨v, hvK⟩ := by
    apply D.θ.injective
    simpa only [map_mul] using hcomm
  exact (congrArg (fun y : ↥(kZero H M) =>
    (y : ↥H ⧸ kerIn (M.subgroupOf H) ⊤)) hkvx).symm

theorem pkgSp4TwoKF1 : PkgSp4TwoKF1 := by
  intro G _ _ H T M V K hS h2 n hn hSp _ _
  obtain ⟨k, _, _, _, _, ⟨D⟩⟩ := exists_sp4Data hS h2 hn hSp
  have hMH : M ≤ H := hS.hyp.minParabolic.maximal.1.le
  have hKH : K ≤ H := hS.eq_sup.symm ▸ le_sup_left
  have hnormH : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hS.eq_sup]
    exact sup_le Subgroup.le_normalizer h2.1
  have hKnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnormH
  have hstarKnormal : (E2.star M H K).Normal :=
    hKnormal.map _ (QuotientGroup.mk'_surjective _)
  have hVKbar : barIn M H V ≤ barIn M H K := by
    rw [← D.kZero_eq]
    exact D.V_le
  have hVK : E2.star M H V ≤ E2.star M H K := by
    rw [← map_barIn_starEquiv hMH V, ← map_barIn_starEquiv hMH K]
    exact Subgroup.map_mono hVKbar
  have hcentBar := barIn_le_centralizer_of_sp4Data D
  have hmapinf : ((barIn M H T ⊓ barIn M H K).map
      (starEquiv hMH).toMonoidHom : Subgroup (E2.StarQuot M H)) =
      E2.star M H T ⊓ E2.star M H K := by
    rw [Subgroup.map_inf (barIn M H T) (barIn M H K) (starEquiv hMH).toMonoidHom
      (starEquiv hMH).injective, map_barIn_starEquiv hMH T, map_barIn_starEquiv hMH K]
  have himage : (starEquiv hMH).toMonoidHom ''
      ((barIn M H T ⊓ barIn M H K : Subgroup _) : Set _) =
      ((E2.star M H T ⊓ E2.star M H K : Subgroup _) : Set _) := by
    rw [← Subgroup.coe_map, hmapinf]
  have hcent : E2.star M H V ≤ Subgroup.centralizer
      ((E2.star M H T ⊓ E2.star M H K : Subgroup _) : Set _) := by
    rw [← map_barIn_starEquiv hMH V]
    have h1 := (Subgroup.map_mono hcentBar).trans
      (CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv (starEquiv hMH)
        ((barIn M H T ⊓ barIn M H K : Subgroup _) : Set _)).le
    rwa [himage] at h1
  exact ⟨E2.star M H K, hstarKnormal, hVK, hcent⟩

end CFSG.Quasithin.SimsE2.KF1
