module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporBK
public import CFSG.Monster.B.TwoA.Base.FullCent
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105InJ
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace BK

open Subgroup CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Open (IsElemAbelian)
open CFSG.QuasithinUnique (IsSylowTwoOf)

theorem hJ_B_of_rank
    (hS1 : ∀ E : Subgroup Cbar, IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 14)
    (hT8 : ∃ (S : Subgroup Dfull) (A : Fin 4 → Subgroup Dfull), S ≤ Jhat ∧ IsPGroup 2 S ∧
      (∀ i, A i ≤ S ∧ IsElemAbelian 2 (A i) ∧ Nat.card (A i) = 2 ^ 14) ∧
      Nat.card (⨅ i, A i : Subgroup Dfull) ≤ 4) :
    ∃ T : Subgroup Cbar, IsSylowTwoOf T ⊤ ∧ T ≤ Jbar ∧
      K105In (normalizer (CFSG.Quasithin.thompsonJ T : Set Cbar)) T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, A, hSJ, hS2, hA, hAc⟩ := hT8
  have hSr : S ≤ iotaD.range := hSJ.trans (Jhat_eq_map ▸ Subgroup.map_le_range iotaD Jbar)
  set S' : Subgroup Cbar := S.comap iotaD
  have hS'J : S' ≤ Jbar := by
    have h := Subgroup.comap_mono (f := iotaD) (hSJ.trans (le_of_eq Jhat_eq_map))
    rwa [Subgroup.comap_map_eq_self_of_injective iotaD_injective] at h
  have hS'2 : IsPGroup 2 S' := hS2.comap_of_injective iotaD iotaD_injective
  have hS''2 : IsPGroup 2 (S'.subgroupOf Jbar) :=
    hS'2.of_equiv (Subgroup.subgroupOfEquivOfLe hS'J).symm
  obtain ⟨P, hP⟩ := hS''2.exists_le_sylow
  obtain ⟨Q, hQ, -⟩ := short_centralizer_quotient_sylow_two.1 P
  set T : Subgroup Cbar := (P : Subgroup Jbar).map Jbar.subtype
  have hT : IsSylowTwoOf T ⊤ := by
    rw [← hQ]
    refine ⟨le_top, Q.isPGroup', ?_⟩
    change ¬ 2 ∣ (Q : Subgroup Cbar).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact Sylow.not_dvd_index Q
  have hTJ : T ≤ Jbar := Subgroup.map_subtype_le _
  have hS'T : S' ≤ T := fun c hc =>
    ⟨⟨c, hS'J hc⟩, hP (Subgroup.mem_subgroupOf.mpr hc), rfl⟩
  set A' : Fin 4 → Subgroup Cbar := fun i => (A i).comap iotaD
  have hcard : ∀ i, Nat.card (A' i) = 2 ^ 14 := fun i => by
    rw [← (hA i).2.2, ← Subgroup.map_comap_eq_self ((hA i).1.trans hSr),
      Subgroup.card_map_of_injective iotaD_injective]
  have hmax : ∀ i, CFSG.Quasithin.IsMaxElemAbelian T (A' i) := fun i =>
    ⟨(Subgroup.comap_mono (hA i).1).trans hS'T, (hA i).2.1.comap iotaD_injective,
      fun B _ hB => (hS1 B hB).trans (hcard i).ge⟩
  have hcap : Nat.card (⨅ i, A' i : Subgroup Cbar) ≤ 4 := by
    have he : (⨅ i, A' i : Subgroup Cbar) = (⨅ i, A i : Subgroup Dfull).comap iotaD :=
      (Subgroup.comap_iInf _ _).symm
    rw [he, ← Subgroup.card_map_of_injective iotaD_injective]
    exact (Subgroup.card_le_of_le (Subgroup.map_comap_le _ _)).trans hAc
  have hzT : xbar ∈ T := ebar_le hT hTJ xbar_mem_Ebar
  have hz : ∀ t ∈ T, t * xbar = xbar * t := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp (Jbar_le_centralizer_xbar (hTJ ht))
  have hz2 : xbar ^ 2 = 1 := by rw [pow_two, xbar_mul_self]
  exact ⟨T, hT, hTJ, k105In_normalizer_thompsonJ_of_iInf hT hzT hz hz2
    (k105In_centralizer_xbar T hT hTJ) A' hmax hcap⟩

end BK

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
