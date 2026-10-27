module

public import CFSG.LocalAnalysis.StandardType.GGSummandStructBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem le_normalizer_inf_of_le {X : Type*} [Group X] {E K V : Subgroup X} (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) :
    E ≤ Subgroup.normalizer ((K ⊓ V : Subgroup X) : Set X) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hK := Subgroup.mem_normalizer_iff.mp (hEK he) x
  have heV : e ∈ V := hEV he
  constructor
  · rintro ⟨hxK, hxV⟩
    exact ⟨hK.mp hxK, V.mul_mem (V.mul_mem heV hxV) (V.inv_mem heV)⟩
  · rintro ⟨hxK, hxV⟩
    refine ⟨hK.mpr hxK, ?_⟩
    have := V.mul_mem (V.mul_mem (V.inv_mem heV) hxV) heV
    simpa [mul_assoc] using this

theorem normal_subgroupOf_sup_of_le_normalizer {X : Type*} [Group X] {E N : Subgroup X}
    (hEN : E ≤ Subgroup.normalizer (N : Set X)) : (N.subgroupOf (E ⊔ N)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
  exact sup_le hEN Subgroup.le_normalizer

theorem normal_pCoreOf_subgroupOf_sup {X : Type} [Group X] {E N : Subgroup X}
    (hEN : E ≤ Subgroup.normalizer (N : Set X)) :
    ((pCoreOf 2 N).subgroupOf (E ⊔ N)).Normal := by
  have hle : pCoreOf 2 N ≤ E ⊔ N := (pCoreOf_le' 2 N).trans le_sup_right
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  refine sup_le ?_ ?_
  · intro e he
    have hN : N.map (MulAut.conj e).toMonoidHom = N := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hEN he) y).mp hy
      · intro hx
        refine ⟨e⁻¹ * x * e, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        have := (Subgroup.mem_normalizer_iff.mp (hEN he) (e⁻¹ * x * e)).mpr
          (by simpa [mul_assoc] using hx)
        exact this
    have hP : (pCoreOf 2 N).map (MulAut.conj e).toMonoidHom = pCoreOf 2 N := by
      rw [← pCoreOf_map_conj 2 N e, hN]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hP]
      exact Subgroup.mem_map_of_mem _ hx
    · intro hx
      rw [← hP] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        simpa [MulAut.conj_apply] using hyx
      rwa [this] at hy
  · intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_pCoreOf' 2 hn hx
    · intro hx
      have := conj_mem_pCoreOf' 2 (N.inv_mem hn) hx
      simpa [mul_assoc] using this

theorem pCoreOf_normal_subgroupOf' {X : Type} [Group X] (p : ℕ) (H : Subgroup X) :
    ((pCoreOf p H).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (pCoreOf_le' p H)]
  intro q h hq hh
  exact conj_mem_pCoreOf' p hh hq

theorem ggSum_normal_subgroupOf_Q {X : Type} [Group X] [Finite X] {E K V Q : Subgroup X}
    {𝒞 : Set (Subgroup X)} (hS : GGSummandStruct E K V Q 𝒞) {S : Subgroup X} (hS𝒞 : S ∈ 𝒞) :
    (Q.subgroupOf S).Normal := by
  obtain ⟨hSN, hQS, -⟩ := hS.2.2 S hS𝒞
  have hQn : (Q.subgroupOf (K ⊓ V)).Normal := hS.1 ▸ pCoreOf_normal_subgroupOf' 2 (K ⊓ V)
  exact ggRCS_normal_subgroupOf hSN hQS hQn

end CFSG.StandardType
