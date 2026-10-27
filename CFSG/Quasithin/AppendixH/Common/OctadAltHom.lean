module

public import CFSG.Quasithin.AppendixH.Common.OctadActionRange

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

@[expose] noncomputable def octActAlt {O : Finset (Fin 24)}
    (hO : IsOctad O) : ↥(octStab O) →* ↥(alternatingGroup ↥O) :=
  (octAct O).codRestrict (alternatingGroup ↥O) fun g => by
    rw [← range_octAct hO]
    exact ⟨g, rfl⟩

theorem octActAlt_apply {O : Finset (Fin 24)} (hO : IsOctad O)
    (g : ↥(octStab O)) : ((octActAlt hO g : ↥(alternatingGroup ↥O)) : Equiv.Perm ↥O) = octAct O g :=
  rfl

theorem octActAlt_surjective {O : Finset (Fin 24)}
    (hO : IsOctad O) : Function.Surjective (octActAlt hO) := by
  intro h
  obtain ⟨g, hg⟩ := show (h : Equiv.Perm ↥O) ∈ (octAct O).range by
    rw [range_octAct hO]; exact h.2
  exact ⟨g, Subtype.ext (by rw [octActAlt_apply]; exact hg)⟩

theorem ker_octActAlt {O : Finset (Fin 24)} (hO : IsOctad O) :
    (octActAlt hO).ker = (octFix O).subgroupOf (octStab O) := by
  unfold octActAlt
  rw [MonoidHom.ker_codRestrict, ker_octAct]

theorem eq_octFix_or_eq_octStab_of_normal {O : Finset (Fin 24)}
    (hO : IsOctad O) {N : Subgroup S24} (h1 : octFix O ≤ N) (h2 : N ≤ octStab O)
    (hN : (N.subgroupOf (octStab O)).Normal) : N = octFix O ∨ N = octStab O := by
  set φ := octActAlt hO with hφ
  have hsurj : Function.Surjective φ := by rw [hφ]; exact octActAlt_surjective hO
  have hker : φ.ker = (octFix O).subgroupOf (octStab O) := by
    rw [hφ]; exact ker_octActAlt hO
  have hKleN : (octFix O).subgroupOf (octStab O) ≤ N.subgroupOf (octStab O) :=
    Subgroup.subgroupOf_mono (octStab O) h1
  have hα : 5 ≤ Nat.card ↥O := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hO.1]; norm_num
  haveI : IsSimpleGroup (alternatingGroup ↥O) := alternatingGroup.isSimpleGroup hα
  haveI hmapN : ((N.subgroupOf (octStab O)).map φ).Normal := hN.map φ hsurj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf (octStab O)).map φ) with
    hbot | htop
  ·
    left
    have hle : N.subgroupOf (octStab O) ≤ (octFix O).subgroupOf (octStab O) := by
      intro x hx
      rw [← hker, MonoidHom.mem_ker]
      have hx' : φ x ∈ (N.subgroupOf (octStab O)).map φ := Subgroup.mem_map_of_mem φ hx
      rw [hbot] at hx'
      simpa using hx'
    apply le_antisymm _ h1
    intro n hn
    have hxn : (⟨n, h2 hn⟩ : ↥(octStab O)) ∈ (octFix O).subgroupOf (octStab O) :=
      hle (Subgroup.mem_subgroupOf.mpr hn)
    exact Subgroup.mem_subgroupOf.mp hxn
  ·
    right
    apply le_antisymm h2
    intro x hx
    let g : ↥(octStab O) := ⟨x, hx⟩
    have hg : φ g ∈ (N.subgroupOf (octStab O)).map φ := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨n, hn, hφn⟩ := Subgroup.mem_map.mp hg
    have hker_mem : g * n⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφn, mul_inv_cancel]
    have hKmem : g * n⁻¹ ∈ (octFix O).subgroupOf (octStab O) := by
      rwa [hker] at hker_mem
    have hmem : g * n⁻¹ ∈ N.subgroupOf (octStab O) := hKleN hKmem
    have hgg : g = (g * n⁻¹) * n := by group
    have hgN : g ∈ N.subgroupOf (octStab O) := by
      rw [hgg]
      exact (N.subgroupOf (octStab O)).mul_mem hmem hn
    exact hgN

end CFSG.ASVolI.AppH
