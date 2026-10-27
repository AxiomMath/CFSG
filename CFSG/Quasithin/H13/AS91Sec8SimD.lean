module

public import CFSG.Quasithin.H13.AS91Sec8Map
public import CFSG.Quasithin.Recognition.UniquenessSystemDefs

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94 MulAction
open scoped Pointwise

universe u v u' v'

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]
  {Gb : Type v'} [Group Gb] {Xb : Type u'} [MulAction Gb Xb]
  {x y : X} {xb yb : Xb} {I : Subgroup G} {Ib : Subgroup Gb}

private theorem mem_stabilizer_conj_smul_iff {H : Type*} [Group H] {Y : Type*} [MulAction H Y]
    (j c : H) (a : Y) :
    j⁻¹ * c * j ∈ stabilizer H (j⁻¹ • a) ↔ c ∈ stabilizer H a := by
  rw [mem_stabilizer_iff, mem_stabilizer_iff, mul_smul, mul_smul, smul_inv_smul, inv_smul_eq_iff,
    smul_inv_smul]

theorem IsSimilarity.conj_target {β : ↥(stabilizer G x) ≃* ↥(stabilizer Gb xb)}
    {ζ : ↥I ≃* ↥Ib} (hs : IsSimilarity I x y Ib xb yb β ζ) {j : Gb} (hjI : j ∈ Ib)
    (hjx : j ∈ stabilizer Gb xb) :
    ∃ (β' : ↥(stabilizer G x) ≃* ↥(stabilizer Gb xb)) (ζ' : ↥I ≃* ↥Ib),
      IsSimilarity I x y Ib xb (j⁻¹ • yb) β' ζ' := by
  have hjfix : j • xb = xb := mem_stabilizer_iff.mp hjx
  have hjinv : j⁻¹ • xb = xb := inv_smul_eq_iff.mpr hjfix.symm
  have hpair : j⁻¹ • ({xb, yb} : Set Xb) = {xb, j⁻¹ • yb} := by
    rw [Set.smul_set_insert, Set.smul_set_singleton, hjinv]
  obtain ⟨β', hβ'⟩ : ∃ β' : ↥(stabilizer G x) ≃* ↥(stabilizer Gb xb),
      ∀ g : ↥(stabilizer G x),
        ((β' g : ↥(stabilizer Gb xb)) : Gb) = j⁻¹ * ((β g : ↥(stabilizer Gb xb)) : Gb) * j :=
    ⟨β.trans (MulAut.conj ((⟨j, hjx⟩ : ↥(stabilizer Gb xb))⁻¹)), fun g => by
      simp [MulAut.conj_apply]⟩
  obtain ⟨ζ', hζ'⟩ : ∃ ζ' : ↥I ≃* ↥Ib,
      ∀ g : ↥I, ((ζ' g : ↥Ib) : Gb) = j⁻¹ * ((ζ g : ↥Ib) : Gb) * j :=
    ⟨ζ.trans (MulAut.conj ((⟨j, hjI⟩ : ↥Ib)⁻¹)), fun g => by
      simp [MulAut.conj_apply]⟩
  refine ⟨β', ζ', ?_, ?_, ?_, ?_⟩
  ·
    refine (map_subgroupOf_eq_iff _ _ _).mpr ?_
    intro g
    rw [hζ' g, (map_subgroupOf_eq_iff ζ _ _).mp hs.map_stab g]
    have h := mem_stabilizer_conj_smul_iff j ((ζ g : ↥Ib) : Gb) xb
    rw [hjinv] at h
    exact h.symm
  ·
    intro i h
    rw [hβ' ⟨i, h⟩, hζ' i, hs.eq_on i h]
  ·
    refine (map_subgroupOf_eq_iff _ _ _).mpr ?_
    intro g
    rw [hβ' g, (map_subgroupOf_eq_iff β _ _).mp hs.map_stab_two g]
    exact (mem_stabilizer_conj_smul_iff j _ yb).symm
  ·
    refine (map_subgroupOf_eq_iff _ _ _).mpr ?_
    intro g
    rw [hζ' g, ← hpair, (map_subgroupOf_eq_iff ζ _ _).mp hs.map_edge g]
    exact (mem_stabilizer_conj_smul_iff j _ _).symm

end CFSG.Quasithin.H13.AS91
