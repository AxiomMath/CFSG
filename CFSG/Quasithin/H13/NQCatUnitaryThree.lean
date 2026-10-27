module

public import CFSG.Quasithin.H13.NQCatDegreeThree
public import CFSG.Quasithin.H13.LocDblMatrix
public import CFSG.LieType.SteinbergBRUnitaryThreePerfect

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem map_subgroupOf_range_normal {B A : Type*} [Group B] [Group A] (β : B →* A)
    (N : Subgroup B) [N.Normal] : ((N.map β).subgroupOf β.range).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := hx
  obtain ⟨z, hz⟩ := g.2
  refine ⟨z * y * z⁻¹, Subgroup.Normal.conj_mem inferInstance y hy z, ?_⟩
  rw [map_mul, map_mul, map_inv, hz, hyx]
  rfl

theorem unitary_three_embeddable_Ccomponent_quasisimple {G : Type*} [Group G] [Finite G]
    {H B : Subgroup G} (hB : B ∈ cComp H) {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (D : Subgroup (unitarySU p f K 3)) [D.Normal]
    (hD : D ≤ unitaryScalars h 3) (β : ↥B →* unitarySU p f K 3 ⧸ D)
    (hβ : Function.Injective β) : CFSG.IsQuasisimple ↥B := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have : CharP K p := h.charP
  by_contra hnq
  obtain ⟨-, -, -, -, hcomm⟩ := LocDbl.nonquasisimple_Fitting_of_mem_cComp hB hnq
  apply hcomm
  refine LocDbl.commutator_fitting_eq_bot_of_pCore fun ℓ hℓ => ?_
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hBperf : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hB)
  have hB' : ⁅β.range, β.range⁆ = β.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hNB : (CFSG.pCore ℓ ↥B).map β ≤ β.range := by
    rw [MonoidHom.range_eq_map]
    exact map_mono le_top
  have : (CFSG.pCore ℓ ↥B).Normal := CFSG.pCore_normal
  have hNn := map_subgroupOf_range_normal β (CFSG.pCore ℓ ↥B)
  have hNp : IsPGroup ℓ ((CFSG.pCore ℓ ↥B).map β) := CFSG.pCore_isPGroup.map β
  have hcen : ∀ y ∈ CFSG.pCore ℓ ↥B, ∀ b : ↥B, b * y = y * b := by
    intro y hy b
    by_cases hℓp : ℓ = p
    · subst hℓp
      have hbot := CFSG.LieType.unitary_three_perfect_defining_prime_core_trivial
        h D hD hB' hNB hNn hNp
      have hy1 : y = 1 := by
        have : β y ∈ (CFSG.pCore ℓ ↥B).map β := ⟨y, hy, rfl⟩
        rw [hbot, mem_bot] at this
        exact hβ (this.trans (map_one β).symm)
      rw [hy1, mul_one, one_mul]
    · have hDs : ∀ d ∈ D, ∃ c : Kˣ, (d : GL (Fin 3) K) =
          Matrix.GeneralLinearGroup.scalar (Fin 3) c := fun d hd => by
        obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp (hD hd)
        exact ⟨c, hc⟩
      have hc := degree_three_scalar_quotient_normal_coprime_prime_subgroup_central D hDs hB'
        hNB hNn hℓ hℓp hNp
      have hy' : (⟨β y, ⟨y, rfl⟩⟩ : β.range) ∈ center β.range :=
        hc (mem_subgroupOf.mpr ⟨y, hy, rfl⟩)
      have h1 := Subgroup.mem_center_iff.mp hy' ⟨β b, ⟨b, rfl⟩⟩
      apply hβ
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro b _
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hcen y hy b).symm

end CFSG.Quasithin.H13.NQCat
