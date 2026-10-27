module

public import CFSG.Quasithin.EmptyFaithful.S153E61DC

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.Quasithin.S153E
open scoped commutatorElement Pointwise MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153E61D

section VU

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N N' : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}

theorem relIndex_VU {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) :
    (VZ T M ⊓ UH153 T M V₁ Mc).relIndex (VZ T M) = 2 := by
  obtain ⟨P', -, h1, h2, -⟩ := d.c54.h53two.perp
  have h := d.c54.h53two.card_Vstar
  rw [h1, ← h2] at h
  exact h

theorem card_VU {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) :
    Nat.card ↥(VZ T M ⊓ UH153 T M V₁ Mc) = 8 := by
  have h := Subgroup.relIndex_mul_card (VZ T M ⊓ UH153 T M V₁ Mc) (VZ T M)
  rw [inf_eq_left.2 (inf_le_left : VZ T M ⊓ UH153 T M V₁ Mc ≤ VZ T M), relIndex_VU d,
    cx.c.hyp.card_VZ] at h
  omega

theorem mul_mem_VU {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) :
    ∀ v ∈ VZ T M, ∀ w ∈ VZ T M, v ∉ UH153 T M V₁ Mc → w ∉ UH153 T M V₁ Mc →
      v * w ∈ UH153 T M V₁ Mc := by
  intro v hv w hw hvU hwU
  have h : ((VZ T M ⊓ UH153 T M V₁ Mc).subgroupOf (VZ T M)).index = 2 := relIndex_VU d
  have hmem := (Subgroup.mul_mem_iff_of_index_two h (a := ⟨v, hv⟩) (b := ⟨w, hw⟩)).2 (by
    constructor
    · intro h1
      exact absurd (Subgroup.mem_subgroupOf.1 h1).2 hvU
    · intro h1
      exact absurd (Subgroup.mem_subgroupOf.1 h1).2 hwU)
  exact (Subgroup.mem_subgroupOf.1 hmem).2

end VU

section Center

variable {G : Type} [Group G]

theorem exists_Z {U : Subgroup G} (hU : CFSG.IsExtraspecial 2 ↥U) : ∃ Z : Subgroup G,
    (∀ u ∈ U, ∀ w ∈ U, u * w * u⁻¹ * w⁻¹ ∈ Z) ∧ (∀ z ∈ Z, ∀ u ∈ U, z * u = u * z) ∧
      (∀ z ∈ Z, z * z = 1) ∧ (∀ z ∈ Z, ∀ z' ∈ Z, z ≠ 1 → z' ≠ 1 → z = z') := by
  have := hU
  have hel := CFSG.IsExtraspecial.quotient_elementary_abelian 2 ↥U
  have hcard := CFSG.IsExtraspecial.center_order_p 2 ↥U
  have hcen : ∀ a b : ↥U, ⁅a, b⁆ ∈ Subgroup.center ↥U := by
    intro a b
    rw [← QuotientGroup.eq_one_iff]
    have h1 := map_commutatorElement (QuotientGroup.mk' (Subgroup.center ↥U)) a b
    have h2 : ⁅(QuotientGroup.mk' (Subgroup.center ↥U)) a, (QuotientGroup.mk' (Subgroup.center ↥U)) b⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (hel.toIsMulCommutative.is_comm.comm _ _)
    exact h1.trans h2
  refine ⟨(Subgroup.center ↥U).map U.subtype, ?_, ?_, ?_, ?_⟩
  · intro u hu w hw
    exact ⟨⁅(⟨u, hu⟩ : ↥U), ⟨w, hw⟩⁆, hcen _ _, rfl⟩
  · rintro z ⟨c, hc, rfl⟩ u hu
    have := Subgroup.mem_center_iff.1 hc ⟨u, hu⟩
    exact congrArg Subtype.val this.symm
  · rintro z ⟨c, hc, rfl⟩
    have h1 : (⟨c, hc⟩ : ↥(Subgroup.center ↥U)) ^ 2 = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have h2 : c * c = 1 := by
      have := congrArg (fun x : ↥(Subgroup.center ↥U) => (x : ↥U)) h1
      simpa [pow_two] using this
    show ((c : ↥U) : G) * ((c : ↥U) : G) = 1
    rw [← Subgroup.coe_mul, h2]
    rfl
  · rintro z ⟨c, hc, rfl⟩ z' ⟨c', hc', rfl⟩ hz hz'
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center ↥U))).1 hcard
    have hc1 : (⟨c, hc⟩ : ↥(Subgroup.center ↥U)) ≠ 1 := fun h => hz (by
      have := congrArg (fun x : ↥(Subgroup.center ↥U) => ((x : ↥U) : G)) h
      simpa using this)
    have hc1' : (⟨c', hc'⟩ : ↥(Subgroup.center ↥U)) ≠ 1 := fun h => hz' (by
      have := congrArg (fun x : ↥(Subgroup.center ↥U) => ((x : ↥U) : G)) h
      simpa using this)
    have := (hy _ hc1).trans (hy _ hc1').symm
    exact congrArg (fun x : ↥(Subgroup.center ↥U) => ((x : ↥U) : G)) this

end Center

end S153E61D

end CFSG.Quasithin
