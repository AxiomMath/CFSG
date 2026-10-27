module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.L3Aut

open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conjAct_fix_of_odd {L P : Subgroup G} (hP : IsSylowTwoOf P L) {v : G}
    (hv : v ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), v * b = b * v) {z : ↥L}
    (hz : z ∈ Subgroup.normalizer (((A4.toSylow hP : Sylow 2 ↥L) : Subgroup ↥L) : Set ↥L))
    (hzo : Odd (orderOf z)) : conjAct L ⟨v, hv⟩ z = z := by
  have hz'N : ∀ x : ↥L, x ∈ P.subgroupOf L ↔ z * x * z⁻¹ ∈ P.subgroupOf L := fun x =>
    Subgroup.mem_normalizer_iff.mp hz x
  have hzG : (z : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hgL : g ∈ L := hP.1 hg
      have := (hz'N ⟨g, hgL⟩).mp hg
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hg
      have hgL : (z : G) * g * (z : G)⁻¹ ∈ L := hP.1 hg
      have hgL' : g ∈ L := by
        have h1 : (z : G)⁻¹ * ((z : G) * g * (z : G)⁻¹) * (z : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem z.2) hgL) z.2
        simpa [mul_assoc] using h1
      exact Subgroup.mem_subgroupOf.mp ((hz'N ⟨g, hgL'⟩).mpr (by
        simpa [Subgroup.mem_subgroupOf] using hg))
  have hzo' : Odd (orderOf (z : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hzo
  have hmem : (z : G) ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)) :=
    mem_oTwoUpper_of_odd ⟨z.2, hzG⟩ hzo'
  have hcomm := hc _ hmem
  apply Subtype.ext
  change v * (z : G) * v⁻¹ = (z : G)
  rw [hcomm]
  group

end CFSG.Quasithin.L3Aut
