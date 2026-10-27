module

public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped commutatorElement

theorem exists_mul_mem_sup_of_commute {G : Type} [Group G] {Q C : Subgroup G} {x : G}
    (hCQ : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c)
    (hx : x ∈ Q ⊔ C) : ∃ q ∈ Q, ∃ c ∈ C, x = q * c := by
  obtain ⟨q, hq, c, hc, hqc⟩ :=
    (CFSG.mem_sup_of_commute (A := Q) (B := C)
      (fun q hq c hc => (hCQ c hc q hq).symm)).mp hx
  exact ⟨q, hq, c, hc, hqc.symm⟩

theorem commutator_mem_center_of_mem_sup {G : Type} [Group G] {Q C : Subgroup G} {x : G}
    (hx : x ∈ Q ⊔ C)
    (hCQ : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c)
    (hQQ : ⁅Q, Q⁆ ≤ (Subgroup.center ↥Q).map Q.subtype)
    {q' : G} (hq' : q' ∈ Q) :
    ⁅x, q'⁆ ∈ (Subgroup.center ↥Q).map Q.subtype := by
  obtain ⟨q, hq, c, hc, rfl⟩ := exists_mul_mem_sup_of_commute hCQ hx
  have hcq' : Commute c q' := hCQ c hc q' hq'
  have hcalc : ⁅q * c, q'⁆ = ⁅q, q'⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hcq'.commutator_eq]
    group
  rw [hcalc]
  exact hQQ (Subgroup.commutator_mem_commutator (H₁ := Q) (H₂ := Q) hq hq')

theorem centralizes_center_of_mem_sup {G : Type} [Group G] {Q C : Subgroup G} {x : G}
    (hx : x ∈ Q ⊔ C)
    (hCQ : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c)
    {z : G} (hz : z ∈ (Subgroup.center ↥Q).map Q.subtype) :
    x * z = z * x := by
  obtain ⟨q, hq, c, hc, rfl⟩ := exists_mul_mem_sup_of_commute hCQ hx
  obtain ⟨zQ, hzQ, hz_eq⟩ := Subgroup.mem_map.mp hz
  rw [← hz_eq]
  have hqz : Commute q (zQ : G) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzQ ⟨q, hq⟩)
  have hcz : Commute c (zQ : G) := hCQ c hc (zQ : G) zQ.2
  exact (hqz.mul_left hcz).eq

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
