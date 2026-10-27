module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecNS
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.H13.P31Sec

section Sup

variable {G : Type} [Group G] (A B : Subgroup G)

theorem normal_subgroupOf_sup (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    (A.subgroupOf (A ⊔ B)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  exact sup_le Subgroup.le_normalizer hB

theorem exists_surj_sup [(A.subgroupOf (A ⊔ B)).Normal] :
    ∃ f : ↥B →* (↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)), Function.Surjective f := by
  have htop : A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self _
  refine ⟨(QuotientGroup.mk' (A.subgroupOf (A ⊔ B))).comp (Subgroup.inclusion le_sup_right), ?_⟩
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx : x ∈ ((A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) : Subgroup ↥(A ⊔ B)) :
      Set ↥(A ⊔ B)) := by
    rw [htop]
    exact Subgroup.mem_top x
  rw [Subgroup.normal_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  refine ⟨⟨(b : G), hb⟩, ?_⟩
  change (QuotientGroup.mk b : ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) = QuotientGroup.mk (a * b)
  rw [QuotientGroup.eq]
  have h := (inferInstance : (A.subgroupOf (A ⊔ B)).Normal).conj_mem a ha b⁻¹
  simpa [mul_assoc] using h

theorem AllNS.sup_of_normalizes {S : Type} [Group S] (hB : B ≤ Subgroup.normalizer (A : Set G))
    (hA : AllNS S ↥A) (hB' : AllNS S ↥B) : AllNS S ↥(A ⊔ B) := by
  haveI := normal_subgroupOf_sup A B hB
  refine AllNS.of_split (A.subgroupOf (A ⊔ B)) ?_ ?_
  · exact AllNS.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm hA
  · obtain ⟨f, hf⟩ := exists_surj_sup A B
    exact AllNS.of_surjective f hf hB'

theorem isSolvable_sup_of_normalizes (hB : B ≤ Subgroup.normalizer (A : Set G))
    (hA : Group.IsSolvable ↥A) (hB' : Group.IsSolvable ↥B) : Group.IsSolvable ↥(A ⊔ B) := by
  haveI := normal_subgroupOf_sup A B hB
  obtain ⟨f, hf⟩ := exists_surj_sup A B
  have h1 : Group.IsSolvable (↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_surjective hf
  have h2 : Group.IsSolvable ↥(A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).injective
  exact Group.isSolvable_of_ker_le_range (A.subgroupOf (A ⊔ B)).subtype
    (QuotientGroup.mk' (A.subgroupOf (A ⊔ B)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Sup

section Family

variable {G : Type} [Group G] {S : Type} [Group S]

theorem allNS_finset_sup {ι : Type} [DecidableEq ι] (f : ι → Subgroup G) (K₀ : Subgroup G)
    (hle : ∀ i, f i ≤ K₀) (hnorm : ∀ i, K₀ ≤ Subgroup.normalizer (f i : Set G))
    (hall : ∀ i, AllNS S ↥(f i)) (s : Finset ι) : AllNS S ↥(s.sup f) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact AllNS.of_solvable
  | insert a s ha ih =>
    rw [Finset.sup_insert]
    exact AllNS.sup_of_normalizes (f a) (s.sup f)
      (Finset.sup_le fun i _ => (hle i).trans (hnorm a)) (hall a) ih

end Family

section Surjection

variable {S : Type} [Group S]

theorem AllNS.of_surjective_solvable_ker {Q Q' : Type} [Group Q] [Group Q'] (φ : Q →* Q')
    (hφ : Function.Surjective φ) (hker : Group.IsSolvable ↥φ.ker) (h : AllNS S Q') :
    AllNS S Q := by
  haveI : φ.ker.Normal := φ.normal_ker
  refine AllNS.of_split φ.ker ?_ ?_
  · haveI := hker
    exact AllNS.of_solvable
  · exact AllNS.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm h

theorem AllNS.of_range_solvable_ker {Q Q' : Type} [Group Q] [Group Q'] (φ : Q →* Q')
    (hker : Group.IsSolvable ↥φ.ker) (h : AllNS S ↥φ.range) : AllNS S Q :=
  AllNS.of_surjective_solvable_ker φ.rangeRestrict φ.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hker) h

end Surjection

end CFSG.Quasithin.H13.P31Sec
