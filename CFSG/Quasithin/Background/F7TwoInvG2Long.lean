module

public import CFSG.Quasithin.Background.F7TwoInvG2Root

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F7Two.G2Ev

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

section Long


variable {K : Type} [Field K] [CharP K 2]

theorem commute_rootElt_g2a_g2c (x y : K) : Commute (rootElt K g2a x) (rootElt K g2c y) := by
  obtain ⟨-, -, -, -, -, -, -, -, hac, -⟩ := g2_even_root_commutator_table (R := K) x y
  exact Subtype.ext hac.eq

theorem commute_rootElt_g2r_g2c (x y : K) : Commute (rootElt K g2r x) (rootElt K g2c y) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrc, -⟩ := g2_even_root_commutator_table (R := K) x y
  exact Subtype.ext hrc.eq

theorem invAutGen_g2_long :
    InvAutGen ↥(adjointGroup .G2 K) (MulAut.conj (rootElt K g2c 1)) := by
  set U : Subgroup ↥(adjointGroup .G2 K) := Subgroup.closure
    {g | ∃ s : K, g = rootElt K g2a s ∨ g = rootElt K g2r s} with hU
  have hUa : ∀ s : K, rootElt K g2a s ∈ U := fun s => Subgroup.subset_closure ⟨s, Or.inl rfl⟩
  have hUr : ∀ s : K, rootElt K g2r s ∈ U := fun s => Subgroup.subset_closure ⟨s, Or.inr rfl⟩
  have hcent : U ≤ Subgroup.centralizer {rootElt K g2c 1} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨s, rfl | rfl⟩
    · exact Subgroup.mem_centralizer_singleton_iff.2 (commute_rootElt_g2a_g2c s 1).eq
    · exact Subgroup.mem_centralizer_singleton_iff.2 (commute_rootElt_g2r_g2c s 1).eq
  have hw : n0 K ∈ invXiAut (MulAut.conj (rootElt K g2c 1)) := by
    rw [mem_invXiAut_conj_iff]
    have e : rootElt K g2c 1 * n0 K * (rootElt K g2c 1)⁻¹ * (n0 K)⁻¹ =
        rootElt K g2c 1 * rootElt K (-g2c) 1 := by
      calc rootElt K g2c 1 * n0 K * (rootElt K g2c 1)⁻¹ * (n0 K)⁻¹
          = rootElt K g2c 1 * (n0 K * rootElt K g2c 1 * (n0 K)⁻¹)⁻¹ := by group
        _ = _ := by rw [n0_conj_rootElt_pos isPos_g2c, rootElt_inv]
    rw [e]
    exact not_isPGroup_two_zpowers_rootElt_mul_neg isRoot_g2c
  refine invAutGen_conj_of_centralizing hcent hw ?_
  have hmap : ∀ g ∈ U, n0 K * g * (n0 K)⁻¹ ∈ U.map (MulAut.conj (n0 K)).toMonoidHom :=
    fun g hg => ⟨g, hg, rfl⟩
  refine eq_top_of_hasRoot (fun s => ?_) (fun s => ?_) (fun s => ?_) (fun s => ?_)
  · exact Subgroup.mem_sup_left (hUa s)
  · rw [← n0_conj_rootElt_pos isPos_g2a]
    exact Subgroup.mem_sup_right (hmap _ (hUa s))
  · exact Subgroup.mem_sup_left (hUr s)
  · rw [← n0_conj_rootElt_pos isPos_g2r]
    exact Subgroup.mem_sup_right (hmap _ (hUr s))

end Long

end CFSG.Quasithin.F7Two.G2Ev
