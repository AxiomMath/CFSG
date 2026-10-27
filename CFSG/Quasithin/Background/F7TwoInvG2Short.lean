module

public import CFSG.Quasithin.Background.F7TwoInvG2Root

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F7Two.G2Ev

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

section Short

variable {K : Type} [Field K] [CharP K 2]

theorem commute_rootElt_self (γ : Fin Tag.G2.rank → ℤ) (x y : K) :
    Commute (rootElt K γ x) (rootElt K γ y) := by
  rw [Commute, SemiconjBy, ← rootElt_add, ← rootElt_add, add_comm]

theorem commute_rootElt_g2a_g2v (x y : K) : Commute (rootElt K g2a x) (rootElt K g2v y) := by
  obtain ⟨-, -, -, -, -, -, -, hav, -⟩ := g2_even_root_commutator_table (R := K) x y
  exact Subtype.ext hav.eq

theorem commute_rootElt_g2v_g2b (x y : K) : Commute (rootElt K g2v x) (rootElt K g2b y) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hvb, -⟩ :=
    g2_even_root_commutator_table (R := K) x y
  exact Subtype.ext hvb.eq

theorem n0_mem_invXiAut {γ : Fin Tag.G2.rank → ℤ} (hγ : IsPos γ) :
    n0 K ∈ invXiAut (MulAut.conj (rootElt K γ 1)) := by
  rw [mem_invXiAut_conj_iff]
  have e : rootElt K γ 1 * n0 K * (rootElt K γ 1)⁻¹ * (n0 K)⁻¹ =
      rootElt K γ 1 * rootElt K (-γ) 1 := by
    calc rootElt K γ 1 * n0 K * (rootElt K γ 1)⁻¹ * (n0 K)⁻¹
        = rootElt K γ 1 * (n0 K * rootElt K γ 1 * (n0 K)⁻¹)⁻¹ := by group
      _ = _ := by rw [n0_conj_rootElt_pos hγ, rootElt_inv]
  rw [e]
  exact not_isPGroup_two_zpowers_rootElt_mul_neg hγ.isRoot

theorem rootReflection_g2b_g2v : rootReflection g2b • g2v = -g2r := by
  rw [rootReflection_smul isRoot_g2b]
  exact List.ofFn_injective (by decide +kernel)

theorem invAutGen_g2_short :
    InvAutGen ↥(adjointGroup .G2 K) (MulAut.conj (rootElt K g2v 1)) := by
  have hn := n0_mem_invXiAut (K := K) isPos_g2v
  have hK := centralizer_le_closure_invXiAut_conj ⟨_, hn⟩
  set H : Subgroup ↥(adjointGroup .G2 K) := Subgroup.closure (invXiAut (MulAut.conj
    (rootElt K g2v 1))) with hH
  have hn0 : n0 K ∈ H := Subgroup.subset_closure hn
  have ha : HasRoot K H g2a := fun x =>
    hK (Subgroup.mem_centralizer_singleton_iff.2 (commute_rootElt_g2a_g2v x 1).eq)
  have hb : HasRoot K H g2b := fun x =>
    hK (Subgroup.mem_centralizer_singleton_iff.2 (commute_rootElt_g2v_g2b 1 x).symm.eq)
  have hv : HasRoot K H g2v := fun x =>
    hK (Subgroup.mem_centralizer_singleton_iff.2 (commute_rootElt_self g2v x 1).eq)
  have ha' : HasRoot K H (-g2a) := hasRoot_neg hn0 isPos_g2a ha
  have hb' : HasRoot K H (-g2b) := hasRoot_neg hn0 isPos_g2b hb
  have hr' : HasRoot K H (-g2r) := by
    have := hasRoot_reflect isRoot_g2b isRoot_g2v hb hb' hv
    rwa [rootReflection_g2b_g2v] at this
  have hr : HasRoot K H g2r := hasRoot_of_neg hn0 isPos_g2r hr'
  exact eq_top_of_hasRoot ha ha' hr hr'

end Short

end CFSG.Quasithin.F7Two.G2Ev
