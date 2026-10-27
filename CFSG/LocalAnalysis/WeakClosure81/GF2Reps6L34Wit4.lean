module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L34Wit

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.PSL3Four.Native
open CFSG.Quasithin.H.L34Cov
open scoped commutatorElement

@[expose] def a₁ : Equiv.Perm (Fin 42) := wordPerm [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1]

@[expose] def d₁ : Equiv.Perm (Fin 42) := wordPerm [1, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1]

@[expose] def b₂ : Equiv.Perm (Fin 42) := wordPerm [2, 0, 1, 0, 1, 0, 0, 2, 0, 0, 2]

@[expose] def d₂ : Equiv.Perm (Fin 42) := wordPerm [2, 0, 0, 1, 0, 0, 1, 0, 2, 0, 2]

@[expose] def p₁ : Equiv.Perm (Fin 42) := ⁅⁅a₁, g₁⁆, ⁅a₁, d₁⁆⁆

@[expose] def p₂ : Equiv.Perm (Fin 42) := ⁅⁅g₁, b₂⁆, ⁅d₁, d₂⁆⁆

private theorem tabRep_a₁ : TabRep (wordTab [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1]) a₁ :=
  tabRep_wordTab _

private theorem tabRep_a₁_inv :
    TabRep (wordTab (invW [1, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1])) a₁⁻¹ := tabRep_invWord _

private theorem tabRep_d₁ : TabRep (wordTab [1, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1]) d₁ :=
  tabRep_wordTab _

private theorem tabRep_d₁_inv :
    TabRep (wordTab (invW [1, 0, 0, 2, 0, 0, 2, 0, 1, 0, 1])) d₁⁻¹ := tabRep_invWord _

private theorem tabRep_b₂ : TabRep (wordTab [2, 0, 1, 0, 1, 0, 0, 2, 0, 0, 2]) b₂ :=
  tabRep_wordTab _

private theorem tabRep_b₂_inv :
    TabRep (wordTab (invW [2, 0, 1, 0, 1, 0, 0, 2, 0, 0, 2])) b₂⁻¹ := tabRep_invWord _

private theorem tabRep_d₂ : TabRep (wordTab [2, 0, 0, 1, 0, 0, 1, 0, 2, 0, 2]) d₂ :=
  tabRep_wordTab _

private theorem tabRep_d₂_inv :
    TabRep (wordTab (invW [2, 0, 0, 1, 0, 0, 1, 0, 2, 0, 2])) d₂⁻¹ := tabRep_invWord _

private theorem p₁_eq_word :
    p₁ = wordPerm [1, 0, 2, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1] := by
  have h1 := TabRep.commTab tabRep_a₁ tabRep_g₁ tabRep_a₁_inv (tabRep_invWord [0])
  have h2 := TabRep.commTab tabRep_a₁ tabRep_d₁ tabRep_a₁_inv tabRep_d₁_inv
  have h1i := (commutatorElement_inv a₁ g₁).symm ▸
    TabRep.commTab tabRep_g₁ tabRep_a₁ (tabRep_invWord [0]) tabRep_a₁_inv
  have h2i := (commutatorElement_inv a₁ d₁).symm ▸
    TabRep.commTab tabRep_d₁ tabRep_a₁ tabRep_d₁_inv tabRep_a₁_inv
  exact ((TabRep.commTab h1 h2 h1i h2i).beq_iff (tabRep_wordTab _)).mp (by decide +kernel)

private theorem p₂_eq_word :
    p₂ = wordPerm [1, 0, 2, 0, 2, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0] := by
  have h1 := TabRep.commTab tabRep_g₁ tabRep_b₂ (tabRep_invWord [0]) tabRep_b₂_inv
  have h2 := TabRep.commTab tabRep_d₁ tabRep_d₂ tabRep_d₁_inv tabRep_d₂_inv
  have h1i := (commutatorElement_inv g₁ b₂).symm ▸
    TabRep.commTab tabRep_b₂ tabRep_g₁ tabRep_b₂_inv (tabRep_invWord [0])
  have h2i := (commutatorElement_inv d₁ d₂).symm ▸
    TabRep.commTab tabRep_d₂ tabRep_d₁ tabRep_d₂_inv tabRep_d₁_inv
  exact ((TabRep.commTab h1 h2 h1i h2i).beq_iff (tabRep_wordTab _)).mp (by decide +kernel)

private theorem tabRep_r₄_inv : TabRep r₄T r₄⁻¹ :=
  tabRep_r₄.inv tabRep_r₄.1 (by decide +kernel)

private theorem tabRep_r₄_x₃ : TabRep
    (comp 42 (comp 42 (comp 42 r₄T (wordTab [1, 0, 1, 0, 0, 1])) r₄T)
      (wordTab (invW [1, 0, 1, 0, 0, 1]))) (r₄ * x₃ * r₄⁻¹ * x₃⁻¹) :=
  ((tabRep_r₄.comp tabRep_x₃).comp tabRep_r₄_inv).comp tabRep_x₃_inv

theorem p₁_mem : p₁ ∈ ambientDerived C₄ 2 := by
  have hca : a₁ * r₄ = r₄ * a₁ :=
    ((tabRep_a₁.comp tabRep_r₄).beq_iff (tabRep_r₄.comp tabRep_a₁)).mp (by decide +kernel)
  have hcd : d₁ * r₄ = r₄ * d₁ :=
    ((tabRep_d₁.comp tabRep_r₄).beq_iff (tabRep_r₄.comp tabRep_d₁)).mp (by decide +kernel)
  have hcg : g₁ * r₄ = r₄ * g₁ :=
    ((tabRep_g₁.comp tabRep_r₄).beq_iff (tabRep_r₄.comp tabRep_g₁)).mp (by decide +kernel)
  have haC : a₁ ∈ C₄ :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hca, wordPerm_mem _⟩
  have hdC : d₁ ∈ C₄ :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcd, wordPerm_mem _⟩
  have hgC : g₁ ∈ C₄ :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcg, g₁_mem_S⟩
  exact Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator haC hgC)
    (Subgroup.commutator_mem_commutator haC hdC)

theorem p₂_mem : p₂ ∈ ambientDerived C₄ 2 := by
  have hcb : b₂ * r₄ = r₄ * b₂ :=
    ((tabRep_b₂.comp tabRep_r₄).beq_iff (tabRep_r₄.comp tabRep_b₂)).mp (by decide +kernel)
  have hcd : d₁ * r₄ = r₄ * d₁ :=
    ((tabRep_d₁.comp tabRep_r₄).beq_iff (tabRep_r₄.comp tabRep_d₁)).mp (by decide +kernel)
  have hcd₂ : d₂ * r₄ = r₄ * d₂ :=
    ((tabRep_d₂.comp tabRep_r₄).beq_iff (tabRep_r₄.comp tabRep_d₂)).mp (by decide +kernel)
  have hcg : g₁ * r₄ = r₄ * g₁ :=
    ((tabRep_g₁.comp tabRep_r₄).beq_iff (tabRep_r₄.comp tabRep_g₁)).mp (by decide +kernel)
  have hbC : b₂ ∈ C₄ :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcb, wordPerm_mem _⟩
  have hdC : d₁ ∈ C₄ :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcd, wordPerm_mem _⟩
  have hd₂C : d₂ ∈ C₄ :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcd₂, wordPerm_mem _⟩
  have hgC : g₁ ∈ C₄ :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcg, g₁_mem_S⟩
  exact Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator hgC hbC)
    (Subgroup.commutator_mem_commutator hdC hd₂C)

theorem p₁_pow_three : p₁ ^ 3 = 1 := by
  rw [p₁_eq_word]
  exact ((tabRep_wordTab [1, 0, 2, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1]).pow 3).beq_iff
    TabRep.idTab |>.1 (by decide +kernel)

theorem p₂_pow_three : p₂ ^ 3 = 1 := by
  rw [p₂_eq_word]
  exact ((tabRep_wordTab [1, 0, 2, 0, 2, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0]).pow 3).beq_iff
    TabRep.idTab |>.1 (by decide +kernel)

theorem orderOf_r₄_x₃ : orderOf (r₄ * x₃ * r₄⁻¹ * x₃⁻¹) = 4 :=
  orderOf_eq_four_of_tab tabRep_r₄_x₃ (by decide +kernel) (by decide +kernel)

theorem k₃_mul_inv_r₄ :
    k₃ * (r₄ * k₃ * r₄⁻¹)⁻¹ = r₄ * (r₄ * x₃ * r₄⁻¹ * x₃⁻¹) ^ 2 * r₄⁻¹ := by
  have hAi : TabRep (comp 42 (comp 42 r₄T (wordTab (invW [0, 1, 0, 1, 0, 1]))) r₄T)
      (r₄ * k₃ * r₄⁻¹)⁻¹ := by
    rw [show (r₄ * k₃ * r₄⁻¹)⁻¹ = r₄ * k₃⁻¹ * r₄⁻¹ by group]
    exact (tabRep_r₄.comp tabRep_k₃_inv).comp tabRep_r₄_inv
  exact ((tabRep_k₃.comp hAi).beq_iff
    ((tabRep_r₄.comp (tabRep_r₄_x₃.pow 2)).comp tabRep_r₄_inv)).mp (by decide +kernel)

theorem g₁_eq_of_p : g₁ = p₁⁻¹ * p₂⁻¹ := by
  simp only [g₁_eq_word, p₁_eq_word, p₂_eq_word, ← wordPerm_invW, ← wordPerm_append]
  apply wordPerm_eq_of_tab
  decide +kernel

theorem g₂_eq_of_p : g₂ = p₂ * (k₃ * p₁ * k₃⁻¹) * (k₃ * p₂ * k₃⁻¹) * p₂⁻¹ *
    (k₃ * p₁ * k₃⁻¹)⁻¹ * (k₃ * p₂ * k₃⁻¹)⁻¹ * p₂ := by
  simp only [g₂_eq_word, p₁_eq_word, p₂_eq_word, k₃, ← wordPerm_invW, ← wordPerm_append]
  apply wordPerm_eq_of_tab
  decide +kernel

theorem g₃_eq_of_p : g₃ = p₂ * (k₃ * p₁ * k₃⁻¹) * (k₃ * p₂ * k₃⁻¹) * p₂ *
    (k₃ * p₁ * k₃⁻¹)⁻¹ * (k₃ * p₂ * k₃⁻¹)⁻¹ := by
  simp only [g₃_eq_word, p₁_eq_word, p₂_eq_word, k₃, ← wordPerm_invW, ← wordPerm_append]
  apply wordPerm_eq_of_tab
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

end
