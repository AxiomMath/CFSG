module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Regimes
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces

private lemma l02qj13_subgroupOfEquivOfLe_symm_coe {G : Type*} [Group G] {J L : Subgroup G}
    (hJL : J ≤ L) (j : J) :
    ((((Subgroup.subgroupOfEquivOfLe hJL).symm j : J.subgroupOf L) : L) : G) = (j : G) := by
  have h1 := Subgroup.subgroupOfEquivOfLe_apply_coe hJL
    ((Subgroup.subgroupOfEquivOfLe hJL).symm j)
  rw [MulEquiv.apply_symm_apply] at h1
  exact h1.symm

theorem q1_marking_of_component_conclusion {G : Type} [Group G] {p : ℕ} {Bs L J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hJL : J ≤ L)
    (hNJ : Bs ≤ Subgroup.normalizer (J : Set G)) {lab : LargeEvenLabel}
    {Rel : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (h : Q1ComponentConclusion p lab (ggGamma L hN).range (J.subgroupOf L) Rel) :
    CFSG.StandardType.LargeEvenMarking J (fun labJ _ _ IJ _ θJ =>
      Rel p lab labJ ∧ Bs ≤ Subgroup.normalizer (J : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ IJ,
          LargeEvenInduces θJ (fun j j' => (j' : G) = b⁻¹ * j * b) φ) := by
  unfold Q1ComponentConclusion at h
  refine CFSG.StandardType.largeEvenMarking_congr
    (Subgroup.subgroupOfEquivOfLe hJL).symm ?_ h
  intro lab R _ I F θ hθ
  obtain ⟨hRel, _, hInd⟩ := hθ
  refine ⟨hRel, hNJ, ?_⟩
  intro b hb
  obtain ⟨φ, hφI, hφ⟩ := hInd (ggGamma L hN ⟨b⁻¹, inv_mem hb⟩)
    (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  refine ⟨φ, hφI, ?_⟩
  intro j j' hj
  have key : (fun u u' : ↥(J.subgroupOf L) =>
      ggGamma L hN ⟨b⁻¹, inv_mem hb⟩ (u : ↥L) = (u' : ↥L))
      ((Subgroup.subgroupOfEquivOfLe hJL).symm j)
      ((Subgroup.subgroupOfEquivOfLe hJL).symm j') := by
    apply Subtype.ext
    rw [ggGamma_coe, l02qj13_subgroupOfEquivOfLe_symm_coe hJL j,
      l02qj13_subgroupOfEquivOfLe_symm_coe hJL j', hj]
    simp
  have hh := hφ ((Subgroup.subgroupOfEquivOfLe hJL).symm j)
    ((Subgroup.subgroupOfEquivOfLe hJL).symm j') key
  simpa only [MulEquiv.trans_apply, centerQuotCongr_mk] using hh

end CFSG.StandardType
