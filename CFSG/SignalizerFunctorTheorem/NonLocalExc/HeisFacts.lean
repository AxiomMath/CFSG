module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.HeisRoots
public import CFSG.LieType.Chevalley.SimplyLacedCommutation

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

section Basic

variable {τ : Tag}

theorem height_neg' (β : Fin τ.rank → ℤ) : height (-β) = -height β := by
  simp [height]

theorem height_sub' (α β : Fin τ.rank → ℤ) : height (α - β) = height α - height β := by
  simp [height, Finset.sum_sub_distrib]

theorem height_add' (α β : Fin τ.rank → ℤ) : height (α + β) = height α + height β := by
  simp [height, Finset.sum_add_distrib]

theorem simplyLaced_of (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
  rcases hτ with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem isRoot_decodeVec {c : ℕ} (h : c ∈ τ.rootCertificate.roots) :
    IsRoot τ (decodeVec c) := by
  obtain ⟨k, hk, hkc⟩ := List.getElem_of_mem h
  rw [RootCertificate.isRoot_iff τ.rootCertificate_check]
  refine ⟨k, hk, ?_⟩
  simp [RootCertificate.root, hk, hkc]

theorem symmetrizedCartan_eq_cartan_of_E (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    τ.symmetrizedCartan = τ.cartan := by
  rcases hτ with rfl | rfl | rfl <;>
  · change Tag.symmetrizer _ * Tag.cartan _ = _
    rw [show Tag.symmetrizer _ = 1 from rfl, one_mul]

theorem dotProduct_symmetrizedCartan_eq_heisForm (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (x : Fin τ.rank → ℤ) : x ⬝ᵥ (τ.symmetrizedCartan *ᵥ x) = heisForm τ x x := by
  rw [symmetrizedCartan_eq_cartan_of_E hτ]
  simp only [heisForm, dotProduct, mulVec]

theorem not_isRoot_of_heisForm_ne
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {v : Fin τ.rank → ℤ}
    (h : heisForm τ v v ≠ 2) : ¬ IsRoot τ v := fun hv =>
  h ((dotProduct_symmetrizedCartan_eq_heisForm hτ v).symm.trans
    (rootForm_self (simplyLaced_of hτ) hv))

end Basic

structure HeisFacts (τ : Tag) : Prop where
  isRoot_α0 : IsRoot τ (heisα0 τ)
  isRoot_of_mem : ∀ β ∈ heisS τ, IsRoot τ β
  isRoot_sub : ∀ β ∈ heisS τ, IsRoot τ (heisα0 τ - β)
  pos_of_mem : ∀ β ∈ heisS τ, 0 < height β
  two_height_lt : ∀ β ∈ heisS τ, 2 * height β < height (heisα0 τ)
  sub_not_mem : ∀ β ∈ heisS τ, heisα0 τ - β ∉ heisS τ
  not_isRoot_SS : ∀ β ∈ heisS τ, ∀ γ ∈ heisS τ, ¬ IsRoot τ (β + γ)
  not_isRoot_TT : ∀ β ∈ heisS τ, ∀ γ ∈ heisS τ, ¬ IsRoot τ ((heisα0 τ - β) + (heisα0 τ - γ))
  not_isRoot_α0_S : ∀ β ∈ heisS τ, ¬ IsRoot τ (heisα0 τ + β)
  not_isRoot_α0_T : ∀ β ∈ heisS τ, ¬ IsRoot τ (heisα0 τ + (heisα0 τ - β))
  not_isRoot_ST : ∀ γ ∈ heisS τ, ∀ β ∈ heisS τ, γ ≠ β → ¬ IsRoot τ (γ + (heisα0 τ - β))

theorem HeisFacts.of_codeFacts
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h : HeisCodeFacts τ) : HeisFacts τ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hα : heisα0 τ = decodeVec (heisα0Code τ) := rfl
  refine ⟨isRoot_decodeVec h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_heisS.1 hβ
    exact isRoot_decodeVec (h2 c hc)
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_heisS.1 hβ
    obtain ⟨ht1, ht2⟩ := h3 c hc
    rw [← ht2]
    exact isRoot_decodeVec ht1
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_heisS.1 hβ
    exact (h4 c hc).1
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_heisS.1 hβ
    exact (h4 c hc).2
  · intro β hβ hmem
    obtain ⟨c, hc, rfl⟩ := mem_heisS.1 hβ
    obtain ⟨d, hd, hdc⟩ := mem_heisS.1 hmem
    have e1 := (h4 c hc).2
    have e2 := (h4 d hd).2
    have e3 : height (decodeVec (τ := τ) d) =
        height (heisα0 τ) - height (decodeVec (τ := τ) c) := by
      rw [hdc, height_sub']
    have e4 : height (decodeVec (τ := τ) c) = ∑ j, decodeVec (τ := τ) c j := rfl
    have e5 : height (decodeVec (τ := τ) d) = ∑ j, decodeVec (τ := τ) d j := rfl
    have e6 : height (heisα0 τ) = ∑ j, heisα0 τ j := rfl
    omega
  · intro β hβ γ hγ
    obtain ⟨c, hc, rfl⟩ := mem_heisS.1 hβ
    obtain ⟨d, hd, rfl⟩ := mem_heisS.1 hγ
    exact not_isRoot_of_heisForm_ne hτ (h5 c hc d hd)
  · intro β hβ γ hγ
    obtain ⟨c, hc, rfl⟩ := mem_heisS.1 hβ
    obtain ⟨d, hd, rfl⟩ := mem_heisS.1 hγ
    exact not_isRoot_of_heisForm_ne hτ (h6 c hc d hd)
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_heisS.1 hβ
    exact not_isRoot_of_heisForm_ne hτ (h7 c hc)
  · intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_heisS.1 hβ
    exact not_isRoot_of_heisForm_ne hτ (h8 c hc)
  · intro γ hγ β hβ hne
    obtain ⟨c, hc, rfl⟩ := mem_heisS.1 hγ
    obtain ⟨d, hd, rfl⟩ := mem_heisS.1 hβ
    have hcd : c ≠ d := fun h => hne (by rw [h])
    exact not_isRoot_of_heisForm_ne hτ (h9 c hc d hd hcd)

theorem heisFacts_E6
    : HeisFacts .E6 := .of_codeFacts (Or.inl rfl) heisCodeFacts_E6

theorem heisFacts_E7
    : HeisFacts .E7 := .of_codeFacts (Or.inr (Or.inl rfl)) heisCodeFacts_E7

theorem heisFacts_E8
    : HeisFacts .E8 := .of_codeFacts (Or.inr (Or.inr rfl)) heisCodeFacts_E8

end CFSG.SignalizerFunctorTheorem.NonLocalExc
