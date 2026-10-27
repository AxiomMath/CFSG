module

public import CFSG.Quasithin.Vol2.Ch10SecKRKb

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRK

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem mem_normalizer_subgroupOf_iff {J A : Subgroup Γ} (hA : A ≤ J) (g : ↥J) :
    g ∈ Subgroup.normalizer ((A.subgroupOf J : Subgroup ↥J) : Set ↥J) ↔
      (g : Γ) ∈ Subgroup.normalizer (A : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg v
    constructor
    · intro hv
      have := (hg ⟨v, hA hv⟩).mp (by rw [Subgroup.mem_subgroupOf]; exact hv)
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    · intro hv
      have hvJ : v ∈ J := by
        have h1 : (g : Γ) * v * (g : Γ)⁻¹ ∈ J := hA hv
        have := J.mul_mem (J.mul_mem (J.inv_mem g.2) h1) g.2
        simpa [mul_assoc] using this
      have := (hg ⟨v, hvJ⟩).mpr (by rw [Subgroup.mem_subgroupOf]; exact hv)
      rw [Subgroup.mem_subgroupOf] at this
      exact this
  · intro hg v
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hg v

namespace K1Hyp

variable {H R J L V₁ : Subgroup Γ} (h : K1Hyp H R J L V₁)
include h

theorem lift_hyp :
    ∃ (I : Type) (_ : Group I) (_ : Finite I) (π : I →* QJ J), Function.Surjective π ∧
      π.ker ≤ Subgroup.center I ∧ IsPGroup 2 π.ker ∧
      ⁅(⊤ : Subgroup I), (⊤ : Subgroup I)⁆ = ⊤ ∧
      ∃ W : Subgroup I, W.map π = imJ J V₁ ∧
        Subgroup.normalizer (W : Set I) ≤
          Subgroup.normalizer (((imJ J L).comap π : Subgroup I) : Set I) := by
  refine ⟨↥J, inferInstance, inferInstance, piJ J, QuotientGroup.mk'_surjective _, ?_,
    isPGroup_ker_piJ, ?_, V₁.subgroupOf J, rfl, ?_⟩
  · rw [QuotientGroup.ker_mk']
    exact h.pCore_le_center
  · have hp := h.quasi.1
    rw [Group.isPerfect_def, commutator_def] at hp
    exact hp
  · intro g hg
    have hgV := (mem_normalizer_subgroupOf_iff (h.vle.trans h.le) g).mp hg
    have hgL : g ∈ Subgroup.normalizer ((L.subgroupOf J : Subgroup ↥J) : Set ↥J) :=
      (mem_normalizer_subgroupOf_iff h.le g).mpr (h.vJ ⟨g.2, hgV⟩)
    exact Subgroup.le_normalizer_comap _ (Subgroup.le_normalizer_map _ ⟨g, hgL, rfl⟩)

end K1Hyp

end CFSG.Quasithin.Vol2.Ch10.SecC.KRK
