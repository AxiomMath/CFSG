module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSTrans

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

variable {G : Type} [Group G] [Finite G]

theorem comap_symm_eq_map (σ : MulAut G) (H : Subgroup G) :
    H.comap σ.symm.toMonoidHom = H.map σ.toMonoidHom := by
  rw [Subgroup.comap_equiv_eq_map_symm', MulEquiv.symm_symm]

theorem sigGenConcl_of_map (σ : MulAut G) {P K Q D : Subgroup G}
    (h : SigGenHyp (P.map σ.toMonoidHom) (K.map σ.toMonoidHom) (Q.map σ.toMonoidHom)
      (D.map σ.toMonoidHom) → SigGenConcl (P.map σ.toMonoidHom) (K.map σ.toMonoidHom))
    (hh : SigGenHyp P K Q D) : SigGenConcl P K := by
  have hfi : Function.Injective σ.symm.toMonoidHom := σ.symm.injective
  have hfr : ∀ H : Subgroup G, H ≤ σ.symm.toMonoidHom.range := fun H x _ =>
    ⟨σ x, by simp⟩
  refine SigGenConcl.of_comap _ hfi (hfr P) (hfr K) ?_
  rw [comap_symm_eq_map, comap_symm_eq_map]
  have h' := hh.comap _ hfi (hfr P) (hfr K) (hfr Q)
  rw [comap_symm_eq_map, comap_symm_eq_map, comap_symm_eq_map, comap_symm_eq_map] at h'
  exact h h'

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
