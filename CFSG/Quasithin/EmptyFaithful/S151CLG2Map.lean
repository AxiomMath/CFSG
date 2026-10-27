module

public import CFSG.Quasithin.EmptyFaithful.S151CLG2Step
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.L239

theorem RankTwoPar.map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] [Finite Y'] {U : Subgroup Y}
    {P : Fin 2 → Subgroup Y} (h : RankTwoPar Y U P) (e : Y ≃* Y') :
    RankTwoPar Y' (U.map e.toMonoidHom) (fun j => (P j).map e.toMonoidHom) where
  pkg := h.pkg.map e
  inv := by
    intro α' hα' j
    set α : MulAut Y := e.trans (α'.trans e.symm) with hα
    have hαU : U.map α.toMonoidHom = U := by
      have h1 := hα'
      rw [map_comm_equiv] at h1
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h1
    have h2 := h.inv α hαU j
    rw [map_comm_equiv, ← hα, h2]
  good j := (h.good j).map e

theorem RankTwoPar.exists_of_equiv {Y C : Type} [Group Y] [Group C] [Finite Y] [Finite C]
    (e : Y ≃* C) {U₀ : Subgroup C} {P₀ : Fin 2 → Subgroup C} (h : RankTwoPar C U₀ P₀)
    (hU₀ : IsSylowTwoOf U₀ ⊤) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, RankTwoPar Y U P := by
  have h1 := h.map e.symm
  have hU₁ := CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_map_top e.symm hU₀
  obtain ⟨k, -, hk⟩ :=
    (isSylowTwoOf_iff_isSylowOf.1 hU₁).exists_mem_conj (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : (U₀.map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  refine ⟨fun j => ((P₀ j).map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom, ?_⟩
  have := h1.map (MulAut.conj k)
  rwa [hconj] at this

end CFSG.Quasithin.CLG2
