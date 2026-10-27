module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG4b
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5
public import CFSG.LocalAnalysis.StandardType.GGLangData

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly

theorem exists_ggModelFamily_langData
    : ∃ Mod : GGModelFamily, GGModelLangData (AlgebraicClosure (ZMod 2)) Mod := by
  have h5 : ∀ (t : StatedLieTag) (n f : ℕ) (ht : GGExcFive t) (_ : GGKnownAdm t n f) (p : ℕ)
      (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f),
      ∃ K : GGKGModel t n f p,
        Nonempty (GGLangData GGL t n f p K.Bfull K.S K.π K.coord) := by
    intro t n f ht hadm p hp hp2 hreg
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hf : 1 ≤ f := hadm.1.2.1
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    obtain ⟨M, hrf, hf5, hw⟩ := G5.ggG5_exists (n := n) ht hf hp hp2 hreg
    exact ⟨{ S := gram t f
             π := piB t p f
             hS := isRootGram_gram f ht
             hπ := piCond_piB p f ht
             Bfull := (M.torusData (n := n) hf hp hp2 hreg).ggBfull
             isElemAbelian := (M.torusData (n := n) hf hp hp2 hreg).ggBfull_isElemAbelian
             diag := M.ggBfull_diag_all hf hp hp2 hreg
             card_full := (M.torusData (n := n) hf hp hp2 hreg).ggBfull_card
             index_inner := (M.torusData (n := n) hf hp hp2 hreg).ggBfull_index_inner_psi hp3
             coord := (M.torusData (n := n) hf hp hp2 hreg).ggCoord
             coord_inj := (M.torusData (n := n) hf hp hp2 hreg).ggCoord_injective
             coord_fixed := (M.torusData (n := n) hf hp hp2 hreg).ggCoord_fixed
             coord_surj_inner := M.ggBfull_coord_surj_inner_all hf hp hp2 hreg
             rf := hrf
             f5 := hf5
             w := hw }, M.langData hf hp hp2 hreg⟩
  choose Mod hMod using h5
  exact ⟨Mod, hMod⟩

end CFSG.StandardType.GGFinModel
