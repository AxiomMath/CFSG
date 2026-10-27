module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

theorem s16h_H5RowSL2_conj (L : Subgroup (MulAut W)) (U Z : Subgroup W) (a : ℕ) (σ : MulAut W)
    (h : s16h_H5RowSL2 L U Z a) :
    s16h_H5RowSL2 (L.map (MulAut.conj σ).toMonoidHom) (U.map σ.toMonoidHom)
      (Z.map σ.toMonoidHom) a := by
  unfold s16h_H5RowSL2 at h
  obtain ⟨hSL, hBN⟩ := h
  refine ⟨?_, ?_⟩
  · unfold IsSLn at hSL ⊢
    obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSL
    exact ⟨K, hKf, hKfin, hKcard,
      ⟨(CFSG.Quasithin.Vol2.Ch10.SecA.conjEquivMap L σ).symm.trans e⟩⟩
  · unfold BinaryNaturalSL at hBN ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hBN
    refine ⟨K, hKf, hKfin, hKcard, ?_⟩
    unfold FFModel.Realizes at hreal ⊢
    obtain ⟨π, hπ⟩ := hreal
    exact ⟨(CFSG.Quasithin.Vol2.Ch10.SecA.conjEquivMap L σ).toMonoidHom.comp π,
      CFSG.Quasithin.Vol2.Ch10.SecA.realizesVia_map_conj hπ σ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
