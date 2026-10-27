module

public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6Scalar
public import CFSG.LocalAnalysis.StandardType.PhanEStdRootNodes

public noncomputable section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Phan.PhanE


theorem rootLevi_map_eq_of_le_rankOne_E7 {q : ℕ} (hq : 1 ≤ q)
    (Phi : (ggU .twistedE6 0 q).K →* e7Data_valid.minGroup (GaloisField 2 q))
    (hPhiker : Phi.ker ≤ Subgroup.center (ggU .twistedE6 0 q).K)
    (j : Fin Tag.E7.rank) (v : e7Data_valid.minGroup (GaloisField 2 q))
    (hle : (ggRootLevi (ggU .twistedE6 0 q).D (Pi.single (0 : Fin 4) 1)).map Phi ≤
      (rankOne (e7Datum (GaloisField 2 q)).rootGroup j).map (MulAut.conj v).toMonoidHom) :
    (ggRootLevi (ggU .twistedE6 0 q).D (Pi.single (0 : Fin 4) 1)).map Phi =
      (rankOne (e7Datum (GaloisField 2 q)).rootGroup j).map (MulAut.conj v).toMonoidHom := by
  have hi : rhoPerm (1 : Fin Tag.E6.rank) = 1 := by decide +kernel
  have hp : proj (Pi.single (1 : Fin Tag.E6.rank) 1) = Pi.single (0 : Fin 4) 1 := by
    funext k
    fin_cases k <;> rfl
  have hmodels := exists_selectedSL2Model_twistedE6_fixed hq 1 hi
  rw [hp] at hmodels
  obtain ⟨model, hmodel, -, -⟩ := hmodels
  have hinj : Function.Injective (Phi.comp model.phi) :=
    PsiDiag.injective_comp_of_ker_le_center model.phi model.injective Phi hPhiker
  have hchildrange : (Phi.comp model.phi).range =
      (ggRootLevi (ggU .twistedE6 0 q).D (Pi.single (0 : Fin 4) 1)).map Phi :=
    (MonoidHom.range_comp Phi model.phi).trans (congrArg (Subgroup.map Phi) hmodel)
  have hchildcard :
      Nat.card ((ggRootLevi (ggU .twistedE6 0 q).D (Pi.single (0 : Fin 4) 1)).map Phi) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 q)) := by
    rw [← hchildrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  obtain ⟨phi, hphiinj, hphirange, -, -⟩ :=
    exists_e7_primitive_simpleNode (k := GaloisField 2 q) j
  have hparentcard : Nat.card (rankOne (e7Datum (GaloisField 2 q)).rootGroup j) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 q)) := by
    rw [← hphirange]
    exact (Nat.card_congr (MonoidHom.ofInjective hphiinj).toEquiv).symm
  have hrightcard :
      Nat.card ((rankOne (e7Datum (GaloisField 2 q)).rootGroup j).map
        (MulAut.conj v).toMonoidHom) =
          Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 q)) :=
    (Nat.card_congr ((rankOne (e7Datum (GaloisField 2 q)).rootGroup j).equivMapOfInjective
      (MulAut.conj v).toMonoidHom (MulAut.conj v).injective).toEquiv).symm.trans hparentcard
  exact Subgroup.eq_of_le_of_card_ge hle (hrightcard.trans hchildcard.symm).le

end CFSG.StandardType
