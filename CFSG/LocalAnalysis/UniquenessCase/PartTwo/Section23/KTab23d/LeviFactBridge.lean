module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FlagGeneric
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Quasithin.Vol2.Ch11.SecA (stabW)

variable {W : Type} [CommGroup W] [Finite W]

theorem nonempty_bar2_hinf_pointStab_equiv_of_levi (H : Subgroup (MulAut W)) (S : Sylow 2 ↥H)
    {A : Type} [Group A] :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nonempty (↥(CFSG.Quasithin.perfectCore (H ⊓ stabW (CFSG.fixedPointSubgroup ↥S W))) ⧸
        CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (H ⊓ stabW (CFSG.fixedPointSubgroup ↥S W)))
          ≃* A) →
      Nonempty (Bar2 (Hinf (pointStab H S)) ≃* A) := by
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  intro h
  have heq : (Hinf (pointStab H S)).map H.subtype =
      CFSG.Quasithin.perfectCore (H ⊓ stabW (CFSG.fixedPointSubgroup ↥S W)) := by
    rw [Hinf_map H.subtype (pointStab H S), pointStab_map_eq H S]
    exact (CFSG.Quasithin.perfectCore_eq_map_perfectResidual _).symm
  let eA : ↥(Hinf (pointStab H S)) ≃* ↥(CFSG.Quasithin.perfectCore
      (H ⊓ stabW (CFSG.fixedPointSubgroup ↥S W))) :=
    ((Hinf (pointStab H S)).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr heq)
  obtain ⟨eLev⟩ := h
  exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥(Hinf (pointStab H S)))
    (CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (H ⊓ stabW (CFSG.fixedPointSubgroup ↥S W))))
    eA (CFSG.pCore_map_iso 2 eA)).trans eLev⟩

theorem isL2_bar2_hinf_pointStab_of_levi (H : Subgroup (MulAut W)) (S : Sylow 2 ↥H)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    Nonempty (↥(CFSG.Quasithin.perfectCore (H ⊓ stabW (CFSG.fixedPointSubgroup ↥S W))) ⧸
        CFSG.pCore 2 ↥(CFSG.Quasithin.perfectCore (H ⊓ stabW (CFSG.fixedPointSubgroup ↥S W)))
          ≃* Matrix.SpecialLinearGroup (Fin 2) K) →
      IsL2 (Bar2 (Hinf (pointStab H S))) n := by
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  intro h
  obtain ⟨e⟩ := nonempty_bar2_hinf_pointStab_equiv_of_levi H S h
  exact isL2_of_mulEquiv_sl2 hn hK e

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
