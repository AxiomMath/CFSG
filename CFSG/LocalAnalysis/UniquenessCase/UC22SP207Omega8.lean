module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Coxeter
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Datum
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Transfer
import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ASVolI.ChIJK CFSG.GH74.BNPair CFSG.GroupActions CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.GH74.GLS.SP CFSG.Assembly.LowTwoRank

theorem uc22sp207_hasCentralLongest_Omega8m {X : Type} [Group X] {n : ℕ} (h : IsOmega8m X n) :
    HasCentralLongest X := by
  obtain ⟨⟨hp, hf, hn⟩, F, hFf, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : CharP F 2 := burnsideI2BN_charP_of_card hp hf hcard
  have : Finite (spinGroup (quadMinus 4 F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hct := minusDatum_isCTGroupDatum 4 hirr hn
  have hext := minusDatum_steinbergExtras 4 hirr
  have hN := cartan_normal_of_datum hct hext
  have : Finite (coxeterMatrix (isFiniteType_cartanB 3)).Group :=
    Finite.of_equiv _ (weylEquiv hct hext).toEquiv
  have hz := uc22sp207_exists_central_longest_B3
    (coxeterMatrix (isFiniteType_cartanB 3)).toCoxeterSystem (p := (0 : Fin 3))
    (l := (1 : Fin 3)) (π := (2 : Fin 3)) (by decide) (by decide) (by decide) (by decide)
    (OddCT.coxeterMatrix_of_succ (n := 3) (i := 0) (j := 1) rfl (by decide))
    (OddCT.coxeterMatrix_of_succ_last (n := 3) (i := 1) (j := 2) rfl rfl)
    (OddCT.coxeterMatrix_of_far (n := 3) (i := 0) (j := 2) (by decide) (by decide) (by decide))
  have hdvd : 2 ∣ Nat.card F := hcard ▸ dvd_pow_self 2 (by omega)
  have hSpin : HasCentralLongest ↥(spinGroup (quadMinus 4 F b c)) :=
    uc22sp207_hasCentralLongest_of_datum (D := minusDatum 4 hirr) (n := minusWeyl 4 hirr)
      (H := minusTorus 4 hirr) hct hext (SpinMinusClosed.bruhatExtras hirr hn)
      (isPGroup_iSup_pos hext fun γ hγ => isPGroup_minusRootGroup hirr hγ) (by
        refine burnsideI2BN_not_dvd_card_of_pow_eq_one (m := Nat.card F ^ 2 - 1) (fun x hx => ?_)
          (burnsideI2BN_not_dvd_sub_one hp (Nat.one_le_pow _ _ Nat.card_pos)
            (dvd_pow hdvd two_ne_zero))
        exact SpinMinusClosed.pow_eq_one_of_mem_iSup
          (fun i h hh => by
            have := SpinMinusClosed.pow_eq_one_of_mem_minusTorus hirr i hh
            rwa [SpinMinusClosed.card_shortField] at this)
          (fun i j h hh h' hh' => hext.torus_commute i j h hh h' hh') hx) hz
  exact hSpin.quotient_center.of_mulEquiv ((spinQuotientCenterEquivQuadMinus hn hirr).trans e.symm)

end CFSG.LocalAnalysis.UniquenessCase.UC22
