module

public import CFSG.LocalAnalysis.StandardType.GGSporKM5Comp
public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
public import Certificates.Certificate716201
import CFSG.LocalAnalysis.StandardType.GGSporKM5Gmat
import CFSG.LocalAnalysis.StandardType.GGSporKM5Comm
import CFSG.LocalAnalysis.StandardType.GGSporKBMBridgeZ
import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
import CFSG.LocalAnalysis.StandardType.GGSporKCompConj
import CFSG.LocalAnalysis.StandardType.GGSporKF1F4Conj

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Assembly CFSG.Monster.Generated CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Dickson.I271

theorem ggSporK_bmPCentralF1F4_gmat_five :
    BMPCentralF1 5 Gmat ∧ BMPCentralF4 5 Gmat := by
  have hzo : orderOf xFiveB = 5 := fiveCommData.orderOf_z
  have key : ∀ s : Gmat, orderOf s = 5 →
      (∀ C : Subgroup Gmat, ¬ LargeEvenPComponent 5 (Subgroup.centralizer ({s} : Set Gmat)) C) →
      BMPCentralF1At 5 s ∧ BMPCentralF4At 5 s := by
    intro s hs hno
    by_cases hinv : InvertedByTwoA s
    · obtain ⟨J, hJ⟩ := gmat_five_pComponent_of_invertedByTwoA hs hinv
      exact (hno J hJ).elim
    · obtain ⟨j, hj, hconj⟩ := MonsterFiveB.m5bClass_of_certs s hs hinv
      obtain ⟨c, hc⟩ := isConj_iff.1 hconj
      have hk : j % 5 ≠ 0 := fun h0 =>
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hj.symm (Nat.dvd_of_mod_eq_zero h0)
      have hno' : ∀ C : Subgroup Gmat,
          ¬ LargeEvenPComponent 5 (Subgroup.centralizer ({xFiveB} : Set Gmat)) C := by
        intro C hC
        obtain ⟨J, hJ⟩ := bmPComponent_of_conj_pow Nat.prime_five hzo hk hc ⟨C, hC⟩
        exact hno J hJ
      exact bmPCentralF1At_F4At_of_conj_pow Nat.prime_five hzo hk hc
        (gmat_bmPCentralF1At_F4At_xFiveB hno')
  exact ⟨fun s hs hno => (key s hs hno).1, fun s hs hno => (key s hs hno).2⟩

theorem ggSporK_bmPCentralF1F4_M_five_of_simple
    [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMPCentralF1 5 (TauCeti.CFSGIndex.sporadic .M).Group ∧
      BMPCentralF4 5 (TauCeti.CFSGIndex.sporadic .M).Group := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  have := hS
  let e' : (TauCeti.CFSGIndex.sporadic .M).Group ≃* CFSG.Blueprint.NativeSporadic.Carrier .M :=
    e.symm.trans (MulEquiv.refl _)
  obtain ⟨f⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := (TauCeti.CFSGIndex.sporadic .M).Group) e'
  have : Finite CFSG.Monster.Generated.Gmat :=
    CFSG.Monster.Generated.generated_rational_group_finite_simple.2.2
  exact ⟨bmPCentralF1_of_mulEquiv 5 f.symm ggSporK_bmPCentralF1F4_gmat_five.1,
    bmPCentralF4_of_mulEquiv 5 f.symm ggSporK_bmPCentralF1F4_gmat_five.2⟩

theorem ggSporK_bmCentreZ_M_five_of_simple
    [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMCentreZ 5 (TauCeti.CFSGIndex.sporadic .M).Group :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  bmCentreZ_of_F1_F4 5 _ (ggSporK_bmPCentralF1F4_M_five_of_simple hS).1
    (ggSporK_bmPCentralF1F4_M_five_of_simple hS).2


end CFSG.StandardType.SporadicShape
