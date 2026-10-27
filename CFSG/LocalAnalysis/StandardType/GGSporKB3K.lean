module

public import CFSG.LocalAnalysis.StandardType.GGSporKF1F4At
public import CFSG.LocalAnalysis.StandardType.GGSporKB3Heis
public import CFSG.LocalAnalysis.StandardType.GGSporKB3Comp
public import CFSG.Sporadic.Bridge.BBound
import CFSG.LocalAnalysis.StandardType.GGSporKBMBridgeZ
import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
import CFSG.LocalAnalysis.StandardType.GGSporKCompConj
import CFSG.LocalAnalysis.StandardType.GGSporKF1F4Conj
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BRank0

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23

theorem ggSporK_bmPCentralF1F4_B_three_native
    :
    BMPCentralF1 3 NativeSporadic.B ∧ BMPCentralF4 3 NativeSporadic.B := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨z, hzo, hzrk, hz14⟩ := ggSporK_bThree_F1F4_z
  have hzc : IsConj z (phiB (t3 1)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.B3B.isConj_phiB_t3_one_of_rk hzo hzrk
  have key : ∀ x : NativeSporadic.B, orderOf x = 3 →
      (∀ C : Subgroup NativeSporadic.B,
        ¬ LargeEvenPComponent 3 (Subgroup.centralizer ({x} : Set NativeSporadic.B)) C) →
      BMPCentralF1At 3 x ∧ BMPCentralF4At 3 x := by
    intro x hx hno
    by_cases hinv : ∃ d : NativeSporadic.B, CFSG.Monster.GMS.BabyInv 0 d ∧ d * x * d⁻¹ = x⁻¹
    · obtain ⟨d, hd, hdx⟩ := hinv
      obtain ⟨J, hJ⟩ := ggSporK_bThree_component_of_inverted hx hd hdx
      exact (hno J hJ).elim
    · have hnot0 : ¬ IsConj x (phiB (t3 0)) := by
        intro hc
        obtain ⟨d, hd, hdr⟩ := phiB_t3_zero_inverted
        obtain ⟨c, hcx⟩ := isConj_iff.1 hc
        refine hinv ⟨c⁻¹ * d * c, CFSG.Monster.GMS.BabyInv.of_isConj hd
          (isConj_iff.2 ⟨c⁻¹, by simp⟩), ?_⟩
        have hx' : x = c⁻¹ * phiB (t3 0) * c := by rw [← hcx]; group
        calc c⁻¹ * d * c * x * (c⁻¹ * d * c)⁻¹
            = c⁻¹ * (d * phiB (t3 0) * d⁻¹) * c := by rw [hx']; group
          _ = x⁻¹ := by rw [hdr, hx']; group
      have hxc : IsConj x (phiB (t3 1)) := by
        obtain ⟨i, hi⟩ := bThree_classes x hx
        fin_cases i
        · exact absurd hi hnot0
        · exact hi
        · exact absurd (hi.trans bThreeRc_holds) hnot0
        · exact hi.trans bThreeRd_holds
      obtain ⟨m, hm⟩ := isConj_iff.1 (hxc.trans hzc.symm)
      have hm' : m * x * m⁻¹ = z ^ 1 := by rw [pow_one]; exact hm
      have hnoz : ∀ C : Subgroup NativeSporadic.B,
          ¬ LargeEvenPComponent 3 (Subgroup.centralizer ({z} : Set NativeSporadic.B)) C := by
        intro C hC
        obtain ⟨C', hC'⟩ := bmPComponent_of_conj_pow Nat.prime_three hzo (k := 1) (by norm_num)
          hm' ⟨C, hC⟩
        exact hno C' hC'
      exact bmPCentralF1At_F4At_of_conj_pow Nat.prime_three hzo (k := 1) (by norm_num) hm'
        (hz14 hnoz)
  exact ⟨fun x hx hno => (key x hx hno).1, fun x hx hno => (key x hx hno).2⟩

theorem ggSporK_bmPCentralF1F4_B_three
    [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BMPCentralF1 3 (TauCeti.CFSGIndex.sporadic .B).Group ∧
      BMPCentralF4 3 (TauCeti.CFSGIndex.sporadic .B).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  let e' : CFSG.Blueprint.NativeSporadic.B ≃* (TauCeti.CFSGIndex.sporadic .B).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite CFSG.Blueprint.NativeSporadic.B := Finite.of_equiv _ e'.symm.toEquiv
  have h := ggSporK_bmPCentralF1F4_B_three_native
  exact ⟨@bmPCentralF1_of_mulEquiv CFSG.Blueprint.NativeSporadic.B
      (TauCeti.CFSGIndex.sporadic .B).Group _ _ _ _ 3 e' h.1,
    @bmPCentralF4_of_mulEquiv CFSG.Blueprint.NativeSporadic.B
      (TauCeti.CFSGIndex.sporadic .B).Group _ _ _ _ 3 e' h.2⟩

theorem ggSporK_bmCentreZ_B_three
    [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BMCentreZ 3 (TauCeti.CFSGIndex.sporadic .B).Group :=
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  bmCentreZ_of_F1_F4 3 _ ggSporK_bmPCentralF1F4_B_three.1 ggSporK_bmPCentralF1F4_B_three.2

end CFSG.StandardType.SporadicShape
