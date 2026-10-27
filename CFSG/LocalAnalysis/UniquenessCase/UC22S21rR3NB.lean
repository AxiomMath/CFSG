module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3R136b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3R847
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_21U3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, c.B ≠ ⊥ → Hyp2120 D c →
    (∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) → ∀ p ∈ D.sig,
      ∃ L ∈ calC D.M, ∃ n : ℕ, IsPowTwo n ∧ p ∣ 2 ^ n + 1 ∧ IsU3 (Bar2 L) n

theorem s21_21U3_three_of_r847E3
    (hSE : StronglyEmbeddedFive) (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hS : Standing G) (hUC : rankThreeUC G) (S : Setup G) {Ch : Choice2011 G}
    (h78 : R7_8R3p3 (PartTwo.Three.dataOfSetup hS S))
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h846 : F08.R846 (PartTwo.Three.dataOfSetup hS S))
    (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S))
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h216 : S21_16 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h218 : S21_18 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h2119 : S21_19 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h219 : S21_9Sig3 (PartTwo.Three.dataOfSetup hS S) Ch) :
    S21_21U3 (PartTwo.Three.dataOfSetup hS S) Ch := by
  intro h1930 c hB hH h0 p hp
  have hSig := UC6S846.sigmaStd_dataOfSetup hS S
  have h61 := PartTwo.Three.r6_1_dataOfSetup hS S
  have hS13 := uc22s2121e3_setting13_r847E3 hThin hCyc hSig h61 h847T h211 h216 h218 h219 h2119
    hS.rank h1930 c hH
  obtain ⟨L, K, n, hL, hK, hne, hall, hpL, hpK, hn, hpn, -, hLs, -⟩ :=
    uc22s2121e3_r136b_r847E3 hSE hThin hCyc hS S hS13 hSig h847T h847S h78 h82
      (fun _ hL => uc22s2121e3_shape hThin hCyc hS13 hSig
        (PartTwo.Three.sigmaRankThree13_dataOfSetup hS hUC S) h846
        (uc22s2121e3_r847Four_of_r847E3Thin h847T h61 c hH) hL) hp
      (uc22s13xe_case136b hThin hCyc hSig hS13.hyp131.thinOrU3 hS13.hyp131.normal hS13.sig_eq
        h1930 c hB hH hp) c.hB.2.1
  rcases hLs with ⟨-, h1⟩ | ⟨hU, -⟩
  swap
  · exact ⟨L, hL, n, hn, hpn, hU⟩
  exfalso
  obtain ⟨hpp, -⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  have hns : PartTwo.s13_NormalSimple (Bar2 S.M) := PartTwo.s13_normalSimple hThin _ hS13
  have hLc := PartTwo.s13_barImage_isComponent hL
  have hKc := PartTwo.s13_barImage_isComponent hK
  have hE2 : CFSG.layer (Bar2 S.M) = barImage S.M L ⊔ barImage S.M K := by
    refine le_antisymm ?_ (sup_le (CFSG.LocalCores.component_le_layer hLc)
      (CFSG.LocalCores.component_le_layer hKc))
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun J hJ => ?_
    rcases hall J hJ with rfl | rfl
    exacts [le_sup_left, le_sup_right]
  have hLp : barImage S.M (F13.Lp S.M p) = CFSG.layer (Bar2 S.M) := by
    refine le_antisymm (PartTwo.s13_barImage_Lp_le_layer S.M p) ?_
    rw [PartTwo.s13_barImage_Lp S.M hpp, PartTwo.s13_pElementSubgroup_layer_eq hns hpp, hE2]
    exact sup_le
      (le_iSup₂ (f := fun J (_ : J ∈ PartTwo.s13_compsP (Bar2 S.M) p) => J) _
        (PartTwo.s13_mem_compsP.mpr ⟨hLc, hpL⟩))
      (le_iSup₂ (f := fun J (_ : J ∈ PartTwo.s13_compsP (Bar2 S.M) p) => J) _
        (PartTwo.s13_mem_compsP.mpr ⟨hKc, hpK⟩))
  have hSp : F13.Sp S.M p = Opp p (barPreimage S.M (centE S.M)) :=
    congrArg (fun Y : Subgroup (Bar2 S.M) => Opp p (barPreimage S.M
      (Subgroup.centralizer (Y : Set (Bar2 S.M))))) hLp
  have h0' : CFSG.Open.pRank p (barPreimage S.M (centE S.M)) = 0 := h0 p hp
  have h2 := CFSG.SectionRank.pRank_mono hpp.one_lt
    (F09.opp_le_self p (barPreimage S.M (centE S.M)))
  rw [h0', ← hSp, h1] at h2
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
