module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructSpLong
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructSpShort
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
import CFSG.LocalAnalysis.StandardType.GGRootCentKGPiece
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpRank
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 CFSG.SeitzReduction.SymplecticPilot

section Tags

theorem ggRootCentKGStructTag_PSp : GGRootCentKGStructTag .PSp := by
  intro G _ _ p n f ψ hp hp2 hadm hrank hker _ _ hC _ hBs r hr _ E _ hEC _ hEinn
  have hn2 : 2 ≤ n := hrank
  obtain ⟨Bs, hBsE, hcard, -, hBsI⟩ := hBs
  have hn4 : 4 ≤ n := by
    let ψs : StatedSp n (GaloisField 2 f) →* G := ψ
    exact AutPSp.four_le_of_bstar (K := GaloisField 2 f) hn2 ψs hker hC hp hp2 hBsE hcard hBsI
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hf : 1 ≤ f := hadm.2.1
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  haveI : NeZero (m + 3) := ⟨by omega⟩
  have hcenter : Subgroup.center (ggU .PSp (m + 3) f).K = ⊥ := AutPSp.center_eq_bot
  have hψ : Function.Injective ψ :=
    (MonoidHom.ker_eq_bot_iff ψ).mp
      (le_antisymm (hker.trans (le_of_eq hcenter)) bot_le)
  have hEψ : E ≤ ψ.range := by
    intro e he
    exact mem_of_mul_mem_centralizer hC
      (PsiDiag.Symp.exists_mem_centralizer (by omega : 2 ≤ m + 3) ψ hker (hEinn e he))
  obtain ⟨u, hu | hu⟩ :=
    KGSp.exists_std_of_rootInvolution (K := GaloisField 2 f) (m := m) hr
  · obtain ⟨i, hi⟩ := hu
    let ψ' : StatedSp (m + 3) (GaloisField 2 f) →* G :=
      ψ.comp (MulAut.conj u).toMonoidHom
    have hψ' : Function.Injective ψ' := RCSTSp.comp_conj_injective hψ u
    have hrange : ψ'.range = ψ.range := RCSTSp.range_comp_conj ψ u
    have hx : ψ' (siegDiag (GaloisField 2 f) i 1) = r := by
      rw [hi]
      rfl
    have hC₀ : ψ.range ⊓ Subgroup.centralizer ({r} : Set G) =
        ψ'.range ⊓ Subgroup.centralizer
          ({ψ' (siegDiag (GaloisField 2 f) i 1)} : Set G) := by
      rw [hrange, hx]
    have hE' : E ≤ ψ'.range ⊓ Subgroup.centralizer
        ({ψ' (siegDiag (GaloisField 2 f) i 1)} : Set G) := by
      rw [← hC₀]
      exact le_inf hEψ hEC
    obtain ⟨𝒥, hcov, hpiece⟩ :=
      KGSp.exists_kgPieces_siegDiag (F := GaloisField 2 f) (m := m) hF
        (by omega : 1 ≤ m) ψ' hψ' i hE'
    refine ⟨𝒥, ?_, ?_⟩
    · intro P hP hPperf
      rw [hC₀] at hP
      exact hcov P hP hPperf
    · intro J hJ
      rw [hC₀]
      exact hpiece J hJ
  · let ψ' : StatedSp (m + 3) (GaloisField 2 f) →* G :=
      ψ.comp (MulAut.conj u).toMonoidHom
    have hψ' : Function.Injective ψ' := RCSTSp.comp_conj_injective hψ u
    have hrange : ψ'.range = ψ.range := RCSTSp.range_comp_conj ψ u
    have hx : ψ' (twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1) = r := by
      rw [hu]
      rfl
    have hC₀ : ψ.range ⊓ Subgroup.centralizer ({r} : Set G) =
        ψ'.range ⊓ Subgroup.centralizer
          ({ψ' (twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1)} : Set G) := by
      rw [hrange, hx]
    have hE' : E ≤ ψ'.range ⊓ Subgroup.centralizer
        ({ψ' (twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1)} : Set G) := by
      rw [← hC₀]
      exact le_inf hEψ hEC
    obtain ⟨𝒥, hcov, hpiece⟩ :=
      KGSp.exists_kgPieces_twoCentralElt (F := GaloisField 2 f) (m := m) hF
        (by omega : 1 ≤ m) ψ' hψ' hE'
    refine ⟨𝒥, ?_, ?_⟩
    · intro P hP hPperf
      rw [hC₀] at hP
      exact hcov P hP hPperf
    · intro J hJ
      rw [hC₀]
      exact hpiece J hJ

end Tags

end CFSG.StandardType
