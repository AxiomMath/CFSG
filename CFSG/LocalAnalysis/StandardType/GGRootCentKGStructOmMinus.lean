module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructOmFrame
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmMinus
import CFSG.LocalAnalysis.StandardType.GGRootCentKGPiece
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus

public section

namespace CFSG.StandardType

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)

section Tags

theorem ggRootCentKGStructTag_POmegaMinus : GGRootCentKGStructTag .POmegaMinus := by
  intro G _ _ p n f ψ _ _ hadm _ hker _ _ hC _ _ r hr _ E _ hEC _ hEinn
  obtain ⟨-, -, hn⟩ := hadm
  have hirr := minusCoeffs_irr 2 f
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (PsiDiag.SpinM.center_eq_bot (K := GaloisField 2 f) hirr hn).le
  have hEψ : E ≤ ψ.range := by
    intro e he
    exact mem_of_mul_mem_centralizer hC
      (PsiDiag.SpinM.exists_mem_centralizer (K := GaloisField 2 f) hirr hn ψ hker (hEinn e he))
  obtain ⟨hr2, γ, ⟨-, hγl⟩, u, hru⟩ := hr
  obtain ⟨i, j, hij, s, t, hst⟩ :=
    RootCentOmega.exists_long_of_ggLongRoot_minus hirr hn (hγl (Or.inr (Or.inl rfl)))
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hEC ⊢
  have hE : E ≤ ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)} := le_inf hEψ hEC
  obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hst).mp hx
  have ha : a ≠ 0 := by
    rintro rfl
    exact hx1 (map_one _)
  rcases (show n ≤ 5 ∨ 6 ≤ n by omega) with hn5 | hn6
  · exact KGOm.exists_kgPieces_minus_small hn hn5 hirr hij s t ha ψ hinj u hE
  · obtain ⟨k, l, m, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm⟩ :=
      RCSTOm.exists_three_ne (by omega : 5 ≤ n - 1) i j
    refine KGOm.exists_kgPieces_hypFrame_five _
      (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) hirr)
      (elementaryGroup_quadMinus_le_omegaGroup hirr hn) ?_ hij hik hil him hjk hjl hjm hkl hkm
      hlm s t ha (spinAction_quadMinus_injective hirr) (range_spinAction_quadMinus hn hirr)
      (spinAction_longRoot_eq_eichler _ hij s t a) ψ hinj u hE
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn hirr]

end Tags

end CFSG.StandardType
