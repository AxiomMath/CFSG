module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructOmFrame
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructOmFour
import CFSG.LocalAnalysis.StandardType.GGRootCentKGPiece
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusFour
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.LieType.Universal.Spin.Datum
import CFSG.LieType.Universal.Spin.Forms
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.StandardType

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.RankThree.Classical2 (orthDerived)

section Tags

private theorem exists_kgPieces_POmegaPlus {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hn4 : 4 ≤ n) {ψ : (ggU .POmegaPlus n f).K →* G}
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {r : G}
    (hr : GGRootInvolution (ggU .POmegaPlus n f).D .POmegaPlus ψ r) {E : Subgroup G}
    (hEC : E ≤ Subgroup.centralizer {r})
    (hEinn : ∀ e ∈ E, GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ e) :
    ∃ 𝒥 : Set (Subgroup G),
      (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer {r} → ⁅P, P⁆ = P → P ≤ sSup 𝒥) ∧
      ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer {r}) E J := by
  have hn : 3 ≤ n := by omega
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hker hC hr hEinn
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn).le
  have hEψ : E ≤ ψ.range := fun e he => mem_of_mul_mem_centralizer hC
    (PsiDiag.SpinP.exists_mem_centralizer (K := GaloisField 2 f) hn ψ hker (hEinn e he))
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 hEC ⊢
  have hE : E ≤ ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)} := le_inf hEψ hEC
  obtain ⟨i, j, hij, s, t, -, hX⟩ := exists_plusRootGroup_eq (K := GaloisField 2 f) hn hγ
  have hx' : x ∈ ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t).range := hX ▸ hx
  obtain ⟨c₀, rfl⟩ := hx'
  have hc : Multiplicative.toAdd c₀ ≠ 0 := by
    intro h0
    have hc₀ : c₀ = 1 := by rw [← ofAdd_toAdd c₀, h0, ofAdd_zero]
    rw [hc₀, map_one, mul_one, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hσx : spinAction (quadPlus n (GaloisField 2 f))
      ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t c₀) =
      eichler (quadPlus n (GaloisField 2 f)) ((plusFrame n (GaloisField 2 f) hn).vec j t)
        (Multiplicative.toAdd c₀ • (plusFrame n (GaloisField 2 f) hn).vec i s) := by
    rw [← RootCentOmega.spinAction_longRoot_eq_eichler, ofAdd_toAdd]
  have hOE : orthDerived (quadPlus n (GaloisField 2 f)) ≤
      elementaryGroup (quadPlus n (GaloisField 2 f)) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadPlus hn]
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  · obtain ⟨k, l, hik, hil, hjk, hjl, hkl⟩ := RCSTOm.exists_two_ne le_rfl i j
    exact KGOm.exists_kgPieces_frame_four (nondegenerate_polarBilin_quadPlus 4 _)
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE
      (plusFrame 4 (GaloisField 2 f) hn) (fun x hx => RootCentOmega.eq_zero_of_polar_plusVec hx)
      hij hik hil hjk hjl hkl s t hc RootCentOmega.spinAction_quadPlus_injective
      (range_spinAction_quadPlus hn) hσx ψ hinj u hE
  · obtain ⟨k, l, m, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm⟩ :=
      RCSTOm.exists_three_ne hn5 i j
    exact KGOm.exists_kgPieces_hypFrame_five (plusFrame n (GaloisField 2 f) hn)
      (nondegenerate_polarBilin_quadPlus n (GaloisField 2 f))
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE hij hik hil him hjk hjl hjm
      hkl hkm hlm s t hc RootCentOmega.spinAction_quadPlus_injective
      (range_spinAction_quadPlus hn) hσx ψ hinj u hE

theorem ggRootCentKGStructTag_POmegaPlus : GGRootCentKGStructTag .POmegaPlus := by
  intro G _ _ p n f ψ _ _ hadm _ hker _ _ hC _ _ r hr _ E _ hEC _ hEinn
  exact exists_kgPieces_POmegaPlus hadm.2.2 hker hC hr hEC hEinn

end Tags

end CFSG.StandardType
