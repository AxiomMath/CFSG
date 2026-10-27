module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameSeven
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameSetup
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameRoot
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameSwap
public import CFSG.LocalAnalysis.StandardType.FS81.RootD6Frame
public import CFSG.LocalAnalysis.StandardType.FS81.CapE7
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthMono
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNativeCentralizer
public import CFSG.LocalAnalysis.StandardType.FS81.E7FramePsiTau

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley

theorem e7FrameAt_of_native (hC : E7NatCent) (hP : E7NatPsi) (hT : E7NatTau) (hA5 : E7NatA5) :
    E7FrameAt := by
  have hC : E7NatCent := e7NatCent_of_doubleCentralizer hC.1
  intro G _ _ b₀ K E hstd B hB hrec
  have hF := e7NatFrame_holds
  have hH := e7NatHigh_holds
  have hW := e7NatWeyl_holds
  obtain ⟨-, ⟨⟨hb₀3, hKC, hKn, hKz, -, hcyc, -, -⟩, -⟩, hrow, -, -, hmax, hAcard, -⟩ := id hstd
  have hKs : IsSimpleGroup ↥K := e7_isSimpleGroup hrow hKz
  have hCK : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn
  have hOut : Subgroup.normalizer (K : Set G) ≤ K ⊔ Subgroup.centralizer (K : Set G) :=
    le_sup_centralizer_of_isRow_E7 hrow le_rfl
  have hNK : Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
    have hA3 : IsPGroup 3 ↥(E ⊓ K) :=
      CFSG.StandardType.TableB.isPGroup_of_isElemAbelian hmax.2.1
    have hAnc : ¬ IsCyclic ↥(E ⊓ K) := by
      refine CFSG.StandardType.TableB.not_isCyclic_of_card (p := 3) (by norm_num) hmax.2.1.2 ?_
      rw [hAcard]
      show 9 ≤ 3 ^ 7
      norm_num
    exact normalizer_zpowers_le_normalizer hKs hKC hKn hcyc (A := E ⊓ K) inf_le_right hA3 hAnc
  obtain ⟨ψ₀⟩ := exists_model hstd
  have hcard := card_realized_centralizer hstd hB
  obtain ⟨ψ, z, hz, hψz⟩ :=
    exists_model_b1 e7TorusRootLines_holds hW hstd hB hrec hcard (hCK.trans hOut) ψ₀
  obtain ⟨n, hnE, hn1, hn0⟩ := exists_swap hstd hB hrec hcard (fus42_of_std hstd hB)
  obtain ⟨σ, hσM, hout, h0, h0', h1, h3, h4, h5, h6, -, hlam, m, hmK, hσnm⟩ :=
    exists_sigma hstd hB hrec hF hH hC hP ψ hz hψz hOut hNK hnE hn1 hn0
  have hK₀ := K0_le_centralizer hstd hB hF hH hC ψ hz hψz hOut hNK hnE hn1 hn0
  have hb₀K₀ : b₀ ∈ (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom :=
    ⟨B.b 1, mem_tr.mpr ⟨z, hz, hψz⟩, hn1⟩
  obtain ⟨R, hRC, hRn, hR3, hCdec, hRK⟩ := exists_R hstd hB hrec
  have hσb : σ * b₀ * σ⁻¹ ∈ K := by
    refine tr_le_K ψ (Jn 0) ?_
    rw [← h0']
    exact ⟨b₀, hb₀K₀, rfl⟩
  obtain ⟨-, hRσ⟩ := e7RootCoreAt_holds G b₀ K E hstd B hB hrec σ hσb
    (root_of_mem_tr_jn0 hW ψ (conj_inv_mem_of_map h0 hb₀K₀)) R hRC hRn hR3
  obtain ⟨U, hU⟩ := e7Frame_inv_of_sigma ψ σ hK₀ hb₀K₀ h0 h0' hσM h1 h3 h4 h5 h6
    (h77_of_sigma hF hC hT hA5 hW ψ σ hK₀ hb₀K₀ hb₀3 hRC hR3 hRK (fun x hx _ => hCdec.le hx) hRσ
      hσM hout h0 h0' h1 h3 h5 h6 hlam)
  have hgN : σ⁻¹ ∈ K ⊔ Subgroup.normalizer (E : Set G) := by
    have hnE' : n ∈ Subgroup.normalizer (E : Set G) := hB.1 ▸ hnE
    rw [hσnm, mul_inv_rev]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (inv_mem hmK))
      (Subgroup.mem_sup_right (inv_mem hnE'))
  exact ⟨U, σ⁻¹, hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.1, hU.2.2.2.2.1, hU.2.2.2.2.2.1, hgN,
    hU.2.2.2.2.2.2⟩

theorem l2ConstructYAt_E7_of_native (hC : E7NatCent) (hP : E7NatPsi) (hT : E7NatTau)
    (hA5 : E7NatA5) : L2ConstructYAt Row.E7 :=
  l2ConstructYAt_E7_of (e7FrameAt_of_native hC hP hT hA5) e7RootCoreAt_holds e7CapAt_holds

theorem l2ConstructYAt_E7_of_nativeAutomorphisms (hP : E7NatPsi) (hT : E7NatTau) :
    L2ConstructYAt Row.E7 :=
  l2ConstructYAt_E7_of_native e7NatCent_holds hP hT e7NatA5_holds

theorem l2ConstructYAt_E7_holds : L2ConstructYAt Row.E7 :=
  l2ConstructYAt_E7_of_nativeAutomorphisms e7NatPsi_holds e7NatTau_holds

end CFSG.StandardType.FrameRoute.FS81.E7Frame
