module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixDispY
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixX
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitFiveCell
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFiveSix
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFarSix
import CFSG.LocalAnalysis.StandardType.GGQTwoDFarSixUnit
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeQuot
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixXTrans
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXFacts
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMemberLe
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFiveSix
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6TwE6
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorHolds
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelModuleOfB2
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem ggQTwoDUnitSix_member (hL1 : GGQTwoL1InputOn fun m => m = 6)
    (hEA : GGQTwoEdgeAmbientInputOn fun m => m = 6) (hLB : GGLBalanceInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (e' : Fin 6 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 6).reindex e') (hcell : qtwoOrthL.compl G L 𝒦) :
    p = 3 ∧ ∃ X Y : Subgroup G, QTwoMemberFacts Bs X M (ggAutomizerJoin L Bs 𝒦) e ∧
      QTwoFrameAt Bs X M (ggAutomizerJoin L Bs 𝒦) e e' ∧ X ≤ ggG0 p B x L D J ∧ X ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = 5 ∧
        Subgroup.center ↥Y = ⊥ := by
  classical
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hmark := ggQTwoDUnit_u62_of_six hRig hTBF hWI hcfg e' hM hcell
  obtain ⟨hp3, K, hKf, hKfin, hKchar, Q, hQ, hQfin, f, ψ, ε, hx, βL, ω, hD, hbase, hω, hxcoord',
    hind, hpermβ, hjoin, hcox, hcoxRoot, hnode⟩ := ggQTwoDUnitSix_coords hTBF hWI hcfg e' hM hmark
  subst hp3
  refine ⟨rfl, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxBs, hxord, hcent⟩ := ggQTwoDUnit_base_cent hcfg rfl
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    have hxC : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hcent]
      exact Subgroup.mem_zpowers x
    exact (Subgroup.mem_inf.mp hxC).2
  have hxcoord := hxcoord' hxBs
  have hK : Nat.card K = 4 := hbase.card_field
  have hψr : ψ.range = NsQuot.img _ f L := hbase.range
  have hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6) := hbase.hyp.ker
  have hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs := by
    intro σ q hq
    have hmem := ((ε σ).1 ⟨q, hq⟩).2
    rw [hbase.perm σ ⟨q, hq⟩] at hmem
    exact hmem
  have hcard : Nat.card ↥Bs = 3 ^ 6 := (Nat.card_congr hD.tau.toEquiv).trans hbase.card_bs
  have hBBs : B ≤ Bs := hcfg.1.1.1.2.1.1
  obtain ⟨u, v, hshape⟩ : ∃ u v : Fin 6, B = Bs ∨ ∀ s : ↥Bs,
      ((s : G) ∈ B ↔ βL (Additive.ofMul s) u = βL (Additive.ofMul s) v) := by
    rcases ggQTwoDUnitSix_B_shape hTBF hWI hcfg e' hM hmark hD hbase hω hind with h | ⟨u, v, -, h⟩
    · exact ⟨0, 0, Or.inl h⟩
    · exact ⟨u, v, Or.inr h⟩
  obtain ⟨a, c, hac, -, -, -, -, b', hb', hb'B⟩ :=
    ggQTwoDUnitSix_selected_coordinates hBBs hshape
  obtain ⟨J₁, hJ₁L, hJ₁perf, hJ₁, hJ₁Z⟩ := ggQTwoDUnitSix_block hK hD hψr hψk c
  obtain ⟨α, -, hα, g, hgJ, hgN, hg⟩ := ggQTwoDUnitSix_signLift hjoin hac
  obtain ⟨Y, hJ₁Y, hJ₂Y, Φ, hΦF, hΦr, hΦZ⟩ := ggQTwoDUnitSix_orthY hRig hLB hcfg hcfg.1.1.2.2.1.1
    hcard hK hD hψr hψk hε hxBs hxord hxL hxcoord hω hind hpermβ hjoin hac hJ₁L hJ₁Z hJ₁ hα hgN
    hg hb' hb'B
  have hb'J : (b' : G) ∈ Subgroup.centralizer (J₁ : Set G) := by
    have hmem : (b' : G) ∈ Subgroup.closure {x, (b' : G)} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rw [← ggQTwoDUnitSix_cent_J hK hD hψk hxBs hxL hxcoord hω hind hJ₁L hJ₁Z hJ₁ hb'] at hmem
    exact (Subgroup.mem_inf.mp hmem).2
  refine ⟨J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom, Y, ?_, ?_, ?_, sup_le hJ₁Y hJ₂Y, Φ, hΦF, hΦr,
    hΦZ⟩
  · exact qtwoMemberFacts_of_le_orth (sup_le hJ₁Y hJ₂Y)
      (qtwoOrthMemberFacts_of_frameCore hcfg.1.1.1.2.1.2.1 Φ hΦF hΦZ)
      (fun r hr => ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr)
      (ggQTwoDUnitSix_X_rankOne hL1 hcfg hM hmark hD hbase hω hind hpermβ hxBs hxL hxcoord hjoin
        hcox hcoxRoot hac hJ₁L hJ₁Z hJ₁ hb' hb'J hα hgN hg)
      (ggQTwoDUnitSix_X_rankTwo hEA hcfg hM hmark hD hbase hω hind hpermβ hxBs hxL hxcoord hjoin
        hcox hcoxRoot hac hJ₁L hJ₁Z hJ₁ hb' hb'J hα hgN hg)
  · exact ggQTwoDUnitSix_X_frame hK hD hψk hε hind hpermβ hxBs hxL hxcoord hac hJ₁L hJ₁Z hJ₁ hb'
      hb'J hα hgN hg hjoin hnode
  · exact qtwoDB22_X_le_ggG0_of hcfg hJ₁L hgJ

theorem ggQTwoCellInputOn_unit_six (hL1 : GGQTwoL1InputOn fun m => m = 6)
    (hEA : GGQTwoEdgeAmbientInputOn fun m => m = 6) (hLB : GGLBalanceInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoCellInputOn (fun m => m = 6) qtwoOrthL.compl := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hcell
  subst hm
  obtain ⟨-, X, _, hfacts, hframe, hG0, -⟩ :=
    ggQTwoDUnitSix_member hL1 hEA hLB hTBF hWI hcfg e' hM hcell
  exact ⟨X, hfacts, hframe, hG0⟩

theorem ggQTwoCellInputOn_unit_fiveSix (hL1 : GGQTwoL1InputOn fun m => m = 6)
    (hEA : GGQTwoEdgeAmbientInputOn fun m => m = 6) (hLB : GGLBalanceInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoCellInputOn (fun m => m = 5 ∨ m = 6) qtwoOrthL.compl :=
  (ggQTwoCellInputOn_unit_five hLB hTBF hWI (ggQTwoRMInputOn_five hTBF hWI)).or
    (ggQTwoCellInputOn_unit_six hL1 hEA hLB hTBF hWI)

theorem ggSecFivePhanDQTwoFiveSix_of_far (hRk1 : GGSecFiveRk1PhanInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hZS : ZS.UseInput) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hRk : GGTwE6ThreeNbrRankInput)
    (hFarOrth : GGQTwoFarInputOn (fun m => m = 6) qtwoOrthL)
    (hFarUnit : GGQTwoFarInputOn (fun m => m = 6) qtwoOrthL.compl) :
    GGSecFivePhanDQTwoFiveSix := by
  have hNonc : GGLNoncyclicInput := ggLNoncyclicInput_holds
  have hRM6 : GGQTwoRMInputOn fun m => m = 6 := ggQTwoRMInputOn_six hTBF hWI hZS
  have hSel : GGQTwoDSelModuleInputOn fun m => m = 6 :=
    ggQTwoDSelModuleInputOn_of_selectedModule (R := fun m => m = 6) (fun m hm => by omega) hTBF hWI
  have hOJ : GGQTwoDOrthJInput := ggQTwoDOrthJInput_holds
  have hTw : GGQTwoDSixTwE6InputOn fun m => m = 6 := ggQTwoDSixTwE6InputOn_of_nbrRank hRk
  exact ggSecFivePhanDQTwoFiveSix_of_leaves hRk1 hTBF hWI hZS hTCJ hLB hPJ hRk
    (ggQTwoCellInputOn_unit_fiveSix
      (ggQTwoL1InputOn_six hNonc hTBF hWI hRM6 hTCJ hLB hPJ hSel hOJ hTw)
      (ggQTwoEdgeAmbientInputOn_six hNonc hTBF hWI hRM6 hTCJ hLB hPJ hSel hOJ hTw) hLB hTBF hWI)
    hFarOrth hFarUnit

theorem ggSecFivePhanDQTwoFiveSix_of_gen (hRk1 : GGSecFiveRk1PhanInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hZS : ZS.UseInput) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hRk : GGTwE6ThreeNbrRankInput) (hgen : GGQTwoSixPlaneGenInput) :
    GGSecFivePhanDQTwoFiveSix := by
  have hEA : GGQTwoEdgeAmbientInputOn fun m => m = 6 :=
    ggQTwoEdgeAmbientInputOn_six ggLNoncyclicInput_holds hTBF hWI (ggQTwoRMInputOn_six hTBF hWI hZS)
      hTCJ hLB hPJ
      (ggQTwoDSelModuleInputOn_of_selectedModule (R := fun m => m = 6) (fun m hm => by omega) hTBF
        hWI)
      ggQTwoDOrthJInput_holds (ggQTwoDSixTwE6InputOn_of_nbrRank hRk)
  exact ggSecFivePhanDQTwoFiveSix_of_far hRk1 hTBF hWI hZS hTCJ hLB hPJ hRk
    (ggQTwoFarInputOn_six_orth hTBF hWI hEA hgen) (ggQTwoFarInputOn_six_unit hEA hLB hTBF hWI hgen)

end CFSG.StandardType.QTwo

end
