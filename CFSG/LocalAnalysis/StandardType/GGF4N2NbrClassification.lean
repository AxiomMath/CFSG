module

public import CFSG.LocalAnalysis.StandardType.GGF4N2NbrReflection
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.StandardType.GGTPNA3PlusFinal
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsCover
import CFSG.LocalAnalysis.StandardType.GGResQTwoLinearJ
import CFSG.LocalAnalysis.StandardType.GGK0ExcB3Holds
import CFSG.LocalAnalysis.StandardType.GGF4N2NbrReflectionMinus
import CFSG.LocalAnalysis.StandardType.GGF4N2TorusTraceWitness

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Classification


private theorem ggF4N2_five_dvd_card_J
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra) (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hK : GGCentralImage .PSL 6 2 K) :
    5 ∣ Nat.card J := by
  obtain ⟨-, ⟨F0, hField0, hFinite0, hChar0, hF0, ⟨eJ⟩⟩, -⟩ :=
    ggF4N2J_original_mixed_recognition hR hNbr hL hK
  letI : Field F0 := hField0
  letI : Finite F0 := hFinite0
  have hcardJ : Nat.card J = Nat.card (Matrix.SpecialLinearGroup (Fin 4) F0) :=
    Nat.card_congr eJ.toEquiv
  rw [hcardJ, CFSG.OrderReductions.LinearOrders.card_specialLinear F0 4 (by norm_num), hF0]
  have hmem : (2 : ℕ) ∈ Finset.Icc 2 4 := by norm_num
  have hfactor : 5 ∣ 4 ^ 2 - 1 := by norm_num
  have hprod : 5 ∣ ∏ index ∈ Finset.Icc 2 4, (4 ^ index - 1) :=
    hfactor.trans (Finset.dvd_prod_of_mem (fun index : ℕ => 4 ^ index - 1) hmem)
  exact dvd_mul_of_dvd_right hprod 4096

theorem ggF4N2_nbr_centralImage (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra) (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hK : GGCentralImage .PSL 6 2 K)
    {z : G} {Y : Subgroup G} (hNY : GGNbr 5 B x D J z Y) :
    GGCentralImage .PSL 6 2 Y ∨ GGCentralImage .POmegaMinus 4 2 Y := by
  have hc : GGConfig 5 B Bs x L D J := hR.1
  have hLinn : GGInnerDiagOn Bs L := hR.2.2.1.1
  have hYinn : GGInnerDiagOn Bs Y := hR.2.2.1.2 z Y hNY
  have hJY : J ≤ Y :=
    (N2KAllNeighborComponent.arbitrary_neighbor_component hR hNbr hL hK hLB z Y hNY).1
  have hpJ : 5 ∣ Nat.card J := ggF4N2_five_dvd_card_J hR hNbr hL hK
  have hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D :=
    (ggF4N2_D_eq_Bs_inf_centralizer_J hR hL).ge
  have hΛJ : LargeEvenInLambda2 ⟨.A, 3, 2⟩ := by
    refine ⟨by norm_num, by norm_num, fun h => absurd h (by norm_num)⟩
  have hhJ : GGHasLabel ⟨.A, 3, 2⟩ (J ⧸ Subgroup.center J) := by
    obtain ⟨-, ⟨F0, hField0, hFinite0, hChar0, hF0, ⟨eJ⟩⟩, -⟩ :=
      ggF4N2J_original_mixed_recognition hR hNbr hL hK
    letI : Field F0 := hField0
    letI : Finite F0 := hFinite0
    exact ggHasLabel_of_mulEquiv_specialLinear (k := 4) (f := 2) (by norm_num)
      (by rw [hF0]; norm_num) (by decide) (by decide) eJ.symm
  obtain ⟨labY, hlabY, -, hhY⟩ :=
    ggNbrLabel_a3Plus_of_config GGK0ExcB3Prod.ggK0ExcB3_holds hLB hc hLinn hYinn hNY hJY hpJ
      hI1 (m := 2) le_rfl (by norm_num) hΛJ hhJ
  rcases hlabY with rfl | rfl
  · exact Or.inl (ggF4Ends_centralImage_PSL hYinn.1 (m := 5) (by norm_num) le_rfl
      (by norm_num) hhY)
  · exact Or.inr (ggF4Ends_centralImage_POmegaMinus hYinn.1 le_rfl hhY)

theorem ggF4N2_nbrReflectionAt_all_of_minus (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra) (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hK : GGCentralImage .PSL 6 2 K)
    (eJ : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2))
    (hminus : ∀ (z : G) (Y : Subgroup G), GGNbr 5 B x D J z Y →
      GGCentralImage .POmegaMinus 4 2 Y → GGF4N2NbrReflectionAt Bs D J Y z eJ) :
    ∀ (z : G) (Y : Subgroup G), GGNbr 5 B x D J z Y → GGF4N2NbrReflectionAt Bs D J Y z eJ := by
  intro z Y hNY
  rcases ggF4N2_nbr_centralImage hLB hR hNbr hL hK hNY with hY | hY
  · exact ggF4N2_nbrReflectionAt_of_psl6 hR hL eJ hNY hY
  · exact hminus z Y hNY hY

theorem ggF4N2_nbrReflectionAt_all (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra) (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hK : GGCentralImage .PSL 6 2 K)
    (eJ : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) :
    ∀ (z : G) (Y : Subgroup G), GGNbr 5 B x D J z Y → GGF4N2NbrReflectionAt Bs D J Y z eJ := by
  obtain ⟨g, hg, h0, h1, hinv⟩ :=
    ggF4N2_exists_torus_trace_witness hR hNbr hL hK eJ
  exact ggF4N2_nbrReflectionAt_all_of_minus hLB hR hNbr hL hK eJ fun z Y hNY hY =>
    ggF4N2_nbrReflectionAt_of_minus hR hL eJ hg.1 h0 h1 hinv hNY hY

end Classification

end CFSG.StandardType

end
