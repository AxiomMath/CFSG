module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDGN6Assembly
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Raw
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6TwE6
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrEsu
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelModuleOfB2
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorHolds
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxCore
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG1
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG2
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG3
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG4
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelBases

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan


theorem qTwoD_gn_of_u62 {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x y : G}
    {X : Subgroup G} (hC : GGConfig 3 B Bs x L D J) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hnbr : GGNbr 3 B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs X) :
    X ≤ ⨆ (g : G) (_ : g ∈ X) (_ : ∃ φ : MulAut ↥Bs,
        g ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹),
      J.map (MulAut.conj g).toMonoidHom := by
  have hJX : J ≤ X := le_of_ggNbr hLB hC.1 hC.2.2 (hPJ G 3 B x L D J hC.1 hC.2.2) hnbr
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hC hnbr hJX
  obtain ⟨K, hKf, hKfin, lab, m', θ, hK, -, hmrank, hSide, -, -, -, -, -⟩ :=
    ggNSLieN3A_esuCore hmark (fun p lab hl => hl.1)
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn, hr5⟩ := hSide
  change n = 1 at hn
  change rank = 5 at hr5
  change m' = rank + 1 at hmrank
  subst hn
  subst hr5
  have hm6 : m' = 6 := by omega
  subst hm6
  have hLie : LieModel (↥X ⧸ Subgroup.center ↥X) .PSU 6 2 1 :=
    qtwoDNbr_lieModel_of_su hK (by norm_num) le_rfl θ
  obtain ⟨hM⟩ := qTwoNbrRec_core hC hLB hPJ hnbr hJX hcomp (by norm_num)
    (hmark.mono' fun _ h => h.1) hLie
  exact qTwoNbr_gen hM (qTwoNbr_comp_transport hM) (qTwoNbr_fourBlock hM)
    (qTwoNbr_normalTransport hC.2.1 hM)

theorem ggQTwoGNInputOn_six (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hRM : GGQTwoRMInputOn fun m => m = 6) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hTw : GGQTwoDSixTwE6InputOn fun m => m = 6) :
    GGQTwoGNInputOn fun m => m = 6 := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y X hnbr _
  subst hm
  obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp3
  have hC : GGConfig 3 B Bs x L D J := hcfg.1.1.1
  rcases qtwoDNbr6_chart4_or (R := fun m => m = 6) (fun m hm => by omega) hRM hTCJ hLB hPJ
      (ggQTwoDSelModuleInputOn_of_selectedModule (fun m hm => by omega) hTBF hWI) hTw hcfg e'
      rfl hM (qtwoD6_jlabel hTBF hWI ggQTwoDOrthJInput_holds hcfg e' hM) hnbr with
    hch | ⟨-, -, h5⟩
  · exact qTwoD_gn_of_chart4 hC hLB hPJ qTwoOrthJAnchor4Input_holds hnbr hch
  · exact qTwoD_gn_of_u62 hC hLB hPJ hnbr h5

end CFSG.StandardType.QTwo

end
