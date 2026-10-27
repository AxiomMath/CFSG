module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKind
import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase
import CFSG.LocalAnalysis.StandardType.GGQTwoLMModQm
import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullTorus2

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord CFSG.Assembly
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

theorem qTwoLMDivF_fullW {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
    {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (_h3 : 3 ∣ m)
    (_hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hcard : Nat.card Bs = 3 ^ m) :
    ∃ Θ : QTwoQm m ≃* ↥(ggGamma L hN).range,
      (∀ (n : ↥L) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
        ∃ π : Equiv.Perm (Fin m),
          ggConjAut (ggGamma L hN).range hn = MulAut.congr Θ (qTwoLMDivF_permQ m π)) ∧
      (∀ σ : Equiv.Perm (Fin m), ∃ (n : ↥L) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
        ggConjAut (ggGamma L hN).range hn = MulAut.congr Θ (qTwoLMDivF_permQ m σ)) := by
  subst hFm
  letI := hFrameL.fieldF0
  letI := hFrameL.finiteF0
  letI := hFrameL.charF0
  letI := hFrameL.groupL0
  have hU : QTwoDivInnerFrame hFrameL.m Bs L hN hFrameL.F0 hFrameL.L0 hFrameL.c hFrameL.πSU
      hFrameL.ρ :=
    ⟨hFrameL.hcardF0, hFrameL.hc_surj, hFrameL.hc_ker, hFrameL.hc_two, hFrameL.hπ_surj,
      hFrameL.hπ_ker, hFrameL.hdiag, hFrameL.hρ_induced⟩
  have hperf : commutator ↥L = ⊤ := qTwoLMFrameC_perfect hG
  obtain ⟨δ, hδ⟩ := qTwoLMDivF_torus hU.card hFrameL.m
  have hS : LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
  have hx : x ∈ Bs := hBs.1 hS.2.1
  have hord : orderOf x = 3 := orderOf_eq_prime (hBs.2.1.2 x hx) hS.2.2.1
  have hsurj := qTwoLMDivF_phi_surjective (by omega) hperf hU hU.card hδ hord
    (qTwoLMSkel_div_ker hG hBs hN) hx hcard
    (qTwoLMSkel_isQmModel_card (qTwoLMDivF_isQmModel hFrameL.m))
  exact ⟨qTwoLMDivF_theta (by omega) hperf hU hU.card hδ hsurj,
    fun n hn => qTwoLMDivF_weyl_norm (by omega) hperf hU hU.card hδ hsurj n hn,
    fun σ => qTwoLMDivF_weyl_ind (by omega) hperf hU hU.card hδ hsurj σ⟩

end CFSG.StandardType.QTwo

end
