module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatRootCent
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummand
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeAbstract
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeBar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggRCS_exists_normal_of_quasi (hSch : SchreierFor InCatalog)
    (hKF : GGKGroupFusionLayerInputFlat) (h3 : GGRootCentAutKIIIFlatInput)
    (h4 : GGRootCentAutKIVFlatInput) (hexc : GGRootCentAutKNotExcInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J)
    (s2 : GGSixStepTwo p B Bs x L D J) {E : Subgroup G} {r : G}
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r) (hp3 : p = 3)
    {S₁ : Subgroup (GGRCSNbar r)} (hS₁ : GGRCSQuasiPiece p (ggRCSImg r (ggM p B x L D J)) S₁)
    {ē : GGRCSNbar r} (hēS : ē ∈ S₁) (hē3 : orderOf ē = 3)
    (hcent : Subgroup.centralizer ({ē} : Set (GGRCSNbar r)) ≤ ggRCSImg r (ggM p B x L D J))
    {S : Subgroup (GGRCSNbar r)} (hS : GGRCSSThreePiece (ggRCSImg r (ggM p B x L D J)) S) :
    ∃ R : Subgroup (GGRCSNbar r), R.Normal ∧
      IsPGroup p ↥(R.map (QuotientGroup.mk' (LargeEvenPPrimeCore p (GGRCSNbar r)))) ∧ S ≤ R := by
  subst hp3
  have : IsSimpleGroup G := hctx.1.1
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hfus := ggSixRootCentralizer_quotientFusion hctx hch
  have hO := ggSixRootCentralizer_pPrimeCore_le hctx hch
  have hEr := hch.le_centralizer
  obtain ⟨hEel, hEc⟩ := ggBarE_elem_card hp hp2 hEr hch.2.1
  have hEc' := hEc.trans hch.2.2.1
  have hr1 : r ≠ 1 := by
    intro h
    have h2 := hch.2.2.2.2.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hNtop := ggStepTwo_centralizer_ne_top hctx.1.2.1 hr1
  have hKP : KProper InCatalog G := hctx.1.2.2.1
  have hO2 := ggRCS_pCore_two_quot_eq_bot ↥(Subgroup.centralizer ({r} : Set G))
  have hOut : ∀ K : Subgroup (GGRCSNbar r), CFSG.IsComponent K →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    fun K hK => ggRCS_outer_solvable hKP hSch hNtop _ hK
  obtain ⟨K, hK, hS₁K⟩ := ggRCS_exists_component hp2 hO2 hOut hfus hEel hEc' hS₁
  have hKp : 3 ∣ Nat.card K := hS₁.choose_spec.2.2.2.1.trans (Subgroup.card_dvd_of_le hS₁K)
  have hXK : CFSG.Open.IsKGroup (GGRCSNbar r) :=
    (CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup hKP _
      hNtop).quotient _
  have hKV : K ≤ ggRCSImg r (ggM 3 B x L D J) :=
    ggAutKConfigFlat_le hKF hXK hp hp2 hfus hEel hEc' hO hK fun hKV => by
      have hEK := ggLemmaThreeThirteen_top hfus hEel hEc' hK hKp hKV
      have hset : GGRCSAutKSetting 3 (ggRCSImg r (ggM 3 B x L D J)) (ggRCSImg r E) K S₁ :=
        ⟨hK, hKV, hEK, hS₁K, hS₁⟩
      exact ggRCS_autKConfigFlat hp hfus hEel hEc' hEK hK
        (ggRCS_inCatalog_center_quot hKP hNtop _ hK) hS₁ hS₁K
        (h3 G 3 B Bs x L D J t n f ψ hctx s1 s2 E r hch K S₁ hset)
        (h4 G 3 B Bs x L D J t n f ψ hctx s1 s2 E r hch K S₁ hset)
        (hexc G 3 B Bs x L D J t n f ψ hctx s1 s2 E r hch K S₁ hset)
  obtain ⟨R₀, Q, hSR₀, hR₀V, hR₀n, hQS, hQ2, hQn, hcard, hiso⟩ := hS
  exact ggSThree_exists_normal hK hKV (hS₁K hēS) hē3 hcent hSR₀ hR₀V hR₀n hQS hQ2 hQn hcard hiso

end Inputs

end CFSG.StandardType
