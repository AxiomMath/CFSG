module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAbsorb
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggStdPair_L_of_dvd {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hpJ : p ∣ Nat.card J)
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hAJ : ggAutomizer J Bs ≠ ⊥) : GGStdPair p Bs x L := by
  obtain ⟨hcfg, -, hIDAll, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hBsabel : IsElemAbelian p Bs := hBstar.2.1
  have hxBs : x ∈ Bs := hBstar.1 hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
  obtain ⟨hJL, hLpc, huniq⟩ := eq_of_le_of_stdSub hI hStdSub hpJ
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hIDAll.1
  have hF1 : ∀ b ∈ Bs, (⁅L, Subgroup.zpowers b⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p L → b ∈ Subgroup.zpowers x := by
    intro b hb hcomm
    have hbC : b ∈ Subgroup.centralizer (L : Set G) := by
      refine mem_centralizer_of_commutator_le_coprime hp hS.2.2.2.1.2.2
        (hpJ.trans (Subgroup.card_dvd_of_le hJL)) ?_ ?_ (hBsL hb) hcomm
      · rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective L.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
      · intro l hl
        exact mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer hl)
    have hbm : b ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hb, hbC⟩
    have hE : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
      inf_centralizer_eq_zpowers_of_elemAbelian hp hBsabel hxBs hx1 hS.2.2.2.1.1 hS.2.2.2.2
    rwa [hE] at hbm
  refine ⟨hxBs, hx1, hLpc, hBsL, ?_, ?_⟩
  · intro b hb
    constructor
    · exact hF1 b hb
    · intro hbw
      have hbxC : Subgroup.zpowers b ≤ Subgroup.centralizer (L : Set G) :=
        (Subgroup.zpowers_le.mpr hbw).trans (Subgroup.zpowers_le.mpr hxL)
      have hbot : (⁅L, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (Subgroup.le_centralizer_iff.mpr hbxC)
      rw [hbot]
      exact bot_le
  · intro hbot
    exact hAJ (le_bot_iff.mp (hbot ▸ ggAutomizer_mono Bs hJL))

theorem ggStdPair_L {G : Type} [Group G] [Finite G] (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hAJ : ggAutomizer J Bs ≠ ⊥) : GGStdPair p Bs x L :=
  ggStdPair_L_of_dvd (hP G p B x L D J hHyp.1.1 hHyp.1.2.2) hHyp hAJ

theorem ggStdPair_nbr_of_dvd {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hpJ : p ∣ Nat.card J)
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    GGStdPair p Bs y K := by
  obtain ⟨hcfg, -, hIDAll, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hBsabel : IsElemAbelian p Bs := hBstar.2.1
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hStdSub.1.2.2.2.2.2.1.2.2
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJq
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hIDAll.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBstar.1 hStdSub.1 hBsL
  have hyB : y ∈ B := hnbr.1.2.1
  have hy1 : y ≠ 1 := hnbr.1.2.2.1
  have hyBs : y ∈ Bs := hBstar.1 hyB
  have hKc : K ≤ Subgroup.centralizer ({y} : Set G) := hnbr.1.2.2.2.1
  have hKpc : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    hnbr.1.2.2.2.2.1
  have hJK : J ≤ K := le_of_ggNbr hLB hI hStdSub hpJ hnbr
  have hBsy : Bs ≤ Subgroup.centralizer ({y} : Set G) :=
    (GGBstar.le_centralizer hBstar).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyB))
  have hBsK : Bs ≤ Subgroup.normalizer (K : Set G) :=
    GGDichotomy.le_normalizer_of_pComponent hBsy hKpc hJK hJJ hpJ hBsJ
  refine ⟨hyBs, hy1, hKpc, hBsK, ?_, ?_⟩
  · intro b hb
    constructor
    · exact hK1 y K hnbr b hb
    · intro hby
      have hyC : y ∈ Subgroup.centralizer (K : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact Subgroup.mem_centralizer_singleton_iff.mp (hKc hk)
      have hbyC : Subgroup.zpowers b ≤ Subgroup.centralizer (K : Set G) :=
        (Subgroup.zpowers_le.mpr hby).trans (Subgroup.zpowers_le.mpr hyC)
      have hbot : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (Subgroup.le_centralizer_iff.mpr hbyC)
      rw [hbot]
      exact bot_le
  · intro hbot
    exact hAJ (le_bot_iff.mp (hbot ▸ ggAutomizer_mono Bs hJK))

theorem ggStdPair_nbr {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    GGStdPair p Bs y K :=
  ggStdPair_nbr_of_dvd hLB (hP G p B x L D J hHyp.1.1 hHyp.1.2.2) hHyp hAJ hK1 hnbr

theorem ggQ2_stdPair_le_G0_component {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hpJ : p ∣ Nat.card J)
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) :
    LargeEvenPComponent p (Subgroup.centralizer (D : Set G)) J := by
  obtain ⟨hcfg, -, -, -, -⟩ := hHyp
  obtain ⟨hI, -, hStdSub⟩ := hcfg
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hCD_le : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer (D : Set G) :=
    inf_eq_right.mpr
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hStdSub.1.2.2.2.1))
  have hLinfD_sn : IsSubnormal (L ⊓ Subgroup.centralizer (D : Set G))
      (Subgroup.centralizer (D : Set G)) := by
    have h := LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hS.2.2.2.1.2.1
      (Subgroup.centralizer (D : Set G))
    rwa [hCD_le] at h
  have hJcompD : IsComponentOf J (Subgroup.centralizer (D : Set G)) :=
    isComponentOf_of_isSubnormal_of_isComponentOf hStdSub.1.2.2.2.2.2.1 hLinfD_sn
  exact (largeEvenPComponent_iff_lBalance p (Subgroup.centralizer (D : Set G)) J).2
    ⟨hJcompD.1, lBalanceIsPComponent_of_isComponentOf hJcompD
      (not_le_lBalancePrimeCore_of_dvd (Y := Subgroup.centralizer (D : Set G)) hpJ)⟩

theorem ggQ2_not_mem_zpowers_of_ne {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} (hp : p.Prime) (hBstar : GGBstar p B Bs) (hxBs : x ∈ Bs) (hx1 : x ≠ 1)
    {w : G} {X : Subgroup G} (hX : GGStdPair p Bs w X)
    (hzw : Subgroup.zpowers w ≠ Subgroup.zpowers x) :
    w ∉ Subgroup.zpowers x ∧ x ∉ Subgroup.zpowers w := by
  constructor
  · intro hw
    apply hzw
    refine le_antisymm (Subgroup.zpowers_le.mpr hw) ?_
    exact Subgroup.zpowers_le.mpr
      (mem_zpowers_of_mem_zpowers_of_ne_one hp (hBstar.2.1.2 x hxBs) hw hX.2.1)
  · intro hxw
    apply hzw
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr hxw)
    exact Subgroup.zpowers_le.mpr
      (mem_zpowers_of_mem_zpowers_of_ne_one hp (hBstar.2.1.2 w hX.1) hxw hx1)

theorem ggQ2_stdPair_le_G0_of_dvd {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hpJ : p ∣ Nat.card J)
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥) {w : G}
    {X : Subgroup G} (hX : GGStdPair p Bs w X) (hwD : w ∈ D) :
    X ≤ ggG0 p B x L D J := by
  have hHyp' : GGCorFiveTwentyHyp p B Bs x L D J := hHyp
  obtain ⟨hcfg, -, -, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hBstar.1 hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hStdSub.1.2.2.2.2.2.1.2.2
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJq
  have hQ : LargeEvenPComponent p (Subgroup.centralizer (D : Set G)) J :=
    ggQ2_stdPair_le_G0_component hpJ hHyp'
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  have hJX : J ≤ X := ggQ2_absorb hLB hHyp' hDBs hwD hX hQ hAJ
  by_cases hzw : Subgroup.zpowers w = Subgroup.zpowers x
  · obtain ⟨-, hLpc, huniq⟩ := eq_of_le_of_stdSub hI hStdSub hpJ
    have hXpc : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) X :=
      (centralizer_singleton_eq_of_zpowers_eq hzw) ▸ hX.2.2.1
    have hXL : X = L := huniq X hXpc hJX
    rw [hXL]
    exact le_ggG0_left p B x L D J
  · obtain ⟨hwx, hxw⟩ := ggQ2_not_mem_zpowers_of_ne hp hBstar hxBs hx1 hX hzw
    have hD : D = Subgroup.closure {x, w} := eq_closure_pair_of_mem hI hStdSub hwD hwx
    obtain ⟨hKpc, hJK, -, hcase⟩ :=
      pumpup_of_stdSub (ggPumpupInput_of_lBalance hLB) hI hStdSub hpJ hD
    have hKlb : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer ({w} : Set G))
        (ggLayerClosure p (Subgroup.centralizer ({w} : Set G)) J) :=
      ((largeEvenPComponent_iff_lBalance p _ _).1 hKpc).2
    have hXlb : CFSG.Open.lBalanceIsPComponent p (Subgroup.centralizer ({w} : Set G)) X :=
      ((largeEvenPComponent_iff_lBalance p _ X).1 hX.2.2.1).2
    have hKX : X = ggLayerClosure p (Subgroup.centralizer ({w} : Set G)) J :=
      GGDichotomy.eq_of_le_of_pComponent hKlb hXlb hJK hJX hJJ hpJ
    rcases hcase with hnb | htriv
    · have hKG0 : ggLayerClosure p (Subgroup.centralizer ({w} : Set G)) J ≤
          ggG0 p B x L D J := le_ggG0_of_ggNbr hnb
      rw [hKX]
      exact hKG0
    · exfalso
      have htriv' : (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X := by
        rw [hKX]
        exact htriv
      exact hxw ((hX.2.2.2.2.1 x hxBs).1 htriv')

theorem ggQ2_stdPair_le_G0 {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥) {w : G}
    {X : Subgroup G} (hX : GGStdPair p Bs w X) (hwD : w ∈ D) :
    X ≤ ggG0 p B x L D J :=
  ggQ2_stdPair_le_G0_of_dvd hLB (hP G p B x L D J hHyp.1.1 hHyp.1.2.2) hHyp hAJ hX hwD

end CFSG.StandardType

end
