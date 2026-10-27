module

public import CFSG.LocalAnalysis.StandardType.GGTBJOrthSide
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigUnpack
public import CFSG.LocalAnalysis.StandardType.GGTBJOmRank
public import CFSG.LocalAnalysis.StandardType.GGTBJOmModelNs
public import CFSG.LocalAnalysis.StandardType.GGTBJOmRow
public import CFSG.LocalAnalysis.StandardType.GGTBJRowR5O2
public import CFSG.LocalAnalysis.StandardType.GGTBJR1OmPlusRow
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus
public import CFSG.LocalAnalysis.StandardType.GGTBJOmPlusPlusRaw
public import CFSG.ClassicalGroups.Orthogonal.RingEquivDerived

import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeft
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitCompletion
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.Classical2 (orthDerived)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJ_card_range_ggGamma_bstar_ge_nbr {G : Type} [Group G] [Finite G] {p r : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hK : commutator ↥K = ⊤) {R : Type} [Group R]
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hlift : GGTorusLift p r R) :
    p ^ r ≤ Nat.card ↥(ggGamma K hN).range ∧ p ^ 3 ≤ Nat.card ↥(ggGamma K hN).range :=
  ⟨pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hH.2.2.2.2.1 hK θ hN hlift,
    pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN⟩

theorem ggTBJ_config_unpack_nbr (hI3 : GGNbrSubcomponentInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    J ≤ K ∧ ∃ y' : MulAut ↥K, y' ∈ (ggGamma K hN).range ∧ y' ≠ 1 ∧
      CFSG.Open.IsComponentOf (J.subgroupOf K) (fixSubgroup y') := by
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  refine ⟨hJK, ggGamma K hN ⟨x, hxBs⟩, ⟨_, rfl⟩, ?_, ?_⟩
  · intro h
    exact not_mem_centralizer_of_nbr hnb ((ggGamma_eq_one_iff K hN ⟨x, hxBs⟩).1 h)
  · exact isComponentOf_subgroupOf_fixSubgroup hN ⟨x, hxBs⟩
      (ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK)

theorem ggTBJOrthNbr_rowR5O1
    (hI3 : GGNbrSubcomponentInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ GGTBRowR5O1 p lab) p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => 1 ≤ lab.n ∧ GGTBRowR5O1 p lab)
    (fun lab hlab hs => nbrC_labelAll_guard (ggO1Row_labelAll_adjoint hp hlab hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, m, n, k, _, _, _, b, c, e, hlift, hm, hn, hk,
    hbc, hpq, hIc⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces K θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := ggTBJ_card_range_ggGamma_bstar_ge_nbr hH hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hI : ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R) := fun φ hφ => hIc hφ
  have hTB' := GGTorusTBGroup.mulEquiv
    (I' := Set.range (MulAut.conj : OrthRest.RMinus k m b c →* MulAut (OrthRest.RMinus k m b c)))
    e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hI φ hφ
      exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have := charP_two_of_card hk
  obtain ⟨r', E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hW⟩ :=
    ggTBJ_om_stdModel hp hp2 hbc hm (by rw [hk]; exact hpq)
      (e.toMonoidHom.comp (ggQuotHom θ)) _ hTB'
  obtain ⟨-, hcp⟩ := OrthExc.center_data_omegaMinus hp hp2 hm hbc
  have hZ := ggTBJ_noPElt_center_of_not_dvd (hcp ↥K _ hTB'.1 hTB'.2.1 hTB'.2.2.1)
  have hQ := TableBOrth.nondegenerate_qMinusForm m hbc
  have hT := (OrthTorus.charSum_qMinusForm m hbc).2 hm
  have hcardA : Nat.card ↥(ggGamma K hBsN).range = p ^ r' := by
    rw [← Nat.card_congr Θ.toEquiv]
    exact FrameBs.card_zmodFrame p r'
  have hr2 : 2 ≤ r' := by
    have h3r : 3 ≤ r' := (Nat.pow_le_pow_iff_right hp.one_lt).mp (by rwa [hcardA] at h3)
    omega
  obtain ⟨hJK, y', hy', hy1, hJcomp⟩ := ggTBJ_config_unpack_nbr hI3 hH hBsN
  exact OrthTorus.ggTBJOrth_fixed_sideDatum_of_countBs hp2 hBs hSC hBsN hQ hT
    hTB'.1 hTB'.2.1 hZ hψσ hΘ hWeyl hW hr2 hy' hy1 hJK hJcomp
    (OrthTorus.ggTBJ_sq_mul_card_inf_centralizer_le hcfg) hcfg.card_bstar_inf_centralizer_J_le

theorem ggTBJOrthNbr_rowR5O2
    (hI3 : GGNbrSubcomponentInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ GGTBRowR5O2 p lab) p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => 1 ≤ lab.n ∧ GGTBRowR5O2 p lab)
    (fun lab hlab hs => nbrC_labelAll_guard (ggO2Row_labelAll_adjoint hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, m, n, k, _, _, b, c, e, hlift, hk, hn, hbc,
    hm, hme, hpn, hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces K θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := ggTBJ_card_range_ggGamma_bstar_ge_nbr hH hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hTB' := GGTorusTBGroup.mulEquiv
    (I' := Set.range (MulAut.conj : OrthRest.RMinus k m b c →* MulAut (OrthRest.RMinus k m b c)))
    e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hI φ hφ
      exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have := charP_two_of_card hk
  obtain ⟨r', E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hnf⟩ :=
    ggTBJ_om_stdModel_nf hp hp2 hbc hm hme (by rw [hk]; exact hpn)
      (e.toMonoidHom.comp (ggQuotHom θ)) _ hTB'
  obtain ⟨-, hcp⟩ := OrthExc.center_data_omegaMinus hp hp2 hm hbc
  have hZ := ggTBJ_noPElt_center_of_not_dvd (hcp ↥K _ hTB'.1 hTB'.2.1 hTB'.2.2.1)
  have hr4 : 4 ≤ r' := by
    have h1 := Δ.finrank_le_two_mul_of_noFixed hnf
    have h2 : Module.finrank k (LargeEvenMinusIdx m → k) = 2 * m + 2 := by
      simp [Module.finrank_fintype_fun_eq_card, LargeEvenMinusIdx]
      ring
    omega
  obtain ⟨hJK, y', hy', hy1, hJcomp⟩ := ggTBJ_config_unpack_nbr hI3 hH hBsN
  exact OrthTorus.ggTBJOrth_nf_sideDatum_of_countBs hp2 hBs hSC hBsN
    (TableBOrth.nondegenerate_qMinusForm m hbc) ((OrthTorus.charSum_qMinusForm m hbc).2 hm)
    hTB'.1 hTB'.2.1 hZ hψσ hΘ hWeyl hnf hr4 hy' hy1 hJK hJcomp
    (OrthTorus.ggTBJ_sq_mul_card_inf_centralizer_le hcfg) hcfg.card_bstar_inf_centralizer_J_le

theorem ggTBJOrthNbr_rowOmPlusMinus
    (hI3 : GGNbrSubcomponentInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n - 1) p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1)
    (fun lab _ hs => nbrC_labelAll_guard
      (ggOmPlusRow_labelAll_adjoint (ggLabQFour_of_dvd_pow_sub_one hp hs.1 hs.2.2.2) hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, m, n, k, _, _, e, hlift, hk, hn, hm, hpn,
    hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces K θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := ggTBJ_card_range_ggGamma_bstar_ge_nbr hH hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hTB' := GGTorusTBGroup.mulEquiv
    (I' := Set.range (MulAut.conj : OrthRest.RPlus k (m + 1) →* MulAut (OrthRest.RPlus k (m + 1))))
    e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hI φ hφ
      exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have := charP_two_of_card hk
  obtain ⟨r', E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hnf⟩ :=
    ggTBJ_omPlus_stdModel_nf hp hm (by rw [hk]; exact hpn)
      (e.toMonoidHom.comp (ggQuotHom θ)) _ hTB'
  obtain ⟨-, hcp⟩ := OrthNs.center_data_omegaPlus (K := k) hp hp2 (by omega : 3 ≤ m + 1)
  have hZ := ggTBJ_noPElt_center_of_not_dvd (hcp ↥K _ hTB'.1 hTB'.2.1 hTB'.2.2.1)
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qPlusForm k (m + 1))).Nondegenerate :=
    TableBOrth.nondegenerate_qPlusForm (m + 1)
  have hT : ∃ T : Submodule k (Fin (m + 1) ⊕ Fin (m + 1) → k),
      Module.finrank k T = 3 ∧ ∀ v ∈ T, TableBOrth.qPlusForm k (m + 1) v = 0 :=
    OrthTorus.exists_totallySingular_qPlusForm (n := m) hm
  have hr4 : 4 ≤ r' := by
    have h1 := Δ.finrank_le_two_mul_of_noFixed hnf
    have h2 : Module.finrank k (Fin (m + 1) ⊕ Fin (m + 1) → k) = 2 * m + 2 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    omega
  obtain ⟨hJK, y', hy', hy1, hJcomp⟩ := ggTBJ_config_unpack_nbr hI3 hH hBsN
  exact OrthTorus.ggTBJOrth_nf_sideDatum_of_countBs hp2 hBs hSC hBsN hQ hT
    hTB'.1 hTB'.2.1 hZ hψσ hΘ hWeyl hnf hr4 hy' hy1 hJK hJcomp
    (OrthTorus.ggTBJ_sq_mul_card_inf_centralizer_le hcfg) hcfg.card_bstar_inf_centralizer_J_le

theorem ggTBJOrthNbr_rowOmPlusPlusEven
    (hI3 : GGNbrSubcomponentInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      Even lab.rank ∧ p ∣ 2 ^ lab.n + 1) p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧
      p ∣ 2 ^ lab.n + 1)
    (fun lab _ hs => nbrC_labelAll_guard (ggOmPlusPlusRowEven_labelAll_adjoint hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, m, n, k, _, _, e, hlift, hk, hn, hm, hmo, hpn,
    hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces K θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := ggTBJ_card_range_ggGamma_bstar_ge_nbr hH hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hTB' := GGTorusTBGroup.mulEquiv
    (I' := Set.range (MulAut.conj : OrthRest.RPlus k (m + 1) →* MulAut (OrthRest.RPlus k (m + 1))))
    e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hI φ hφ
      exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have := charP_two_of_card hk
  obtain ⟨r', E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hnf⟩ :=
    ggTBJ_omPlus_stdModel_nf_ns hp hp2 hm hmo (by rw [hk]; exact hpn)
      (e.toMonoidHom.comp (ggQuotHom θ)) _ hTB'
  obtain ⟨-, hcp⟩ := OrthNs.center_data_omegaPlus (K := k) hp hp2 (by omega : 3 ≤ m + 1)
  have hZ := ggTBJ_noPElt_center_of_not_dvd (hcp ↥K _ hTB'.1 hTB'.2.1 hTB'.2.2.1)
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qPlusForm k (m + 1))).Nondegenerate :=
    TableBOrth.nondegenerate_qPlusForm (m + 1)
  have hT : ∃ T : Submodule k (Fin (m + 1) ⊕ Fin (m + 1) → k),
      Module.finrank k T = 3 ∧ ∀ v ∈ T, TableBOrth.qPlusForm k (m + 1) v = 0 :=
    OrthTorus.exists_totallySingular_qPlusForm (n := m) hm
  have hr4 : 4 ≤ r' := by
    have h1 := Δ.finrank_le_two_mul_of_noFixed hnf
    have h2 : Module.finrank k (Fin (m + 1) ⊕ Fin (m + 1) → k) = 2 * m + 2 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    omega
  obtain ⟨hJK, y', hy', hy1, hJcomp⟩ := ggTBJ_config_unpack_nbr hI3 hH hBsN
  exact OrthTorus.ggTBJOrth_nf_sideDatum_of_countBs hp2 hBs hSC hBsN hQ hT
    hTB'.1 hTB'.2.1 hZ hψσ hΘ hWeyl hnf hr4 hy' hy1 hJK hJcomp
    (OrthTorus.ggTBJ_sq_mul_card_inf_centralizer_le hcfg) hcfg.card_bstar_inf_centralizer_J_le

theorem ggTBJOrthNbr_rowOmPlusPlusOdd
    (hI3 : GGNbrSubcomponentInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1) p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧ Odd lab.rank ∧
      p ∣ 2 ^ lab.n + 1)
    (fun lab _ hs => nbrC_labelAll_guard (ggOmPlusPlusRowOdd_labelAll_adjoint hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, m, n, k, _, _, e, hlift, hk, hn, hm, hme, hpn,
    hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces K θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := ggTBJ_card_range_ggGamma_bstar_ge_nbr hH hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hTB' := GGTorusTBGroup.mulEquiv
    (I' := Set.range (MulAut.conj : OrthRest.RPlus k (m + 1) →* MulAut (OrthRest.RPlus k (m + 1))))
    e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hI φ hφ
      exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have := charP_two_of_card hk
  obtain ⟨r', E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hW⟩ :=
    ggTBJ_omPlus_stdModel_ns hp hp2 hm hme (by rw [hk]; exact hpn)
      (e.toMonoidHom.comp (ggQuotHom θ)) _ hTB'
  obtain ⟨-, hcp⟩ := OrthNs.center_data_omegaPlus (K := k) hp hp2 (by omega : 3 ≤ m + 1)
  have hZ := ggTBJ_noPElt_center_of_not_dvd (hcp ↥K _ hTB'.1 hTB'.2.1 hTB'.2.2.1)
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qPlusForm k (m + 1))).Nondegenerate :=
    TableBOrth.nondegenerate_qPlusForm (m + 1)
  have hT : ∃ T : Submodule k (Fin (m + 1) ⊕ Fin (m + 1) → k),
      Module.finrank k T = 3 ∧ ∀ v ∈ T, TableBOrth.qPlusForm k (m + 1) v = 0 :=
    OrthTorus.exists_totallySingular_qPlusForm (n := m) hm
  have hcardA : Nat.card ↥(ggGamma K hBsN).range = p ^ r' := by
    rw [← Nat.card_congr Θ.toEquiv]
    exact FrameBs.card_zmodFrame p r'
  have hr2 : 2 ≤ r' := by
    have h3r : 3 ≤ r' := (Nat.pow_le_pow_iff_right hp.one_lt).mp (by rwa [hcardA] at h3)
    omega
  obtain ⟨hJK, y', hy', hy1, hJcomp⟩ := ggTBJ_config_unpack_nbr hI3 hH hBsN
  exact OrthTorus.ggTBJOrth_fixed_sideDatum_of_countBs hp2 hBs hSC hBsN hQ hT
    hTB'.1 hTB'.2.1 hZ hψσ hΘ hWeyl hW hr2 hy' hy1 hJK hJcomp
    (OrthTorus.ggTBJ_sq_mul_card_inf_centralizer_le hcfg) hcfg.card_bstar_inf_centralizer_J_le

section MarkedDeletionChart

variable {G F : Type} [Group G] [Field F] [Finite F] [CharP F 2]
  {r p : ℕ} {b c : F}

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Spin

local notation "I" => Fin (r + 1)
local notation "C" =>
  (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c))
local notation "D0" => (deletionPlanes r)

theorem ggTBJOrthNbr_exists_markedDeletionChart_of_conj_of_three_le
    (hr : 3 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (Bs L K : Subgroup G) (eta : ↥Bs ≃* (I → Multiplicative (ZMod p)))
    (ell : Equiv.Perm I) (u : I)
    (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hact : MulAut.congr eta (ggConjAut Bs hw) =
      SpCoord.permAut (ell * Equiv.swap 0 u * ell⁻¹))
    (hK : L.map (MulAut.conj w).toMonoidHom = K)
    (a : ↥(C D0) →* G) (ha : Function.Injective a) (haL : a.range = L)
    (hmarkL : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ((C S).subgroupOf (C D0)).map a = ggBlockComm Bs eta (ell '' (S : Set I))) :
    ∃ (P : ↥(C D0) ≃* ↥(C (Finset.univ.erase u)))
      (k : ↥(C (Finset.univ.erase u)) →* G),
      k.comp P.toMonoidHom = (MulAut.conj w).toMonoidHom.comp a ∧
      (∀ z : ↥(C D0),
        (P z : orthDerived (quadMinus (r + 2) F b c)) =
          (MulAut.conj (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega)
            (Equiv.swap 0 u))) (z : orthDerived (quadMinus (r + 2) F b c))) ∧
      Function.Injective k ∧ k.range = K ∧
      (∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ Finset.univ.erase u →
        ((C S).subgroupOf (C (Finset.univ.erase u))).map k =
          ggBlockComm Bs eta (ell '' (S : Set I))) := by
  classical
  let pi : Equiv.Perm I := Equiv.swap 0 u
  let rho : orthDerived (quadMinus (r + 2) F b c) :=
    splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) pi
  have hD0image : (D0).image pi = Finset.univ.erase u := by
    change (Finset.univ.erase (0 : I)).image pi = Finset.univ.erase u
    rw [Finset.image_erase pi.injective, Finset.image_univ_equiv]
    simp [pi]
  have hCmap : (C D0).map (MulAut.conj rho).toMonoidHom = C (Finset.univ.erase u) := by
    rw [show (C D0).map (MulAut.conj rho).toMonoidHom = C ((D0).image pi) by
      simpa [rho, pi] using
        (chartSubgroup_map_conj_splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c)
          hirr (by omega) pi D0)]
    rw [hD0image]
  let P : ↥(C D0) ≃* ↥(C (Finset.univ.erase u)) :=
    TauCeti.Subgroup.congrOfMapEq (MulAut.conj rho) hCmap
  have hPval : ∀ z : ↥(C D0),
      (P z : orthDerived (quadMinus (r + 2) F b c)) =
        (MulAut.conj rho) (z : orthDerived (quadMinus (r + 2) F b c)) := by
    intro z
    simpa [P] using
      (TauCeti.Subgroup.coe_congrOfMapEq_apply (MulAut.conj rho) hCmap z)
  let k : ↥(C (Finset.univ.erase u)) →* G :=
    (MulAut.conj w).toMonoidHom.comp (a.comp P.symm.toMonoidHom)
  have hsquare : k.comp P.toMonoidHom = (MulAut.conj w).toMonoidHom.comp a := by
    ext z
    simp [k]
  have hinj : Function.Injective k := by
    dsimp [k]
    exact (MulAut.conj w).injective.comp (ha.comp P.symm.injective)
  have hAP : (a.comp P.symm.toMonoidHom).range = a.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ P.symm.surjective]
    exact (MonoidHom.range_eq_map a).symm
  have hrange : k.range = K := by
    change ((MulAut.conj w).toMonoidHom.comp (a.comp P.symm.toMonoidHom)).range = K
    rw [MonoidHom.range_comp (g := (MulAut.conj w).toMonoidHom)
      (f := a.comp P.symm.toMonoidHom), hAP, haL, hK]
  refine ⟨P, k, hsquare, ?_, hinj, hrange, ?_⟩
  · intro z
    simpa [rho, pi] using hPval z
  · intro S hSne hScard hSub
    let T : Finset I := S.image pi
    have hTne : T.Nonempty := by
      obtain ⟨x, hx⟩ := hSne
      exact ⟨pi x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    have hTcard : T.card ≤ 2 := by
      dsimp [T]
      rw [Finset.card_image_of_injective _ pi.injective]
      exact hScard
    have hTsub : T ⊆ D0 := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hyS, rfl⟩ := hx
      have hyDu : y ≠ u := (Finset.mem_erase.mp (hSub hyS)).1
      change pi y ∈ deletionPlanes r
      rw [deletionPlanes, Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hxy
      exact hyDu (pi.injective (hxy.trans (by simp [pi])))
    have hTmap : T.image pi = S := by
      have hpp : pi ∘ pi = id := by
        funext x
        have h2 : pi * pi = 1 := Equiv.swap_mul_self 0 u
        have h := congrFun (congrArg (fun f : Equiv.Perm I => (f : I → I)) h2) x
        simpa [Equiv.Perm.mul_apply] using h
      dsimp [T]
      rw [Finset.image_image, hpp, Finset.image_id]
    have hpiT : pi '' (T : Set I) = (S : Set I) := by
      have h := congrArg (fun U : Finset I => (U : Set I)) hTmap
      simpa [Finset.coe_image] using h
    have hmarkT : ((C T).subgroupOf (C D0)).map a =
        ggBlockComm Bs eta (ell '' (T : Set I)) := hmarkL T hTne hTcard hTsub
    have hCT : (C T).map (MulAut.conj rho).toMonoidHom = C S := by
      rw [show (C T).map (MulAut.conj rho).toMonoidHom = C (T.image pi) by
        simpa [rho, pi] using
          (chartSubgroup_map_conj_splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c)
            hirr (by omega) pi T)]
      rw [hTmap]
    have hTP : ((C T).subgroupOf (C D0)).map P.toMonoidHom =
        (C S).subgroupOf (C (Finset.univ.erase u)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hyT : (y : orthDerived (quadMinus (r + 2) F b c)) ∈ C T :=
          Subgroup.mem_subgroupOf.mp hy
        have hPS : (P y : orthDerived (quadMinus (r + 2) F b c)) ∈ C S := by
          rw [hPval y, ← hCT]
          exact Subgroup.mem_map_of_mem (MulAut.conj rho).toMonoidHom hyT
        exact Subgroup.mem_subgroupOf.mpr hPS
      · intro hx
        have hxS : (x : orthDerived (quadMinus (r + 2) F b c)) ∈ C S :=
          Subgroup.mem_subgroupOf.mp hx
        have hxmap : (x : orthDerived (quadMinus (r + 2) F b c)) ∈
            (C T).map (MulAut.conj rho).toMonoidHom := by
          rw [hCT]
          exact hxS
        obtain ⟨y, hyT, hyx⟩ := Subgroup.mem_map.mp hxmap
        have hyD0 : y ∈ C D0 :=
          chartSubgroup_mono (F := F) (b := b) (c := c) hirr hTsub hyT
        refine ⟨⟨y, hyD0⟩, Subgroup.mem_subgroupOf.mpr hyT, ?_⟩
        apply Subtype.ext
        change (P ⟨y, hyD0⟩ : orthDerived (quadMinus (r + 2) F b c)) =
          (x : orthDerived (quadMinus (r + 2) F b c))
        rw [hPval]
        exact hyx
    have hYmap : ((C S).subgroupOf (C (Finset.univ.erase u))).map P.symm.toMonoidHom =
        (C T).subgroupOf (C D0) :=
      (Subgroup.map_symm_eq_iff_map_eq
        (H := (C S).subgroupOf (C (Finset.univ.erase u)))
        (K := (C T).subgroupOf (C D0)) (e := P)).mpr hTP
    have h1 : ((C S).subgroupOf (C (Finset.univ.erase u))).map k =
        (((C T).subgroupOf (C D0)).map a).map (MulAut.conj w).toMonoidHom := by
      change ((C S).subgroupOf (C (Finset.univ.erase u))).map
          ((MulAut.conj w).toMonoidHom.comp (a.comp P.symm.toMonoidHom)) =
        (((C T).subgroupOf (C D0)).map a).map (MulAut.conj w).toMonoidHom
      rw [← Subgroup.map_map (g := (MulAut.conj w).toMonoidHom)
          (f := a.comp P.symm.toMonoidHom),
        ← Subgroup.map_map (f := P.symm.toMonoidHom) (g := a), hYmap]
    have hblock : (ggBlockComm Bs eta (ell '' (T : Set I))).map
        (MulAut.conj w).toMonoidHom = ggBlockComm Bs eta (ell '' (S : Set I)) := by
      rw [ggBlockComm_image_map_conj (Bs := Bs) (eta := eta) (π := ell) (ρ := pi)
        hw (by simpa [pi] using hact) (T : Set I)]
      rw [hpiT]
    calc
      ((C S).subgroupOf (C (Finset.univ.erase u))).map k
          = (((C T).subgroupOf (C D0)).map a).map (MulAut.conj w).toMonoidHom := h1
      _ = (ggBlockComm Bs eta (ell '' (T : Set I))).map
            (MulAut.conj w).toMonoidHom := by rw [hmarkT]
      _ = ggBlockComm Bs eta (ell '' (S : Set I)) := hblock

theorem ggTBJOrthNbr_exists_markedDeletionChart_of_conj
    (hr : 4 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (Bs L K : Subgroup G) (eta : ↥Bs ≃* (I → Multiplicative (ZMod p)))
    (ell : Equiv.Perm I) (u : I) (h0u : (0 : I) ≠ u)
    (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    (hact : MulAut.congr eta (ggConjAut Bs hw) =
      SpCoord.permAut (ell * Equiv.swap 0 u * ell⁻¹))
    (hK : L.map (MulAut.conj w).toMonoidHom = K)
    (a : ↥(C D0) →* G) (ha : Function.Injective a) (haL : a.range = L)
    (hmarkL : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ((C S).subgroupOf (C D0)).map a = ggBlockComm Bs eta (ell '' (S : Set I))) :
    ∃ (P : ↥(C D0) ≃* ↥(C (Finset.univ.erase u)))
      (k : ↥(C (Finset.univ.erase u)) →* G),
      k.comp P.toMonoidHom = (MulAut.conj w).toMonoidHom.comp a ∧
      (∀ z : ↥(C D0),
        (P z : orthDerived (quadMinus (r + 2) F b c)) =
          (MulAut.conj (splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr
            (Equiv.swap 0 u))) (z : orthDerived (quadMinus (r + 2) F b c))) ∧
      Function.Injective k ∧ k.range = K ∧
      (∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ Finset.univ.erase u →
        ((C S).subgroupOf (C (Finset.univ.erase u))).map k =
          ggBlockComm Bs eta (ell '' (S : Set I))) := by
  have hρ : splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr (Equiv.swap 0 u) =
      splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega)
        (Equiv.swap 0 u) :=
    Subtype.ext ((coe_splitMinusRho_apply r hirr hr _).trans
      (coe_splitMinusRhoOfTwoLe_apply r hirr (by omega) _).symm)
  rw [hρ]
  exact ggTBJOrthNbr_exists_markedDeletionChart_of_conj_of_three_le (by omega) hirr Bs L K eta ell
    u w hw hact hK a ha haL hmarkL

theorem ggTBJOrthNbr_exists_markedDeletionChart_relabel
    (hr : 2 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (Bs : Subgroup G) (eta : ↥Bs ≃* (I → Multiplicative (ZMod p)))
    (ell : Equiv.Perm I) (a : ↥(C D0) →* G) (ha : Function.Injective a)
    (hmarkL : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
      ((C S).subgroupOf (C D0)).map a = ggBlockComm Bs eta (ell '' (S : Set I)))
    (τ : Equiv.Perm I) (hτ : τ 0 = 0) :
    ∃ a' : ↥(C D0) →* G, Function.Injective a' ∧ a'.range = a.range ∧
      ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ D0 →
        ((C S).subgroupOf (C D0)).map a' = ggBlockComm Bs eta ((ell * τ) '' (S : Set I)) := by
  classical
  let rho : orthDerived (quadMinus (r + 2) F b c) :=
    splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr τ
  have hCT : ∀ T : Finset I, (C T).map (MulAut.conj rho).toMonoidHom = C (T.image τ) :=
    fun T => chartSubgroup_map_conj_splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c)
      hirr hr τ T
  have hD0image : (D0).image τ = D0 := by
    change (Finset.univ.erase (0 : I)).image τ = Finset.univ.erase 0
    rw [Finset.image_erase τ.injective, Finset.image_univ_equiv, hτ]
  have hCmap : (C D0).map (MulAut.conj rho).toMonoidHom = C D0 := by
    rw [hCT, hD0image]
  let Q : ↥(C D0) ≃* ↥(C D0) := TauCeti.Subgroup.congrOfMapEq (MulAut.conj rho) hCmap
  have hQval : ∀ z : ↥(C D0),
      (Q z : orthDerived (quadMinus (r + 2) F b c)) =
        (MulAut.conj rho) (z : orthDerived (quadMinus (r + 2) F b c)) := by
    intro z
    simpa [Q] using (TauCeti.Subgroup.coe_congrOfMapEq_apply (MulAut.conj rho) hCmap z)
  refine ⟨a.comp Q.toMonoidHom, ha.comp Q.injective, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ Q.surjective]
    exact (MonoidHom.range_eq_map a).symm
  · intro S hSne hScard hSub
    let T : Finset I := S.image τ
    have hTne : T.Nonempty := hSne.image τ
    have hTcard : T.card ≤ 2 := by
      dsimp only [T]
      rw [Finset.card_image_of_injective _ τ.injective]
      exact hScard
    have hTsub : T ⊆ D0 := by
      rw [← hD0image]
      exact Finset.image_subset_image hSub
    have hQS : ((C S).subgroupOf (C D0)).map Q.toMonoidHom = (C T).subgroupOf (C D0) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hyS : (y : orthDerived (quadMinus (r + 2) F b c)) ∈ C S :=
          Subgroup.mem_subgroupOf.mp hy
        have hQT : (Q y : orthDerived (quadMinus (r + 2) F b c)) ∈ C T := by
          rw [hQval y, ← hCT]
          exact Subgroup.mem_map_of_mem (MulAut.conj rho).toMonoidHom hyS
        exact Subgroup.mem_subgroupOf.mpr hQT
      · intro hx
        have hxT : (x : orthDerived (quadMinus (r + 2) F b c)) ∈
            (C S).map (MulAut.conj rho).toMonoidHom := by
          rw [hCT]
          exact Subgroup.mem_subgroupOf.mp hx
        obtain ⟨y, hyS, hyx⟩ := Subgroup.mem_map.mp hxT
        have hyD0 : y ∈ C D0 := chartSubgroup_mono (F := F) (b := b) (c := c) hirr hSub hyS
        refine ⟨⟨y, hyD0⟩, Subgroup.mem_subgroupOf.mpr hyS, ?_⟩
        apply Subtype.ext
        change (Q ⟨y, hyD0⟩ : orthDerived (quadMinus (r + 2) F b c)) =
          (x : orthDerived (quadMinus (r + 2) F b c))
        rw [hQval]
        exact hyx
    have himage : (ell * τ) '' (S : Set I) = ell '' (T : Set I) := by
      rw [Equiv.Perm.coe_mul, Set.image_comp]
      simp only [T, Finset.coe_image]
    rw [himage, ← hmarkL T hTne hTcard hTsub, ← hQS, Subgroup.map_map]

end MarkedDeletionChart

end CFSG.StandardType

end
