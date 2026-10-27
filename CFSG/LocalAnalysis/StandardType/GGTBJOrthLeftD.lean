module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmRank
public import CFSG.LocalAnalysis.StandardType.GGTBJOmModelNs
public import CFSG.LocalAnalysis.StandardType.GGTBJOmPlusPlusRaw
public import CFSG.LocalAnalysis.StandardType.GGTBJR1OmPlusRow
public import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeftGlue

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJOrthLeft_rowOmPlusMinus
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n - 1) p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1)
    (fun lab _ hs => nbrC_labelAll_guard
      (ggOmPlusRow_labelAll_adjoint (ggLabQFour_of_dvd_pow_sub_one hp hs.1 hs.2.2.2) hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, rt, m, n, K, _, _, e, hlift, hK, hn, hm, hpn,
    hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr0, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr0 h3
  let ψ₀ : ↥L →* OrthRest.RPlus K (m + 1) := e.toMonoidHom.comp (ggQuotHom θ)
  have hTB' : GGTorusTBGroup p rt (OrthRest.RPlus K (m + 1))
      (Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →* MulAut (OrthRest.RPlus K (m + 1))))
      ↥L ψ₀ (ggGamma L hBsN).range :=
    GGTorusTBGroup.mulEquiv
      (I' := Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →*
        MulAut (OrthRest.RPlus K (m + 1))))
      e (fun φ hφ => by
        obtain ⟨g, rfl⟩ := hI φ hφ
        exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have := charP_two_of_card hK
  obtain ⟨r, E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hnf⟩ :=
    ggTBJ_omPlus_stdModel_nf hp hm (by rw [hK]; exact hpn) ψ₀ (ggGamma L hBsN).range hTB'
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qPlusForm K (m + 1))).Nondegenerate :=
    TableBOrth.nondegenerate_qPlusForm (m + 1)
  have hT : ∃ T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, TableBOrth.qPlusForm K (m + 1) v = 0 :=
    OrthTorus.exists_totallySingular_qPlusForm (n := m) hm
  have hZc : ¬ p ∣ Nat.card (Subgroup.center ↥L) :=
    (OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m + 1)).2 ↥L ψ₀
      hTB'.1 hTB'.2.1 hTB'.2.2.1
  have hV : Module.finrank K (Fin (m + 1) ⊕ Fin (m + 1) → K) = 2 * (m + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hle := Δ.finrank_le_two_mul_of_noFixed hnf
  rw [hV] at hle
  have hr : 4 ≤ r := by omega
  exact OrthTorus.ggTBJOrthLeft_nf_of_cfg hcfg hBsN hQ hT hTB'.1 hTB'.2.1 hZc
    hψσ hΘ hWeyl hnf hr

theorem ggTBJOrthLeft_rowOmPlusPlusEven
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      Even lab.rank ∧ p ∣ 2 ^ lab.n + 1) p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧
      p ∣ 2 ^ lab.n + 1)
    (fun lab _ hs => nbrC_labelAll_guard (ggOmPlusPlusRowEven_labelAll_adjoint hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, rt, m, n, K, _, _, e, hlift, hK, hn, hm, hmo, hpn,
    hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr0, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr0 h3
  let ψ₀ : ↥L →* OrthRest.RPlus K (m + 1) := e.toMonoidHom.comp (ggQuotHom θ)
  have hTB' : GGTorusTBGroup p rt (OrthRest.RPlus K (m + 1))
      (Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →* MulAut (OrthRest.RPlus K (m + 1))))
      ↥L ψ₀ (ggGamma L hBsN).range :=
    GGTorusTBGroup.mulEquiv
      (I' := Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →*
        MulAut (OrthRest.RPlus K (m + 1))))
      e (fun φ hφ => by
        obtain ⟨g, rfl⟩ := hI φ hφ
        exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have := charP_two_of_card hK
  obtain ⟨r, E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hnf⟩ :=
    ggTBJ_omPlus_stdModel_nf_ns hp hp2 hm hmo (by rw [hK]; exact hpn) ψ₀
      (ggGamma L hBsN).range hTB'
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qPlusForm K (m + 1))).Nondegenerate :=
    TableBOrth.nondegenerate_qPlusForm (m + 1)
  have hT : ∃ T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, TableBOrth.qPlusForm K (m + 1) v = 0 :=
    OrthTorus.exists_totallySingular_qPlusForm (n := m) hm
  have hZc : ¬ p ∣ Nat.card (Subgroup.center ↥L) :=
    (OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m + 1)).2 ↥L ψ₀
      hTB'.1 hTB'.2.1 hTB'.2.2.1
  have hV : Module.finrank K (Fin (m + 1) ⊕ Fin (m + 1) → K) = 2 * (m + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hle := Δ.finrank_le_two_mul_of_noFixed hnf
  rw [hV] at hle
  have hr : 4 ≤ r := by omega
  exact OrthTorus.ggTBJOrthLeft_nf_of_cfg hcfg hBsN hQ hT hTB'.1 hTB'.2.1 hZc
    hψσ hΘ hWeyl hnf hr

theorem ggTBJOrthLeft_rowOmPlusPlusOdd
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1) p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => 1 ≤ lab.n ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧ Odd lab.rank ∧
      p ∣ 2 ^ lab.n + 1)
    (fun lab _ hs => nbrC_labelAll_guard (ggOmPlusPlusRowOdd_labelAll_adjoint hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, rt, m, n, K, _, _, e, hlift, hK, hn, hm, hme, hpn,
    hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr0, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr0 h3
  let ψ₀ : ↥L →* OrthRest.RPlus K (m + 1) := e.toMonoidHom.comp (ggQuotHom θ)
  have hTB' : GGTorusTBGroup p rt (OrthRest.RPlus K (m + 1))
      (Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →* MulAut (OrthRest.RPlus K (m + 1))))
      ↥L ψ₀ (ggGamma L hBsN).range :=
    GGTorusTBGroup.mulEquiv
      (I' := Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →*
        MulAut (OrthRest.RPlus K (m + 1))))
      e (fun φ hφ => by
        obtain ⟨g, rfl⟩ := hI φ hφ
        exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have := charP_two_of_card hK
  obtain ⟨r, E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hW⟩ :=
    ggTBJ_omPlus_stdModel_ns hp hp2 hm hme (by rw [hK]; exact hpn) ψ₀
      (ggGamma L hBsN).range hTB'
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qPlusForm K (m + 1))).Nondegenerate :=
    TableBOrth.nondegenerate_qPlusForm (m + 1)
  have hT : ∃ T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K),
      Module.finrank K T = 3 ∧ ∀ v ∈ T, TableBOrth.qPlusForm K (m + 1) v = 0 :=
    OrthTorus.exists_totallySingular_qPlusForm (n := m) hm
  have hZc : ¬ p ∣ Nat.card (Subgroup.center ↥L) :=
    (OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m + 1)).2 ↥L ψ₀
      hTB'.1 hTB'.2.1 hTB'.2.2.1
  have hcardA : Nat.card (ggGamma L hBsN).range = p ^ r := by
    rw [← Nat.card_congr Θ.toEquiv, FrameBs.card_zmodFrame]
  have hr : 2 ≤ r := by
    have h3r : 3 ≤ r := (Nat.pow_le_pow_iff_right hp.one_lt).mp (by rwa [hcardA] at h3)
    omega
  exact OrthTorus.ggTBJOrthLeft_fixed_of_cfg hcfg hBsN hQ hT hTB'.1 hTB'.2.1 hZc
    hψσ hΘ hWeyl hW hr

end CFSG.StandardType

end
