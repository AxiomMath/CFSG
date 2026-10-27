module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Aset
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R35
public import CFSG.LocalAnalysis.WeakClosure81.SixNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem wClos_le_centralizer_of_case1633 (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D)
    (hext : DataExt D) (h5 : R16_5 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {m : ℕ} (hm : Case1633 D V₀ V hV L m) {i : ℕ} (hi : i + 1 ≤ m) :
    E3.wClos V i D.T ≤ centralizer (V : Set G) := by
  classical
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  obtain ⟨hδ, hr⟩ := r16_35_holds D h61 hext h5 V₀ V L hV hS m hm
  have h := hS.setting.hyp16
  have hP := h.hyp125.pairFacts
  have hempty := S.aSet_succ_eq_empty hSK (Mbar_le_normalizer_lBar hS S hSω)
  refine E3.wClos_le_of_forall fun A hA => ?_
  have hAM : A ∈ E3.gammaSet V i D.M := E3.gammaSet_mono D.sylowM.le hA
  obtain ⟨hAT, g, hAg, -⟩ := hA
  have hAMle : A ≤ D.M := hAT.trans D.sylowM.le
  have hbar : barSub V₀ V hV A = ⊥ := by
    by_contra hne
    have hrk : (((m + 1) + i + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V :=
      le_trans (by exact_mod_cast (by omega : (m + 1) + i + mSub V₀ ≤ 2 * m + mSub V₀)) hr
    have hδ' : (((m + 1) + i : ℕ) : ℕ∞) ≤ deltaInf D.M V :=
      le_trans (by exact_mod_cast (by omega : (m + 1) + i ≤ 2 * m)) hδ
    have hmem := barSub_mem_calABar_of_gammaSet D hSg h1219 h21 h22 h hrk hδ' hAM hne
    exact (Set.eq_empty_iff_forall_notMem.1 hempty) _ hmem
  have hi0 : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : i + mSub V₀ < 2 * m + mSub V₀)) hr
  obtain ⟨-, hc, -⟩ := sixteen_twentyThree_one D h22 h hAM hAg hi0
  have hCt := (WeakClosure81.barSub_eq_bot_iff hV hP.le_normalizer hP.le_normalizer₀
    hAMle).1 hbar
  have hVc : V ≤ centralizer (A : Set G) := fun v hv => hc v hv fun a ha => by
    have hcm := WeakClosure81.centralizesMod_of_mem_cTilde hV hP.le_normalizer
      hP.le_normalizer₀ (hCt ha) v hv
    have e : ⁅v, a⁆ = (a * v * a⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact V₀.inv_mem hcm
  exact Subgroup.le_centralizer_iff.1 hVc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
