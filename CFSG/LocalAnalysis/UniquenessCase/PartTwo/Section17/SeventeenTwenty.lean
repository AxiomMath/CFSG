module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicArithHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicCoverHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KGroupSporadic
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.GroupTheory.PRankCommutingPerfect
public import CFSG.Quasithin.H13.U3L14D6
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certificates


theorem seventeen_twenty
    (D : Data G) (V₀ V : Subgroup G)
    (h18 : R17_18At D V₀ V) (h19 : R17_19At D V₀ V) :
    R17_20At D V₀ V := by
  intro L c
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := c.mem_calC.2.2
  have hLle : L ≤ UC22.conjClosure D.M L := TwelveTwentyThree.le_conjClosure D.M L
  have h18O : CFSG.Open.pRank 3 (UC22.conjClosure D.M L) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (UC22.conjClosure D.M L),
      ← CFSG.SectionRank.pRank_eq_open_pRank_top (p := 3) ↥(UC22.conjClosure D.M L)]
    exact h18 L c
  have hle2O : CFSG.Open.pRank 3 L ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hLle).trans h18O
  obtain ⟨s, hspor⟩ := c.sporadic
  obtain ⟨eBI⟩ := UC22.uc22p21k_barInf_equiv_of_calC c.mem_calC
  have hoddC : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    UC22.uc22p20p_odd_center_bar2 ↥L
  have hsporQuot : IsSpor (Bar2 L ⧸ Subgroup.center (Bar2 L)) s := by
    obtain ⟨e⟩ := hspor
    exact ⟨eBI.symm.trans e⟩
  have hLbar : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = CFSG.Open.pRank 3 L :=
    pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)
  have hK4' : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) :=
    k_SporadicCoverThreeRank_holds (Bar2 L) s hq hoddC hsporQuot (hLbar.trans_le hle2O)
  have hBIeq : CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eBI
  have hBIleO : CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) ≤ 2 := by
    rw [hBIeq]
    exact hK4'.trans (by rw [hLbar]; exact hle2O)
  have hsne : s ≠ .J1 := by
    intro hs
    apply h19 L c
    have hJ1BI : IsSpor (BarInf L) .J1 := hs ▸ hspor
    obtain ⟨e⟩ := hJ1BI
    have hquot : IsSpor (Bar2 L ⧸ Subgroup.center (Bar2 L)) .J1 :=
      ⟨eBI.symm.trans e⟩
    have hcen : Subgroup.center (Bar2 L) = ⊥ :=
      k_J1IsCenterless_holds (Bar2 L) hq hoddC hquot
    obtain ⟨e2⟩ := UC22.uc22p21k_quotCenter_equiv (X := Bar2 L) hcen
    exact ⟨e2.symm.trans (eBI.symm.trans e)⟩
  have : Nontrivial (BarInf L) := by
    have := hq.2.toNontrivial
    exact eBI.toEquiv.nontrivial
  have hK1BI := PartOne.Section8.kSporadicThreeRank_holds (BarInf L) s hspor
  have hposO : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) :=
    k_SporadicThreeRankPos_holds (BarInf L) s hspor
  have hposC : 1 ≤ CFSG.pRank 3 (⊤ : Subgroup (BarInf L)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top (p := 3) ↥(⊤ : Subgroup (BarInf L)),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup (BarInf L))]
    exact hposO
  have hne1C : CFSG.pRank 3 (⊤ : Subgroup (BarInf L)) ≠ 1 :=
    fun h1 => hsne (hK1BI.1.mpr h1)
  have hBIleC : CFSG.pRank 3 (⊤ : Subgroup (BarInf L)) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top (p := 3) ↥(⊤ : Subgroup (BarInf L)),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup (BarInf L))]
    exact hBIleO
  have hBI2 : CFSG.pRank 3 (⊤ : Subgroup (BarInf L)) = 2 := by
    by_contra hne2
    have hge3 : 3 ≤ CFSG.pRank 3 (⊤ : Subgroup (BarInf L)) := by omega
    omega
  have hBI2O : CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) = 2 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup (BarInf L)),
      ← CFSG.SectionRank.pRank_eq_open_pRank_top (p := 3) ↥(⊤ : Subgroup (BarInf L))]
    exact hBI2
  have hlist : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J2 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4 := hK1BI.2.mpr hBI2
  have hbar2O : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 2 := by
    apply le_antisymm ?_ ?_
    · rw [hLbar]; exact hle2O
    · calc 2 = CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) := hBI2O.symm
        _ = CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) := hBIeq
        _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) := hK4'
  have hrankLO : CFSG.Open.pRank 3 L = 2 := by rw [← hLbar]; exact hbar2O
  have hrankL : CFSG.pRank 3 ↥L = 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top (p := 3) ↥L,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact hrankLO
  refine ⟨hrankL, ?_, s, hlist, hspor⟩
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have h3L : 3 ∣ Nat.card L := by
    obtain ⟨E, -, hEab, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup (BarInf L))
    have h3E : 3 ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self 3 (by omega)
    exact (h3E.trans (Subgroup.card_subgroup_dvd_card _)).trans
      (Subgroup.card_quotient_dvd_card (CFSG.solvableRadical ↥L))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLM]
  intro g hg
  by_contra hgN
  set K : Subgroup G := L.map (MulAut.conj g).toMonoidHom with hKdef
  have hKcal : K ∈ calC D.M := by
    have h := UC22.uc22p22u_calC_conj (X := D.M) Subgroup.le_normalizer c.mem_calC
      (m := g⁻¹) (D.M.inv_mem hg)
    simpa [hKdef, uniqueFourConj] using h
  have hKne : L ≠ K := by
    intro heq
    apply hgN
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    have hmap : L.map (MulAut.conj g).toMonoidHom = L := hKdef ▸ heq.symm
    exact hmap
  have hcommK : ⁅L, K⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 K :=
    calC_commutator_le_of_ne c.mem_calC hKcal hKne
  have hKperf : ⁅K, K⁆ = K := by
    rw [hKdef, ← Subgroup.map_commutator, c.mem_calC.2.1]
  have h3K : 3 ∣ Nat.card K := by
    rw [hKdef, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h3L
  set H : Subgroup G := L ⊔ K with hHdef
  have hLH : L ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKL : K ≤ Subgroup.normalizer (L : Set G) :=
    calC_le_normalizer_of_ne c.mem_calC hKcal hKne
  have hcommH : ⁅L, K⁆ ≤ pCoreOf 2 H :=
    hcommK.trans (inf_le_left.trans
      (CFSG.Quasithin.H13.U3.pCoreOf_le_pCoreOf_sup_of_le hKL))
  have hlt : CFSG.Open.pRank 3 L + 1 ≤ CFSG.Open.pRank 3 H :=
    CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf
      (q := 3) (by norm_num) hLH hKH hcommH hKperf h3K
  have hHle : H ≤ UC22.conjClosure D.M L := by
    refine sup_le hLle ?_
    rw [hKdef]
    exact le_iSup₂_of_le (L.map (MulAut.conj g).toMonoidHom) ⟨g, hg, rfl⟩ le_rfl
  have hHle2 : CFSG.Open.pRank 3 H ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hHle).trans h18O
  omega

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
