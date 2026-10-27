module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Ctx
public import CFSG.LocalAnalysis.RankFourTheoremC.UniqueFourEndpoints
public import CFSG.LocalAnalysis.UniqueFourCatalog.Glue
public import CFSG.LocalAnalysis.UniquenessCase.UC6Star36a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G]

theorem frob4P_core_le_of_sylow (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ uniqueFourSigma M) (P : Sylow p G)
    (hPM : (P : Subgroup G) ≤ M) : GLBCore p 2 (P : Subgroup G) ≤ M := by
  haveI : Fact p.Prime := ⟨hp.1.1⟩
  obtain ⟨Q, hQM, hQΓ⟩ :=
    CFSG.LocalAnalysis.UniqueFourCatalog.exists_sylow_le_of_uniqueFour hU hM hp
  exact uc22p22q_gamma_two_of_exists (uc22p22q_isSylowOf_of_sylow Q hQM) hQΓ
    (uc22p22q_isSylowOf_of_sylow P hPM)

theorem frob4P_preuniqueness (hU : uniqueFourUnique G) : GLBPreuniqueness G := by
  intro q hq
  refine ⟨?_, fun P => ?_⟩
  · have := CFSG.PreuniquenessRankFour.Helpers.betaFour_globalRank hq
    omega
  · obtain ⟨N, hN, hqN, hPN⟩ := UC6.exists_sigma_ge hU (q := q) hq P.isPGroup'
    exact ⟨N, hN.1, (CFSG.PreuniquenessRankFour.Helpers.weakCore_le_fullCore q _).trans
      (frob4P_core_le_of_sylow hU hN hqN P hPN)⟩

theorem frob4P_d1For (hU : uniqueFourUnique G) : CFSG.AGLEmbeddingD2.D1For G := by
  intro p hp P M hM hcore H hH h3
  exact CFSG.LocalAnalysis.RankFourTheoremC.confinementAtCore_of_uniqueFour hU p P M
    ⟨hp, hM, hcore⟩ H hH (by omega)

theorem frob4P_fullCoreLocality (hU : uniqueFourUnique G) :
    CFSG.LocalAnalysis.RankFourTheoremC.FullCoreLocality G := by
  intro p P M hloc
  exact frob4P_core_le_of_sylow hU hloc.maxLocal
    (CFSG.LocalAnalysis.RankFourTheoremC.mem_sigma_of_core hloc) P
    (CFSG.LocalAnalysis.RankFourTheoremC.sylow_le_of_core hloc)

theorem frob4P_frobGlobal (hS : Standing4 G) (hU : uniqueFourUnique G) : FrobGlobal G := by
  exact ⟨hS.simple, hS.nonab, hS.kProper, hS.charTwo, hS.rank, frob4P_preuniqueness hU,
    frob4P_d1For hU, frob4P_fullCoreLocality hU⟩

theorem frob4P_frobLocal (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) {p : ℕ}
    {P P₀ : Subgroup G} (hH : UC6.Hyp612 (UC6.dataOfSetup4 hS hU S) p P P₀) (h5 : 5 ≤ p)
    (hab : IsMulCommutative P)
    (hcl : uniqueFourClauseTwo (UC6.dataOfSetup4 hS hU S).M P P₀ p) :
    ∃ (P' : Sylow p G) (x : G), (P' : Subgroup G) = P ∧ zpowers x = P₀ ∧
      FrobLocal p P' (UC6.dataOfSetup4 hS hU S).M x := by
  classical
  have hpσ : p ∈ uniqueFourSigma S.M := hH.mem_sig2.1
  have hp : p.Prime := hpσ.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hPtop : CFSG.ABGLocalTools.IsSylowOf p P ⊤ :=
    uc22p22q_isSylowOf_top (UC6.dataOfSetup4 hS hU S) (sigma23Std_ofSetup4 hS hU S) hpσ hH.sylow
  obtain ⟨P', hP'⟩ : ∃ P' : Sylow p G, (P' : Subgroup G) = P := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hPtop
    obtain ⟨-, hPp, hdvd⟩ := hPtop
    exact ⟨hPp.toSylow (by simpa [Subgroup.relIndex_top_right] using hdvd), rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : G, zpowers x = P₀ := by
    haveI : IsCyclic ↥P₀ := isCyclic_of_prime_card (p := p) hH.card
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥P₀)
    refine ⟨(g : G), le_antisymm ?_ ?_⟩
    · rw [zpowers_le]; exact g.2
    · intro y hy
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hg ⟨y, hy⟩)
      exact mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
  refine ⟨P', x, hP', hx, ?_⟩
  subst hP' hx
  obtain ⟨hP₀P, hcard, hwc, hlay, hnotle, hcyc, hfrob, hnorm⟩ := hcl
  have hxP : x ∈ (P' : Subgroup G) := hP₀P (mem_zpowers x)
  have hxM : x ∈ S.M := hH.sylow.le hxP
  have hPcent : (P' : Subgroup G) ≤ centralizer ({x} : Set G) := by
    intro g hg
    rw [mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hab.is_comm.comm ⟨x, hxP⟩ ⟨g, hg⟩)).symm
  have hβ : p ∈ GLBBetaFour G := hpσ.1
  have hrank : 4 ≤ CFSG.Open.pRank p (P' : Subgroup G) :=
    CFSG.LocalAnalysis.RankFourTheoremC.four_le_pRank_sylow hβ P'
  have hPle : (P' : Subgroup G) ≤ S.M ⊓ centralizer ({x} : Set G) :=
    le_inf hH.sylow.le hPcent
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p ((P' : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)) := by
    rw [inf_eq_left.2 hPcent]
    exact uc22p22q_isSylowOf_of_sylow P' hPcent
  refine
    { p5 := h5
      loc := ⟨hβ, S.maxLocal, (CFSG.PreuniquenessRankFour.Helpers.weakCore_le_fullCore p _).trans
        (frob4P_core_le_of_sylow hU S.maxLocal hpσ P' hH.sylow.le)⟩
      point :=
        { elem := ⟨hxM, ?_, ?_, ?_⟩
          mem := hxP
          sylow := hsyl
          three_le := ?_ }
      conf := fun H hH2 hr => (hU S.M S.maxLocal ⟨p, hpσ⟩).2 H hH2 ⟨p, hpσ, hr⟩
      abel := hab
      weak := hwc
      norm := hnorm
      layer := hlay
      not_le := hnotle
      cyclic := hcyc }
  · rw [← Nat.card_zpowers]; exact hcard
  · exact (by omega : 3 ≤ 4).trans (hrank.trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hPle))
  · intro h
    exact hH.not_le (by rw [← centralizer_zpowers_eq] at h; exact h)
  · rw [inf_eq_left.2 hPcent]
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
