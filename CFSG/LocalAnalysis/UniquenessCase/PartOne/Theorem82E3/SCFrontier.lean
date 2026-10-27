module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFixedCentralizers
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332THolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd
import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Lift
import CFSG.LocalAnalysis.GLTheoremA.S3.Basic

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha.Theta
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha.FivePrime
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha.Lift
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha.Actor
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCTransitive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs812Outer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableAltTenOf
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection
public import CFSG.CGT.PushingUpLit.SolKNA.RankGe2Sz
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputK11Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1L3Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs812Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.L3OvergroupHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1CoverHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49Core
public import CFSG.LocalAnalysis.UniquenessCase.UCK461Holds
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Yardstones.M50b1bb4a7c08.SlotInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.Yardstones.Mf4cdcdf2e013 (Asc83CComponent QuasisimpleModOTwo)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G] {D : Data G}





section RankOneControl



theorem sc_fixed_three_prime_theta_normalizes_outside_M_of_cyclic_p_prime_orbit_gt_five
    {G : Type} [Group G] [Finite G] (hS : Standing G) (_hUC : CFSG.Open.rankThreeUC G)
    (_hC : AGL81TheoremC G) (S : Setup G) (_hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (_h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (_hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (_hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (_hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (_hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (_hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (_hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (_hPL : P ≤ c.L) (_hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (_hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (_ha : a ∈ d.AA) (_ha1 : a ≠ 1)
    (_hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype)
    (_hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M)
    (_hFull : CFSG.Open.rankThreeGamma 2 3 d.AA = ⊤)
    (_hdelta : ¬ p ∣ Nat.card ↥(d.M ⊓ centralizer (d.AA : Set G)))
    (hp5 : 5 < p) : ∀ x ∈ d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
      ¬ 3 ∣ Nat.card L → ¬ L ≤ d.M →
      let C := centralizer ({x} : Set G)
      let ρ := QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 C)
      let A := (d.AA.subgroupOf C).map ρ
      let J := (L.subgroupOf C).map ρ
      let K := CFSG.SignalizerFunctorTheorem.McBride.orbitClosure J A
      ¬ p ∣ Nat.card J →
      (∃ i : Fin 3, ∃ a : C, (a : G) ∈ d.A i ∧
        A ≤ centralizer (K : Set (C ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 C)) ⊔ zpowers (ρ a)) →
        d.AA ≤ normalizer (L : Set G) := by
  intro x hx _hx1 L hL hL3 _hLM
  dsimp only
  intro hpJ hcyclic
  classical
  let C := centralizer ({x} : Set G)
  let θ := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 C
  let ρ := QuotientGroup.mk' θ
  let A := (d.AA.subgroupOf C).map ρ
  let J := (L.subgroupOf C).map ρ
  have hcal : ∀ i, d.Lf i ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC d.M := by
    intro i
    rw [hdM]
    exact ⟨(hcomp i).2.1, (hcomp i).2.2.1, (hcomp i).2.2.2.2⟩
  have hK : CFSG.Open.IsKGroup d.M := by rw [hdM]; exact c.kProper.isKGroup _ c.M_ne_top
  have hLsub : L.subgroupOf C ∈ CFSG.RankThree.thetaComponents 3 C := by
    obtain ⟨L0, hL0, he⟩ := hL
    rw [← he, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact hL0
  have hLC : L ≤ C := by
    obtain ⟨L0, hL0, he⟩ := hL
    rw [← he]
    exact Subgroup.map_subtype_le _
  have hJ : CFSG.IsComponent J := CFSG.RankThree.isComponent_map_of_mem_thetaComponents Nat.prime_three hLsub
  have hJ3 : ¬ 3 ∣ Nat.card J := by
    intro h
    have hd : Nat.card J ∣ Nat.card (L.subgroupOf C) := by
      simpa only [MonoidHom.range_comp, Subgroup.range_subtype] using
        Subgroup.card_range_dvd (ρ.comp (L.subgroupOf C).subtype)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv] at hd
    exact hL3 (h.trans hd)
  have hAC : d.AA ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (d.S_commute a x (d.AA_le_S ha) (d.AA_le_S hx))
  by_contra hn
  have hmove : ¬ A ≤ normalizer (J : Set (C ⧸ θ)) := by
    intro h
    have hN := ((CFSG.RankThree.theta_component_quotient_structure Nat.prime_three hLsub).2.2.2.2.2.2.2.2.2.2
      (d.AA.subgroupOf C)).mpr h
    have hg := CFSG.LocalAnalysis.GLTheoremA.I113.le_normalizer_map_subtype hAC hN
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLC] at hg
    exact hn hg
  have hFactorPlane : ∀ i j : Fin 3, i ≠ j → ∀ b ∈ d.A i ⊔ d.A j, b ≠ 1 →
      let C := centralizer ({b} : Set G)
      C = (C ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 C).map C.subtype := by
    intro i j _hij b hb hb1
    have hAi : ∀ i, d.A i ≤ d.AA := by
      intro i
      rw [d.AA_def]
      fin_cases i
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    have hbAA := (sup_le (hAi i) (hAi j)) hb
    have h := hFactor (zpowers b) (Subgroup.zpowers_le.mpr hbAA) (by
      rw [Nat.card_zpowers]; exact orderOf_eq_prime (d.isElemAbelian_AA.2 b hbAA) hb1)
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  exact hmove (SCThetaComponents.le_normalizer_component_of_cyclic_orbit_of_actual_data c d hcal hinj
    (hdM.symm ▸ c.pRank_three_M.le) hK hdL
    ((PartTwo.Three.dataOfSetup hS S).sig_prime p hSC.1).1 hp5 hRank hFactorPlane hx hJ hJ3 hcyclic)



theorem sc_fixed_three_prime_theta_normalizes_outside_M
    {G : Type} [Group G] [Finite G] (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPL : P ≤ c.L) (hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (ha : a ∈ d.AA) (ha1 : a ≠ 1)
    (hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype)
    (hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M)
    (hFull : CFSG.Open.rankThreeGamma 2 3 d.AA = ⊤) : ∀ x ∈ d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
      ¬ 3 ∣ Nat.card L → ¬ L ≤ d.M → d.AA ≤ normalizer (L : Set G) := by
  intro x hx hx1 L hL hL3 hLM
  by_cases hnorm : d.AA ≤ normalizer (L : Set G)
  · exact hnorm
  let C := centralizer ({x} : Set G)
  let ρ := QuotientGroup.mk' (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 C)
  let A := (d.AA.subgroupOf C).map ρ
  let J := (L.subgroupOf C).map ρ
  have hcal : ∀ i, d.Lf i ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC d.M := by
    intro i
    rw [hdM]
    exact ⟨(hcomp i).2.1, (hcomp i).2.2.1, (hcomp i).2.2.2.2⟩
  have hK : CFSG.Open.IsKGroup d.M := by
    rw [hdM]
    exact c.kProper.isKGroup _ c.M_ne_top
  have hLC : L ≤ C := by
    obtain ⟨J₀, hJ₀, he⟩ := hL
    rw [← he]
    exact Subgroup.map_subtype_le _
  have hJs : L.subgroupOf C ∈ CFSG.RankThree.thetaComponents 3 C := by
    obtain ⟨J₀, hJ₀, he⟩ := hL
    rw [← he, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact hJ₀
  have hcompJ : CFSG.IsComponent J :=
    CFSG.RankThree.isComponent_map_of_mem_thetaComponents Nat.prime_three hJs
  have hJ3 : ¬ 3 ∣ Nat.card J := by
    have hcard : Nat.card J ∣ Nat.card (L.subgroupOf C) := by
      change Nat.card ((L.subgroupOf C).map ρ) ∣ Nat.card (L.subgroupOf C)
      simpa only [MonoidHom.range_comp, Subgroup.range_subtype] using
        Subgroup.card_range_dvd (ρ.comp (L.subgroupOf C).subtype)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv] at hcard
    exact fun h => hL3 (h.trans hcard)
  have hAC : d.AA ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (d.S_commute a x (d.AA_le_S ha) (d.AA_le_S hx))
  have hmove : ¬ A ≤ normalizer (J : Set (C ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 C)) := by
    intro hm
    have hsN := ((CFSG.RankThree.theta_component_quotient_structure Nat.prime_three hJs).2.2.2.2.2.2.2.2.2.2
      (d.AA.subgroupOf C)).mpr hm
    have hGN := CFSG.LocalAnalysis.GLTheoremA.I113.le_normalizer_map_subtype hAC hsN
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLC] at hGN
    exact hnorm hGN
  have hcyclic := SCThetaComponents.cyclic_component_orbit_action_of_three_prime d hcal hinj
    (hdM.symm ▸ c.pRank_three_M.le) hK (fun i =>
      (Subgroup.centralizer_le_normalizer _).trans (hdM.symm ▸ hAxis i)) hx hcompJ hJ3 hmove
  have hdelta : ¬ p ∣ Nat.card ↥(d.M ⊓ centralizer (d.AA : Set G)) := by
    rw [hdM]
    exact SCFixedAxes.not_dvd_card_centralizer_AA_of_fixed_factors c hSC d hdM hdL
      hP hdS hinj hperm hPn hRank
  have hpJ : ¬ p ∣ Nat.card J := by
    intro hpJ
    exact hdelta (SCThetaComponents.dvd_card_centralizer_AA_of_cyclic_component_orbit d hx
      (fun i => (Subgroup.centralizer_le_normalizer _).trans (hdM.symm ▸ hAxis i))
      hcompJ hJ3 hmove hcyclic ((PartTwo.Three.dataOfSetup hS S).sig_prime p hSC.1).1 hpJ)
  have hp5 : 5 < p := by
    have hpge := c.five_le_of_mem_sigma hSC.1
    by_contra hlt
    have hpeq : p = 5 := by omega
    have hKC : CFSG.Open.IsKGroup C := by
      have hc : Nat.card (zpowers x) = 3 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (d.isElemAbelian_AA.2 x hx) hx1
      have hkg := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
        (PartTwo.Three.dataOfSetup hS S).standing.simple
        (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
        (E := zpowers x) (by intro hb; rw [hb, Subgroup.card_bot] at hc; norm_num at hc)
      rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hkg
    have h := SCThetaComponents.le_normalizer_component_of_five_prime_actual_data
      CFSG.RankThree.PartTwo.KFacts.kpSz d hcal hinj (hdM.symm ▸ c.pRank_three_M.le) hK
      (fun i => (Subgroup.centralizer_le_normalizer _).trans (hdM.symm ▸ hAxis i)) hx hKC hcompJ hJ3
      (hpeq ▸ hdelta)
    exact hmove h
  exact sc_fixed_three_prime_theta_normalizes_outside_M_of_cyclic_p_prime_orbit_gt_five hS hUC hC S hMS c h812 hSC
    d hdM hdL hP hdS hinj hcomp hperm hPn hRank hAxis hNA hPL hNP hPG a ha ha1 hEscape hFactor hGamma hFull
      hdelta hp5 x hx hx1 L hL hL3 hLM hpJ hcyclic



theorem sc_fixed_three_prime_theta_normalizes_of_outside_M
    {G : Type} [Group G] [Finite G] (hS : Standing G) (_hUC : CFSG.Open.rankThreeUC G)
    (_hC : AGL81TheoremC G) (S : Setup G) (_hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (_h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (_hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (_hdL : d.L = c.L) {P : Subgroup G}
    (_hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (_hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (_hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (_hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (_hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (_hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (_hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (_hPL : P ≤ c.L) (_hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (_hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (_ha : a ∈ d.AA) (_ha1 : a ≠ 1)
    (_hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (_hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype)
    (_hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M)
    (_hFull : CFSG.Open.rankThreeGamma 2 3 d.AA = ⊤)
      (houtside : ∀ x ∈ d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
        ¬ 3 ∣ Nat.card L → ¬ L ≤ d.M → d.AA ≤ normalizer (L : Set G)) :
    ∀ x ∈ d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
      ¬ 3 ∣ Nat.card L → d.AA ≤ normalizer (L : Set G) := by
  intro x hx hx1 L hL hL3
  by_cases hLM : L ≤ d.M
  · have hcal : ∀ i, d.Lf i ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC d.M := by
      intro i
      rw [hdM]
      exact ⟨(hcomp i).2.1, (hcomp i).2.2.1, (hcomp i).2.2.2.2⟩
    have hK : CFSG.Open.IsKGroup d.M := by
      rw [hdM]
      exact c.kProper.isKGroup _ (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Ctx82E3.M_ne_top c)
    exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCThetaComponents.le_normalizer_theta_component_of_three_prime_of_le_M
      d hcal hinj (hdM.symm ▸ c.pRank_three_M.le) hK hx hL hL3 (hdM.symm ▸ hLM)
  · exact houtside x hx hx1 L hL hL3 (by simpa only [hdM] using hLM)



theorem sc_fixed_three_prime_theta_normalizes
    {G : Type} [Group G] [Finite G] (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPL : P ≤ c.L) (hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (ha : a ∈ d.AA) (ha1 : a ≠ 1)
    (hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype)
    (hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M)
    (hFull : CFSG.Open.rankThreeGamma 2 3 d.AA = ⊤) : ∀ x ∈ d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
      ¬ 3 ∣ Nat.card L → d.AA ≤ normalizer (L : Set G) := by
  exact sc_fixed_three_prime_theta_normalizes_of_outside_M hS hUC hC S hMS c h812 hSC d hdM hdL
    hP hdS hinj hcomp hperm hPn hRank hAxis hNA hPL hNP hPG a ha ha1 hEscape hFactor hGamma hFull
    (sc_fixed_three_prime_theta_normalizes_outside_M hS hUC hC S hMS c h812 hSC d hdM hdL
      hP hdS hinj hcomp hperm hPn hRank hAxis hNA hPL hNP hPG a ha ha1 hEscape hFactor hGamma hFull)


theorem sc_fixed_theta_normalizes
    {G : Type} [Group G] [Finite G] (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPL : P ≤ c.L) (hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (ha : a ∈ d.AA) (ha1 : a ≠ 1)
    (hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype)
    (hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M)
    (hFull : CFSG.Open.rankThreeGamma 2 3 d.AA = ⊤) : ∀ x ∈ d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
      d.AA ≤ normalizer (L : Set G) := by
  intro x hx hx1 L hL
  by_cases hdiv : 3 ∣ Nat.card L
  · have hSP : d.S = P := hdS.trans (inf_eq_left.mpr hPL)
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 d.S ⊤ := hSP.symm ▸ hPG
    have hSC : d.S ≤ centralizer ({x} : Set G) := fun s hs =>
      mem_centralizer_singleton_iff.mpr (d.S_commute s x hs (d.AA_le_S hx))
    exact SCThetaComponents.le_normalizer_theta_component_of_actual_sylow_of_dvd
      d (hSyl.of_le hSC le_top) hx hL hdiv
  · exact sc_fixed_three_prime_theta_normalizes hS hUC hC S hMS c h812 hSC d hdM hdL hP hdS
      hinj hcomp hperm hPn hRank hAxis hNA hPL hNP hPG a ha ha1 hEscape hFactor hGamma hFull
      x hx hx1 L hL hdiv

end RankOneControl

section FixedThetaAction


theorem sc_fixed_three_divisible_theta_action_alpha
    {G : Type} [Group G] [Finite G] (hS : Standing G) (_hUC : CFSG.Open.rankThreeUC G)
    (_hC : AGL81TheoremC G) (S : Setup G) (_hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (_h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (_hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (_hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (_hinj : Function.Injective d.Lf)
    (_hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (_hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (_hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (_hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (_hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPL : P ≤ c.L) (_hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (_ha : a ∈ d.AA) (_ha1 : a ≠ 1)
    (_hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype)
    (_hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M)
    (_hFull : CFSG.Open.rankThreeGamma 2 3 d.AA = ⊤) : ∀ x ∈ d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
      3 ∣ Nat.card L →
      Nat.card (CFSG.RankThree.PartTwo.Sec4.autThetaQuot d.AA L) = 9 →
        CFSG.RankThree.LocalRank.thetaAlpha 3
          ((CFSG.RankThree.PartTwo.Sec4.autThetaQuot d.AA L).subgroupOf
            (CFSG.RankThree.PartTwo.Sec4.autThetaQuot (centralizer ({x} : Set G)) L)) = ⊥ := by
  intro x hx hx1 L hL hdiv h9
  have hSP : d.S = P := hdS.trans (inf_eq_left.mpr hPL)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 d.S ⊤ := hSP.symm ▸ hPG
  have hSylM : CFSG.ABGLocalTools.IsSylowOf 3 d.S d.M := by
    rw [hSP, hdM]
    exact hP
  have _hSC : d.S ≤ centralizer ({x} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (d.S_commute s x hs (d.AA_le_S hx))
  have hc : Nat.card (zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (d.isElemAbelian_AA.2 x hx) hx1
  have hK := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
    (PartTwo.Three.dataOfSetup hS S).standing.simple
    (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
    (E := zpowers x) (by intro hb; rw [hb, Subgroup.card_bot] at hc; norm_num at hc)
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hK
  have hfac := hFactor (zpowers x) (zpowers_le.mpr hx) hc
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hfac
  have hle := SCThetaComponents.autThetaQuot_card_le_three_of_mem_thetaComponentsAt_of_dvd
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.kFactInnerAction_holds
    d (hSyl.of_le _hSC le_top) hSylM
    (by simpa only [hdM] using hperm) hx hL hK hdiv hfac
  rw [h9] at hle
  exact False.elim (by omega)

theorem sc_fixed_theta_action_alpha
    {G : Type} [Group G] [Finite G] (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPL : P ≤ c.L) (hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (ha : a ∈ d.AA) (ha1 : a ≠ 1)
    (hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype)
    (hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M)
    (hFull : CFSG.Open.rankThreeGamma 2 3 d.AA = ⊤) : ∀ x ∈ d.AA, x ≠ 1 → ∀ L ∈ CFSG.RankThree.thetaComponentsAt 3 x,
      Nat.card (CFSG.RankThree.PartTwo.Sec4.autThetaQuot d.AA L) = 9 →
        CFSG.RankThree.LocalRank.thetaAlpha 3
          ((CFSG.RankThree.PartTwo.Sec4.autThetaQuot d.AA L).subgroupOf
            (CFSG.RankThree.PartTwo.Sec4.autThetaQuot (centralizer ({x} : Set G)) L)) = ⊥ := by
  intro x hx hx1 L hL h9
  by_cases hdiv : 3 ∣ Nat.card L
  · exact sc_fixed_three_divisible_theta_action_alpha hS hUC hC S hMS c h812 hSC d hdM hdL
      hP hdS hinj hcomp hperm hPn hRank hAxis hNA hPL hNP hPG a ha ha1 hEscape hFactor
      hGamma hFull x hx hx1 L hL hdiv h9
  · have hSP : d.S = P := hdS.trans (inf_eq_left.mpr hPL)
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 d.S ⊤ := hSP.symm ▸ hPG
    have hc : Nat.card (zpowers x) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (d.isElemAbelian_AA.2 x hx) hx1
    have hK := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
      (PartTwo.Three.dataOfSetup hS S).standing.simple
      (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
      (E := zpowers x) (by intro hb; rw [hb, Subgroup.card_bot] at hc; norm_num at hc)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hK
    exact False.elim ((SCThetaComponents.autThetaQuot_card_ne_nine_of_actual_sylow_of_not_three_dvd
      CFSG.RankThree.PartTwo.KFacts.kpSz d
        (hSyl.of_le (fun s hs => mem_centralizer_singleton_iff.mpr
          (d.S_commute s x hs (d.AA_le_S hx))) le_top) hx hL hK hdiv) h9)

end FixedThetaAction

section FixedZeroAlpha



theorem sc_fixed_zero_alpha_false
    {G : Type} [Group G] [Finite G] (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPL : P ≤ c.L) (hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (ha : a ∈ d.AA) (ha1 : a ≠ 1)
    (hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype)
    (hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M)
    (hFull : CFSG.Open.rankThreeGamma 2 3 d.AA = ⊤)
    (hAlpha : ∀ E : Subgroup G, E ≤ d.AA → Nat.card E = 9 →
      CFSG.RankThree.LocalRank.thetaAlpha 3 E = ⊥) : False := by
  classical
  have hcal : ∀ i, d.Lf i ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC d.M := by
    intro i
    rw [hdM]
    exact ⟨(hcomp i).2.1, (hcomp i).2.2.1, (hcomp i).2.2.2.2⟩
  have hM : CFSG.Open.IsKGroup d.M := by
    rw [hdM]
    exact c.kProper.isKGroup _ c.M_ne_top
  have hM3 : CFSG.Open.pRank 3 d.M ≤ 3 := hdM.symm ▸ c.pRank_three_M.le
  have hAxisC : ∀ i, centralizer (d.A i : Set G) ≤ d.M := fun i =>
    (Subgroup.centralizer_le_normalizer _).trans (hdM.symm ▸ hAxis i)
  have hCM : centralizer (d.AA : Set G) ≤ d.M := by
    have hA0 : d.A 0 ≤ d.AA := by rw [d.AA_def]; exact le_sup_left.trans le_sup_left
    exact (Subgroup.centralizer_le hA0).trans (hAxisC 0)
  have hdelta : ¬ p ∣ Nat.card ↥(d.M ⊓ centralizer (d.AA : Set G)) := by
    rw [hdM]
    exact SCFixedAxes.not_dvd_card_centralizer_AA_of_fixed_factors c hSC d hdM hdL
      hP hdS hinj hperm hPn hRank
  have hp : p.Prime := ((PartTwo.Three.dataOfSetup hS S).sig_prime p hSC.1).1
  have hpge : 5 ≤ p := c.five_le_of_mem_sigma hSC.1
  have hMstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded p d.M :=
    hdM.symm ▸ c.isStronglyPEmbedded_of_mem_sigma hSC.1
  have hfacA := hFactor (zpowers a) (Subgroup.zpowers_le.mpr ha) (by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (d.isElemAbelian_AA.2 a ha) ha1)
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hfacA
  have hEA : d.A 0 ⊔ d.A 1 ≤ d.AA := by rw [d.AA_def]; exact le_sup_left
  have hE9 : Nat.card ↥(d.A 0 ⊔ d.A 1) = 9 := by
    simpa using d.card_A_sup_A (by decide : (0 : Fin 3) ≠ 1)
  have hEscA : ¬ centralizer ({a} : Set G) ≤ d.M := by simpa only [hdM] using hEscape
  obtain ⟨b, hb, hb1, hEscB⟩ :=
    SCFixedCentralizers.exists_centralizer_not_le_of_factorization_of_plane
      Nat.prime_three d.isElemAbelian_AA hEA (by simpa using hE9) ha hfacA hEscA
  have hbAA : b ∈ d.AA := hEA hb
  let C : Subgroup G := centralizer ({b} : Set G)
  have hAC : d.AA ≤ C := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr
    (d.S_commute u b (d.AA_le_S hu) (d.AA_le_S hbAA))
  have hKC : CFSG.Open.IsKGroup C := by
    have hc : Nat.card (zpowers b) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (d.isElemAbelian_AA.2 b hbAA) hb1
    have hkg := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
      (PartTwo.Three.dataOfSetup hS S).standing.simple
      (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
      (E := zpowers b) (by intro hb; rw [hb, Subgroup.card_bot] at hc; norm_num at hc)
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hkg
  let θ := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 C
  let ρ := QuotientGroup.mk' θ
  have hθC : CFSG.inSubgroup
      (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3) C ≤ centralizer (d.AA : Set G) :=
    SCZeroAlpha.inSubgroup_le_centralizer_AA_of_thetaAlpha_eq_bot d
      (by decide : (0 : Fin 3) ≠ 1) hb hb1 hAlpha
  have hθM : CFSG.inSubgroup
      (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3) C ≤ d.M := hθC.trans hCM
  have hcoreM : (CFSG.pPrimeCore 3 C).map C.subtype ≤ d.M := by
    by_cases hp5 : p = 5
    · have hnorm : ∀ J : Subgroup (C ⧸ θ), CFSG.IsComponent J → ¬ 3 ∣ Nat.card J →
          (d.AA.subgroupOf C).map ρ ≤ normalizer (J : Set (C ⧸ θ)) := by
        intro J hJ hJ3
        exact SCThetaComponents.le_normalizer_component_of_five_prime_actual_data
          CFSG.RankThree.PartTwo.KFacts.kpSz d hcal hinj hM3 hM hAxisC hbAA hKC hJ hJ3
          (hp5 ▸ hdelta)
      have hno := SCZeroAlpha.three_dvd_card_component_of_five
        CFSG.RankThree.PartTwo.KFacts.kpSz hAC d.isElemAbelian_AA hCM hKC hnorm (hp5 ▸ hdelta)
      exact SCZeroAlpha.pPrimeCore_map_le_of_three_dvd_components hθM hno
    · have hgt : 5 < p := by omega
      obtain ⟨Q, hQC, hQM, hpQ, hcomm⟩ :=
        SCZeroAlpha.exists_perfect_commutator_pPrimeCore_eq_bot c d hcal hdL
          (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
          hp hgt (hRank 2) hb hKC
      exact SCZeroAlpha.pPrimeCore_map_le_of_commutator_eq_bot
        hMstrong hθM hQC hQM hpQ hcomm
  have hfacB := hFactor (zpowers b) (Subgroup.zpowers_le.mpr hbAA) (by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (d.isElemAbelian_AA.2 b hbAA) hb1)
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hfacB
  apply hEscB
  rw [hfacB]
  exact sup_le inf_le_right hcoreM

end FixedZeroAlpha



theorem sc_fixed_full_gamma_two_false
    {G : Type} [Group G] [Finite G] (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPL : P ≤ c.L) (hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (ha : a ∈ d.AA) (ha1 : a ≠ 1)
    (hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype)
    (hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M)
    (hFull : CFSG.Open.rankThreeGamma 2 3 d.AA = ⊤) : False := by
  classical
  have hSP : d.S = P := hdS.trans (inf_eq_left.mpr hPL)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 d.S ⊤ := hSP.symm ▸ hPG
  have hSM : d.S ≤ (PartTwo.Three.dataOfSetup hS S).M := hSP.symm ▸ hP.le
  have hrG := SCFixedCentralizers.pRank_top_le_three_of_actual_sylow c d hSyl hSM
  have hmax := SCFixedCentralizers.maximal_AA_of_pRank_top_le_three d hrG
  have hK : ∀ x ∈ d.AA, x ≠ 1 → CFSG.Open.IsKGroup ↥(centralizer ({x} : Set G)) := by
    intro x hx hx1
    have hc : Nat.card (zpowers x) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (d.isElemAbelian_AA.2 x hx) hx1
    have hkg := CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
      (PartTwo.Three.dataOfSetup hS S).standing.simple
      (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
      (E := zpowers x) (by intro hb; rw [hb, Subgroup.card_bot] at hc; norm_num at hc)
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hkg
  have hlocal : ∀ x ∈ d.AA, x ≠ 1 →
      CFSG.Open.twoLocalPrimeRank 3 ↥(centralizer ({x} : Set G)) ≤ 3 :=
    fun x _ _ => SCFixedCentralizers.twoLocalPrimeRank_centralizer_le_three c x
  have hnorm := sc_fixed_theta_normalizes hS hUC hC S hMS c h812 hSC d hdM hdL hP hdS
    hinj hcomp hperm hPn hRank hAxis hNA hPL hNP hPG a ha ha1 hEscape hFactor hGamma hFull
  have hact := sc_fixed_theta_action_alpha hS hUC hC S hMS c h812 hSC d hdM hdL hP hdS
    hinj hcomp hperm hPn hRank hAxis hNA hPL hNP hPG a ha ha1 hEscape hFactor hGamma hFull
  obtain ⟨hSolv, hInd⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.k341_holds
    G d.AA d.isElemAbelian_AA d.card_AA hmax hK hlocal hnorm hact
  have hAlpha := SCFixedCentralizers.thetaAlpha_eq_bot_of_full_gamma d
    (PartTwo.Three.dataOfSetup hS S).standing.simple
    (PartTwo.Three.dataOfSetup hS S).standing.nonab hFull hSolv hInd
  exact sc_fixed_zero_alpha_false hS hUC hC S hMS c h812 hSC d hdM hdL hP hdS
    hinj hcomp hperm hPn hRank hAxis hNA hPL hNP hPG a ha ha1 hEscape hFactor hGamma hFull hAlpha

theorem sc_fixed_gamma_two_escape_false
    {G : Type} [Group G] [Finite G] (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPL : P ≤ c.L) (hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (ha : a ∈ d.AA) (ha1 : a ≠ 1)
    (hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype)
    (hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M) : False := by
  let X : Ctx82E3.C4Data G (PartTwo.Three.dataOfSetup hS S).M :=
    ⟨S.notCatalog, S.V, S.le, S.le_normalizer, S.elemAbelian, S.not_isTI⟩
  have hFull := c.rankThreeGamma_eq_top_of_isSCPrime
    Section7.SEFive.stronglyEmbeddedFive_holds Section7.stronglyEmbeddedSolvable_holds
    X hSC d hdM hdL hGamma
  exact sc_fixed_full_gamma_two_false hS hUC hC S hMS c h812 hSC d hdM hdL
    hP hdS hinj hcomp hperm hPn hRank hAxis hNA hPL hNP hPG a ha ha1 hEscape hFactor hGamma hFull

theorem sc_fixed_centralizer_escape_false
    {G : Type} [Group G] [Finite G] (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hPn : ∀ i, P ≤ normalizer (d.Lf i : Set G))
    (hRank : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    (hAxis : ∀ i, normalizer (d.A i : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hNA : normalizer (d.AA : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPL : P ≤ c.L) (hNP : normalizer (P : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (a : G) (ha : a ∈ d.AA) (ha1 : a ≠ 1)
    (hEscape : ¬ centralizer ({a} : Set G) ≤ (PartTwo.Three.dataOfSetup hS S).M) : False := by
  classical
  have hSP : d.S = P := hdS.trans (inf_eq_left.mpr hPL)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 d.S ⊤ := hSP.symm ▸ hPG
  have hSr : CFSG.Open.pRank 3 d.S ≤ 3 := by
    have hSM : d.S ≤ (PartTwo.Three.dataOfSetup hS S).M := hSP.symm ▸ hP.le
    exact (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hSM).trans c.pRank_three_M.le
  have hAX : ∀ i, centralizer (d.A i : Set G) ≤ d.M := by
    intro i
    exact (Subgroup.centralizer_le_normalizer (d.A i : Set G)).trans (hdM.symm ▸ hAxis i)
  have hN : normalizer (d.AA : Set G) ≤ d.M := hdM.symm ▸ hNA
  have hPerm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j :=
    hdM.symm ▸ hperm
  have hK : ∀ B : Subgroup G, Nat.card B = 3 → CFSG.Open.IsKGroup ↥(centralizer (B : Set G)) := by
    intro B hc
    exact CFSG.LocalAnalysis.GLTheoremA.S3.isKGroup_cen
      (PartTwo.Three.dataOfSetup hS S).standing.simple
      (PartTwo.Three.dataOfSetup hS S).standing.nonab c.kProper
      (by intro hb; rw [hb, Subgroup.card_bot] at hc; norm_num at hc)
  let h332 := CFSG.LocalAnalysis.UniquenessCase.UCK.k332ThreeAb_holds
  have hFactor : ∀ B : Subgroup G, B ≤ d.AA → Nat.card B = 3 →
      let H : Subgroup G := centralizer (B : Set G)
      H = (H ⊓ d.M) ⊔ (CFSG.pPrimeCore 3 H).map H.subtype := by
    intro B hb hc
    exact SCFixedCentralizers.centralizer_factorization_of_abelian_sylow d hinj hPerm
      hSyl hSr hN hAX h332 hb hc (hK B hc)
  have hGamma : ¬ CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M := by
    intro hG
    have ho : orderOf a = 3 := orderOf_eq_prime (d.isElemAbelian_AA.2 a ha) ha1
    have hc : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, ho]
    have hh := SCFixedCentralizers.centralizer_le_of_abelian_sylow_of_gamma_two_le
      d hinj hPerm hSyl hSr hN hAX h332 (zpowers_le.mpr ha) hc (hK (zpowers a) hc) hG
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, hdM] at hh
    exact hEscape hh
  exact sc_fixed_gamma_two_escape_false hS hUC hC S hMS c h812 hSC d hdM hdL
    hP hdS hinj hcomp hperm hPn hRank hAxis hNA hPL hNP hPG a ha ha1 hEscape hFactor hGamma

theorem sc_transitive_factors_false
    {G : Type} [Group G] [Finite G] (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma)
    (c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S))
    (h812 : ¬ QuasisimpleModOTwo c.L) {p : ℕ} (hSC : c.IsSCPrime p)
    (d : SylowThreeData G) (hdM : d.M = (PartTwo.Three.dataOfSetup hS S).M)
    (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (PartTwo.Three.dataOfSetup hS S).M)
    (hdS : d.S = P ⊓ c.L) (hinj : Function.Injective d.Lf)
    (hcomp : ∀ i, Asc83CComponent (PartTwo.Three.dataOfSetup hS S).M (d.Lf i))
    (hperm : ∀ m ∈ (PartTwo.Three.dataOfSetup hS S).M, ∀ i,
      ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hTrans : ¬ ∀ i, P ≤ normalizer (d.Lf i : Set G)) : False := by
  exact sc_transitive_factors_false_of_inputs hS S c hSC d hdM hdL hP hdS
    hinj hcomp hperm hTrans outerThreeSplit_holds
    Section7.SEFive.stronglyEmbeddedFive_holds
    (stronglyEmbeddedSolvableAltTen_of_kFacts
        CFSG.LocalAnalysis.UniquenessCase.UCK.kFactSmallIdent_holds
        CFSG.LocalAnalysis.UniquenessCase.UCK.kFactOneLieTorus_holds
        CFSG.LocalAnalysis.UniquenessCase.UCK.stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4) Section7.stronglyEmbeddedSolvable_holds
    CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt_holds (perfectAutInner_of_schreier
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds)
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.k326P2S_holds Theorem82.k11_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.k32_holds CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds CFSG.LocalAnalysis.UniquenessCase.UCK.k332ThreeAb_holds
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.asc81bNineThree_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalCGTBlock_proved
    Theorem82.l3NotEvenClassical_holds Theorem82.l3EvenParabolic_holds CFSG.LocalAnalysis.UniquenessCase.UCK.k461_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.k462_holds CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49.k49I_core49
    (CGT.PushingUpLit.SolKNA.solomonTimmesfeldMainNonAbelian_of_cit_lie_sz
        CFSG.Milestones.cl_lit_classical_involution_theorem_models
        (CGT.PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3
            (CGT.PushingUpLit.SolKNA.cit3Inductive_of_citInputs
                CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
            (CGT.PushingUpLit.SolKNA.tightLiftSimple_of_citInputs
                CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots))
        CGT.PushingUpLit.SolKNA.szFpfSimpleNatural_of_certificate) Theorem82.l3Overgroup_holds
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.k341_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.kFactInnerAction_holds

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
