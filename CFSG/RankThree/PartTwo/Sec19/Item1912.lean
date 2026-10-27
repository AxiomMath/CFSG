module

public import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements
public import CFSG.RankThree.PartTwo.Sec17.Item1729
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec13.Item136
public import CFSG.RankThree.PartTwo.Sec13.Naturality
public import CFSG.RankThree.PartTwo.Sec19.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_map_conj_subgroupOf {C H : Subgroup G} (hHC : H ≤ C) (g : C) :
    ((H.subgroupOf C).map (MulAut.conj g).toMonoidHom).map C.subtype =
      H.map (MulAut.conj (g : G)).toMonoidHom := by
  rw [Subgroup.map_map]
  have hcomp : C.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp C.subtype := by
    ext y
    simp [MulAut.conj_apply]
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hHC]

theorem exists_omegaA_partTwoT_le_centralizer (h1730 : Sec17.Item1730) (h195 : Item195)
    (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (hset : Sec17.Item13Setup) (hG : Sec19Std G) (hne : ∃ A ∈ partTwoE G, A ∉ partTwoT G) :
    ∃ A ∈ partTwoE G, A ∉ partTwoT G ∧ ∃ c : G, Subgroup.zpowers c ∈ omegaA A ∧
      ∃ E ∈ partTwoT G, E ≤ Subgroup.centralizer ({c} : Set G) := by
  by_contra hcon
  push Not at hcon
  have hst := hG.toPartTwoStanding
  have hS := hG.partTwoS_eq
  have hFE : partTwoF G = partTwoE G := (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hS).1
  obtain ⟨A₀, hA₀, hA₀T⟩ := hne
  obtain ⟨c₀, L₀, hc₀, hL₀⟩ := hset G hst hS A₀ (hFE ▸ hA₀) hA₀T
  have hD₀ : Sec13Data G A₀ c₀ L₀ := ⟨hst, hS, hFE ▸ hA₀, hA₀T, hc₀, hL₀⟩
  have hch := chosen136_of_forall_not_mem h131 hspor hSLC hD₀ (h195 G hG A₀ hA₀ hA₀T).2.2
  refine (h1730 G hst hS A₀ hA₀ hA₀T c₀ hc₀ L₀ hL₀).1 ⟨fun B hB => ?_, hch⟩
  obtain ⟨-, hpath⟩ := hB
  induction hpath with
  | refl => exact hA₀T
  | @tail V B _ hVB ih =>
    obtain ⟨hVE, hBE, F, hF, hFB⟩ := hVB
    intro hBT
    obtain ⟨-, -, a, haF, -⟩ := id hF
    have ha : Subgroup.zpowers a ∈ omegaA V := haF ▸ hF
    have haB : a ∈ B := hFB (haF ▸ Subgroup.mem_zpowers a)
    exact hcon V hVE ih a ha B hBT (le_centralizer_of_mem hBE.1.1 haB)

theorem exists_ctx1912 (h1730 : Sec17.Item1730) (h195 : Item195) (h131 : Item131)
    (hspor : SporadicModels131) (hSLC : SLTwoCenter) (hset : Sec17.Item13Setup)
    (hsetAt : Item13SetupAt) (hG : Sec19Std G) (hne : ∃ A ∈ partTwoE G, A ∉ partTwoT G) :
    ∃ (A : Subgroup G) (c : G) (L E M : Subgroup G), Ctx1912 G A c L E M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, hA, hAT, c, hc, E₀, hE₀, hE₀C⟩ :=
    exists_omegaA_partTwoT_le_centralizer h1730 h195 h131 hspor hSLC hset hG hne
  have hFE : partTwoF G = partTwoE G :=
    (hG.toTheoremFourHyp.partTwoF_eq_partTwoE hG.partTwoS_eq).1
  obtain ⟨L, hL⟩ := hsetAt G hG.toPartTwoStanding hG.partTwoS_eq A (hFE ▸ hA) hAT c hc
  have hAS := h195 G hG A hA hAT
  have hD : Sec13Data G A c L := ⟨hG.toPartTwoStanding, hG.partTwoS_eq, hFE ▸ hA, hAT, hc, hL⟩
  obtain ⟨-, M₀, hM₀⟩ := mem_partTwoT_iff.mp hE₀
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hAC : A ≤ C := le_centralizer_of_mem hA.1.1 (hc.1 (Subgroup.mem_zpowers c))
  have hA3 : IsPGroup 3 (A.subgroupOf C) :=
    (isE27_of_mem_partTwoE hA).isPGroup.comap_subtype
  have hE3 : IsPGroup 3 (E₀.subgroupOf C) :=
    (isE27_of_mem_partTwoE hE₀.1).isPGroup.comap_subtype
  obtain ⟨P, hAP⟩ := hA3.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_map_conj_le_sylow hE3 P
  have hEeq := map_subtype_map_conj_subgroupOf hE₀C g
  have hPG : IsPGroup 3 ((P : Subgroup C).map C.subtype) := P.isPGroup'.map _
  have hEP : E₀.map (MulAut.conj (g : G)).toMonoidHom ≤ (P : Subgroup C).map C.subtype := by
    rw [← hEeq]
    exact Subgroup.map_mono hg
  have hAP' : A ≤ (P : Subgroup C).map C.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAC]
    exact Subgroup.map_mono hAP
  have hEC : E₀.map (MulAut.conj (g : G)).toMonoidHom ≤ C := by
    rw [← hEeq]
    exact Subgroup.map_subtype_le _
  exact ⟨A, c, L, E₀.map (MulAut.conj (g : G)).toMonoidHom,
    M₀.map (MulAut.conj (g : G)).toMonoidHom,
    { hG with
      mem_partTwoE := hA
      not_mem_partTwoT := hAT
      zpowers_mem_omegaA := hc
      mem_lA := hL
      mem_partTwoT := (map_mem_partTwoT_iff (MulAut.conj (g : G))).mpr hE₀
      le_centralizer := hEC
      mem_scriptM := map_conj_mem_scriptM_gamma hM₀ (g : G)
      isPGroup_sup := hPG.to_le (sup_le hEP hAP')
      hypS := hAS
      chosen136 := chosen136_of_forall_not_mem h131 hspor hSLC hD hAS.2.2 }⟩

theorem rank3II_19_12_of (h1730 : Sec17.Item1730) (h131 : Item131) (hspor : SporadicModels131)
    (hSLC : SLTwoCenter) (hset : Sec17.Item13Setup) (hsetAt : Item13SetupAt)
    (h181 : Item181_1) (h1812 : Item181_2) (h195 : Item195)
    (h1918 : Step1918) (h1919O2 : Step1919O2) (h1919 : Step1919) (h1919E : Step1919End) :
    Item1912 := by
  intro G _ _ hG E₀ hE₀
  by_contra hE₀T
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, c, L, E, M, hctx⟩ :=
    exists_ctx1912 h1730 h195 h131 hspor hSLC hset hsetAt hG ⟨E₀, hE₀, hE₀T⟩
  have hLM := h1918 G A c L E M hctx
  have hO2 := h1919O2 G A c L E M hctx hLM
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have h18 : Sec18Std G E M := ⟨hG.toPartTwoStanding, hG.partTwoS_eq, hEE, hctx.mem_scriptM⟩
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E :=
    mem_of_le_centralizer hG.toPartTwoStanding hG.partTwoS_eq hEE
      (hctx.mem_partTwoE.1.2 c hcA) hctx.le_centralizer
  have hc1 : c ≠ 1 := by
    rintro rfl
    have h3 := hctx.zpowers_mem_omegaA.2.1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    omega
  set X := Subgroup.centralizer ({c} : Set G) with hX
  have hQ := pCoreOf_centralizer_ne_bot h181 h1812 hG.hyp191 h18 hcE hc1 hO2
  obtain ⟨H, hH, -⟩ := exists_mem_scriptM_of_isTwoLocal (X := (X : Set G))
    (H := Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G))
    ⟨CFSG.Open.pCoreOf 2 X, hQ, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X, rfl⟩
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  have hXH : X ≤ H := fun x hx => hH.2 hx
  have hLX : L ≤ X := by
    obtain ⟨L', -, hL'⟩ := hctx.mem_lA.1
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hHM : H ≠ M := fun hHM => hLM (hHM ▸ hLX.trans hXH)
  obtain ⟨K, hK, hEK⟩ := h1919 G A c L E M hctx hLM H hH hHM
  exact h1919E G A c L E M hctx hLM H hH hHM K hK hEK

end CFSG.RankThree.PartTwo.Sec19
