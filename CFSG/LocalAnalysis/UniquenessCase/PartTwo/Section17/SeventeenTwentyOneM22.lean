module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmall17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic
public import CFSG.LocalAnalysis.GL83PartI.I713.Extension
public import CFSG.LocalAnalysis.SectionRank.PRankIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_21_M22Data (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → IsSpor (BarInf L) .M22 →
    Nat.card V₀ ≤ 4 ∧ D.sig = {3} ∧
      CFSG.Open.pRank 3 (Mbar D.M V₀ V hV.isElemAbelian) ≤ 2 ∧
        ∀ x : IntMod V hV.isElemAbelian, x.val ∉ V₀ →
          1 < CFSG.Open.pRank 3 (F11.CElt D.M V₀ x.val)

theorem cTilde_normal_of_hyp11 {D : Data G} {V₀ V : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) :
    ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := by
  obtain ⟨hN, -, hle⟩ := ElevenNine.hyp11_ctilde D hH
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 hN

theorem pRank_three_M_eq_three {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (hcard4 : Nat.card V₀ ≤ 4) (hsig : D.sig = {3})
    (hbar : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV.isElemAbelian) ≤ 2) :
    CFSG.Open.pRank 3 D.M = 3 ∧ CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) ≤ 1 ∧
      1 ≤ CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) := by
  have hH : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 hV
  have := cTilde_normal_of_hyp11 (D := D) (V₀ := V₀) (V := V) hH
  obtain ⟨-, -, hCTle⟩ := ElevenNine.hyp11_ctilde D hH
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  obtain ⟨e, -⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V)
    (hV := hV.isElemAbelian) hMs
  have hbarEq : CFSG.Open.pRank 3 (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) =
      CFSG.Open.pRank 3 (Mbar D.M V₀ V hV.isElemAbelian) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    exact (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
  have h3sig : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have h3M : 3 ≤ CFSG.Open.pRank 3 D.M := hx.three_le 3 h3sig
  have h115 := uc22p22q_r115_of D hx h61
  obtain ⟨hCT1, -, -⟩ := h115 V₀ V hH hcard4 3 h3sig
  have hsub := GL83.I713.pRank_top_le_add_pRank_quotient (G := ↥D.M) Nat.prime_three
    ((F11.CTilde D.M V₀ V).subgroupOf D.M)
  have hleft : CFSG.Open.pRank 3 (⊤ : Subgroup ↥D.M) = CFSG.Open.pRank 3 D.M :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup D.M).symm
  rw [hleft] at hsub
  have hCTeq : CFSG.Open.pRank 3 ((F11.CTilde D.M V₀ V).subgroupOf D.M) =
      CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3,
      ← CFSG.SectionRank.pRank_coe_eq_openPRank 3]
    exact CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCTle) 3
  rw [hCTeq] at hsub
  have hbar' : CFSG.Open.pRank 3 (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) ≤ 2 := by
    rw [hbarEq]; exact hbar
  have hle : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) + 2 :=
    hsub.trans (Nat.add_le_add_left hbar' _)
  refine ⟨by omega, hCT1, by omega⟩

theorem isTI_of_cover_bot {D : Data G} {V : Subgroup G} (hV : InCalV D.M V)
    (hcov : ∀ u ∈ V, u ≠ 1 → ∃ X : Subgroup G, X ≤ D.M ∧ UniqueMax D.M X ∧
      X ≤ centralizer ({u} : Set G)) : IsTI V := by
  have hCA : ∀ t ∈ V, t ≠ 1 → centralizer ({t} : Set G) ≤ D.M := by
    intro t ht ht1
    obtain ⟨X, -, hU, hXt⟩ := hcov t ht ht1
    obtain ⟨N, hNmax, hCN⟩ := uc22p22u_exists_isMaxTwoLocal
      (uc22p22u_isTwoLocal_centralizer ht1 (hV.2.2.2.2 t ht))
    have hmem : N ∈ calMOf X := ⟨hNmax, hXt.trans hCN⟩
    rw [hU] at hmem
    have hNM : N = D.M := Set.mem_singleton_iff.mp hmem
    exact hCN.trans (le_of_eq hNM)
  intro g
  by_cases hbot : V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨⟨u, hu⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hu1 : u ≠ 1 := fun h => hne (Subtype.ext h)
  have huV : u ∈ V := hu.1
  have hw : g⁻¹ * u * g ∈ V := CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hu.2
  have hw1 : g⁻¹ * u * g ≠ 1 := by
    intro h
    apply hu1
    have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [this, h]
    group
  have hCu : centralizer ({u} : Set G) ≤ D.M := hCA u huV hu1
  obtain ⟨X, -, hU, hXw⟩ := hcov _ hw hw1
  have hgM : g ∈ D.M := by
    have hXM' : X ≤ uniqueFourConj g D.M := by
      intro x hx
      rw [UC6.mem_uniqueFourConj_iff]
      apply hCu
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hxa : (g⁻¹ * u * g) * x = x * (g⁻¹ * u * g) :=
        Subgroup.mem_centralizer_iff.mp (hXw hx) (g⁻¹ * u * g) rfl
      calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [hxa]
        _ = (g * x * g⁻¹) * u := by group
    have hmem : uniqueFourConj g D.M ∈ calMOf X :=
      ⟨UC6.isMaxTwoLocal_conj D.maxLocal g, hXM'⟩
    rw [hU] at hmem
    have hconj : uniqueFourConj g D.M = D.M := Set.mem_singleton_iff.mp hmem
    rw [← UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal]
    exact UC6.uniqueFourConj_eq_self_iff.mp hconj
  have hgV : g ∈ normalizer (V : Set G) := hV.2.2.1 hgM
  have hVc : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V := by
    ext x
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    exact ((Subgroup.mem_normalizer_iff'').mp hgV x).symm
  change V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = V
  rw [hVc, inf_idem]

theorem pRank_centralizer_eq_of_relIndex_two_pow {D : Data G} {V₀ V : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) (hcard4 : Nat.card V₀ ≤ 4) {v : G} (hv : v ∈ V) (hv0 : v ∉ V₀) :
    CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) =
      CFSG.Open.pRank 3 (F11.CElt D.M V₀ v) := by
  obtain ⟨-, -, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  obtain ⟨n, -, hrel⟩ := r113_holds D V₀ V hH hcard4 v hv hv0
  have hKH : D.M ⊓ centralizer ({v} : Set G) ≤ F11.CElt D.M V₀ v := by
    intro m hm
    obtain ⟨hmM, hmC⟩ := Subgroup.mem_inf.mp hm
    refine ⟨hmM, hMV₀ hmM, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hmC
    have h1 : m * v * m⁻¹ * v⁻¹ = 1 := by rw [hmC]; group
    rw [h1]
    exact V₀.one_mem
  have hnot : ¬ 3 ∣ ((D.M ⊓ centralizer ({v} : Set G)).subgroupOf
      (F11.CElt D.M V₀ v)).index := by
    rw [show ((D.M ⊓ centralizer ({v} : Set G)).subgroupOf
      (F11.CElt D.M V₀ v)).index =
      (D.M ⊓ centralizer ({v} : Set G)).relIndex (F11.CElt D.M V₀ v) from rfl, hrel]
    intro hd
    have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have h1 := CFSG.SectionRank.pRank_top_le_of_not_dvd_index Nat.prime_three
    ((D.M ⊓ centralizer ({v} : Set G)).subgroupOf (F11.CElt D.M V₀ v)) hnot
  have htopCE : CFSG.Open.pRank 3 (⊤ : Subgroup (F11.CElt D.M V₀ v)) =
      CFSG.Open.pRank 3 (F11.CElt D.M V₀ v) :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
  have h2 : CFSG.Open.pRank 3 ((D.M ⊓ centralizer ({v} : Set G)).subgroupOf
      (F11.CElt D.M V₀ v)) =
      CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3,
      ← CFSG.SectionRank.pRank_coe_eq_openPRank 3]
    exact CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH) 3
  have h1' : CFSG.Open.pRank 3 (F11.CElt D.M V₀ v) ≤
      CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) := by
    rw [← htopCE, ← h2]
    exact h1
  exact le_antisymm (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hKH) h1'

theorem pRank_centralizer_ge_two_of_mem_V0 {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (hcard4 : Nat.card V₀ ≤ 4)
    (h3M : CFSG.Open.pRank 3 D.M = 3) {v : G} (hv : v ∈ V₀) (hv1 : v ≠ 1) :
    1 < CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) := by
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) := hV.pairFacts.le_normalizer₀
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) D.M
  have hEcard27 : Nat.card E = 27 := by rw [hEcard, h3M]; norm_num
  have hEV₀ : E ≤ normalizer (V₀ : Set G) := hEM.trans hMV₀
  have : ((E ⊓ centralizer (V₀ : Set G)).subgroupOf E).Normal :=
    ElevenFourteen.normal_inf_centralizer_subgroupOf hEV₀
  have hcyc : IsCyclic (↥E ⧸ (E ⊓ centralizer (V₀ : Set G)).subgroupOf E) :=
    ElevenFourteen.isCyclic_quotient_of_card_le_four Nat.prime_three (by norm_num)
      hEel.isPGroup hEV₀ hcard4
  have hquot : CFSG.Open.pRank 3
      (⊤ : Subgroup (↥E ⧸ (E ⊓ centralizer (V₀ : Set G)).subgroupOf E)) ≤ 1 :=
    CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three
      (Subgroup.topEquiv.isCyclic.2 hcyc)
  have hadd := GL83.I713.pRank_top_le_add_pRank_quotient (G := ↥E) Nat.prime_three
    ((E ⊓ centralizer (V₀ : Set G)).subgroupOf E)
  have htopE' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥E) = CFSG.Open.pRank 3 E :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup E).symm
  rw [htopE'] at hadd
  have hE3 : CFSG.Open.pRank 3 E = 3 := by
    have hle : CFSG.Open.pRank 3 E ≤ 3 := by
      have h := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hEM
      rwa [h3M] at h
    have hge : 3 ≤ CFSG.Open.pRank 3 E := by
      have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := E) le_rfl hEel hEcard
      rwa [h3M] at h
    omega
  rw [hE3] at hadd
  have hNeq : CFSG.Open.pRank 3 ((E ⊓ centralizer (V₀ : Set G)).subgroupOf E) =
      CFSG.Open.pRank 3 (E ⊓ centralizer (V₀ : Set G)) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3,
      ← CFSG.SectionRank.pRank_coe_eq_openPRank 3]
    exact CFSG.pRank_congr_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ centralizer (V₀ : Set G) ≤ E)) 3
  rw [hNeq] at hadd
  have hN2 : 2 ≤ CFSG.Open.pRank 3 (E ⊓ centralizer (V₀ : Set G)) := by omega
  have hNle : E ⊓ centralizer (V₀ : Set G) ≤ D.M ⊓ centralizer ({v} : Set G) := by
    refine le_inf (inf_le_left.trans hEM) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2) v hv).symm
  exact lt_of_lt_of_le (by norm_num : 1 < 2)
    (hN2.trans (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hNle))

theorem gap17_21_M22_of (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (hdata : Gap17_21_M22Data D V₀ V hV) : Gap17_21_M22 D V₀ V := by
  intro L c hk hspor
  obtain ⟨hcard4, hsig, hbar3, hstab⟩ := hdata L c hspor
  have hH : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 hV
  obtain ⟨hPR, -, hCT3⟩ := pRank_three_M_eq_three hV hx h61 h127 hcard4 hsig hbar3
  have h3sig : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have hcov : ∀ u ∈ V, u ≠ 1 → ∃ X : Subgroup G, X ≤ D.M ∧ IsPGroup 3 ↥X ∧
      ¬ IsCyclic ↥X ∧ X ≤ centralizer ({u} : Set G) := by
    intro u hu hu1
    by_cases hu0 : u ∈ V₀
    · have h2 := pRank_centralizer_ge_two_of_mem_V0 hV hcard4 hPR hu0 hu1
      obtain ⟨X, hX, hXel, hXcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
        (D.M ⊓ centralizer ({u} : Set G))
      refine ⟨X, hX.trans inf_le_left, hXel.isPGroup, ?_, hX.trans inf_le_right⟩
      refine uc22p22n_not_isCyclic_of_card Nat.prime_three hXel ?_
      rw [hXcard]
      exact Nat.pow_le_pow_right (by norm_num) h2
    · let x : IntMod V hV.isElemAbelian :=
        IntMod.mk hV.isElemAbelian ⟨u, hu⟩
      have hxval : x.val = u := rfl
      have hxnot : x.val ∉ V₀ := by rw [hxval]; exact hu0
      have hge : 1 < CFSG.Open.pRank 3 (F11.CElt D.M V₀ u) := by
        have := hstab x hxnot
        rwa [hxval] at this
      have hCeq : CFSG.Open.pRank 3 (D.M ⊓ centralizer ({u} : Set G)) =
          CFSG.Open.pRank 3 (F11.CElt D.M V₀ u) :=
        pRank_centralizer_eq_of_relIndex_two_pow hH hcard4 hu hu0
      have hC2 : 2 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({u} : Set G)) := by
        rw [hCeq]; omega
      obtain ⟨X, hX, hXel, hXcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
        (D.M ⊓ centralizer ({u} : Set G))
      refine ⟨X, hX.trans inf_le_left, hXel.isPGroup, ?_, hX.trans inf_le_right⟩
      refine uc22p22n_not_isCyclic_of_card Nat.prime_three hXel ?_
      rw [hXcard]
      exact Nat.pow_le_pow_right (by norm_num) hC2
  have hcovU : ∀ u ∈ V, u ≠ 1 → ∃ X : Subgroup G, X ≤ D.M ∧ UniqueMax D.M X ∧
      X ≤ centralizer ({u} : Set G) := by
    intro u hu hu1
    obtain ⟨X, hXM, hXp, hXnc, hXt⟩ := hcov u hu hu1
    exact ⟨X, hXM, h61 3 h3sig X hXM hXp hXnc, hXt⟩
  have hTI : IsTI V := by
    by_cases hV0 : V₀ = ⊥
    · exact isTI_of_cover_bot hV.inCalV hcovU
    · have hV₀cal : InCalV D.M V₀ := hyp125_inCalV hV hV0
      have hTI₀ : IsTI V₀ := hyp125_isTI hV hV0
      refine ElevenNine.isTI_of_cover_uniqueMax D hV.inCalV hV₀cal hTI₀ ?_
      intro u hu hu0
      exact hcovU u hu (fun h1 => hu0 (h1 ▸ V₀.one_mem))
  exact hH.2.1 hTI

section Certified


theorem seventeen_twentyone_of_data (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) (h17_4 : R17_4AtA D V₀ V hV) (h17_20 : R17_20At D V₀ V)
    (h869 : F08.R869 D) (hC117 : C117 D V₀ V)
    (hKS5 : Inputs1719.K_SporadicNine)
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (hB21 : B17_21Bound D V₀ V hV)
    (hKS6 : Inputs1719.K_M12SThreePair)
    (hKS7 : Inputs1719.K_HSRuParabolics)
    (hdata : Gap17_21_M22Data D V₀ V hV) :
    R17_21At D V₀ V :=
  seventeen_twentyone D V₀ V hV h17_1 h17_4 h17_20 h869 hC117 hKS5 hx h61 h127 h1114 h162 hTor
    h1482 h126 h111 hB21 hKS6 hKS7 (gap17_21_M22_of D V₀ V hV hx h61 h127 hdata)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
