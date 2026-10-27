module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixO2
public import CFSG.Quasithin.Vol2.F134Orders
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
public import CFSG.LocalAnalysis.UniquenessCase.UC22S206r
public import CFSG.GroupTheory.StronglyEmbeddedTwoResidual
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.Quasithin.EmptyFaithful.S146zXGOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase (fundPred)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certificates


@[expose] def K_G176FunOrder : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (q p : ℕ) (Kb : Subgroup X),
    CFSG.LocalAnalysis.UniquenessCase.IsFundamentalOver q Kb → p.Prime → p ≠ 2 →
      p ∣ q * (q ^ 2 - 1) → p ∣ Nat.card ↥Kb

@[expose] def K_G176L2RankThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), 3 ≤ f → IsL2Over17 X (3 ^ f) →
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)

theorem three_dvd_card_of_isL2Over17_abs {X : Type} [Group X] [Finite X] {q : ℕ}
    (h : IsL2Over17 X q) : 3 ∣ Nat.card X := by
  obtain ⟨r, f, hr, hr2, hq, hf, hm⟩ := h
  exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSL_two
    (CFSG.Blueprint.LieModel.statedClassicalModel hm (by simp [CFSG.Blueprint.classicalTags]))

theorem three_dvd_card_of_isFundamentalOver {X : Type} [Group X] [Finite X]
    (hK : K_G176FunOrder) {q : ℕ} {Kb : Subgroup X}
    (h : CFSG.LocalAnalysis.UniquenessCase.IsFundamentalOver q Kb) :
    3 ∣ Nat.card ↥Kb :=
  hK X q 3 Kb h Nat.prime_three (by norm_num) (CFSG.Quasithin.S146zX.three_dvd_mul_sq_sub_one q)

theorem char_dvd_card_of_isFundamentalOver {X : Type} [Group X] [Finite X]
    (hK : K_G176FunOrder) {q r : ℕ} {Kb : Subgroup X}
    (h : CFSG.LocalAnalysis.UniquenessCase.IsFundamentalOver q Kb)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ q) : r ∣ Nat.card ↥Kb :=
  hK X q r Kb h hr hr2 (hrq.trans (dvd_mul_right q (q ^ 2 - 1)))

theorem three_dvd_card_of_mem_delta_two (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {H X : Subgroup G} (hXL : X ≤ L)
    (hL2 : IsL2Over17 (Bar2 X) q) (hH : H = D.T ⊔ X) : 3 ∣ Nat.card H := by
  have hBar : 3 ∣ Nat.card (Bar2 X) := three_dvd_card_of_isL2Over17_abs hL2
  have hX : 3 ∣ Nat.card X :=
    hBar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥X))
  exact hX.trans (Subgroup.card_dvd_of_le (by rw [hH]; exact le_sup_right))

theorem three_dvd_card_of_mem_delta_three (D : Data G) (hK : K_G176FunOrder)
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    {x : G} {X H : Subgroup G}
    (hXLx : X ≤ L.map (MulAut.conj x).toMonoidHom) (hH : H = D.T ⊔ X)
    (hKb : let Lx := L.map (MulAut.conj x).toMonoidHom
      ((X.subgroupOf Lx).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx))) ∈
        FunSet (fundPred q) (Bar2 Lx)
          (((NTL17 D L ⊓ Lx).subgroupOf Lx).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)))) :
    3 ∣ Nat.card H := by
  let Lx : Subgroup G := L.map (MulAut.conj x).toMonoidHom
  let mk : ↥Lx →* Bar2 Lx := QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)
  let Kb : Subgroup (Bar2 Lx) := (X.subgroupOf Lx).map mk
  have hfund : CFSG.LocalAnalysis.UniquenessCase.IsFundamentalOver q Kb := hKb.1
  have hKb3 : 3 ∣ Nat.card ↥Kb := three_dvd_card_of_isFundamentalOver hK hfund
  have hKbX : Nat.card ↥Kb ∣ Nat.card X := by
    have h1 : Nat.card ↥Kb ∣ Nat.card (X.subgroupOf Lx) := Subgroup.card_map_dvd _ mk
    have h2 : Nat.card (X.subgroupOf Lx) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXLx).toEquiv
    rwa [h2] at h1
  have hX : 3 ∣ Nat.card X := hKb3.trans hKbX
  exact hX.trans (Subgroup.card_dvd_of_le (by rw [hH]; exact le_sup_right))

theorem char_dvd_card_of_mem_delta_three (D : Data G) (hK : K_G176FunOrder)
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    {x : G} {X H : Subgroup G}
    (hXLx : X ≤ L.map (MulAut.conj x).toMonoidHom) (hH : H = D.T ⊔ X)
    (hKb : let Lx := L.map (MulAut.conj x).toMonoidHom
      ((X.subgroupOf Lx).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx))) ∈
        FunSet (fundPred q) (Bar2 Lx)
          (((NTL17 D L ⊓ Lx).subgroupOf Lx).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)))) :
    r ∣ Nat.card H := by
  obtain ⟨hr, hr2, t, n, f, hadm, hq, hm⟩ := hC.lie
  have hf : 1 ≤ f := hadm.2.1
  have hrq : r ∣ q := by
    rw [hq]
    exact dvd_pow_self r (by omega)
  let Lx : Subgroup G := L.map (MulAut.conj x).toMonoidHom
  let mk : ↥Lx →* Bar2 Lx := QuotientGroup.mk' (CFSG.pCore 2 ↥Lx)
  let Kb : Subgroup (Bar2 Lx) := (X.subgroupOf Lx).map mk
  have hfund : CFSG.LocalAnalysis.UniquenessCase.IsFundamentalOver q Kb := hKb.1
  have hKbr : r ∣ Nat.card ↥Kb :=
    char_dvd_card_of_isFundamentalOver hK hfund hr hr2 hrq
  have hKbX : Nat.card ↥Kb ∣ Nat.card X := by
    have h1 : Nat.card ↥Kb ∣ Nat.card (X.subgroupOf Lx) := Subgroup.card_map_dvd _ mk
    have h2 : Nat.card (X.subgroupOf Lx) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXLx).toEquiv
    rwa [h2] at h1
  have hX : r ∣ Nat.card X := hKbr.trans hKbX
  exact hX.trans (Subgroup.card_dvd_of_le (by rw [hH]; exact le_sup_right))

theorem gap17_6_O2Rest_of_k_one (D : Data G) (hK : K_G176FunOrder) (hk : D.k = 1)
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q) :
    Gap17_6_O2Rest D V₀ V L r q hC := by
  intro hV₀ h1 H hH g hg
  have hHM : H ≤ D.M := delta_le_M_mem D (fundPred q) hC hH
  have hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra hns
    exact absurd ((Data.k_eq_two_iff D).2 hns) (by omega)
  have h3 : 3 ∣ Nat.card H := by
    by_cases h2 : P17_12_2 q L
    · have hHeq := hH
      rw [Delta17_12, dif_neg h1, dif_pos h2] at hHeq
      obtain ⟨X, hXL, hperm, hL2, hH'⟩ := hHeq
      exact three_dvd_card_of_mem_delta_two D hC hXL hL2 hH'
    · have hHeq := hH
      rw [Delta17_12, dif_neg h1, dif_neg h2] at hHeq
      obtain ⟨x, hx, X, hXLx, hO2, hH', hKb⟩ := hHeq
      exact three_dvd_card_of_mem_delta_three D hK hC hXLx hH' hKb
  exact CFSG.GroupTheory.twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded Nat.prime_three
    (by norm_num) hHM h3 hsp3 g hg

theorem false_of_ree_case_two (D : Data G) (h82 : F08.R82 D) (hk : D.k = 2)
    (hK : K_G176L2RankThree) {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (h2 : P17_12_2 q L) {X : Subgroup G} (hXL : X ≤ L) (hL2 : IsL2Over17 (Bar2 X) q) : False := by
  obtain ⟨n, hq, hRee⟩ := h2
  have hn1 : 1 ≤ n := by
    have hadm := hRee.admissible
    simp [CFSG.Open.StatedLieAdmissible] at hadm
    omega
  have hf3 : 3 ≤ 2 * n + 1 := by omega
  obtain ⟨r₀, f₀, hr₀, hr₀2, hq₀, hf₀, hm₀⟩ := hL2
  have hr₀3 : r₀ = 3 := by
    have hd : r₀ ∣ 3 ^ (2 * n + 1) := by
      rw [← hq, hq₀]
      exact dvd_pow_self r₀ (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hr₀ Nat.prime_three).1 (hr₀.dvd_of_dvd_pow hd)
  subst hr₀3
  have hf₀' : f₀ = 2 * n + 1 := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    change 3 ^ f₀ = 3 ^ (2 * n + 1)
    rw [← hq₀, hq]
  subst hf₀'
  have hL2' : IsL2Over17 (Bar2 X) (3 ^ (2 * n + 1)) :=
    ⟨3, 2 * n + 1, Nat.prime_three, by norm_num, rfl, by omega, hm₀⟩
  have hrank := hK (Bar2 X) (2 * n + 1) hf3 hL2'
  rw [pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)] at hrank
  have hmono : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3 L :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num : 1 < 3) hXL
  have hL3 : CFSG.Open.pRank 3 L ≤ 2 := by
    have h := uc22s206r_pRank_le D h82 hk hC.memL
    rwa [pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)] at h
  omega

theorem gap17_6_O2Rest_of_char (D : Data G) (hSg : UC6S846.SigmaStd D)
    (hK : K_G176FunOrder) {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (h2 : ¬ P17_12_2 q L) (hr : r ∈ D.sig) :
    Gap17_6_O2Rest D V₀ V L r q hC := by
  intro hV₀ h1 H hH g hg
  have hHM : H ≤ D.M := delta_le_M_mem D (fundPred q) hC hH
  have hrp : r.Prime := (D.sig_prime r hr).1
  have hr2 : r ≠ 2 := (D.sig_prime r hr).2
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hC.memL) hr
  have hrdvd : r ∣ Nat.card H := by
    have hHeq := hH
    rw [Delta17_12, dif_neg h1, dif_neg h2] at hHeq
    obtain ⟨x, hx, X, hXLx, hO2, hH', hKb⟩ := hHeq
    exact char_dvd_card_of_mem_delta_three D hK hC hXLx hH' hKb
  exact CFSG.GroupTheory.twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded hrp hr2 hHM
    hrdvd hsp g hg

@[expose] def Gap17_6_O2RestChar (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  V₀ ≠ ⊥ → D.k = 2 → ¬ P17_12_1 r q L → ¬ P17_12_2 q L → r ∉ D.sig →
    ∀ H ∈ Delta17_12 D (fundPred q) r q L, ∀ g : G, g ∉ D.M →
      ¬ twoResidual H ≤ conjSubgroup D.M g

theorem gap17_6_O2Rest_of_inputs (D : Data G) {V₀ V : Subgroup G} (h82 : F08.R82 D)
    (hSg : UC6S846.SigmaStd D) (hKorder : K_G176FunOrder)
    (hKrank : K_G176L2RankThree)
    (hChar : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      Gap17_6_O2RestChar D V₀ V L r q hC) :
    ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      Gap17_6_O2Rest D V₀ V L r q hC := by
  intro L r q hC hV₀ h1 H hH g hg
  by_cases hk : D.k = 1
  · exact gap17_6_O2Rest_of_k_one D hKorder hk hC hV₀ h1 H hH g hg
  · have hk2 : D.k = 2 := by
      have hone : D.k = 1 ∨ D.k = 2 := by
        unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
        split_ifs <;> omega
      omega
    by_cases h2 : P17_12_2 q L
    · have hHeq := hH
      rw [Delta17_12, dif_neg h1, dif_pos h2] at hHeq
      obtain ⟨X, hXL, hperm, hL2, hH'⟩ := hHeq
      exact (false_of_ree_case_two D h82 hk2 hKrank hC h2 hXL hL2).elim
    · by_cases hr : r ∈ D.sig
      · exact gap17_6_O2Rest_of_char D hSg hKorder hC h2 hr hV₀ h1 H hH g hg
      · exact hChar L r q hC hV₀ hk2 h1 h2 hr H hH g hg

section CertificatesTheorem


theorem seventeen_six_of_steps_of_char (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h7 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q), R17_7At D V₀ V L r q hC)
    (h15 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_15At D (fundPred q) V₀ V L r q hC)
    (h16 : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      R17_16At D (fundPred q) V₀ V L r q hC)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h117 : C117 D V₀ V)
    (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D)
    (hKorder : K_G176FunOrder) (hKrank : K_G176L2RankThree)
    (hChar : ∀ (L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q),
      Gap17_6_O2RestChar D V₀ V L r q hC)
    (hK2 : CFSG.ComponentClassification.GS82PumpInputs.OddLieCharUnique) :
    R17_6At D V₀ V :=
  seventeen_six_of_steps D V₀ V hV h7 h15 h16 hx h61 h126 h111 h127 h1114 h162 hTor h1482 h117
    (fun L r q hC =>
      gap17_6_O2Rest_of_inputs D h82 hSg hKorder hKrank hChar L r q hC) hK2

end CertificatesTheorem

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
