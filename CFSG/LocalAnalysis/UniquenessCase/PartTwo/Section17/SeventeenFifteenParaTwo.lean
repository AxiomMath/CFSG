module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmallPermuting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmallNormal914
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNAbstract
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNReduction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27
import CFSG.GroupTheory.PerfectCoreSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_dvd_three_of_isL2Over17_seven {K X : Subgroup G} (h7 : IsL2Over17 (Bar2 K) 7)
    (hXK : X ≤ K) (hX : IsPGroup 3 X) : Nat.card X ∣ 3 := by
  have hbar : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168 :=
    card_of_isL2Odd_seven (isL2Odd_seven_of_isL2Over17_seven h7)
  have hK := Subgroup.card_eq_card_quotient_mul_card_subgroup (s := CFSG.pCore 2 ↥K)
  rw [hbar] at hK
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hdvd : Nat.card X ∣ Nat.card K := Subgroup.card_dvd_of_le hXK
  rw [hK, ha, hn] at hdvd
  have hcop : Nat.Coprime (3 ^ n) (2 ^ a) := Nat.Coprime.pow n a (by norm_num)
  have h168 : 3 ^ n ∣ 168 := hcop.dvd_of_dvd_mul_right hdvd
  rw [hn]
  have hle : n ≤ 1 := by
    by_contra h
    have h9 : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    have h9' := h9.trans h168
    norm_num at h9'
  interval_cases n <;> norm_num

theorem inf_conjSubgroup_eq_bot_of_mem_conjSetOf {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h17_7 : R17_7At D V₀ V L r q hC)
    (h7 : IsL2Over17 (Bar2 L) 7) {K X : Subgroup G} (hK : K ∈ conjSetOf D.M L)
    (hXK : X ≤ K) (hXp : IsPGroup 3 X) :
    ∀ g : G, g ∉ D.M → X ⊓ conjSubgroup D.M g = ⊥ := by
  intro g hg
  have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.RankThree.PartOne.K1214.eq_bot_of_pGroup_le (hXp.to_le inf_le_left)
    (le_inf (inf_le_left.trans hXK) inf_le_right)
    (by simpa [CFSG.Quasithin.conjSubgroup] using
      not_dvd_card_inf_of_mem_conjSetOf hC h17_7 h7 hK g⁻¹ hg')

theorem rankThreeGamma_le_of_mem_conjSetOf {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h17_3 : R17_3At D V₀ V)
    (h7 : IsL2Over17 (Bar2 L) 7) {K X : Subgroup G} (hK : K ∈ conjSetOf D.M L)
    (hXK : X ≤ K) (hXp : IsPGroup 3 X) : rankThreeGamma 1 3 X ≤ D.M := by
  obtain ⟨u, huM, rfl⟩ := hK
  have hMu : D.M.map (MulAut.conj u).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer huM)
  have hKC : L.map (MulAut.conj u).toMonoidHom ∈ calC D.M :=
    UC6S846.calC_map D.M _ hMu hC.memL
  have h7K : IsL2Over17 (Bar2 (L.map (MulAut.conj u).toMonoidHom)) 7 :=
    isL2Over17_of_mulEquiv
      (UC6S846.bar2Equiv (Subgroup.equivMapOfInjective L (MulAut.conj u).toMonoidHom
        (MulAut.conj u).injective)).symm h7
  have hthin : F08.Thin8 (L.map (MulAut.conj u).toMonoidHom) :=
    thin8_of_isL2Over17_seven h7K
  have hXdvd : Nat.card X ∣ 3 := card_dvd_three_of_isL2Over17_seven h7K hXK hXp
  rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
  intro Y hYX hYrank
  obtain ⟨A, hAY, -, hAcard⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained 3 Y (by omega)
  have h3A : 3 ∣ Nat.card A := by
    rw [hAcard]
    exact dvd_pow_self 3 (by omega)
  have h3Y : 3 ∣ Nat.card Y := h3A.trans (Subgroup.card_dvd_of_le hAY)
  have hY3 : Nat.card Y = 3 :=
    Nat.dvd_antisymm ((Subgroup.card_dvd_of_le hYX).trans hXdvd) h3Y
  exact h17_3 _ hKC hthin Y ⟨3, Nat.prime_three, by norm_num, hY3, hYX.trans hXK⟩

theorem mem_calP_of_mem_conjSetOf {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h17_3 : R17_3At D V₀ V)
    (h17_7 : R17_7At D V₀ V L r q hC) (h7 : IsL2Over17 (Bar2 L) 7) {K X : Subgroup G}
    (hK : K ∈ conjSetOf D.M L) (hXK : X ≤ K) (hXp : IsPGroup 3 X) :
    X ∈ CFSG.LocalAnalysis.WeakClosure81.calP V₀ := by
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    refine ⟨3, Nat.prime_three, by norm_num, hXp, ?_, ?_, ?_⟩
    · rw [Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))]
      exact le_top
    · rw [Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))]
      exact le_top
    · intro g hg
      rw [Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))] at hg
      exact absurd (Subgroup.mem_top g) hg
  · exact TwelveSixteen.mem_calP D (hyp125_inCalV hC.hyp125 hV0) (hyp125_isTI hC.hyp125 hV0)
      Nat.prime_three (by norm_num) hXp
      (fun g hg _ => inf_conjSubgroup_eq_bot_of_mem_conjSetOf hC h17_7 h7 hK hXK hXp g hg)
      (rankThreeGamma_le_of_mem_conjSetOf hC h17_3 h7 hK hXK hXp)

theorem sylow_three_mem_calP_of_normal {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h17_3 : R17_3At D V₀ V)
    (h17_7 : R17_7At D V₀ V L r q hC) (h7 : IsL2Over17 (Bar2 L) 7)
    (hN : (L.subgroupOf (L ⊔ D.T)).Normal) :
    ∀ P : Subgroup G, IsSylowIn 3 P (L ⊔ D.T) →
      P ∈ CFSG.LocalAnalysis.WeakClosure81.calP V₀ := by
  intro P hP
  have hTL : D.T ≤ normalizer (L : Set G) :=
    le_sup_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hN)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact mem_calP_of_mem_conjSetOf hC h17_3 h17_7 h7 (PartOne.Section8.mem_conjSetOf_self D.M L)
    (CFSG.AGLEmbedding.le_of_le_sup_of_isPGroup_of_ne (by norm_num) D.sylowM.isPGroup hTL
      hP.isPGroup (sup_comm L D.T ▸ hP.le)) hP.isPGroup

theorem exists_swap_pair_mem_calP (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h17_3 : R17_3At D V₀ V) (h17_7 : R17_7At D V₀ V L r q hC)
    (h7 : IsL2Over17 (Bar2 L) 7) (h3 : ¬ 2 < (conjSetOf D.M L).ncard)
    (hN : ¬ (L.subgroupOf (L ⊔ D.T)).Normal) :
    ∃ L₂ X : Subgroup G,
      (∃ t ∈ D.T, L₂ = CFSG.Quasithin.conjSubgroup L t) ∧ L ≠ L₂ ∧
      (∀ t ∈ D.T, CFSG.Quasithin.conjSubgroup L t = L ∨
        CFSG.Quasithin.conjSubgroup L t = L₂) ∧
      IsSylowIn 3 X (L ⊔ D.T) ∧
      X ⊓ L ∈ CFSG.LocalAnalysis.WeakClosure81.calP V₀ ∧
      X ⊓ L₂ ∈ CFSG.LocalAnalysis.WeakClosure81.calP V₀ := by
  obtain ⟨L₂, hL₂conj, hLne, hall⟩ := exists_conj_pair_of_not_normal h3 hN
  obtain ⟨X, hXsyl, -⟩ :=
    @exists_isSylowIn_ge G _ _ 3 ⟨Nat.prime_three⟩ (L ⊔ D.T) (⊥ : Subgroup G) bot_le
      (IsPGroup.of_card (n := 0) (by simp))
  have hL₂mem : L₂ ∈ conjSetOf D.M L := by
    obtain ⟨s, hs, rfl⟩ := hL₂conj
    exact ⟨s⁻¹, D.sylowM.le (D.T.inv_mem hs), by rw [CFSG.Quasithin.conjSubgroup]⟩
  have hLL : L ∈ conjSetOf D.M L := PartOne.Section8.mem_conjSetOf_self D.M L
  exact ⟨L₂, X, hL₂conj, hLne, hall, hXsyl,
    mem_calP_of_mem_conjSetOf hC h17_3 h17_7 h7 hLL inf_le_right
      (hXsyl.isPGroup.to_le inf_le_left),
    mem_calP_of_mem_conjSetOf hC h17_3 h17_7 h7 hL₂mem inf_le_right
      (hXsyl.isPGroup.to_le inf_le_left)⟩

theorem gap17_15_paraTwo_inner_holds (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G)
    (h88 : W3Thm88 G) (h126 : R126 D) {V₀ V L : Subgroup G} {r q : ℕ}
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) (hKL0 : K_L27Local)
    (hC : Ctx17_6 D V₀ V L r q) (h17_3 : R17_3At D V₀ V) (h17_7 : R17_7At D V₀ V L r q hC)
    (h7 : IsL2Over17 (Bar2 L) 7) (hYs : IsL2Over17 (Bar2 (L ⊔ D.T)) 7) :
    Nat.card V₀ ≤ 4 := by
  obtain ⟨X₁, X₂, hX₁L, hX₂L, hX₁c, hX₂c, hperm₁, hperm₂, hLgen⟩ :=
    exists_pair_of_bar2_l2 D hC.memL h7 hYs hKL0
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hC.memL.1
  have hX₁p : IsPGroup 3 X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁c]; norm_num)
  have hX₂p : IsPGroup 3 X₂ := IsPGroup.of_card (n := 1) (by rw [hX₂c]; norm_num)
  have hLL := PartOne.Section8.mem_conjSetOf_self D.M L
  have hU : UniqueMax D.M (X₁ ⊔ X₂ ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D hLgen
      (sup_le (sup_le (hX₁L.trans hLM) (hX₂L.trans hLM)) D.sylowM.le) h17_7.1
  exact card_vzero_le_four_of_permuting_pair hTim hcat D h66 h86 h88 h126 hC.hyp125 h93
    Nat.prime_three (by norm_num) hX₁p
    (fun g hg _ => inf_conjSubgroup_eq_bot_of_mem_conjSetOf hC h17_7 h7 hLL hX₁L hX₁p g hg)
    (rankThreeGamma_le_of_mem_conjSetOf hC h17_3 h7 hLL hX₁L hX₁p) hperm₁ hX₂p
    (fun g hg _ => inf_conjSubgroup_eq_bot_of_mem_conjSetOf hC h17_7 h7 hLL hX₂L hX₂p g hg)
    (rankThreeGamma_le_of_mem_conjSetOf hC h17_3 h7 hLL hX₂L hX₂p) hperm₂ hU

theorem gap17_15_paraTwoOuter_holds (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G)
    (h88 : W3Thm88 G) (h126 : R126 D) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h17_3 : R17_3At D V₀ V)
    (h17_7 : R17_7At D V₀ V L r q hC) (h915 : W3Lem915 G)
    (h3 : Gap17_15_threeConj D V₀ V L r q hC)
    (hAut : Gap17_15_autPGL2 D V₀ V L r q hC) :
    Gap17_15_paraTwoOuter D V₀ V L r q hC := by
  intro h7 hYs
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hC.memL.1
  have hNM : L ⊔ D.T ≤ D.M := sup_le hLM D.sylowM.le
  have hsubN : CFSG.Open.IsSubnormal L (L ⊔ D.T) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hC.memL.1 le_sup_left hNM
  have hLperf : L = CFSG.Quasithin.perfectCore (L ⊔ CFSG.Open.pCoreOf 2 (L ⊔ D.T)) :=
    (CFSG.GroupTheory.perfectCore_sup_pCoreOf_eq le_sup_left hsubN hC.memL.2.1).symm
  have hU : UniqueMax D.M (L ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D le_sup_left hNM h17_7.1
  by_cases hV0 : V₀ = ⊥
  · rw [hV0]; simp
  · have hNV : L ⊔ D.T ≤ normalizer (V₀ : Set G) :=
      (normalizer_eq_of_inCalV D (hyp125_inCalV hC.hyp125 hV0)) ▸ hNM
    by_cases hN : (L.subgroupOf (L ⊔ D.T)).Normal
    · obtain ⟨-, A, hgrp, φ, hsurj, hker, hPGL⟩ := hAut h7 hYs hN
      exact card_vzero_le_four_of_w3Lem914N7_syl hTim hcat D h66 h86 h88 h126
        (nfReduction7_holds CFSG.LocalAnalysis.WeakClosure81.nfAbstract_holds
            CFSG.LocalAnalysis.WeakClosure81.nfPGL27_holds G) starOfSylThree_holds hC.hyp125 hC.memL hN hLperf
        (exists_bar2_data le_sup_left hsubN hC.memL.2.1 hC.memL.2.2)
        ⟨A, hgrp, φ, hsurj, hker, hPGL⟩
        (sylow_three_mem_calP_of_normal hC h17_3 h17_7 h7 hN) hU
    · obtain ⟨L₂, X, hL₂, hne, hall, hXsyl, hXP1, hXP2⟩ :=
        exists_swap_pair_mem_calP D hC h17_3 h17_7 h7 (h3 h7 hYs) hN
      exact card_vzero_le_four_of_w3Lem915 hTim hcat D h66 h86 h88 h126 h915 hC.hyp125
        (N := L ⊔ D.T) (L := L) (L₁ := L) (L₂ := L₂) le_sup_right hNV (sup_comm ..)
        hLperf (exists_bar2_data_l3 le_sup_left hsubN hC.memL.2.1 hC.memL.2.2 h7) rfl hL₂
        hne hall ⟨X, hXsyl, hXP1, hXP2⟩ hU

theorem gap17_15_paraTwo_holds (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G)
    (h88 : W3Thm88 G) (h126 : R126 D) {V₀ V L : Subgroup G} {r q : ℕ}
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) (hKL0 : K_L27Local)
    (hC : Ctx17_6 D V₀ V L r q) (h17_3 : R17_3At D V₀ V) (h17_7 : R17_7At D V₀ V L r q hC)
    (hOuter : Gap17_15_paraTwoOuter D V₀ V L r q hC) :
    Gap17_15_paraTwo D V₀ V L r q hC := by
  intro h7
  by_cases hYs : IsL2Over17 (Bar2 (L ⊔ D.T)) 7
  · exact gap17_15_paraTwo_inner_holds hTim hcat D h66 h86 h88 h126 h93 hKL0 hC h17_3 h17_7 h7 hYs
  · exact hOuter h7 hYs
