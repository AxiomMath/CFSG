module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightParabolic
public import CFSG.LocalAnalysis.WeakClosure81.NineFiveNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmall17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_8_graphOuter (D : Data G) (V₀ V : Subgroup G) : Prop :=
  Hyp125 D V₀ V → ∀ L : Subgroup G, L ∈ calC D.M → IsL3Odd (Bar2 L) 3 →
    D.T ≤ normalizer (L : Set G) → D.k = 1 →
    (∀ E : Subgroup G, E ≤ L → IsElemAbelian 3 E → Nat.card E = 9 → ¬ Permutes E D.T) →
    8 ≤ Nat.card V₀ →
    L ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 (innerT17_8 D L) : Set G) →
    ¬ normalizer (E3.wClos V₀ 1 D.T : Set G) ≤ D.M →
    E3.wClos V₀ 0 D.T ≤ L ⊔ pCoreOf 2 (L ⊔ D.T)

section Certificates


theorem sup_T_le_normalizer_wClos_innerT
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D)
    (h88 : W3Thm88 G) (hKP : Inputs1719.K_L33ParabolicPair)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (h8 : 8 ≤ Nat.card V₀)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hL3 : IsL3Odd (Bar2 L) 3)
    (hTL : D.T ≤ normalizer (L : Set G)) (hk : D.k = 1) :
    L ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 (innerT17_8 D L) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV h hne
  have hTI : IsTI V₀ := hyp125_isTI h hne
  have h9 : Hyp9 V₀ D.T := hyp9_of_hyp125 hTim hcat D h h8
  have h1 : ¬ normalizer (E3.wClos V₀ 1 D.T : Set G) ≤ D.M :=
    twelve_seven_three_one hTim hcat D h66 h88 h.2 hW hTI h8
      (fun z hz hzc hz1 => hyp125_centralizer_le h hne hz hzc hz1)
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra hns
    have h2 : D.k = 2 := (Data.k_eq_two_iff D).2 hns
    omega
  have hNV : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have h1' : ¬ normalizer (E3.wClos V₀ 1 D.T : Set G) ≤ normalizer (V₀ : Set G) := by
    rwa [hNV]
  have hNM : L ⊔ D.T ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hmemP : ∀ X : Subgroup G, IsPGroup 3 X → X ≤ L ⊔ D.T → X ∈ calP V₀ := by
    intro X hXp hXLT
    have hXM : X ≤ D.M := hXLT.trans hNM
    refine TwelveSixteen.mem_calP D hW hTI Nat.prime_three (by norm_num) hXp ?_ ?_
    · intro g hg _
      have hg' : g⁻¹ ∉ D.M := fun hgM => hg (by simpa using D.M.inv_mem hgM)
      simpa [conjSubgroup] using
        hsp.inf_map_conj_eq_bot Nat.prime_three hXM hXp g⁻¹ hg'
    · exact hsp.rankThreeGamma_one_le_of_le Nat.prime_three hXp hXM
  obtain ⟨X₁, X₂, hR₁, hR₂, hLsup⟩ := exists_radical_pair_17_8 hKP hL hL3 hTL
  have hS1 : innerT17_8 D L ≤ D.T := inf_le_left
  have hTS1 : D.T ≤ normalizer (innerT17_8 D L : Set G) := le_normalizer_innerT17_8 hTL
  have hS2 : ∀ x ∈ D.T, ∀ y ∈ D.T, x ∉ innerT17_8 D L → y ∉ innerT17_8 D L →
      x * y ∈ innerT17_8 D L := innerT17_8_mul_mem hKP hL hL3 hTL
  have hle₁ : X₁ ⊔ innerT17_8 D L ≤
      normalizer (E3.wClos V₀ 0 (innerT17_8 D L) : Set G) :=
    le_normalizer_wClos_of_irreducible_permutes h9 Nat.prime_three (by norm_num)
      (hmemP X₁ hR₁.2.1 hR₁.1) hR₁.2.1 hR₁.2.2.2.1
      hS1 hTS1 hS2 hR₁.2.2.2.2.1
      (fun Y hY hperm => hR₁.2.2.2.2.2 Y hY hperm) h1'
  have hle₂ : X₂ ⊔ innerT17_8 D L ≤
      normalizer (E3.wClos V₀ 0 (innerT17_8 D L) : Set G) :=
    le_normalizer_wClos_of_irreducible_permutes h9 Nat.prime_three (by norm_num)
      (hmemP X₂ hR₂.2.1 hR₂.1) hR₂.2.1 hR₂.2.2.2.1
      hS1 hTS1 hS2 hR₂.2.2.2.2.1
      (fun Y hY hperm => hR₂.2.2.2.2.2 Y hY hperm) h1'
  have hLle : L ≤ normalizer (E3.wClos V₀ 0 (innerT17_8 D L) : Set G) :=
    hLsup.trans (by
      rw [sup_assoc]
      exact sup_le (le_sup_left.trans hle₁) hle₂)
  have hTle : D.T ≤ normalizer (E3.wClos V₀ 0 (innerT17_8 D L) : Set G) :=
    hTS1.trans (E3.normalizer_le_normalizer_wClos (V := V₀) (i := 0) (innerT17_8 D L))
  exact sup_le hLle hTle

theorem gap17_8_graphV0_of (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D)
    (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D) (h869 : F08.R869 D)
    (hKP : Inputs1719.K_L33ParabolicPair) {V₀ V : Subgroup G}
    (hOut : Gap17_8_graphOuter D V₀ V) : Gap17_8_graphV0 D V₀ V := by
  intro hV L hL hL3 hTL hk hE9
  by_contra h4
  have hV₀p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup hV.pairFacts.elemAbelian₀
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV₀p
  rw [hm] at h4
  have h8 : 8 ≤ Nat.card V₀ := by
    rw [hm]
    have hm3 : 3 ≤ m := by
      by_contra h
      apply h4
      have hm2 : m ≤ 2 := by omega
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV hV hne
  have hTI : IsTI V₀ := hyp125_isTI hV hne
  have h1 : ¬ normalizer (E3.wClos V₀ 1 D.T : Set G) ≤ D.M :=
    twelve_seven_three_one hTim hcat D h66 h88 hV.2 hW hTI h8
      (fun z hz hzc hz1 => hyp125_centralizer_le hV hne hz hzc hz1)
  have hN : L ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 (innerT17_8 D L) : Set G) :=
    sup_T_le_normalizer_wClos_innerT hTim hcat D h66 h88 hKP hV h8 hL hL3 hTL hk
  have hWT : E3.wClos V₀ 0 D.T ≤ innerT17_8 D L :=
    le_inf (E3.wClos_le 0 D.T) (hOut hV L hL hL3 hTL hk hE9 h8 hN h1)
  have hEq : E3.wClos V₀ 0 (innerT17_8 D L) = E3.wClos V₀ 0 D.T :=
    CFSG.Quasithin.Vol2.Ch11.SecD.wClos_zero_eq_of_le (T := D.T) inf_le_left hWT
  have hNle : L ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) := by
    rw [← hEq]
    exact hN
  have hNM : L ⊔ D.T ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hF5 : UniqueMax D.M (L ⊔ D.T) :=
    Inputs1719.uniqueMax_sup_T_of_not_thin h869 hL (not_thin8_of_isL3Odd hL3)
  exact twelve_seven_one hTim hcat D h86 h126 hV.2 hW hTI h8
    (uc22p22u_uniqueMax_mono D (le_inf hNM hNle) inf_le_left hF5)

theorem seventeen_eight_of_outer {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h880 : F08.R880 D)
    (h17_1 : R17_1At D V₀ V hC.hyp125)
    (h17_7 : R17_7_1At D V₀ V L r q hC) (h127 : R127 D) (h117 : C117 D V₀ V)
    (hU33 : Inputs1719.K_U33Local) (hL33 : Inputs1719.K_L33Local)
    (hK : Inputs1719.K_U33SThreePair) (hK8 : Inputs1719.K_U33AutE8)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (h86 : W3Lem86_1 G) (h88 : W3Thm88 G)
    (hKP : Inputs1719.K_L33ParabolicPair) (hOut : Gap17_8_graphOuter D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h77 : Inputs1719.W4Lem7_7)
    (hKL : Inputs1719.K_L33AutE8)
    (h411 : W4Lem4_11Prime) (h869 : F08.R869 D)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h111 : W3Thm111 G) (h126 : R126 D) (h618 : W3_6_18 G)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) (h416 : Inputs1719.W4Lem4_16) :
    R17_8At D V₀ V L r q hC :=
  seventeen_eight_of hC h880 h17_1
    (r17_4AtA_holds D h111 h126 h127 h618 hTim hcat h66 h88 h86 hx h61 h1114 h162 hTor h1482
      h183 hC.hyp125 h93 h1669 (Inputs1719.w4Lem4_16b_of_w4Lem4_16 h416) h77)
    h17_7 h127 h117 hU33 hL33 hK hK8
    (gap17_8_graphV0_of hTim hcat D h66 h86 h88 h126 h869 hKP hOut)
    h1669 (b17_8BoundTwo_holds h77 hKL D V₀ V hC.hyp125) h411 hx h61 h66 h1114 h162 hTor
    h1482 h183 h111 h126

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
