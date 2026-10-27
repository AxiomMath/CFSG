module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xDefs
import CFSG.RankThree.PartTwo.Sec15.Ronan155BigTools
import CFSG.RankThree.PartTwo.Sec15.Ronan155BigRQ
import CFSG.RankThree.PartTwo.Sec15.Ronan152SixHelpers
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec15.Gagen155SplitDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155StepDefs
public import CFSG.RankThree.PartTwo.Sec16.Item161Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem exists_end155N_le_of_ctx155w_big {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h152 : Item152Big A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    (h154 : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Sec16.Item154Pi A (lB A) L')
    (h322 : ∀ {H R : Subgroup G}, Hyp322 H R → CFSG.Open.pCoreOf 2 H ≤ R → IsPGroup 2 R →
      R ≠ ⊥ → ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
        H ≤ Subgroup.normalizer (C : Set G))
    (hUp : Step155Up A c L) (hgrow : Step155GrowW A c L) (hcases : Step155CasesNWBig A c L)
    (hRQ : Step155RQNWBig A c L) {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hXb : Big152 X) (hmax : MaxT155 A X K T) (hab : Above155w A X) :
    ∃ P : Subgroup G, End155N A X K Y M T P ∧ CFSG.Open.pCoreOf 2 Y ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKb : Big152 K := big152_k hC hXb
  set R := CFSG.Open.pCoreOf 2 Y with hR
  have hY3 : Y ∈ scriptY3 A (lB A) := hC.isY.1
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hR1 : R ≠ ⊥ := hY3.1.2
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY3.1.1.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hXY : X ≤ Y := hC.res ▸ oPrimeResidualOf_le_self 3 Y
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hC.res]
    exact le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  have hM' : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hC.mem_m
  obtain ⟨hYM, hAM, hM2, hMF⟩ := facts_of_mem_maximalTwoLocalsContaining h hM'
  have hclaim : Claim155 A K Y := by
    by_cases hKR : K ≤ Subgroup.normalizer (R : Set G)
    · exact claim155_of_le_normalizer_big h153 hC.mem_k hKb hKR hAR
    · exact hgrow h X K Y M T hC hmax hab hKR
  have hRchar : (R.subgroupOf R).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.topCharacteristic
  obtain ⟨J, hJM, hXJ, hJ0⟩ := h152 X hX4 hXb M hM2 (hXY.trans hYM) hMF
  obtain ⟨P, D⟩ := hcases h X K Y M T hC hXb hmax hab J hJM hJ0 hXJ
  set Q := CFSG.Open.pCoreOf 2 (P ⊔ J) with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hJ0.1.1.2
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := D.mem_p.prop.1.1.1.2.2
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    (le_normalizer_sup hAP hAJ).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hQR : Q ≤ R := by
    have hQ𝓠 : Q ∈ scriptQ A (lB A) := mem_scriptQ_of_le D.mem_p.prop.1.1 D.le_qp hAQ
    have hNQ𝓠 : Q ⊓ Subgroup.normalizer (R : Set G) ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hQ𝓠 inf_le_left
        (Late.le_normalizer_inf hAQ (hAR.trans (Sec6.normalizer_le_normalizer_normalizer R)))
    have hNQN : Q ⊓ Subgroup.normalizer (R : Set G) ≤ n155 A K :=
      (le_delta hNQ𝓠 inf_le_right).trans (hclaim R hR1 le_rfl hRchar)
    have hRQN := hRQ h X K Y M T P J hC hXb hmax hab hJM hJ0 hXJ D
    exact le_of_inf_normalizer_le155 hR2 hQ2 D.norm_rq
      (le_inf inf_le_left hNQN |>.trans hRQN)
  have hX1 : X ≠ ⊥ := ne_bot_of_mem_scriptY4 hX4
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_mem_thetaComponentsIn (hYM.trans Subgroup.le_normalizer) hJM hXJ
      (isPerfect_of_mem_scriptY4 hX4) hX1 hYX
  have hRmem : R ∈ invariantPiSubgroups (Subgroup.normalizer (J : Set G)) (A ⊔ X) (piOf 2) :=
    ⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYJ,
      (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2, sup_le hAR (hXY.trans hYR)⟩
  have h154J : ⁅R, J⁆ ≤ CFSG.Open.pCoreOf 2 J ∨ Case154Three A L J X R := by
    rcases h154 c L h.toSec13Data.zpowers_mem_omegaA h.toSec13Data.mem_lA J hJ0 X hX4 hXJ R
        hRmem with h1 | ⟨n, m, hn, hm, ⟨e2⟩, hXε, hXπ, hLX⟩ | h3
    · exact Or.inl h1
    · by_cases hcl : ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧
          L' ∈ lA A c' ∧ L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L'
      · obtain ⟨c', L', hc', hL', heq⟩ := hcl
        rcases h154 c' L' hc' hL' J hJ0 X hX4 hXJ R hRmem with h1' |
            ⟨-, -, -, -, -, -, -, hne⟩ | ⟨⟨e3⟩, -⟩
        · exact Or.inl h1'
        · exact absurd heq hne
        · exact (KFacts.KS14.not_isLThreeEpsAt_j2 2 (2 * n * m)
            (Or.inl ⟨e3.symm.trans e2⟩)).elim
      · exact absurd ⟨⟨n, m, hn, hm, ⟨e2⟩, hXε, hLX⟩, hXπ⟩ (D.case_two hcl)
    · exact Or.inr h3
  have hJΔ : J = delta A (lB A) J := hJ0.1.2.2.1
  have hJN : J ≤ n155 A K := by
    rcases h154J with h1 | h3
    ·
      have hRQ' : R = Q := le_antisymm (D.case_a h1) hQR
      have hJR : J ≤ Subgroup.normalizer (R : Set G) := by
        rw [hRQ']
        exact le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      calc J = delta A (lB A) J := hJΔ
        _ ≤ delta A (lB A) (Subgroup.normalizer (R : Set G)) := delta_mono hJR
        _ ≤ n155 A K := hclaim R hR1 le_rfl hRchar
    ·
      obtain ⟨C, hC1, hCR, hCc, hPJC⟩ := h322 (D.case_b h3) hQR hR2 hR1
      calc J = delta A (lB A) J := hJΔ
        _ ≤ delta A (lB A) (Subgroup.normalizer (C : Set G)) :=
          delta_mono (le_sup_right.trans hPJC)
        _ ≤ n155 A K := hclaim C hC1 hCR hCc
  have hJX' : J = X := by
    by_contra hne
    have hXlt : X < J := lt_of_le_of_ne hXJ (Ne.symm hne)
    have hJK : J ≤ K := le_of_le_n155'_big h h152 h153 hC.mem_k hKb hX4 hJ0 hXJ hC.le_k hJN
    have hOm : omg155 A J ∨ K = J ⊔ CFSG.Open.pCoreOf 2 K := by
      rcases hC.hyp with hom | hKX
      · by_cases hcl : ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧
            L' ∈ lA A c' ∧ L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L'
        · exact Or.inl (omg155_of_le hXJ hcl)
        · have hcl1 := hom.resolve_right hcl
          rw [← hC.res] at hcl1 hcl hXlt
          exact hUp h Y hC.isY hcl1.1 hcl1.2 hcl M hC.mem_m J hJM hJ0 hXlt K hC.mem_k hJK
      · exact Or.inr (le_antisymm (hKX.le.trans (sup_le_sup_right hXJ _))
          (sup_le hJK (CFSG.LieType.BorelTits.pCoreOf_le 2 K)))
    obtain ⟨hJY, hJres⟩ := isY155_of_mem_scriptY0 hJ0
    have hlt : X < oPrimeResidualOf 3 J := by
      rw [hJres]
      exact hXlt
    have hMJ : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ J : Subgroup G) : Set G) :=
      ⟨hC.mem_m.1, fun x hx => (sup_le hAM (le_of_mem_thetaComponentsIn hJM)) hx⟩
    have hΓJ : K ∈ gam155 A (lB A) J (oPrimeResidualOf 3 J) :=
      ⟨hC.mem_k, by rw [hJres]; exact hJK, hJK.trans Subgroup.le_normalizer⟩
    exact hC.not_le ((hab J hJY hlt).2 K hΓJ (by rw [hJres]; exact hOm) M hMJ)
  have hRQ' : R ≤ Q := by
    rcases h154J with h1 | ⟨⟨e1⟩, ⟨e2⟩, -⟩
    · exact D.case_a h1
    · exfalso
      rw [hJX'] at e1
      have hc := Nat.card_congr (e1.symm.trans e2).toEquiv
      rw [KFacts.KS14.card_nativeJ2, card_alternatingGroup_five] at hc
      norm_num at hc
  refine ⟨P, ⟨hJX' ▸ hJM, hJX' ▸ D.mem_p, D.le_tp, ?_, hclaim⟩, hRQ'.trans D.le_qp⟩
  rw [← hJX']
  exact le_antisymm hRQ' hQR

theorem two155wN_of_last_big {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152Big A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    (h154 : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Sec16.Item154Pi A (lB A) L')
    (h322 : ∀ {H R : Subgroup G}, Hyp322 H R → CFSG.Open.pCoreOf 2 H ≤ R → IsPGroup 2 R →
      R ≠ ⊥ → ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
        H ≤ Subgroup.normalizer (C : Set G))
    (hUp : Step155Up A c L) (hgrow : Step155GrowW A c L) (hcases : Step155CasesNWBig A c L)
    (hRQ : Step155RQNWBig A c L)
    (hlast : ∀ {X K Y M T P : Subgroup G}, Ctx155 A X K Y M T → Big152 X → MaxT155 A X K T →
      Above155w A X → End155N A X K Y M T P → CFSG.Open.pCoreOf 2 Y ≤ P → False)
    {X : Subgroup G} (hXb : Big152 X) (hab : Above155w A X) {Y : Subgroup G} (hY : IsY155 A Y)
    (hYX : oPrimeResidualOf 3 Y = X) : Two155w A Y := by
  intro K hK hhyp M hM
  by_contra hnot
  obtain ⟨T, hT⟩ := exists_mem_scriptQPiStar155 (A := A) Y (piOf 2)
  have hC : Ctx155 A X K Y M T :=
    ⟨hY, hYX, hK.1, hYX ▸ hK.2.1, hYX ▸ hhyp, hK.2.2, hM, hnot, hT⟩
  obtain ⟨Y₀, M₀, T₀, hC₀, hmax⟩ := exists_maxT155 hC
  obtain ⟨P, hE, hRP⟩ := exists_end155N_le_of_ctx155w_big h h152 h153 h154 h322 hUp hgrow hcases
    hRQ hC₀ hXb hmax hab
  exact hlast hC₀ hXb hmax hab hE hRP

theorem one155w_of_big {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152Big A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    (hUp : Step155Up A c L) {Y : Subgroup G} (hY : IsY155 A Y)
    (hXb : Big152 (oPrimeResidualOf 3 Y)) (hab : Above155w A (oPrimeResidualOf 3 Y))
    (htwo : ∀ Y', IsY155 A Y' → oPrimeResidualOf 3 Y' = oPrimeResidualOf 3 Y → Two155w A Y') :
    One155 A Y := by
  intro hom
  set X := oPrimeResidualOf 3 Y with hX
  have hX4 : X ∈ scriptY4 A (lB A) := hY.2.1
  have hXY : X ≤ Y := oPrimeResidualOf_le_self 3 Y
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  obtain ⟨N₀, hN₀⟩ := exists_mem_maximalTwoLocalsContaining hY.1.1
  have hN₀' : N₀ ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hN₀
  obtain ⟨hYN, hAN, hN2, hNF⟩ := facts_of_mem_maximalTwoLocalsContaining h hN₀
  obtain ⟨K₀, hK₀N, hXK₀, hK₀0⟩ := h152 X hX4 hXb N₀ hN2 (hXY.trans hYN) hNF
  obtain ⟨hK₀Y, hK₀res⟩ := isY155_of_mem_scriptY0 hK₀0
  have hN₀K : N₀ ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ K₀ : Subgroup G) : Set G) :=
    ⟨hN₀.1, fun x hx => (sup_le hAN (le_of_mem_thetaComponentsIn hK₀N)) hx⟩
  have hYΔ : Y ≤ delta A (lB A) N₀ := hY.1.2.le.trans (delta_mono hYN)
  suffices H : ∃ K₁ ∈ scriptY0Star A (lB A), K₀ ≤ K₁ ∧ delta A (lB A) N₀ ≤ n155 A K₁ by
    obtain ⟨K₁, hK₁, hK₀K₁, hΔK₁⟩ := H
    refine ⟨K₁, hK₁, hXK₀.trans hK₀K₁, ?_⟩
    have hK₁b : Big152 K₁ := big152_of_le (hXK₀.trans hK₀K₁) hXb
    have hYN₁ : Y ≤ n155 A K₁ := hYΔ.trans hΔK₁
    have hK₁N₁ : K₁ ∈ thetaComponentsIn (n155 A K₁) :=
      Ronan152Six.mem_thetaComponentsIn_of_big h h152 hK₁ hK₁b
        (n155_mem_maximalTwoLocalsContaining_big h153 hK₁ hK₁b)
    exact le_normalizer_of_mem_thetaComponentsIn (hYN₁.trans Subgroup.le_normalizer) hK₁N₁
      (hXK₀.trans hK₀K₁) (isPerfect_of_mem_scriptY4 hX4) (ne_bot_of_mem_scriptY4 hX4) hYX
  have hΓ₀ : ∀ K₁ ∈ scriptY0Star A (lB A), K₀ ≤ K₁ →
      K₁ ∈ gam155 A (lB A) K₀ (oPrimeResidualOf 3 K₀) := fun K₁ hK₁ hK₀K₁ =>
    ⟨hK₁, by rw [hK₀res]; exact hK₀K₁, hK₀K₁.trans Subgroup.le_normalizer⟩
  rcases eq_or_lt_of_le hXK₀ with hXeq | hXlt
  ·
    obtain ⟨K₁, hK₁le, hK₁⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hK₀0
    refine ⟨K₁, hK₁, hK₁le, ?_⟩
    have hres : oPrimeResidualOf 3 K₀ = oPrimeResidualOf 3 Y := by rw [hK₀res, ← hXeq]
    refine htwo K₀ hK₀Y hres K₁ (hΓ₀ K₁ hK₁ hK₁le) (Or.inl ?_) N₀ hN₀K
    rw [hres]
    exact hom
  ·
    obtain ⟨K₁, hK₀K₁, hK₁⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hK₀0
    have hOm : omg155 A K₀ ∨ K₁ = K₀ ⊔ CFSG.Open.pCoreOf 2 K₁ := by
      by_cases hcl : ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧
          L' ∈ lA A c' ∧ L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L'
      · exact Or.inl (omg155_of_le hXK₀ hcl)
      · have hcl1 := hom.resolve_right hcl
        exact hUp h Y hY hcl1.1 hcl1.2 hcl N₀ hN₀' K₀ hK₀N hK₀0 hXlt K₁ hK₁ hK₀K₁
    refine ⟨K₁, hK₁, hK₀K₁, ?_⟩
    have hlt : oPrimeResidualOf 3 Y < oPrimeResidualOf 3 K₀ := by
      rw [hK₀res]
      exact hXlt
    refine (hab K₀ hK₀Y hlt).2 K₁ (hΓ₀ K₁ hK₁ hK₀K₁) ?_ N₀ hN₀K
    rw [hK₀res]
    exact hOm

theorem rank3II_15_5wN_of_last_big {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h152 : Item152Big A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    (h154 : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Sec16.Item154Pi A (lB A) L')
    (h322 : ∀ {H R : Subgroup G}, Hyp322 H R → CFSG.Open.pCoreOf 2 H ≤ R → IsPGroup 2 R →
      R ≠ ⊥ → ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
        H ≤ Subgroup.normalizer (C : Set G))
    (hUp : Step155Up A c L) (hgrow : Step155GrowW A c L) (hcases : Step155CasesNWBig A c L)
    (hRQ : Step155RQNWBig A c L)
    (hlast : ∀ {X K Y M T P : Subgroup G}, Ctx155 A X K Y M T → Big152 X → MaxT155 A X K T →
      Above155w A X → End155N A X K Y M T P → CFSG.Open.pCoreOf 2 Y ≤ P → False) :
    Item155wBig A (lB A) := by
  rw [item155wBig_iff]
  suffices H : ∀ X : Subgroup G, Big152 X → ∀ Y, IsY155 A Y → oPrimeResidualOf 3 Y = X →
      One155 A Y ∧ Two155w A Y from fun Y hY hb => H _ hb Y hY rfl
  intro X
  induction X using WellFoundedGT.induction with
  | _ X ih =>
    intro hXb
    have hab : Above155w A X := fun Y hY hlt => ih _ hlt (big152_of_le hlt.le hXb) Y hY rfl
    have htwo : ∀ Y, IsY155 A Y → oPrimeResidualOf 3 Y = X → Two155w A Y := fun Y hY hYX =>
      two155wN_of_last_big h h152 h153 h154 h322 hUp hgrow hcases hRQ hlast hXb hab hY hYX
    intro Y hY hYX
    exact ⟨one155w_of_big h h152 h153 hUp hY (hYX ▸ hXb) (hYX ▸ hab)
      fun Y' hY' h' => htwo Y' hY' (h'.trans hYX), htwo Y hY hYX⟩

theorem rank3II_15_5wN_of3x_big {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h152 : Item152Big A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    (h154 : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Sec16.Item154Pi A (lB A) L')
    (h315 : Item3_15) (h316 : Sec19.Item316)
    (h322 : ∀ {H R : Subgroup G}, Hyp322 H R → CFSG.Open.pCoreOf 2 H ≤ R → IsPGroup 2 R →
      R ≠ ⊥ → ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
        H ≤ Subgroup.normalizer (C : Set G))
    (hUp : Step155Up A c L) (hgrow : Step155GrowW A c L) (hcases : Step155CasesNWBig A c L)
    (hRQ : Step155RQNWBig A c L) (hBXW : Step155BXW A c L) (hW315 : Step155W315x A c L)
    (hsubn : Step155BSubn2W A c L) (hfr : Step155FrattiniNWP A c L) : Item155wBig A (lB A) :=
  rank3II_15_5wN_of_last_big h h152 h153 h154 h322 hUp hgrow hcases hRQ
    fun {X K Y M T P} hC hXb hmax hab hE hRP => false_of_end155N_of_wP_big h h153 h315 h316 hBXW
      hsubn hfr hC hXb hmax hab hE hRP (hW315 h X K Y M T P hC hmax hab hE hRP)

end CFSG.RankThree.PartTwo.Sec15.Ronan155Big
