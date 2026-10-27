module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155W315QO
import CFSG.RankThree.PartTwo.Sec15.Ronan155W315QData
import CFSG.RankThree.PartTwo.Sec15.Ronan155W315QLift
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiag
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofWE
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Orders
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PMain

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Ronan155W315

open Proof155P Proof15Res6 Y4Core


theorem false_of_isSL25Case_w155 (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (hHJ : AllPointsHJ A)
    (h148 : Item148 A (lB A)) {X Y M P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P)
    (hX : X ∈ thetaComponentsIn M) (hWO : ¬ w155 A M X ≤ pPrimeCoreOf 3 M)
    (hWM : w155 A M X ∈ thetaComponentsIn M)
    (hΔ : w155 A M X = delta A (lB A) (w155 A M X))
    (hθ : inSubgroup (aschbacherSolvableCore 3) (w155 A M X) = w155 A M X ⊓ pPrimeCoreOf 3 M)
    (hsl : IsSL25Case (w155 A M X)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := w155 A M X with hWdef
  have hA : Late.IsE27 A := h.isE27
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hf.mem_x4.1.2
  have hΔX : X = delta A (lB A) X := hf.mem_x4.2.2.1
  have hctx : Ctx152J A (lB A) M W := ⟨hf.mem_m2, hf.fit_m, hWM, hf.a_le_normalizer_w, hΔ, hsl⟩
  obtain ⟨B, b, d, Lb, hB, hBW, hc⟩ := Ronan152SL25.exists_lbConfig h hctx
  have hcent := Ronan152SL25.sectionCentralizer_eq_of_hyperplane hctx hAF hA hB hBW
  obtain ⟨p, Pp, hPp, hp3⟩ := Ronan152SL25.exists_pData152J h.toTheoremFourHyp hctx hA.isPGroup
  have hp3' : p ≠ 3 := by omega
  have : Fact p.Prime := ⟨hPp.prime⟩
  have hPpp : IsPGroup p Pp := by
    rcases hPp.type_p with ⟨-, h2⟩ | ⟨-, h3⟩
    · exact IsPGroup.of_card h2
    · exact IsPGroup.of_card h3
  obtain ⟨c₀, d₀, L₀, hc₀, hL₀, hJ₀, hd₀A, hd₀1, hd₀c, hd₀M, hXtype, hXθ⟩ :=
    data148_of_not_le h.toSec14Std h148 hf hX hWO
  have h0 : Sec14Std G A c₀ L₀ := { h.toSec14Std with zpowers_mem_omegaA := hc₀, mem_lA := hL₀ }
  have hd₀Ω : Subgroup.zpowers d₀ ∉ omegaA A :=
    Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48 h0 hJ₀ hd₀A hd₀1 hd₀c
  have hθXc : (aschbacherSolvableCore 3 ↥X).Characteristic :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.1
  obtain ⟨⟨y, hyA, hyX, hyC⟩, ⟨B₁, hB₁, hB₁3, hB₁X⟩⟩ :
      (∃ y ∈ A, y ∈ X ∧ y ∉ Sec4.thetaQuotCentralizer X) ∧
      ∃ B₁ : Subgroup G, IsHyperplane A B₁ ∧ IsPGroup 3 B₁ ∧
        ∀ x ∈ X, ∀ b' ∈ B₁, ⁅x, b'⁆ ∈ (aschbacherSolvableCore 3 ↥X).map X.subtype := by
    rcases hXtype with ⟨⟨e⟩⟩ | ⟨htc, hXp⟩
    · exact ⟨exists_mem_not_mem_thetaQuotCentralizer_of_five hAF hA hAX e,
        exists_hyperplane_of_autBound
          (fun F hF => Proof15Res8Diag.card_le_three_of_mulAut_five' (MulEquiv.refl _) F hF)
          h.isElemAbelian h.card_eq hAX (aschbacherSolvableCore 3 ↥X) e⟩
    · exact ⟨exists_mem_not_mem_thetaQuotCentralizer_of_tripleCover hAF hA hAX hΔX hXp htc,
        exists_hyperplane_of_card_range_le_three hA hAX
          (card_range_le_three_of_tripleCover hA hAX hΔX hXp htc)⟩
  have h3X : 3 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rcases hXtype with ⟨⟨e⟩⟩ | ⟨htc, -⟩
    · rw [Proof15Res8Diag.card_five e]
      norm_num
    · rw [Proof15Res8Diag.card_tripleCover htc]
      norm_num
  obtain ⟨b₁, d₁, L₁, hc₁⟩ := exists_lbConfig_of_hyperplane h hΔX hB₁ hB₁3 hB₁X h3X
  obtain ⟨hb₁Ω, -, -, -, hb₁A, -⟩ := Ronan152SL25.lbConfig_facts hA hB₁ hc₁
  have hb₁B₁ : b₁ ∈ B₁ := hc₁.1 ▸ Subgroup.subset_closure (Set.mem_insert b₁ _)
  have hb₁C : b₁ ∈ Sec4.thetaQuotCentralizer X := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAX hb₁A, fun l hl => ?_⟩
    have h1 := hB₁X l⁻¹ (X.inv_mem hl) b₁ hb₁B₁
    have e1 : l⁻¹ * (b₁ * l * b₁⁻¹) = ⁅l⁻¹, b₁⁆ := by
      rw [commutatorElement_def]
      group
    rw [e1]
    exact h1
  have hPpy : Pp ≤ Subgroup.centralizer ({y} : Set G) :=
    le_centralizer_of_mem_x hPp.odd hPp.le_px hPpp hyX (hPp.norm_p hyA)
  have hyB : y ∈ B := Ronan152SL25.mem_of_le_centralizer hctx hcent hPp hp3' hyA hPpy
  have hWΔ0 : W ≤ deltaZero A (lB A) M := hf.w_le_i0.trans hf.i0_le_deltaZero
  have hXΔ0 : X ≤ deltaZero A (lB A) M := hf.le_x_i0.trans hf.i0_le_deltaZero
  have hd₀B : d₀ ∈ B := by
    have hmem : d₀ ∈ Late.sectionCentralizer A W ((aschbacherSolvableCore 3 ↥W).map W.subtype) := by
      refine ⟨hd₀A, fun x hx => ?_⟩
      have hxd : ⁅x, d₀⁆ ∈ W := by
        rw [commutatorElement_def, mul_assoc, mul_assoc]
        refine W.mul_mem hx ?_
        have h1 := (Subgroup.mem_normalizer_iff.mp (hf.a_le_normalizer_w hd₀A) x⁻¹).mp
          (W.inv_mem hx)
        simpa [mul_assoc] using h1
      have h2 : ⁅x, d₀⁆ ∈ inSubgroup (aschbacherSolvableCore 3) W := by
        rw [hθ]
        exact ⟨hxd, hd₀M x (hWΔ0 hx)⟩
      have e1 : d₀ * x * d₀⁻¹ * x⁻¹ = ⁅x, d₀⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e1]
      exact inv_mem h2
    rw [hcent] at hmem
    exact hmem
  have hd₀C : d₀ ∈ Sec4.thetaQuotCentralizer X := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAX hd₀A, fun l hl => ?_⟩
    have hlX : l⁻¹ ∈ X := X.inv_mem hl
    have hxd : ⁅l⁻¹, d₀⁆ ∈ X := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine X.mul_mem hlX ?_
      have h1 := (Subgroup.mem_normalizer_iff.mp (hAX hd₀A) l⁻¹⁻¹).mp (X.inv_mem hlX)
      simpa [mul_assoc] using h1
    have e1 : l⁻¹ * (d₀ * l * d₀⁻¹) = ⁅l⁻¹, d₀⁆ := by
      rw [commutatorElement_def]
      group
    rw [e1]
    exact hXθ ⟨hxd, hd₀M l⁻¹ (hXΔ0 hlX)⟩
  have hy1 : y ≠ 1 := fun h1 => hyC (h1 ▸ (Sec4.thetaQuotCentralizer X).one_mem)
  have hyΩ := zpowers_mem_omegaA_of_cases h134 h48 h.toSec14Std hB hc hyB hy1 hyC hd₀B hd₀1
    hd₀C hd₀Ω hb₁C hb₁Ω
  have hd₀y : d₀ ∉ Subgroup.zpowers y := by
    intro h'
    have hzeq : Subgroup.zpowers d₀ = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h')
        (by rw [Proof152WE.card_zpowers_eq_three hA hd₀A hd₀1,
          Proof152WE.card_zpowers_eq_three hA hyA hy1])
    exact hd₀Ω (hzeq ▸ hyΩ)
  exact false_of_le_centralizer_of_mem_omegaA h142 h hHJ hctx hB hcent hyB hd₀B hy1 hd₀y hyΩ hPp
    hp3' hPpy

theorem isQuasisimple_w155 (h142 : Item142AllS14)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h148R : Item148R) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) {X Y M P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P)
    (hX : X ∈ thetaComponentsIn M) (hWO : ¬ w155 A M X ≤ pPrimeCoreOf 3 M)
    (hWM : w155 A M X ∈ thetaComponentsIn M) (hWc : w155 A M X ∈ comp3In (delta A (lB A) M))
    (hΔ : w155 A M X = delta A (lB A) (w155 A M X))
    (hθ : inSubgroup (aschbacherSolvableCore 3) (w155 A M X) = w155 A M X ⊓ pPrimeCoreOf 3 M) :
    CFSG.IsQuasisimple (↥(w155 A M X) ⧸ CFSG.pCore 2 ↥(w155 A M X)) := by
  set J := w155 A M X with hJdef
  have h14 := h.toSec14Std
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hf.a_le_normalizer_w
  have hJp : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hWM
  have hJq := isQuasisimple_theta_of_mem_thetaComponentsIn hWM
  have hJM' : J ≤ M := le_of_mem_thetaComponentsIn hWM
  have hJtop : J ≠ ⊤ := fun h' => hf.mem_m2.1.1 (top_le_iff.mp (h' ▸ hJM'))
  have hJY : J ∈ scriptY A := ⟨hJtop, hAJ⟩
  have : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr (Y4Core.ne_bot hWc)
  have hO2 : CFSG.pCore 2 ↥J ≠ ⊥ :=
    pCore_ne_bot_of_isCharacteristicP (isCharacteristicP_of_mem_thetaComponentsIn hf.fit_m hWM)
  have hS4 : SectionFourHyp ↥J := h.toTheoremFourHyp.sectionFourHyp hJtop
  have hθc := solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥J
  set K := (Subgroup.center (↥J ⧸ θ)).comap (QuotientGroup.mk' θ)
  have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKs : Group.IsSolvable K := isSolvable_comap_center θ hθc.1
  have : IsSimpleGroup ((↥J ⧸ θ) ⧸ Subgroup.center (↥J ⧸ θ)) := hJq.2.1
  have hKsimp : IsSimpleGroup (↥J ⧸ K) :=
    (quotientComapEquiv θ (Subgroup.center (↥J ⧸ θ))).isSimpleGroup
  have hSL25 : AllPointsHJ A → IsSL25Case J → False := fun hHJ hsl =>
    false_of_isSL25Case_w155 h142 h134 h48 h hHJ (h148R G A c L h) hf hX hWO hWM hΔ hθ hsl
  rcases Sec4.item4_4OTwo_holds ↥J hS4 hJp K hKs hKsimp hO2 with h1 | h2 | ⟨p, hp, hp3, he⟩ | h4
  · exact h1
  ·
    exfalso
    by_cases hHJ : AllPointsHJ A
    · exact hSL25 hHJ (Or.inl h2)
    · obtain ⟨e⟩ := h2
      have : (Sec4.oTwoFitting ↥J).Characteristic := oTwoFitting_characteristic
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact false_of_sl2_nhj h134 h48 h hHJ hΔ hAJ (p := 5) le_rfl (Sec4.oTwoFitting ↥J) e
  ·
    exfalso
    have : Fact p.Prime := ⟨hp⟩
    have : (Sec4.oTwoP p ↥J).Characteristic := oTwoP_characteristic p
    have hp5 : 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with h5 | h5
      · interval_cases p
        exact absurd hp (by norm_num)
      · exact h5
    by_cases hHJ : AllPointsHJ A
    · rcases Nat.lt_or_ge 5 p with hp5' | hp5'
      ·
        obtain ⟨e⟩ := he
        have hΔ0 : J = deltaZero A (lB A) J :=
          eq_deltaZero_of_eq_delta' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
            Sec4.Sporadic.rank3II_4_15
            (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15) h14 hAJ hWc.2 hΔ
        have he' : letI := ker148_normal hAJ
            Nonempty (↥(img148 A J (deltaZero A (lB A) J)) ≃* PSL(2, ZMod p)) := by
          let := ker148_normal hAJ
          rw [← hΔ0]
          obtain ⟨φ⟩ := nonempty_img148_equiv hAJ
          obtain ⟨ψ⟩ := nonempty_quotient_pPrimeCore_equiv_psl hp5' e
          exact ⟨φ.trans ψ⟩
        exact false_of_img148_psl2 (h148R G A c L h) hJY h.isElemAbelian.1 hHJ h.chosen136
          kSL2pNotList148 hp5' he'
      ·
        have hp5'' : p = 5 := le_antisymm hp5' hp5
        subst hp5''
        exact hSL25 hHJ (Or.inr he)
    · obtain ⟨e⟩ := he
      exact false_of_sl2_nhj h134 h48 h hHJ hΔ hAJ hp5 (Sec4.oTwoP p ↥J) e
  ·
    exact isQuasisimple_of_case444 hJp hJq h4

theorem mem_scriptY0_w155 (h142 : Item142AllS14)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h148R : Item148R) (hS : Y4CoreMemSolvR)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (h149 : Item149 A (lB A))
    {X Y M P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P)
    (hX : X ∈ thetaComponentsIn M) (hWO : ¬ w155 A M X ≤ pPrimeCoreOf 3 M)
    (hWc : w155 A M X ∈ comp3In (delta A (lB A) M))
    (hθ : inSubgroup (aschbacherSolvableCore 3) (w155 A M X) = w155 A M X ⊓ pPrimeCoreOf 3 M) :
    w155 A M X ∈ scriptY0 A (lB A) := by
  set J := w155 A M X with hJdef
  have hJM : J ∈ thetaComponentsIn M := Y4Core.mem_thetaComponentsIn_of_item149 h149 hf.mem_m2.1 hWc
  have hJtop : J ≠ ⊤ := fun h' =>
    hf.mem_m2.1.1 (top_le_iff.mp (h' ▸ le_of_mem_thetaComponentsIn hJM))
  have hJY : J ∈ scriptY A := ⟨hJtop, hf.a_le_normalizer_w⟩
  have : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr (Y4Core.ne_bot hWc)
  have hO2 : CFSG.pCore 2 ↥J ≠ ⊥ :=
    pCore_ne_bot_of_isCharacteristicP (isCharacteristicP_of_mem_thetaComponentsIn hf.fit_m hJM)
  have hΔ : J = delta A (lB A) J :=
    Y4Core.eq_delta_of_not_isSolvable h149 hJM hJY
      (hS G A c L h M hf.mem_m2 hf.fit_m J hWc hf.a_le_normalizer_w)
  have hq := isQuasisimple_w155 h142 h134 h48 h148R h hf hX hWO hJM hWc hΔ hθ
  exact ⟨⟨hJY, hWc.2, hΔ, hq⟩, ⟨hJY, pCoreOf_ne_bot_of_pCore_ne_bot hO2⟩⟩

end Ronan155W315

end CFSG.RankThree.PartTwo.Sec15
