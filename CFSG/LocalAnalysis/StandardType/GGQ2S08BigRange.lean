module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigFull
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigShapeD
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigShapeB
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigShapeC
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigShapeAInput
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigShapeLabel
public import CFSG.LocalAnalysis.StandardType.GGQ2S08InnDiagBig

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2s08btop_card_Bs {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) :
    Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := by
  have hE : Finite (Additive ↥Bs) :=
    Finite.of_injective (Additive.ofMul.symm : Additive ↥Bs → ↥Bs)
      Additive.ofMul.symm.injective
  have hVfin : Finite M.V :=
    Finite.of_injective (M.model.toEquiv.symm : M.V → Additive ↥Bs)
      M.model.toEquiv.symm.injective
  have hVft : Fintype M.V := Fintype.ofFinite M.V
  have hNZ : NeZero 3 := ⟨by norm_num⟩
  have hcard : Nat.card ↥Bs = Nat.card M.V :=
    Nat.card_congr (Additive.ofMul.trans M.model.toEquiv)
  rw [hcard, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3), ZMod.card]

private theorem ggQ2s08btop_classical_of_lieRank {lab : LargeEvenLabel}
    (hTB : GGQ2TBLabel lab) (hlie : 9 ≤ GGQ2LieRank lab) :
    (lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD) ∧
      9 ≤ lab.rank := by
  simp only [GGQ2TBLabel] at hTB
  rcases hTB with ⟨htag, -⟩ | ⟨htag | htag, -⟩ | ⟨htag, -, -⟩ | ⟨htag, -, -⟩ |
    htag | htag | htag | htag
  · exact ⟨Or.inl htag, by simpa [GGQ2LieRank, htag] using hlie⟩
  · exact ⟨Or.inr (Or.inl htag), by simpa [GGQ2LieRank, htag] using hlie⟩
  · exact ⟨Or.inr (Or.inr (Or.inl htag)), by simpa [GGQ2LieRank, htag] using hlie⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl htag))),
      by simpa [GGQ2LieRank, htag] using hlie⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr htag))),
      by simpa [GGQ2LieRank, htag] using hlie⟩
  · have h4 : GGQ2LieRank lab = 4 := by simp [GGQ2LieRank, htag]
    omega
  · have h6 : GGQ2LieRank lab = 6 := by simp [GGQ2LieRank, htag]
    omega
  · have h7 : GGQ2LieRank lab = 7 := by simp [GGQ2LieRank, htag]
    omega
  · have h8 : GGQ2LieRank lab = 8 := by simp [GGQ2LieRank, htag]
    omega

theorem ggQ2s08_bigRange_of_shapeA
    (hA : GGQ2S08BigShapeAInput) (hT : GGQ2TableBI1Fail)
    (hKG : GGReflClassLargeThree)
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hΓi : GGQ2GammaXOffI1Input)
    (hTBN : GGQ2TableBNbr) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S)
    (h9 : 3 ^ 9 < Nat.card ↥Bs)
    (g : G) (φ : MulAut ↥Bs) (hInd : GGQ2Ind Bs g φ) (hRefl : GGIsReflection 3 φ) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨labL, hq, hTB, hMark, M, hMW, hSh, -⟩ := hT hS rfl hI1
  have hmark : GGQ2TBMarked 3 L labL := ⟨hq, hTB, hMark⟩
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSS.2.2.1
  have hx0 : M.xV ≠ 0 := by
    intro h0
    apply hx1
    have hm : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 := by
      have hmm : M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) = M.model 0 := by
        rw [map_zero]
        simpa [GGQ2LDatum.xV] using h0
      exact M.model.injective hmm
    have h1 : (⟨x, M.hx⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      rw [ofMul_one]
      exact hm
    simpa using congrArg Subtype.val h1
  have hcardBs : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := ggQ2s08btop_card_Bs M
  have hdim9 : 9 < Module.finrank (ZMod 3) M.V := by
    rw [hcardBs] at h9
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h9
  have hle := ggQ2LD_finrank_le_card_succ M hSh
  have hcardlie := ggQ2LD_card_lie hMW hTB
  have hlie : 9 ≤ GGQ2LieRank labL := by omega
  have hlab : GGQ2S08BigLabel labL := by
    simp only [GGQ2S08BigLabel]
    obtain ⟨htagdisj, hrank9⟩ := ggQ2s08btop_classical_of_lieRank hTB hlie
    exact ⟨hq, htagdisj, hrank9⟩
  have hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L :=
    ggQ2s08_innDiagBig_of_setting hRig hS hlab hMark
  by_cases hF : M.ShapeFull
  · exact ggQ2s08_bigFull_holds hKG hTBW hCen hOut hLB hP hΓi hTBN hS hI1 hCav hnc hRig
      M hF hlab hmark hInn hMW g φ hInd hRefl
  · have hrest : ¬ M.ShapeFull ∧ labL.tag = .twA ∧ 3 ∣ labL.rank + 1 ∧
        12 ≤ labL.rank + 1 := by
      rcases ggQ2s08_big_shape_label M hlab hMW hx0 hSh with h | h
      · exact absurd h.1 hF
      · exact h
    obtain ⟨-, htag, h3, h12⟩ := hrest
    have hshapes : M.ShapeA ∨ M.ShapeB ∨ M.ShapeC ∨ M.ShapeD := by
      simp only [GGQ2LDatum.Shape] at hSh
      rcases hSh with hF' | hA' | hB' | hC' | hD'
      · exact absurd hF' hF
      · exact Or.inl hA'
      · exact Or.inr (Or.inl hB')
      · exact Or.inr (Or.inr (Or.inl hC'))
      · exact Or.inr (Or.inr (Or.inr hD'))
    rcases hshapes with hA' | hB' | hC' | hD'
    · exact hA hS hI1 hCav hnc M hA' hlab hmark hInn hMW htag h3 h12 g φ hInd hRefl
    · exact ggQ2s08_bigB_holds hKG hTBW hCen hOut hLB hP hΓi hTBN hS hI1 hCav hnc
        M hB' hRig hlab hmark hInn hMW htag h3 h12 g φ hInd hRefl
    · exact ggQ2s08_bigC_holds hKG hTBW hCen hOut hLB hP hΓi hTBN hS hI1 hCav hnc
        M hC' hRig hlab hmark hInn hMW htag h3 h12 g φ hInd hRefl
    · exact ggQ2s08_bigD_holds hKG hTBW hCen hOut hLB hP hΓi hTBN hS hI1 hCav hnc
        M hD' hRig hlab hmark hInn hMW htag h3 h12 g φ hInd hRefl

end CFSG.StandardType

end
