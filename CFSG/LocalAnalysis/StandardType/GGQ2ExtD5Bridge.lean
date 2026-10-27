module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtCoverFrame
public import Certificates.Certificate10010
public import Certificates.Certificate10011
import CFSG.LocalAnalysis.StandardType.GGD5LabelJ

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

private theorem extd5_hasLabel_twD3_iff {X : Type} [Group X] :
    GGHasLabel (⟨.twD, 3, 1⟩ : LargeEvenLabel) X ↔
      GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) X := by
  unfold GGHasLabel
  simp only [LargeEvenRawDatum]
  simp

private theorem extd5_labelIso_cases {lab l : LargeEvenLabel}
    (hlab : lab = ⟨.twA, 3, 1⟩ ∨ lab = ⟨.twD, 3, 1⟩) (h : GGLabelIso lab l) :
    l = ⟨.twA, 3, 1⟩ ∨ l = ⟨.twD, 3, 1⟩ := by
  rcases hlab with rfl | rfl
  · rcases h with h | h | h | h | h | h | h | h
    · exact Or.inl h.symm
    · exact absurd h.1 (by decide)
    · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
    · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
    · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
    · exact Or.inr (by simpa using h.2)
    · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
    · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · rcases h with h | h | h | h | h | h | h | h
    · exact Or.inr h.symm
    · exact absurd h.1 (by decide)
    · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
    · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
    · exact Or.inl (by simpa using h.2)
    · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)
    · exact absurd (congrArg LargeEvenLabel.rank h.1) (by decide)
    · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)

private theorem extd5_scData {G : Type} [Group G] [Finite G] {Bs J : Subgroup G} {R : RawFrameData}
    {H : Subgroup G} (real : Realization H Bs R) {j : R.Code} (hjadm : R.admissible j)
    (hjcomp : real.component j = J) (hinter : R.inside j ⊓ R.cent j = ⊥)
    (hsup : R.inside j ⊔ R.cent j = ⊤) (hrank : finrank (ZMod 3) (R.inside j) = 3) :
    lup10d_SCData Bs J := by
  have hin : ggLinImage (p := 3) real.coord J = R.inside j := by
    have h := real.inside_eq j hjadm
    rwa [hjcomp] at h
  have hcent : ggLinImage (p := 3) real.coord (Subgroup.centralizer (J : Set G)) = R.cent j := by
    have h := real.cent_eq j hjadm
    rwa [hjcomp] at h
  refine ⟨?_, ?_, ?_⟩
  · refine le_antisymm (sup_le inf_le_left inf_le_left) fun b hb => ?_
    have hv : real.coord (Additive.ofMul (⟨b, hb⟩ : ↥Bs)) ∈ R.inside j ⊔ R.cent j := by
      rw [hsup]; trivial
    obtain ⟨v₁, hv₁, v₂, hv₂, hsum⟩ := Submodule.mem_sup.mp hv
    rw [← hin] at hv₁
    rw [← hcent] at hv₂
    set b₁ : ↥Bs := Additive.toMul (real.coord.symm v₁) with hb₁
    set b₂ : ↥Bs := Additive.toMul (real.coord.symm v₂) with hb₂
    have hb₁J : (b₁ : G) ∈ J := (mem_ggLinImage (p := 3) real.coord J v₁).mp hv₁
    have hb₂C : (b₂ : G) ∈ Subgroup.centralizer (J : Set G) :=
      (mem_ggLinImage (p := 3) real.coord _ v₂).mp hv₂
    have hbb : (⟨b, hb⟩ : ↥Bs) = b₁ * b₂ := by
      apply Additive.ofMul.injective
      apply real.coord.injective
      rw [ofMul_mul, map_add, ← hsum]
      simp [hb₁, hb₂]
    have hbG : b = (b₁ : G) * (b₂ : G) := by
      simpa using congrArg Subtype.val hbb
    rw [hbG]
    exact Subgroup.mul_mem_sup ⟨b₁.2, hb₁J⟩ ⟨b₂.2, hb₂C⟩
  · rw [eq_bot_iff]
    rintro b ⟨⟨hbBs, hbJ⟩, ⟨-, hbC⟩⟩
    have h1 : real.coord (Additive.ofMul (⟨b, hbBs⟩ : ↥Bs)) ∈ R.inside j := by
      rw [← hin, ofMul_mem_ggLinImage]; exact hbJ
    have h2 : real.coord (Additive.ofMul (⟨b, hbBs⟩ : ↥Bs)) ∈ R.cent j := by
      rw [← hcent, ofMul_mem_ggLinImage]; exact hbC
    have h3 : real.coord (Additive.ofMul (⟨b, hbBs⟩ : ↥Bs)) ∈ R.inside j ⊓ R.cent j := ⟨h1, h2⟩
    rw [hinter, Submodule.mem_bot] at h3
    have h4 : (⟨b, hbBs⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      apply real.coord.injective
      rw [h3, ofMul_one, map_zero]
    have h5 : b = 1 := by simpa using congrArg Subtype.val h4
    rw [h5]
    exact Subgroup.one_mem _
  · rw [← card_ggLinImage (p := 3) real.coord J, hin,
      Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod, hrank]
    norm_num

theorem extD5Bridge_holds
    (R : RawFrameData) : ExtD5Bridge R := by
  intro hLB hP hrig G _ _ B Bs x L D J hS hI1 hxL y K hnb real hxBs hyBs ℓ j k hℓadm hℓcomp hjadm
    hjcomp hkadm hkcomp h
  obtain ⟨W, hWK, hWa, hfix, hyJ, hB, ⟨e, hcart, hae, hbe⟩, hWj, lab, hlab, hiso, hinter, hsup,
    hrank⟩ := h
  have hKk : (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) =
      W.toLin.parab {i | i ≠ W.a} := by
    rw [hWK, ← real.normalizer_eq k hkadm, hkcomp]
  have hmem : W.toLin.simpleRefl W.a ∈ (ggAutomizer L Bs).map (ggLin (p := 3) real.coord) ⊔
      (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) := by
    have hsubℓ : ggAutomizer (real.component ℓ) Bs = ggAutomizer L Bs := by rw [hℓcomp]
    have hsubk : ggAutomizer (real.component k) Bs = ggAutomizer K Bs := by rw [hkcomp]
    rw [← hsubℓ, ← hsubk, real.normalizer_eq ℓ hℓadm, real.normalizer_eq k hkadm]
    exact hWa
  have hJJ : (ggAutomizer J Bs).map (ggLin (p := 3) real.coord) =
      W.toLin.parab {i | i ≠ W.a ∧ i ≠ W.b} := by
    rw [hWj, ← real.normalizer_eq j hjadm, hjcomp]
  have hJaut := W.toLin.closure_simpleAut_eq real.coord hJJ
  have hmark : LargeEvenMarking ↥J (fun lab _ _ _ _ _ => lab = R.label j) := by
    have h := real.marked j hjadm
    rw [hjcomp] at h
    exact h
  obtain ⟨lab₂, hl₂, has₂, R₂, _, I₂, F₂, θ₂, h₂⟩ := largeEvenMarking_exists_hasLabel hmark
  have hlabJ : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
    have hj : R.label j = ⟨.twA, 3, 1⟩ ∨ R.label j = ⟨.twD, 3, 1⟩ := extd5_labelIso_cases hlab hiso
    rw [(h₂ : lab₂ = R.label j)] at has₂
    rcases hj with hj | hj
    · rwa [hj] at has₂
    · rw [hj] at has₂
      exact extd5_hasLabel_twD3_iff.mp has₂
  obtain ⟨hp3, hcop, hinner⟩ := lup10d_labelCore_of_labelJ (p := 3) hS rfl hlabJ
  refine ⟨GGQ2Lin.toAmbModel (p := 3) (by norm_num) W.toLin real.coord hyBs hxBs hKk
    (mem_map_ggAutomizer_sup (p := 3) real.coord hmem) hfix hyJ, e, hcart, hae, hbe, hB.1,
    hB.1.span_eq_top_of_card_eq_finrank' hB.2, hp3, hcop, hJaut, hinner,
    extd5_scData real hjadm hjcomp hinter hsup hrank⟩

end CFSG.StandardType.GGQ2Frame

end
