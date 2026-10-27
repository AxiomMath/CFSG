module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.StatementsDeltaFree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.XBarShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCalV1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.BarSubISup
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1F4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Table137SUFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Table137OmegaPlusFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Table138OmegaSixMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Table137OmegaSixMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def K_18_13_H1 : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ), 2 ≤ n →
    (NatSUn H ⊤ (CFSG.Quasithin.fixV H) 4 n ∨
        NatOmegaMinus H ⊤ (CFSG.Quasithin.fixV H) 6 n ∨
        NatOmegaPlus H ⊤ (CFSG.Quasithin.fixV H) 4 n) →
      CFSG.Quasithin.commSub ⊤ H = ⊤ → CFSG.Quasithin.fixV H = ⊥

theorem sumOfNat_one {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} (hZU : Z ≤ U) (hN : N H U Z) :
    SumOfNat N H U Z 1 := by
  refine ⟨fun _ => U, fun _ => hZU, ?_, ?_, fun _ => hN⟩
  · intro i
    have hbot : (⨆ (j : Fin 1) (_ : j ≠ i), U) = ⊥ := by
      apply iSup_eq_bot.2
      intro j
      apply iSup_eq_bot.2
      intro hji
      exact absurd (Subsingleton.elim j i) hji
    rw [hbot, sup_bot_eq]
    exact inf_le_right
  · rw [show (⨆ i : Fin 1, U) = U from iSup_const]
    exact sup_eq_right.2 hZU

theorem isL2_of_isOmegaMinus_four {X : Type} [Group X] {k : ℕ} (hk : 1 ≤ k)
    (h : IsOmegaMinus X 4 k) : IsL2 X (2 * k) := by
  obtain ⟨-, K, hKf, hKfin, b, c, hcard, hbc, ⟨e⟩⟩ := h
  letI := hKf
  have := hKfin
  have hchar : CharP K 2 := uc22p22d_charP_two hk hcard
  let Q : QuadraticForm K (Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus (4 / 2) K b c
  have hQ : ⇑Q = StatedQuadMinus (4 / 2) K b c :=
    CFSG.LieType.Universal.Spin.coe_quadMinus (n := 4 / 2) (K := K) b c
  have hv : ∃ v, Q v ≠ 0 := by
    refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
    rw [show Q = CFSG.LieType.Universal.Spin.quadMinus (4 / 2) K b c from rfl,
      CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp [Pi.single_eq_same, Pi.single_eq_of_ne]
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus (4 / 2) K b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus (4 / 2) K b c)) :=
    CFSG.SeitzReduction.SymplecticPilot.statedProjOmegaEquiv (Q := Q)
      (Q₀ := StatedQuadMinus (4 / 2) K b c) hQ (by rwa [← hQ])
  exact uc22p22d_isL2_of_omegaMinus4 (k := k) hk hcard b c hbc (e.trans eΩ)

theorem not_omega4minus_of_isL2 {X : Type} [Group X]
    (h12 : ¬ ∃ n : ℕ, IsL2 X n) {f : ℕ} (hf : Even f)
    (hOm : IsOmegaMinus X 4 (f / 2)) : False := by
  have hk : 1 ≤ f / 2 := by
    obtain ⟨-, K, hKf, hKfin, b, c, hcard, -, -⟩ := hOm
    letI := hKf
    have := hKfin
    exact CFSG.ComponentClassification.CatLeafProof.one_le_of_card_eq_pow hcard
  have h2f : 2 * (f / 2) = f := by
    rcases hf with ⟨m, hm⟩
    omega
  exact h12 ⟨2 * (f / 2), by simpa [h2f] using isL2_of_isOmegaMinus_four hk hOm⟩

theorem not_omega4minus_sum {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    {h : Hyp18 D V₀ V p L} (h12 : R18_12At D V₀ V p L h) :
    ¬ ∃ f : ℕ, Even f ∧
      IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 (f / 2) ∧
      SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 (f / 2))
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 2 := by
  rintro ⟨f, hf, hOm, -⟩
  exact not_omega4minus_of_isL2 h12 hf hOm

theorem barSub_conjClosure_eq_iSup {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) :
    barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) =
      ⨆ φ : Mbar D.M V₀ V h.hyp125.isElemAbelian,
        (barSub V₀ V h.hyp125.isElemAbelian L).map
          (MulAut.conj (φ : MulAut (Vtil V₀ V h.hyp125.isElemAbelian))).toMonoidHom := by
  set hV := h.hyp125.isElemAbelian
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hLle : L ≤ stabTil V₀ V := h.hL.1.1.le.trans hMS
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22br4_conjClosure_eq D.M L]
  have hKle : ∀ g : D.M, L.map (MulAut.conj (g : G)).toMonoidHom ≤ stabTil V₀ V := by
    intro g x hx
    obtain ⟨l, hl, rfl⟩ := hx
    exact hMS (D.M.mul_mem (D.M.mul_mem g.2 (h.hL.1.1.le hl)) (D.M.inv_mem g.2))
  rw [barSub_iSup_of_le hV hKle]
  have hstep : (⨆ g : D.M, barSub V₀ V hV
        (L.map (MulAut.conj (g : G)).toMonoidHom)) =
      ⨆ g : D.M, (barSub V₀ V hV L).map
        (MulAut.conj (actTil V₀ V hV ⟨g, hMS g.2⟩)).toMonoidHom :=
    iSup_congr fun g => TwelveTwentyThree.barSub_map_conj hV hLle (hMS g.2)
  rw [hstep]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun g => ?_
    refine le_iSup (fun φ : Mbar D.M V₀ V hV =>
      (barSub V₀ V hV L).map
        (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom)
      ⟨actTil V₀ V hV ⟨g, hMS g.2⟩,
        actTil_mem_barSub V₀ V hV g.2 (hMS g.2)⟩
  · refine iSup_le fun φ => ?_
    obtain ⟨g, hg, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 φ.2
    rw [← hgφ]
    let g' : D.M := ⟨g, hg⟩
    have hg' : (⟨g', hMS g'.2⟩ : stabTil V₀ V) = g := Subtype.ext rfl
    rw [← hg']
    exact le_iSup (fun g : D.M => (barSub V₀ V hV L).map
      (MulAut.conj (actTil V₀ V hV ⟨g, hMS g.2⟩)).toMonoidHom) g'

theorem isSp4_barSub_of_isSp4_bar2 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥) {f : ℕ}
    (hSp : IsSp4 (Bar2 (conjClosure D.M L)) f) :
    IsSp4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) f := by
  have hs : IsSimpleGroup (Bar2 (conjClosure D.M L)) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
  obtain ⟨e⟩ := barSubBar2Equiv_conjClosure_of_isSimpleGroup h.hyp125 h.hL.1 hs hX1
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hSp

theorem commSub_top_barSub_conjClosure_eq_top {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h : Hyp18 D V₀ V p L)
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥) :
    CFSG.Quasithin.commSub (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian))
      (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) = ⊤ := by
  set X : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian)) :=
    barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) with hX
  have hgen := barSub_conjClosure_eq_iSup h
  have hL1 : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥ := by
    intro hbot
    apply hX1
    rw [hX, hgen]
    simp [hbot]
  have hcomp : barSub V₀ V h.hyp125.isElemAbelian L ∈
      compBar D.M V₀ V h.hyp125.isElemAbelian :=
    barSub_mem_compBar_of_ne_bot h.hyp125 h.hL.1 hL1
  have hXM : X ≤ Mbar D.M V₀ V h.hyp125.isElemAbelian :=
    barSub_mono V₀ V h.hyp125.isElemAbelian (TwelveTwentyThree.conjClosure_le h.hL.1.1.le)
  have hXn : (X.subgroupOf (Mbar D.M V₀ V h.hyp125.isElemAbelian)).Normal :=
    barSub_subgroupOf_mbar_normal h.hyp125.isElemAbelian
      (TwelveTwentyThree.conjClosure_le h.hL.1.1.le)
      (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  have hXs : Odd (Nat.card X) ∨ ∃ K ∈ compBar D.M V₀ V h.hyp125.isElemAbelian,
      X = ⨆ φ ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian,
        K.map (MulAut.conj φ).toMonoidHom := by
    refine Or.inr ⟨_, hcomp, ?_⟩
    rw [hX]
    rw [iSup_subtype']
    exact hgen
  have hIrr := twelve_seventeen D hx h61 h127 h1214 h.hyp125 X hX1 hXM hXn hXs
  refine le_antisymm le_top ?_
  have hle : (⨆ I ∈ irrSet X, I) ≤
      CFSG.Quasithin.commSub
        (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) X := by
    refine iSup₂_le fun I hI => ?_
    calc I = CFSG.Quasithin.commSub I X := hI.1.symm
      _ ≤ CFSG.Quasithin.commSub ⊤ X := CFSG.Quasithin.commSub_mono le_top le_rfl
  simpa only [hIrr.1] using hle

section Certified

theorem isG2_barSub_of_isG2_bar2 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥) {f : ℕ}
    (hG2 : IsG2 (Bar2 (conjClosure D.M L)) f) :
    IsG2 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) f := by
  have hs : IsSimpleGroup (Bar2 (conjClosure D.M L)) :=
    (CFSG.LieType.Simplicity.fam_g2_simplicity (Bar2 (conjClosure D.M L)) 2 f
      (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide))).2
  obtain ⟨e⟩ := barSubBar2Equiv_conjClosure_of_isSimpleGroup h.hyp125 h.hL.1 hs hX1
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hG2

theorem survivors_of_hyp18 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥)
    (h10 : R18_10At D V₀ V p L h) (h2 : P18_6_2 D V₀ V p L h)
    (h11 : R18_11At D V₀ V p L h) (h12 : R18_12At D V₀ V p L h) :
    (∃ f : ℕ, IsSUn ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 f ∧
      NatSUn (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 4 f) ∨
    (∃ f : ℕ, IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 6 f ∧
      NatOmegaMinus (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 6 f) ∨
    (∃ f : ℕ, IsOmegaPlus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 f ∧
      NatOmegaPlus (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤
        (CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))) 4 f) := by
  set X := conjClosure D.M L with hX
  have hshape := h10 h2
  obtain ⟨f, hSp | hG2 | hSU | hOM | hOP | hOM4 | hL2⟩ := h2
  · exact absurd ⟨f, isSp4_barSub_of_isSp4_bar2 h hX1 hSp.1⟩ h11
  · have hG2' := isG2_barSub_of_isG2_bar2 h hX1 hG2.1
    rcases hshape with ⟨n, hSU' | hOM' | hOP'⟩
    · have hU : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian X) n :=
        isU4_of_isSUn_four hSU'
      have hcmp := CFSG.ComponentClassification.CatLeafProof.lieModel_eq_of_isChar2LieShape
        hG2' S17.isChar2LieShape_G2 hU
      exact False.elim (absurd hcmp.1 (by decide))
    · have hU : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian X) n :=
        isU4_of_isOmegaMinus hOM'
      have hcmp := CFSG.ComponentClassification.CatLeafProof.lieModel_eq_of_isChar2LieShape
        hG2' S17.isChar2LieShape_G2 hU
      exact False.elim (absurd hcmp.1 (by decide))
    · have hsX : IsSimpleGroup ↥(barSub V₀ V h.hyp125.isElemAbelian X) :=
        (CFSG.LieType.Simplicity.fam_g2_simplicity _
          2 f (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2' (by decide))).2
      exact False.elim (not_isSimpleGroup_of_isOmegaPlus_four hOP' hsX)
  · exact Or.inl ⟨f, hSU.1, hSU.2⟩
  · exact Or.inr (Or.inl ⟨f, hOM.1, hOM.2⟩)
  · exact Or.inr (Or.inr ⟨f, hOP.1, hOP.2⟩)
  · exact False.elim (not_omega4minus_of_isL2 h12 hOM4.1 hOM4.2.1)
  · exact False.elim (h12 ⟨f, hL2.1⟩)

theorem fixV_of_hyp18 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (h10 : R18_10At D V₀ V p L h) (h2 : P18_6_2 D V₀ V p L h)
    (h11 : R18_11At D V₀ V p L h) (h12 : R18_12At D V₀ V p L h)
    (hH1 : K_18_13_H1)
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥) :
    CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) = ⊥ := by
  set X : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian)) :=
    barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) with hX
  have hcomm : CFSG.Quasithin.commSub
      (⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) X = ⊤ := by
    rw [hX]
    exact commSub_top_barSub_conjClosure_eq_top hx h61 h127 h1214 h hX1
  rcases survivors_of_hyp18 h hX1 h10 h2 h11 h12 with
    ⟨f, hSU, hNat⟩ | ⟨f, hOM, hNat⟩ | ⟨f, hOP, hNat⟩
  · have h2f : 2 ≤ f := by
      have h1f := (isU4_barSub_cong h h1742 (isU4_of_isSUn_four hSU)).2.2.1
      omega
    exact hH1 X f h2f (Or.inl hNat) hcomm
  · have h2f : 2 ≤ f := by
      have h1f := (isU4_barSub_cong h h1742 (isU4_of_isOmegaMinus hOM)).2.2.1
      omega
    exact hH1 X f h2f (Or.inr (Or.inl hNat)) hcomm
  · have h2f : 2 ≤ f := (isOmegaPlus_barSub_cong h h1742 hOP).2.2.1
    exact hH1 X f h2f (Or.inr (Or.inr hNat)) hcomm

end Certified

theorem tilOf_eq_one_iff {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {v : G} (hv : v ∈ V) :
    tilOf V₀ V hV v hv = 1 ↔ v ∈ V₀ := by
  have h1 : (1 : Vtil V₀ V hV) = mkTil V₀ V hV (1 : CFSG.Quasithin.IntMod V hV) :=
    (map_one (mkTil V₀ V hV)).symm
  rw [tilOf, h1, mkTil_eq_iff]
  change v * 1⁻¹ ∈ V₀ ↔ v ∈ V₀
  simp

theorem tilOf_ne_one {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {v : G} (hv : v ∈ V)
    (hv0 : v ∉ V₀) : tilOf V₀ V hV v hv ≠ 1 :=
  fun h => hv0 ((tilOf_eq_one_iff hV hv).1 h)

theorem eighteen_fourteen_one
    (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) :
    R18_14_1At D V₀ V p L h := by
  have hTab := @k_Table13_7_SU4_holds
  intro n hn hSUn F _ _ hF ε ψ hcoords v hv hv0
  have hU : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) n :=
    isU4_of_isSUn_four hSUn
  have hcong := (isU4_barSub_cong h h1742 hU).2.2.2
  exact hTab (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) p n hn hSUn
    (D.sig_prime p h.hp).1 hcong F hF ε ψ hcoords
    (tilOf V₀ V h.hyp125.isElemAbelian v hv)
    (tilOf_ne_one h.hyp125.isElemAbelian hv hv0)

theorem eighteen_fourteen_two
    (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L)
    (hTabPi : K_Table13_8_Omega6Minus_pi)
    (h1742 : S17.R17_42At D V₀ V) :
    R18_14_2At D V₀ V p L h := by
  have hTabOn := @k_Table13_7_Omega6MinusOn_holds
  intro hcase n hn hOmega
  have hU : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) n :=
    isU4_of_isOmegaMinus hOmega
  have hcong := (isU4_barSub_cong h h1742 hU).2.2.2
  constructor
  · intro v hv hv0
    obtain ⟨s, hs1, hs2, f, hOmegaF, hsum⟩ := hcase
    have hUf : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) f :=
      isU4_of_isOmegaMinus hOmegaF
    have hcongf := (isU4_barSub_cong h h1742 hUf).2.2.2
    exact hTabPi (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) p f s
      hOmegaF hs1 hs2 hsum (D.sig_prime p h.hp).1 hcongf
      (tilOf V₀ V h.hyp125.isElemAbelian v hv)
      (tilOf_ne_one h.hyp125.isElemAbelian hv hv0)
  · intro W' hW' hW'nat F _ _ b c hF hb ε ψ hcoords v hv hv0 hmem
    exact hTabOn (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) p n hn hOmega
      (D.sig_prime p h.hp).1 hcong W' hW' hW'nat F b c hF hb ε ψ hcoords
      ⟨tilOf V₀ V h.hyp125.isElemAbelian v hv, hmem⟩
      (by simpa using tilOf_ne_one h.hyp125.isElemAbelian hv hv0)

theorem eighteen_fourteen_three
    (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) :
    R18_14_3At D V₀ V p L h := by
  have hTab := @k_Table13_7_Omega4Plus_holds
  intro n hn hOmega F _ _ hF ε ψ hcoords v hv hv0
  have hcong := (isOmegaPlus_barSub_cong h h1742 hOmega).2.2.2
  exact hTab (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) p n hn hOmega
    (D.sig_prime p h.hp).1 hcong F hF ε ψ hcoords
    (tilOf V₀ V h.hyp125.isElemAbelian v hv)
    (tilOf_ne_one h.hyp125.isElemAbelian hv hv0)

theorem eighteen_fourteen
    (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (hIso : K_Omega6Minus_natIsoMod)
    (h1742 : S17.R17_42At D V₀ V) :
    R18_14At D V₀ V p L h :=
  ⟨eighteen_fourteen_one D V₀ V p L h h1742, eighteen_fourteen_two D V₀ V p L h
      (k_Table13_8_Omega6Minus_pi_holds_of hIso) h1742,
    eighteen_fourteen_three D V₀ V p L h h1742⟩

theorem eighteen_thirteen_b
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hm : MBarGT D.M V₀ V 3)
    (h6b : R18_6bAt D V₀ V p L h) (h7b : R18_7bAt D V₀ V p L h)
    (h8 : R18_8At D V₀ V p L h) (h9 : R18_9At D V₀ V p L h)
    (h9b : Gap_18_9b D V₀ V p L h)
    (h10 : R18_10At D V₀ V p L h) (h11 : R18_11At D V₀ V p L h)
    (h12 : R18_12At D V₀ V p L h)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (h117 : C117 D V₀ V)
    (hH1 : K_18_13_H1)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h1742 : S17.R17_42At D V₀ V) :
    R18_13At D V₀ V p L h := by
  have hUL : UniqueMax D.M L := by
    rcases h17_66_1 p h.hp L h.hL (conjClosure D.M L) rfl h.hX with hh | hh
    · exact hh
    · exact absurd hh h18_4
  have hL1 : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_uniqueMax h127 h.hyp125 h117 h.hL.1 hUL
  have hX1 : barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥ :=
    TwelveTwentyThree.barSub_conjClosure_ne_bot h.hyp125.isElemAbelian hL1
  rcases h6b hm h7b with h2 | h3 | h4 | h5 | h6
  · have hFix : CFSG.Quasithin.fixV
        (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) = ⊥ :=
      fixV_of_hyp18 hx h61 h127 h1214 h h1742 h10 h2 h11 h12 hH1 hX1
    rcases survivors_of_hyp18 h hX1 h10 h2 h11 h12 with
      ⟨f, hSU, hNat⟩ | ⟨f, hOm, hNat⟩ | ⟨f, hOp, hNat⟩
    · exact Or.inl ⟨f, hSU, by rw [hFix] at hNat; exact hNat⟩
    · refine Or.inr (Or.inl ⟨1, by norm_num, by norm_num, f, hOm, ?_⟩)
      rw [hFix] at hNat
      exact sumOfNat_one bot_le hNat
    · exact Or.inr (Or.inr ⟨f, hOp, by rw [hFix] at hNat; exact hNat⟩)
  · rcases h3.toP18_6_3 with ⟨f, hSp | ⟨hOm, hSum⟩ | ⟨hEven, hOmega4m, hSum⟩⟩
    · exact absurd ⟨f, isSp4_barSub_of_isSp4_bar2 h hX1 hSp.1⟩ h11
    · exact Or.inr (Or.inl ⟨2, by norm_num, by norm_num, f, hOm, hSum⟩)
    · exact absurd ⟨f, hEven, hOmega4m, hSum⟩ (not_omega4minus_sum h12)
  · exact absurd h4 h9
  · exact absurd h5 h8
  · exact absurd h6 h9b

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
