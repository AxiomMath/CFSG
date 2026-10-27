module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownTwOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsKnownOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsWrap
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylIrredLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailHolds
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldOtherTwOmegaRowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n + 1 ∧ lab.tag = .twD ∧ 4 ≤ lab.rank

@[expose] def GGFieldOtherTwOmegaLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ GGFieldOtherTwOmegaRowLabel p lab ∧
    GGFieldOtherTwOmegaRowLabel p ⟨lab.tag, lab.rank, lab.n / p⟩

section Rows

theorem largeEvenLabelAll_innLift_twOmegaAll {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (h : GGFieldOtherTwOmegaRowLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift p 3 R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hpn, ht, hl⟩ := h
  dsimp only at ht hl hpn ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
    have hlift := ggOrthRestTorusLiftInput_holds.1 K n (l - 1) p b c hK (by omega) hp hpn hbc
    exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', fun g => ⟨g, rfl⟩,
      ggTorusLift_mono hp hlift (by omega)⟩

theorem largeEvenLabelAll_rowPlain_twOmegaAll {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (h : GGFieldOtherTwOmegaRowLabel p lab) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p 3) :=
  (largeEvenLabelAll_and (largeEvenLabelAll_innLift_twOmegaAll hp h)
    (largeEvenLabelAll_torusIrredSC_orthNs hp ⟨Or.inr h.2.1, h.2.2, h.1⟩)).mono
    fun _ _ _ _ ⟨⟨hi, hl⟩, hs⟩ => ⟨hi, hl, fun _ _ => ggTorusNoLine_of_ggTorusIrredSC hp hs⟩

end Rows

theorem ggFieldOtherTwOmegaRowLabel_not {p : ℕ} {lab : LargeEvenLabel}
    (h : GGFieldOtherTwOmegaRowLabel p lab) :
    GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨-, ht, -⟩ := h
  refine ⟨?_, ?_⟩
  · rintro ⟨h', -⟩
    rw [ht] at h'
    cases h'
  · rintro ⟨h', -⟩
    rw [ht] at h'
    cases h'

theorem largeEvenInLambda2_subfieldTwOmegaAll {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGFieldOtherTwOmegaLabel p lab) :
    LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩ := by
  obtain ⟨hn1, -⟩ := hlab
  obtain ⟨hdvd, ⟨-, ht, hl⟩, -⟩ := h
  have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdvd hn1
  refine ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdvd) hp0, ?_⟩
  dsimp only
  rw [ht]
  omega

theorem ggFieldFixKnown_twOmegaAll : GGFieldFixKnown GGFieldOtherTwOmegaLabel := by
  intro p lab hp hp2 hlab hS
  obtain ⟨-, ⟨-, ht, h4⟩, -⟩ := hS
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4 hn
  subst ht
  refine largeEvenLabelAll_omegaMinus (lab := ⟨.twD, l, n⟩) rfl h4 fun K _ _ _ hK b c hirr => ?_
  intro hS' hna f hf hord
  have h2 : l ≠ 2 := by omega
  have h3 : l ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum]
  simp only [h2, h3, ↓reduceIte]
  exact FieldFixTwOmega.exists_fixGeom h4 hn hp hp2 hK hirr hS' hna hf hord

section KnownTwOmega


theorem ggFieldKLevel_twOmegaAll (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherTwOmegaLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  ggFieldKLevel_of_fixKnownRow (r := 3) (Rw := GGFieldOtherTwOmegaRowLabel) le_rfl
    (fun _ _ h => h) (fun _ _ hlab h => largeEvenInLambda2_subfieldTwOmegaAll hlab h)
    (fun _ _ h => ggFieldOtherTwOmegaRowLabel_not h) ggFieldFixKnown_twOmegaAll
    (fun _ _ hp _ _ h => largeEvenLabelAll_rowPlain_twOmegaAll hp h) hpc hconj hcen hinn

theorem ggNbrInnerWeylOn_of_twOmegaAll (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherTwOmegaLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_twOmegaAll hpc hconj hcen hinn) hT

end KnownTwOmega

theorem exists_not_commute_projOmegaPlus_two {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) {m : ℕ} (hm : 4 ≤ m) :
    ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m)), a * b ≠ b * a := by
  haveI : CharP k 2 := charP_two_of_card (m := 1) (by rw [hk]; norm_num)
  haveI hS : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by omega)
  haveI : Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m))) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨-, E, -, -, -, -, hE⟩ := OrthRestTail.torus_plus (K := k) hk hm
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3E : 3 ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := E) 3 h3E
  haveI hN : (Subgroup.zpowers (g : OrthRest.RPlus k m)).Normal :=
    ⟨fun n hn x => by rwa [hcon x n, mul_inv_cancel_right]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers (g : OrthRest.RPlus k m)) with
    h | h
  · have h1 : (g : OrthRest.RPlus k m) = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.mem_zpowers _
    have h2 : g = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hg
    omega
  · have hcard : Nat.card (OrthRest.RPlus k m) = 3 := by
      rw [← Subgroup.card_top, ← h, Nat.card_zpowers, Subgroup.orderOf_coe, hg]
    have hle : Nat.card E ≤ Nat.card (OrthRest.RPlus k m) := Subgroup.card_le_card_group E
    rw [hE, hcard] at hle
    have h27 : 3 ^ 3 ≤ 3 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

namespace FieldOtherOmegaPlus

open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.RankThree.PartOne.KCSpComm (card_descentField)
open FieldFixOmegaPlus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem exists_fixGeom_all (hm : 4 ≤ m) {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ n)
    (hS : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))
    (hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)), a * b ≠ b * a)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m))))
    (hord : orderOf f = p) :
    LargeEvenRecipeOmegaPlus m (2 ^ (n / p)) fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ ∃ θ₀ : ggFixDer f ≃* R₀,
        GGFixGeom (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))) f I₀
          θ₀ := by
  have hm1 : 1 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  obtain ⟨σ, hσf⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_field hm1 hf
  have hinj : Function.Injective (AutOm.fieldAutP (K := K) m) :=
    (injective_iff_map_eq_one _).2 fun τ h => AutOm.eq_one_of_fieldAutP_eq_one hm3 h
  have hσ : orderOf σ = p := by
    rw [← orderOf_injective (AutOm.fieldAutP m) hinj σ, ← hσf, MulEquiv.orderOf_eq]
    exact hord
  set k := descentField σ with hkdef
  have hσk : ∀ x, x ∈ k ↔ σ x = x := fun x => mem_descentField
  obtain ⟨-, hcard⟩ := card_descentField Nat.prime_two hn hK hσ
  have hS₀ : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus hm3
  have hna₀ : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m)), a * b ≠ b * a := by
    by_cases hq : 4 ≤ 2 ^ (n / p)
    · exact FieldFixOmegaPlusNs.exists_not_commute_projOmegaPlus (k := k)
        (by rw [hcard]; exact hq) hm3
    · have h1 : 1 < Nat.card k := Finite.one_lt_card
      have h2 : Nat.card k = 2 := by
        rw [hcard] at h1 ⊢
        rcases Nat.lt_or_ge (n / p) 2 with h | h
        · interval_cases hnp : n / p <;> simp_all
        · exact absurd (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)) hq
      exact exists_not_commute_projOmegaPlus_two (k := k) h2 hm
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) = ⊥ := by
    obtain ⟨x, y, hxy⟩ := hna
    exact TableBOrth.center_eq_bot_of_simple hxy
  have hrange : (subfieldInj k hm1).range = ggFixSub f := by
    ext r
    rw [mem_range_subfieldInj_iff k hp hp2 hσ hσk hm3 hσf r, mem_ggFixSub]
  let e : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m)) ≃* ↥(ggFixSub f) :=
    (MonoidHom.ofInjective (subfieldInj_injective k hm1)).trans (MulEquiv.subgroupCongr hrange)
  haveI := hS₀
  exact ⟨k, inferInstance, inferInstance, hcard, hS₀, hna₀,
    ggFixGeom_of_inn hna₀ hZ (fun _ h => h) (fun _ h => h) e⟩

end FieldOtherOmegaPlus

theorem ggFieldFixKnown_omegaPlusAll :
    GGFieldFixKnown fun _ lab => lab.tag = .D ∧ 4 ≤ lab.rank := by
  intro p lab hp hp2 hlab hS
  obtain ⟨ht, h4⟩ := hS
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4 hn
  subst ht
  refine largeEvenLabelAll_omegaPlus (lab := ⟨.D, l, n⟩) rfl h4 fun K _ _ _ hK => ?_
  intro hS hna f hf hord
  have h3 : l ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum]
  simp only [h3, ↓reduceIte]
  exact FieldOtherOmegaPlus.exists_fixGeom_all h4 hn hp hp2 hK hS hna hf hord

@[expose] def GGFieldOtherOmegaEightLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ 4 ≤ lab.rank ∧ p = 3 ∧ (lab.n = 1 ∨ lab.n = 3)

section KnownOmegaEight


theorem largeEvenLabelAll_rowPlain_omegaTwo {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : 4 ≤ lab.rank) (hn : lab.n = 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain 3 3) := by
  have hinn : LargeEvenLabelAll lab fun R _ I _ =>
      (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift 3 3 R :=
    largeEvenLabelAll_omegaPlus ht h4 fun K _ _ _ hK => by
      have hK2 : Nat.card K = 2 := by rw [hK, hn]; norm_num
      exact ⟨fun g => ⟨g, rfl⟩, ggTorusLift_mono Nat.prime_three
        (ggOrthRestTorusLiftInput_holds.2 K lab.rank hK2 h4) (by omega)⟩
  exact (largeEvenLabelAll_and hinn
    (largeEvenLabelAll_torusIrredSC_orthNs Nat.prime_three
      ⟨Or.inl ht, h4, by rw [hn]; norm_num⟩)).mono
    fun _ _ _ _ ⟨⟨hi, hl⟩, hs⟩ =>
      ⟨hi, hl, fun _ _ => ggTorusNoLine_of_ggTorusIrredSC Nat.prime_three hs⟩

theorem largeEvenLabelAll_rowPlain_omegaEightRow {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : 4 ≤ lab.rank) (hn : lab.n = 3) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain 3 3) :=
  (largeEvenLabelAll_and
    (largeEvenLabelAll_innLift_omegaPlusNs Nat.prime_three (by norm_num)
      ⟨ht, h4, by omega, by rw [hn]; norm_num⟩)
    (largeEvenLabelAll_torusIrredSC_orthNs Nat.prime_three
      ⟨Or.inl ht, h4, by rw [hn]; norm_num⟩)).mono
    fun _ _ _ _ ⟨⟨hi, hl⟩, hs⟩ =>
      ⟨hi, hl, fun _ _ => ggTorusNoLine_of_ggTorusIrredSC Nat.prime_three hs⟩

theorem ggFieldKLevel_omegaEight (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherOmegaEightLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab hS
  obtain ⟨ht, h4, hp3, hn⟩ := hS
  subst hp3
  have hcyc : LargeEvenLabelAll lab (GGRawFieldCycW 3) := ggRawFieldCycWOn_omegaPlus 3 ht h4
  have hc := hconj 3 hp hp2 lab hlab (by rintro ⟨h, -⟩; rw [ht] at h; cases h)
  have hce := hcen lab hlab
  have hi := hinn 3 hp hp2 lab hlab
  rcases hn with hn | hn
  ·
    have hR := largeEvenLabelAll_rowPlain_omegaTwo ht h4 hn
    exact largeEvenLabelAll_fieldKLevelComp_of_std hp le_rfl hR hR hcyc hc hce hi
      (ggRawFieldFixStd_of_not_dvd_omegaPlus hlab ht h4 (by rw [hn]; norm_num))
  ·
    have hR := largeEvenLabelAll_rowPlain_omegaEightRow ht h4 hn
    have hR₀ : LargeEvenLabelAll ⟨lab.tag, lab.rank, lab.n / 3⟩ (GGNbrWeylRowPlain 3 3) :=
      largeEvenLabelAll_rowPlain_omegaTwo (lab := ⟨lab.tag, lab.rank, lab.n / 3⟩) ht h4
        (by dsimp only; rw [hn])
    exact largeEvenLabelAll_fieldKLevelComp_of_std hp le_rfl hR hR₀ hcyc hc hce hi
      (ggFieldFixKnown_omegaPlusAll 3 lab hp hp2 hlab ⟨ht, h4⟩)

theorem ggNbrInnerWeylOn_of_omegaEight (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput)
    (hinn : GGRawInnFieldInput) {T : ℕ → LargeEvenLabel → Prop}
    (hT : GGNbrInnerWeylOn fun p lab => T p lab ∧ ¬ GGFieldOtherOmegaEightLabel p lab) :
    GGNbrInnerWeylOn T :=
  ggNbrInnerWeylOn_of_fieldFixKLevel hL hPJ hG (ggFieldKLevel_omegaEight hconj hcen hinn) hT

end KnownOmegaEight

end CFSG.StandardType

end
