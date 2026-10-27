module

public import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldExcPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.RankThree.PartOne.KF.F122Sp
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylKGInputNoU63OfRest
public import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Known
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylKGInputRest
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylScIrred
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitFive
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBModel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6DerModel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevRecipe

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbrKGFieldRow_of_plainRows {p r : ℕ} {lab lab₀ : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : 3 ≤ r) (hlab : LargeEvenInLambda2 lab)
    (hno_triD4 : ¬ (lab.tag = .triD4 ∧ p = 3))
    (hR : LargeEvenLabelAll lab (GGNbrWeylRowPlain p r))
    (hR₀ : LargeEvenLabelAll lab₀ (GGNbrWeylRowPlain p r))
    (hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p))
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (hstd : LargeEvenLabelAll lab (GGRawFieldFixStd p lab₀)) :
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusLiftFix p r R I F ∧ GGTorusNoLineFieldComp p r R I F := by
  have hRK : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r) :=
    hR.mono fun _ _ _ _ ⟨hi, hl, hn⟩ =>
      ⟨hi, hl, fun hs hna => ggTorusNoLineComp_of_ggTorusNoLine (hn hs hna)⟩
  have hFx : LargeEvenLabelAll lab (GGRawFieldFix p lab₀) :=
    (largeEvenLabelAll_and hcyc
      (largeEvenLabelAll_and (hconj p hp hp2 lab hlab hno_triD4)
        (largeEvenLabelAll_and (hcen lab hlab)
          (largeEvenLabelAll_and (hinn p hp hp2 lab hlab) hstd)))).mono
      fun _ _ _ _ ⟨hcy, hc, hce, hi, hst⟩ hs hna =>
        ggRawFieldFix_of_std hc (ggRawFieldNorm_of_central hce hi hs hna) hcy hst hs hna
  exact largeEvenLabelAll_fieldFix hp hr hRK hR₀ hcyc hFx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem ggFieldFixKnown_E6Three
    : GGFieldFixKnown fun p lab => lab.tag = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1 := by
  intro p lab hp hp2 hlab ⟨ht, _, hd⟩ Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht hd
  subst ht
  have heven : Even n := by
    by_contra hodd
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hodd
    have h2 : 2 ^ n % 3 = 2 := by
      rw [hk, pow_succ, pow_mul]
      norm_num [Nat.mul_mod, Nat.pow_mod]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
    e6_fixStd_der hn hK heven hp hp2 hf hord) hQ

@[expose] def GGFieldFixKnownTwE6 : Prop :=
  GGFieldFixKnown fun p lab => lab.tag = .twE6 ∧
    ((p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (5 ≤ p ∧ p ∣ 2 ^ lab.n + 1))

theorem largeEvenLabelAll_rowPlain_E6Three
    {lab : LargeEvenLabel} (ht : lab.tag = .E6)
    (hd : 3 ∣ 2 ^ lab.n - 1) : LargeEvenLabelAll lab (GGNbrWeylRowPlain 3 5) := by
  have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R :=
    largeEvenLabelAll_torusLift_E6_three ht hd
  have hnl : LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine 3 5 R I := by
    obtain ⟨t, l, m⟩ := lab
    dsimp only at ht hd
    subst ht
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    have hKf : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
    have h3 : 3 ∣ 2 ^ (f : ℕ) - 1 := by rw [← hKf, hK]; exact hd
    exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ =>
      ggTorusNoLine_of_noInvariantLineSCr Nat.prime_three
        (ggNoInvariantLineSCr_of_ggTableBModuleSCr (by norm_num)
          (ggE6DivModuleInput_of_model E6ThreeModel.e6ThreeModel_holds K f f.pos hKf h3))⟩
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_chevalley (Or.inl ht))
    (largeEvenLabelAll_and hl hnl)).mono fun _ _ _ _ h' => h'

theorem largeEvenLabelAll_rowPlain_twE6Three
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twE6) (hd : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain 3 4) := by
  have h3 : ¬ 3 ∣ 2 ^ lab.n + 1 := by
    have hpos : 0 < 2 ^ lab.n := Nat.two_pow_pos lab.n
    intro h3'
    have h2 : 3 ∣ (2 ^ lab.n + 1) - (2 ^ lab.n - 1) := Nat.dvd_sub h3' hd
    have h2' : (2 ^ lab.n + 1) - (2 ^ lab.n - 1) = 2 := by omega
    rw [h2'] at h2
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by norm_num)
  have hnl : LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine 3 4 R I :=
    TwE6Delta.labelAll ht fun K _ _ hK _ _ =>
      ggTorusNoLine_of_scNoLine Nat.prime_three (TwE6Delta.center_recipeR_eq_bot hlab.1 hK)
        (fun φ hφ _ => TwE6Delta.recipeI_subset_inn_of_not_dvd hlab.1 hK h3 hφ)
        (TwE6Delta.ggCenterPrime_three_twE6 hlab.1 hK h3)
        (ggSCNoLine_of_scWeylIrred Nat.prime_three
          (Irred937.ggNbrKGTwE6ThreeSubSCWeylIrred_holds K lab.n hlab.1 hK hd))
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_twE6 ht)
    (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_twE6Dvd Nat.prime_three (by norm_num) hlab
      ⟨ht, hd⟩) hnl)).mono fun _ _ _ _ h' => h'

theorem largeEvenLabelAll_rowPlain_twE6Large
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twE6)
    (hd : p ∣ 2 ^ lab.n + 1) : LargeEvenLabelAll lab (GGNbrWeylRowPlain p 5) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hr : TwE6Delta.liftRank p = 5 := TwE6Delta.liftRank_of_ne (by omega)
  have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 5 R := by
    have h := largeEvenLabelAll_torusLift_twE6Add_holds hp hlab ⟨ht, hd⟩
    rwa [hr] at h
  have hnl : LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine p 5 R I :=
    TwE6Delta.labelAll ht fun K _ _ hK _ _ =>
      ggTorusNoLine_of_noInvariantLineSCr hp
        (TwE6TB.ggNoInvariantLineSCr_of_irredSCr hp (TwE6TB.ggTorusIrredSCr_of_modelSCr hp5
          (ggTwE6TorusModelInput_holds K lab.n p hlab.1 hK hp hd hp5)))
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_twE6 ht)
    (largeEvenLabelAll_and hl hnl)).mono fun _ _ _ _ h' => h'

theorem ggNbrKGFieldE6_of_known
    (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    GGNbrKGFieldE6 := by
  intro p lab hp hp2 hlab ⟨ht, hp3, hd⟩ hdvd
  subst hp3
  have hnot : GGNotD4Three 3 lab := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hno : ¬ (lab.tag = .triD4 ∧ 3 = 3) := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hcyc : LargeEvenLabelAll lab (GGRawFieldCycW 3) :=
    (hpc 3 hp hp2 lab hlab hnot).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  have hR := largeEvenLabelAll_rowPlain_E6Three ht hd
  have hmul : lab.n = 3 * (lab.n / 3) := (Nat.mul_div_cancel' hdvd).symm
  have hd₀ : 3 ∣ 2 ^ (lab.n / 3) - 1 := by
    rw [hmul] at hd
    exact CFSG.RankThree.PartOne.dvd_two_pow_sub_one_of_mul hp hd
  have hR₀ := largeEvenLabelAll_rowPlain_E6Three (lab := ⟨lab.tag, lab.rank, lab.n / 3⟩) ht hd₀
  exact ggNbrKGFieldRow_of_plainRows hp hp2 (by norm_num) hlab hno hR hR₀ hcyc hconj hcen hinn
    (ggFieldFixKnown_E6Three 3 lab hp hp2 hlab ⟨ht, rfl, hd⟩)

theorem ggNbrKGFieldTwE6ThreeDvd_of_known
    (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (hstd : GGFieldFixKnownTwE6) : GGNbrKGFieldTwE6ThreeDvd := by
  intro p lab hp hp2 hlab ⟨ht, hp3, hd⟩ hdvd
  subst hp3
  have hnot : GGNotD4Three 3 lab := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hno : ¬ (lab.tag = .triD4 ∧ 3 = 3) := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hcyc : LargeEvenLabelAll lab (GGRawFieldCycW 3) :=
    (hpc 3 hp hp2 lab hlab hnot).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  have hR := largeEvenLabelAll_rowPlain_twE6Three hlab ht hd
  have hmul : lab.n = 3 * (lab.n / 3) := (Nat.mul_div_cancel' hdvd).symm
  have hd₀ : 3 ∣ 2 ^ (lab.n / 3) - 1 := by
    rw [hmul] at hd
    exact CFSG.RankThree.PartOne.dvd_two_pow_sub_one_of_mul hp hd
  have hlab₀ : LargeEvenInLambda2 (⟨lab.tag, lab.rank, lab.n / 3⟩ : LargeEvenLabel) := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hlab hdvd ⊢
    subst ht
    exact ⟨Nat.div_pos (Nat.le_of_dvd hlab.1 hdvd) hp.pos, hlab.2⟩
  have hR₀ := largeEvenLabelAll_rowPlain_twE6Three hlab₀ ht hd₀
  exact ggNbrKGFieldRow_of_plainRows hp hp2 (by norm_num) hlab hno hR hR₀ hcyc hconj hcen hinn
    (hstd 3 lab hp hp2 hlab ⟨ht, Or.inl ⟨rfl, hd⟩⟩)

theorem ggNbrKGFieldTwE6AddLarge_of_known
    (hpc : GGRawPCyclicOn GGNotD4Three)
    (hconj : GGRawFieldConjInputExc) (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (hstd : GGFieldFixKnownTwE6) : GGNbrKGFieldTwE6AddLarge := by
  intro p lab hp hp2 hlab ⟨ht, hp5, hd⟩ hdvd
  have hnot : GGNotD4Three p lab := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hno : ¬ (lab.tag = .triD4 ∧ p = 3) := by
    rintro ⟨h, -⟩
    rw [ht] at h
    exact absurd h (by decide)
  have hcyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab hnot).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  have hR := largeEvenLabelAll_rowPlain_twE6Large hp hp5 hlab ht hd
  have hmul : lab.n = p * (lab.n / p) := (Nat.mul_div_cancel' hdvd).symm
  have hd₀ : p ∣ 2 ^ (lab.n / p) + 1 := by
    rw [hmul] at hd
    exact CFSG.RankThree.PartOne.dvd_two_pow_add_one_of_mul hp hd
  have hlab₀ : LargeEvenInLambda2 (⟨lab.tag, lab.rank, lab.n / p⟩ : LargeEvenLabel) := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hlab hdvd ⊢
    subst ht
    exact ⟨Nat.div_pos (Nat.le_of_dvd hlab.1 hdvd) hp.pos, hlab.2⟩
  have hR₀ := largeEvenLabelAll_rowPlain_twE6Large hp hp5 hlab₀ ht hd₀
  exact ggNbrKGFieldRow_of_plainRows hp hp2 (by norm_num) hlab hno hR hR₀ hcyc hconj hcen hinn
    (hstd p lab hp hp2 hlab ⟨ht, Or.inr ⟨hp5, hd⟩⟩)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem ggFieldFixKnown_F4
    : GGFieldFixKnown fun _ lab => lab.tag = .F4 := by
  intro p lab hp _ hlab hS
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at hS
  subst hS
  exact recipeChevalley_and (fun K _ _ hK _ _ f hf hord =>
    chev_fixStd (τ := .F4) (Or.inl rfl) hn hK hp.pos hf hord) hQ

end CFSG.StandardType
