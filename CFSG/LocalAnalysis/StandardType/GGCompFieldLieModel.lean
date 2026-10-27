module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.CoverLower
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.Quasithin.Vol2.Ch3Sec3Obs3324
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Ctx
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleFF
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.B4L3Syl
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S153Cases
public import CFSG.Quasithin.EmptyFaithful.S153Five
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (fieldSize suzRee compRel compRelC)

theorem ggCompFieldAt_of_lieModel
    {G : Type} [Group G] {X : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥X) {t : StatedLieTag} {n f : ℕ}
    (h : LieModel (↥X ⧸ Subgroup.center ↥X) t n 2 f)
    (ht : t ≠ .twistedB2 ∧ t ≠ .twistedF4 ∧ t ≠ .Tits) : GGCompFieldAt (2 ^ f) X := by
  have hZ := CFSG.HardMathSupport.Timmesfeld.SporadicRank.center_quotient_center_eq_bot hq
  obtain ⟨lab, hlab, htag, hrank, hchar, hdeg, hraw⟩ := exists_label_rawDatum_of_lieModel hZ h
  have hmk : MarkedModel lab (↥X ⧸ Subgroup.center ↥X) := by
    unfold MarkedModel
    rw [htag, hrank, hchar, hdeg]
    exact h
  refine ⟨lab, hlab, hchar, by rw [hdeg], ?_, ?_, ?_, hraw, _, inferInstance, hmk,
    ⟨MulEquiv.refl _⟩⟩
  · intro h1
    apply ht.1
    rw [← htag]
    unfold markTag
    rw [h1]
  · intro h1
    apply ht.2.1
    rw [← htag]
    unfold markTag
    rw [h1]
  · intro h1
    apply ht.2.2
    rw [← htag]
    unfold markTag
    rw [h1]

theorem exists_lieModel_two_fieldSize_not_suzRee
    {S : Type} [Group S] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (e : S ≃* d.Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel S t n 2 f ∧
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = 2 ^ f ∧
      (¬ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.suzRee d.1 →
        t ≠ .twistedB2 ∧ t ≠ .twistedF4 ∧ t ≠ .Tits) := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  obtain ⟨d, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_A r q hv e
    rw [hp] at h
    exact ⟨_, _, _, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [classicalTags]) h, by show q.card = _; rw [PrimePower.card_def, hp],
      fun _ => ⟨by decide, by decide, by decide⟩⟩
  | twistedA r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_twistedA r q hv e
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := hd
    rw [hc] at h
    exact ⟨_, _, _, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [classicalTags]) h, by
        show q.card = _
        rw [PrimePower.card_def, hp, ValidLieTypeIndex.fieldExponent,
          LieTypeIndex.fieldExponent_twistedA], fun _ => ⟨by decide, by decide, by decide⟩⟩
  | B r q =>
    have hp : q.p = 2 := by simpa using hd
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · rw [hp] at h
      exact ⟨_, _, _, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
        (by simp [classicalTags]) h, by show q.card = _; rw [PrimePower.card_def, hp],
      fun _ => ⟨by decide, by decide, by decide⟩⟩
    · rw [hp] at h
      exact absurd h.1.2.2.2 (by simp)
  | C r q =>
    have hp : q.p = 2 := by simpa using hd
    exact absurd hp hr.2
  | D r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_D r q hv e
    rw [hp] at h
    exact ⟨_, _, _, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [classicalTags]) h, by show q.card = _; rw [PrimePower.card_def, hp],
      fun _ => ⟨by decide, by decide, by decide⟩⟩
  | twistedD r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_twistedD r q hv e
    rw [hp] at h
    exact ⟨_, _, _, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [classicalTags]) h, by show q.card = _; rw [PrimePower.card_def, hp],
      fun _ => ⟨by decide, by decide, by decide⟩⟩
  | E6 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E6, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.e6 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp], fun _ => ⟨by decide, by decide, by decide⟩⟩
  | E7 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E7, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.e7 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp], fun _ => ⟨by decide, by decide, by decide⟩⟩
  | E8 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E8, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.e8 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp], fun _ => ⟨by decide, by decide, by decide⟩⟩
  | F4 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.F4, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.f4 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp], fun _ => ⟨by decide, by decide, by decide⟩⟩
  | G2 q =>
    have hp : q.p = 2 := by simpa using hd
    have h3 : 3 ≤ 2 ^ q.exponent := by
      have h3 : 3 ≤ q.card := hr
      rwa [PrimePower.card_def, hp] at h3
    exact ⟨.G2, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.g2 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp], fun _ => ⟨by decide, by decide, by decide⟩⟩
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.twistedE6, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge hB.twistedE6 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp], fun _ => ⟨by decide, by decide, by decide⟩⟩
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.trialityD4, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge hB.trialityD4 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp], fun _ => ⟨by decide, by decide, by decide⟩⟩
  | suzuki m =>
    exact ⟨.twistedB2, 0, 2 * m + 1, .inr (.inr (.inr ⟨rfl, rfl,
      CFSG.StandardType.ChevTwo.suzukiModel_of_valid m hv e⟩)), rfl, fun h => (h trivial).elim⟩
  | reeG2 m =>
    exact absurd hd (by simp)
  | reeF4 a =>
    exact ⟨.twistedF4, 0, 2 * a + 1, .inr (.inr (.inl ⟨rfl, by simp [reeTitsTags],
      CFSG.StandardType.ChevTwo.reeTitsModel_of_reeF4 a hv e⟩)), rfl, fun h => (h trivial).elim⟩
  | tits =>
    exact ⟨.Tits, 0, 1, .inr (.inr (.inl ⟨rfl, by simp [reeTitsTags],
      CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e⟩)), (pow_one 2).symm,
        fun h => (h trivial).elim⟩

@[expose] def GGCompFieldDataQ {G : Type} [Group G] (q : ℕ) (X : Subgroup G) : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ GGCompFieldAt (q ^ m) X) ∨
    (q = 2 ∧ (Nat.card (↥X ⧸ Subgroup.center ↥X) = 360 ∨
      Nat.card (↥X ⧸ Subgroup.center ↥X) = 6048))

private theorem two_pow_ne_of_odd_ne_one {n c : ℕ} (hc : c % 2 = 1) (h1 : c ≠ 1) : 2 ^ n ≠ c := by
  intro h
  cases n with
  | zero => exact h1 (by simpa using h.symm)
  | succ n =>
    rw [pow_succ] at h
    omega

private theorem primePower_eq_of_card_prime {q : PrimePower} {c : ℕ} (hc : c.Prime)
    (h : q.card = c) : q.p = c ∧ q.exponent = 1 := by
  rw [PrimePower.card_def] at h
  exact (Nat.Prime.pow_eq_iff hc).mp h

theorem ggCompFieldDataQ_of_compRelC
    {G : Type} [Group G] {X : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥X) {d : LieTypeIndex} (hd : d.characteristic = 2)
    (hdsr : ¬ suzRee d) {k : ℕ} (hk : fieldSize d = 2 ^ k) {i : CFSGIndex} (hi : compRelC d i)
    (φ : ↥X ⧸ Subgroup.center ↥X ≃* i.Group) : GGCompFieldDataQ (fieldSize d) X := by
  cases i with
  | lie e =>
    obtain ⟨e, hv⟩ := e
    rcases hi with ⟨hch, ⟨j, hj, hfj⟩, hsr⟩ | ⟨h2, ⟨q', rfl, h7⟩ | ⟨q', rfl, h3⟩⟩ | ⟨h3, -⟩
    ·
      have he2 : ValidLieTypeIndex.characteristic ⟨e, hv⟩ = 2 := hch.trans hd
      obtain ⟨t, n, f, hm, hf, hnsr⟩ :=
        exists_lieModel_two_fieldSize_not_suzRee
          (S := ↥X ⧸ Subgroup.center ↥X) ⟨e, hv⟩ he2 φ
      refine Or.inl ⟨j, hj, ?_⟩
      rw [← hfj, hf]
      exact ggCompFieldAt_of_lieModel hq hm (hnsr (fun h => hdsr (hsr h)))
    ·
      obtain ⟨hp, hex⟩ := primePower_eq_of_card_prime (by norm_num) h7
      have hm := CFSG.Models.lieModel_A 1 q' hv φ
      have hs := (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
        (by simp [classicalTags]) hm).statedClassicalModel (by simp [classicalTags])
      rw [hp, hex] at hs
      have hs3 := CFSG.LocalAnalysis.RankThreeUC.S15.ksm_psl27_psl32 hs
      have hL : LieModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 1 :=
        Or.inl ⟨by simp [classicalTags], hs3⟩
      refine Or.inl ⟨1, le_rfl, ?_⟩
      rw [h2, pow_one, show (2 : ℕ) = 2 ^ 1 from rfl]
      exact ggCompFieldAt_of_lieModel hq hL ⟨by decide, by decide, by decide⟩
    ·
      obtain ⟨hp, hex⟩ := primePower_eq_of_card_prime (by norm_num) h3
      have hm := CFSG.Models.lieModel_twistedA 2 q' hv φ
      have hs := (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
        (by simp [classicalTags]) hm).statedClassicalModel (by simp [classicalTags])
      have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q', hv⟩ = 3 := by
        rw [show ValidLieTypeIndex.characteristic ⟨.twistedA 2 q', hv⟩ = q'.p from
          LieTypeIndex.characteristic_twistedA 2 q', hp]
      have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q', hv⟩ = 1 := by
        rw [show ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q', hv⟩ = q'.exponent from
          LieTypeIndex.fieldExponent_twistedA 2 q', hex]
      rw [hc, hf] at hs
      exact Or.inr ⟨h2, Or.inr (CFSG.Quasithin.H13.card_of_statedClassicalModel_psu_three_three hs)⟩
    · exact absurd (hk.symm.trans h3) (two_pow_ne_of_odd_ne_one (by norm_num) (by norm_num))
  | alternating n hn =>
    rcases hi with ⟨rfl, h5⟩ | ⟨rfl, h6⟩ | ⟨rfl, h8⟩
    ·
      have hL := CFSG.Quasithin.H13.Obs3324.lieModel_of_alt5 (X := ↥X ⧸ Subgroup.center ↥X) φ
      have hA := ggCompFieldAt_of_lieModel hq hL ⟨by decide, by decide, by decide⟩
      rcases h5 with h | h | h
      · exact Or.inl ⟨2, by norm_num, by rw [h]; exact hA⟩
      · exact Or.inl ⟨1, le_rfl, by rw [h, pow_one]; exact hA⟩
      · exact absurd (hk.symm.trans h) (two_pow_ne_of_odd_ne_one (by norm_num) (by norm_num))
    ·
      rcases h6 with h | h | h
      · refine Or.inr ⟨h, Or.inl ?_⟩
        rw [Nat.card_congr φ.toEquiv]
        show Nat.card (alternatingGroup (Fin 6)) = 360
        rw [CFSG.Quasithin.H13.card_alternatingGroup_fin 6 (by norm_num)]
        decide
      · exact absurd (hk.symm.trans h) (two_pow_ne_of_odd_ne_one (by norm_num) (by norm_num))
      · exact absurd (hk.symm.trans h) (two_pow_ne_of_odd_ne_one (by norm_num) (by norm_num))
    ·
      have hs := CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.statedClassicalModel_of_alt8
        (X := ↥X ⧸ Subgroup.center ↥X) φ
      have hL : LieModel (↥X ⧸ Subgroup.center ↥X) .PSL 4 2 1 :=
        Or.inl ⟨by simp [classicalTags], hs⟩
      refine Or.inl ⟨1, le_rfl, ?_⟩
      rw [h8, pow_one, show (2 : ℕ) = 2 ^ 1 from rfl]
      exact ggCompFieldAt_of_lieModel hq hL ⟨by decide, by decide, by decide⟩
  | _ => exact hi.elim

end CFSG.StandardType
