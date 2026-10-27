module

public import CFSG.LocalAnalysis.StandardType.GGK0ExcTrivialTable
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3OfProducers
public import CFSG.LocalAnalysis.StandardType.GGK0MarkedArithmetic
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegNTUnivHolds
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitCyclicCore
public import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwo
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.StandardType.GGK0ExcB3Prod

open CFSG CFSG.Assembly CFSG.StandardType

private abbrev ltrk0t2_P (lab : LargeEvenLabel) (p : ℕ) : LargeEvenRawCont :=
  fun R _ I _ => ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R),
    Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∃ D : GGKacDatum, GGK0ExcCore lab p L' 1 D ∧ GGK0ExcCentre lab p I L' ψ 1 D

private lemma ltrk0t2_center_top_eq_bot {R : Type} [Group R]
    (hZ : Subgroup.center R = ⊥) : Subgroup.center (↥(⊤ : Subgroup R)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hxR : (x : R) ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro r
    have h := (Subgroup.mem_center_iff.mp hx) ⟨r, Subgroup.mem_top r⟩
    simpa using congrArg Subtype.val h
  rw [hZ] at hxR
  simpa using Subgroup.mem_bot.mp hxR

private lemma ltrk0t2_topComponent {L' : Type} [Group L'] [Finite L']
    (hQ : CFSG.IsQuasisimple L') :
    IsComponentOf (⊤ : Subgroup L') (ggFixSub (1 : MulAut L')) := by
  have hQtop : CFSG.IsQuasisimple ↥(⊤ : Subgroup L') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ
  have hQassem : Assembly.IsQuasisimple ↥(⊤ : Subgroup L') :=
    ⟨Group.isPerfect_def.mp hQtop.1, hQtop.2.1⟩
  have hfix : ggFixSub (1 : MulAut L') = ⊤ := by
    ext x
    simp [ggFixSub]
  rw [hfix]
  exact ⟨le_top, IsSubnormal.refl ⊤, hQassem⟩

private lemma ltrk0t2_compBij {L' : Type} [Group L'] [Finite L'] {lab : LargeEvenLabel}
    (hQ : CFSG.IsQuasisimple L')
    (hcomp : ∀ J : Subgroup L', IsComponentOf J (ggFixSub (1 : MulAut L')) → J = ⊤)
    (hlabTop : GGHasLabel lab (↥(⊤ : Subgroup L') ⧸ Subgroup.center (↥(⊤ : Subgroup L')))) :
    GGKacCompBij (GGKacIdentityDatum lab) L' (1 : MulAut L') := by
  have hcompTop : IsComponentOf (⊤ : Subgroup L') (ggFixSub (1 : MulAut L')) :=
    ltrk0t2_topComponent hQ
  haveI : Unique {J : Subgroup L' // IsComponentOf J (ggFixSub (1 : MulAut L'))} :=
    ⟨⟨⊤, hcompTop⟩, fun J => Subtype.ext (hcomp J.1 J.2)⟩
  have horbit : ∀ i : Fin (GGKacIdentityDatum lab).orbits.length,
      (GGKacIdentityDatum lab).orbits[i] = ⟨lab, true⟩ := by
    intro i
    fin_cases i
    simp [GGKacIdentityDatum]
  haveI : Unique {i : Fin (GGKacIdentityDatum lab).orbits.length //
      (GGKacIdentityDatum lab).orbits[i].qs = true} :=
    ⟨⟨⟨0, by simp [GGKacIdentityDatum]⟩, by simp [GGKacIdentityDatum]⟩,
      fun i => Subtype.ext (Fin.ext (by
        have h := i.1.isLt
        have hlen : (GGKacIdentityDatum lab).orbits.length = 1 := rfl
        show (i.1 : ℕ) = 0
        omega))⟩
  let f : {J : Subgroup L' // IsComponentOf J (ggFixSub (1 : MulAut L'))} ≃
      {i : Fin (GGKacIdentityDatum lab).orbits.length //
        (GGKacIdentityDatum lab).orbits[i].qs = true} := Equiv.ofUnique _ _
  refine ⟨f, ?_⟩
  intro J
  have hlab_eq : (GGKacIdentityDatum lab).orbits[(f J).1].lab = lab :=
    congrArg (fun o => o.lab) (horbit (f J).1)
  rw [hlab_eq]
  have hJ : J.1 = ⊤ := hcomp J.1 J.2
  let iso : (↥J.1 ⧸ Subgroup.center ↥J.1) ≃*
      (↥(⊤ : Subgroup L') ⧸ Subgroup.center (↥(⊤ : Subgroup L'))) :=
    QuotientGroup.congr (Subgroup.center ↥J.1) (Subgroup.center (↥(⊤ : Subgroup L')))
      (MulEquiv.subgroupCongr hJ) (Subgroup.map_center_eq (MulEquiv.subgroupCongr hJ))
  exact ggHasLabel_of_mulEquiv iso.symm hlabTop

private lemma ltrk0t2_point {lab : LargeEvenLabel} {p : ℕ}
    (hΛ : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (hT : GGKacValid lab p (GGKacIdentityDatum lab))
    {R : Type} [Group R]
    (hR : GGHasLabel lab R) (hs : IsSimpleGroup R)
    (hZ : Subgroup.center R = ⊥) (hM : MarkedModel lab R) :
    ∀ (I F : Set (MulAut R)), ltrk0t2_P lab p R I F := by
  intro I F
  intro L' _ _ ψ hψ hker hperf
  haveI : Finite R := Finite.of_surjective ψ hψ
  have hZker : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzR : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZ] at hzR
    exact Subgroup.mem_bot.mp hzR
  have hker_eq : ψ.ker = Subgroup.center L' := le_antisymm hker hZker
  let e : L' ⧸ Subgroup.center L' ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hlabL : GGHasLabel lab (L' ⧸ Subgroup.center L') :=
    ggHasLabel_of_mulEquiv e.symm hR
  have hperf' : Group.IsPerfect L' := by
    rw [Group.isPerfect_def]
    exact hperf
  have hQ : CFSG.IsQuasisimple L' :=
    (CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwo.isQuasisimple_of_central_cover
      hperf' (le_refl (Subgroup.center L')) e).1
  have hfix : ggFixSub (1 : MulAut L') = ⊤ := by
    ext x
    simp [ggFixSub]
  have hcomp : ∀ J : Subgroup L', IsComponentOf J (ggFixSub (1 : MulAut L')) → J = ⊤ := by
    intro J hJ
    rw [hfix] at hJ
    exact ExcNonsplit.eq_top_of_isComponentOf_top hQ hJ
  have hcompTop : IsComponentOf (⊤ : Subgroup L') (ggFixSub (1 : MulAut L')) :=
    ltrk0t2_topComponent hQ
  have hlabTop : GGHasLabel lab (↥(⊤ : Subgroup L') ⧸ Subgroup.center (↥(⊤ : Subgroup L'))) :=
    ggHasLabel_quotCenter_of_mulEquiv
      (Subgroup.topEquiv (G := L')).symm hlabL
  have htag : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
      lab.tag = .F4 := hpair.2.2.2
  have hneG2 : lab.tag ≠ .G2der := by
    rintro h
    rcases htag with h' | h' | h' | h' | h' <;> rw [h] at h' <;> exact nomatch h'
  have hneB2 : lab.tag ≠ .B2der := by
    rintro h
    rcases htag with h' | h' | h' | h' | h' <;> rw [h] at h' <;> exact nomatch h'
  have hneTwB2 : lab.tag ≠ .twB2 := by
    rintro h
    rcases htag with h' | h' | h' | h' | h' <;> rw [h] at h' <;> exact nomatch h'
  have hneF4 : lab.tag ≠ .twF4 := by
    rintro h
    rcases htag with h' | h' | h' | h' | h' <;> rw [h] at h' <;> exact nomatch h'
  have hneF4d : lab.tag ≠ .twF4der := by
    rintro h
    rcases htag with h' | h' | h' | h' | h' <;> rw [h] at h' <;> exact nomatch h'
  have hchar : markChar lab = 2 := markChar_eq_two_of_ne hneB2 hneG2
  have hdeg : markDeg lab = lab.n := by
    rcases htag with h | h | h | h | h <;> simp [markDeg, h]
  have hcenterTop : Subgroup.center (↥(⊤ : Subgroup R)) = ⊥ :=
    ltrk0t2_center_top_eq_bot hZ
  let e2 : (↥(⊤ : Subgroup R) ⧸ Subgroup.center (↥(⊤ : Subgroup R))) ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hcenterTop).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have hlabTopR : GGHasLabel lab
      (↥(⊤ : Subgroup R) ⧸ Subgroup.center (↥(⊤ : Subgroup R))) :=
    ggHasLabel_of_mulEquiv e2.symm hR
  have hmodelTop : MarkedModel lab
      (↥(⊤ : Subgroup R) ⧸ Subgroup.center (↥(⊤ : Subgroup R))) :=
    MarkedModel.of_mulEquiv e2.symm hM
  have hfield : GGCompFieldAt (2 ^ markDeg lab) (⊤ : Subgroup R) :=
    ⟨lab, hΛ, hchar, rfl, hneTwB2, hneF4, hneF4d, hlabTopR,
      ⟨_, inferInstance, hmodelTop, ⟨MulEquiv.refl _⟩⟩⟩
  have hdvd : (2 ^ markDeg lab) ^ 2 - 1 ∣ Nat.card (⊤ : Subgroup R) :=
    ggCompFieldAt_dvd hfield
  rw [Subgroup.card_top, hdeg] at hdvd
  have hpSq : p ∣ (2 ^ lab.n) ^ 2 - 1 :=
    CorFourTwoVacMore.dvd_sq_sub_one_of_dvd (hpair.2.2.1.elim Or.inr Or.inl)
  have hpR : p ∣ Nat.card R := hpSq.trans hdvd
  have hquot : Nat.card (L' ⧸ ψ.ker) = Nat.card R :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv
  have hcardL : Nat.card L' = Nat.card R * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, hquot]
  have hpL : p ∣ Nat.card L' := by
    rw [hcardL]
    exact dvd_mul_of_dvd_left hpR _
  have hcore : GGK0ExcCore lab p L' 1 (GGKacIdentityDatum lab) := by
    refine ⟨hT, ?_, ?_, ?_, ?_, ?_⟩
    · intro J hJ
      refine ⟨⟨lab, true⟩, ?_, rfl, dvd_refl lab.n, hΛ, ?_⟩
      · simp [GGKacIdentityDatum]
      · rw [hcomp J hJ]
        exact hlabTop
    · intro o ho _
      have ho' : o = ⟨lab, true⟩ := by
        simpa [GGKacIdentityDatum] using ho
      subst ho'
      exact ⟨⊤, hcompTop, hlabTop⟩
    · intro J hJ
      rw [hcomp J hJ, Subgroup.card_top]
      exact hpL
    · exact ltrk0t2_compBij hQ hcomp hlabTop
    · intro i hi _
      have hget : (GGKacIdentityDatum lab).orbits[i] = ⟨lab, true⟩ := by
        rw [Fin.eq_zero i]
        simp [GGKacIdentityDatum]
      rw [hget] at hi
      have htagA : lab.tag = .A := congrArg (fun l : LargeEvenLabel => l.tag) hi
      rcases htag with h | h | h | h | h <;> rw [h] at htagA <;> exact nomatch htagA
  refine ⟨GGKacIdentityDatum lab, hcore, ?_⟩
  intro _ hrz
  simp [GGKacIdentityDatum] at hrz

private lemma ltrk0t2_excData {lab : LargeEvenLabel} {p : ℕ}
    (hΛ : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p) :
    LargeEvenLabelAll lab fun R _ _ _ =>
      IsSimpleGroup R ∧ Subgroup.center R = ⊥ ∧ GGHasLabel lab R ∧ MarkedModel lab R := by
  intro Q hQ
  obtain ⟨tag, rk, n⟩ := lab
  rcases hpair.2.2.2 with hE6 | htwE6 | hE7 | hE8 | hF4
  · subst hE6
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_, ?_, ?_, ?_⟩
    · exact (CFSG.LieType.Simplicity.fam_e6_simplicity _ 2 n
        ⟨⟨Nat.prime_two, hΛ.1, rfl⟩, untwistedChevalleyModel_largeEven .E6 hKcard⟩).2
    · obtain ⟨K', _, _, _, ⟨e⟩⟩ :=
        (untwistedChevalleyModel_largeEven .E6 hKcard :
          CFSG.Blueprint.UntwistedChevalleyModel _ .E6 (2 ^ n))
      exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e
        (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_adjointQuotient_eq_bot .E6 K')
    · dsimp only [GGHasLabel, LargeEvenRawDatum]
      exact ⟨K, hKf, hKfin, hKcard, ⟨MulEquiv.refl _⟩⟩
    · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg]
      exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hΛ.1, rfl⟩,
        untwistedChevalleyModel_largeEven .E6 hKcard⟩)
  · subst htwE6
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    have hTw : CFSG.Blueprint.TwistedChevalleyModel
        (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))
        .E6 (2 ^ n) :=
      twistedChevalleyModel_largeEven .E6 (n := n) hKcard
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_, ?_, ?_, ?_⟩
    · exact (CFSG.LieType.Simplicity.fam_2e6_simplicity _ 2 n
        ⟨⟨Nat.prime_two, hΛ.1, rfl⟩, hTw⟩).2
    · obtain ⟨K', _, _, hK'card, σ, hσ, ⟨e⟩⟩ := hTw
      have hθ : ∀ c, σ (σ c) = c := fun c => by
        rw [hσ, hσ, CFSG.LieType.Simplicity.pow_pow_card_sq hK'card]
      have h4 : 4 ≤ Nat.card K' := by
        rw [hK'card]
        change 4 ≤ ((2 : ℕ) ^ n) ^ 2
        rw [pow_two]
        have h2 : 2 ≤ (2 : ℕ) ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hΛ.1
        nlinarith
      have hZ : Subgroup.center (CFSG.Blueprint.DerivedCentralQuotient
          (CFSG.Blueprint.twistedFixedGroup .E6 K' σ)) = ⊥ :=
        CFSG.LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple
          (CFSG.LieType.Simplicity.isQuasisimple_derived_twistedFixedGroup σ hθ h4)
      exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e hZ
    · dsimp only [GGHasLabel, LargeEvenRawDatum]
      exact ⟨K, hKf, hKfin, hKcard, ⟨MulEquiv.refl _⟩⟩
    · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg]
      exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hΛ.1, rfl⟩, hTw⟩)
  · subst hE7
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_, ?_, ?_, ?_⟩
    · exact (CFSG.LieType.Simplicity.fam_e7_simplicity _ 2 n
        ⟨⟨Nat.prime_two, hΛ.1, rfl⟩, untwistedChevalleyModel_largeEven .E7 hKcard⟩).2
    · obtain ⟨K', _, _, _, ⟨e⟩⟩ :=
        (untwistedChevalleyModel_largeEven .E7 hKcard :
          CFSG.Blueprint.UntwistedChevalleyModel _ .E7 (2 ^ n))
      exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e
        (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_adjointQuotient_eq_bot .E7 K')
    · dsimp only [GGHasLabel, LargeEvenRawDatum]
      exact ⟨K, hKf, hKfin, hKcard, ⟨MulEquiv.refl _⟩⟩
    · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg]
      exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hΛ.1, rfl⟩,
        untwistedChevalleyModel_largeEven .E7 hKcard⟩)
  · subst hE8
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_, ?_, ?_, ?_⟩
    · exact (CFSG.LieType.Simplicity.fam_e8_simplicity _ 2 n
        ⟨⟨Nat.prime_two, hΛ.1, rfl⟩, untwistedChevalleyModel_largeEven .E8 hKcard⟩).2
    · obtain ⟨K', _, _, _, ⟨e⟩⟩ :=
        (untwistedChevalleyModel_largeEven .E8 hKcard :
          CFSG.Blueprint.UntwistedChevalleyModel _ .E8 (2 ^ n))
      exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e
        (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_adjointQuotient_eq_bot .E8 K')
    · dsimp only [GGHasLabel, LargeEvenRawDatum]
      exact ⟨K, hKf, hKfin, hKcard, ⟨MulEquiv.refl _⟩⟩
    · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg]
      exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hΛ.1, rfl⟩,
        untwistedChevalleyModel_largeEven .E8 hKcard⟩)
  · subst hF4
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq⟩ := hQ
    refine ⟨K, hKf, hKfin, hKcard, hq, ?_, ?_, ?_, ?_⟩
    · exact (CFSG.LieType.Simplicity.fam_f4_simplicity _ 2 n
        ⟨⟨Nat.prime_two, hΛ.1, rfl⟩, untwistedChevalleyModel_largeEven .F4 hKcard⟩).2
    · obtain ⟨K', _, _, _, ⟨e⟩⟩ :=
        (untwistedChevalleyModel_largeEven .F4 hKcard :
          CFSG.Blueprint.UntwistedChevalleyModel _ .F4 (2 ^ n))
      exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e
        (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_adjointQuotient_eq_bot .F4 K')
    · dsimp only [GGHasLabel, LargeEvenRawDatum]
      exact ⟨K, hKf, hKfin, hKcard, ⟨MulEquiv.refl _⟩⟩
    · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg]
      exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hΛ.1, rfl⟩,
        untwistedChevalleyModel_largeEven .F4 hKcard⟩)

theorem ggK0ExcTrivial_of_table
    (hT : ∀ (p : ℕ) (lab : LargeEvenLabel), LargeEvenInLambda2 lab → GGKacExcPair lab p →
      GGKacValid lab p (GGKacIdentityDatum lab)) : GGK0ExcTrivial := by
  intro p lab hΛ hpair
  intro Q hQ
  have hdata := ltrk0t2_excData (p := p) hΛ hpair Q hQ
  obtain ⟨tag, rk, n⟩ := lab
  rcases hpair.2.2.2 with h | h | h | h | h
  all_goals
    subst h
    dsimp only [LargeEvenRawDatum] at hdata ⊢
    obtain ⟨K, hKf, hKfin, hKcard, hq, hs, hZ, hR, hM⟩ := hdata
    refine ⟨K, hKf, hKfin, hKcard, ?_⟩
    exact ⟨hq, ltrk0t2_point hΛ hpair (hT p _ hΛ hpair) hR hs hZ hM _ ∅⟩

end CFSG.StandardType.GGK0ExcB3Prod

end
