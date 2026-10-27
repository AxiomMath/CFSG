module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K324Spor
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35OmP3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLieCharRankProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankFour
public import CFSG.LocalAnalysis.UniquenessCase.UCKOutPHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Md0ec50421ce4 (PSimple IsChevSimple)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
  (innerRankThreeAt_of_isRankThreeIndex rankFourOpen_holds)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3 (four_le_pRank_three_of_isExcBig)

@[expose] def K324TwoIndex : TauCeti.LieTypeIndex → Prop
  | .A _ _ | .twistedA _ _ | .G2 _ | .trialityD4 _ | .reeF4 _ | .tits => True
  | .B r _ => r = 2
  | _ => False

@[expose] def K324Two : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ idx : TauCeti.ValidLieTypeIndex,
    idx.1.characteristic = 2 → K324TwoIndex idx.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ s : S, orderOf s = 5 → ∀ Y : Subgroup S, Y ≤ centralizer ({s} : Set S) →
      (Y.subgroupOf (centralizer ({s} : Set S))).Normal → IsAlt ↥Y 6 → False

section Two


theorem k324Simple_lie_two (h2 : K324Two) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (idx : TauCeti.ValidLieTypeIndex) (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group)
    (hr2 : idx.1.characteristic = 2) (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2) {x : S}
    (hxo : orderOf x = 3) {s : S} (hso : orderOf s = 5) {Y : Subgroup S}
    (hYC : Y ≤ centralizer ({s} : Set S)) (hYn : (Y.subgroupOf (centralizer ({s} : Set S))).Normal)
    (hY : IsAlt ↥Y 6) : False := by
  have hr3 : idx.1.characteristic ≠ 3 := by omega
  have hcen3 : CFSG.Open.pRank 3 (centralizer ({x} : Set S)) ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans h3
  have h2' := fun (h : K324TwoIndex idx.1) => h2 S hS idx hr2 h ⟨e⟩ s hso Y hYC hYn hY
  obtain ⟨d, hv⟩ := idx
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q => exact h2' trivial
  | twistedA r q => exact h2' trivial
  | G2 q => exact h2' trivial
  | trialityD4 q => exact h2' trivial
  | reeF4 m => exact h2' trivial
  | tits => exact h2' trivial
  | B r q =>
    rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | hr4
    · exact h2' rfl
    · have := innerRankThreeAt_of_isRankThreeIndex ⟨_, hv⟩ hr3 rfl S ⟨e⟩ x hxo
      omega
    · have := rankFourOpen_holds ⟨_, hv⟩ hr3 hr4 S ⟨e⟩
      omega
  | C r q =>
    exfalso
    rw [TauCeti.LieTypeIndex.characteristic_C] at hr2
    exact hr.2 hr2
  | D r q =>
    have := rankFourOpen_holds ⟨_, hv⟩ hr3 trivial S ⟨e⟩
    omega
  | twistedD r q =>
    rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
    · have := innerRankThreeAt_of_isRankThreeIndex ⟨_, hv⟩ hr3 rfl S ⟨e⟩ x hxo
      omega
    · have := rankFourOpen_holds ⟨_, hv⟩ hr3 hr5 S ⟨e⟩
      omega
  | E6 q =>
    have := four_le_pRank_three_of_isExcBig ⟨_, hv⟩ trivial e
    omega
  | E7 q =>
    have := four_le_pRank_three_of_isExcBig ⟨_, hv⟩ trivial e
    omega
  | E8 q =>
    have := four_le_pRank_three_of_isExcBig ⟨_, hv⟩ trivial e
    omega
  | F4 q =>
    have := four_le_pRank_three_of_isExcBig ⟨_, hv⟩ trivial e
    omega
  | twistedE6 q =>
    have := four_le_pRank_three_of_isExcBig ⟨_, hv⟩ trivial e
    omega
  | suzuki m =>
    have hcop := CFSG.LieType.SeitzGeneration.card_cat_suzuki_coprime_three hv
    have h3dvd : 3 ∣ Nat.card S := by
      rw [← hxo]
      exact orderOf_dvd_natCard x
    rw [Nat.card_congr e.toEquiv] at h3dvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop h3dvd
  | reeG2 m =>
    exfalso
    rw [TauCeti.LieTypeIndex.characteristic_reeG2] at hr2
    omega

end Two

section Lie


theorem k324Simple_lie (h2 : K324Two) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (idx : TauCeti.ValidLieTypeIndex) (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2) {s : S} (hso : orderOf s = 5) {Y : Subgroup S}
    (hYC : Y ≤ centralizer ({s} : Set S)) (hYn : (Y.subgroupOf (centralizer ({s} : Set S))).Normal)
    (hY : IsAlt ↥Y 6) : False := by
  obtain ⟨hnab, h3S, h25, hcomp, ⟨ψ⟩⟩ := k324Simple_data hS hso hYC hYn hY
  have hchev : IsChevSimple idx.1.characteristic S :=
    Or.inl ⟨TauCeti.CFSGIndex.lie idx, (rfl : idx.1.characteristic = idx.1.characteristic), ⟨e⟩⟩
  have hcomp' : GLAPComponent 5 (fixSubgroup (MulAut.conj s)) Y := by
    rw [CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415.fixSubgroup_conj]
    exact hcomp
  have hα5 : (MulAut.conj s) ^ 5 = 1 := by rw [← map_pow, ← hso, pow_orderOf_eq_one, map_one]
  have hI := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1315.kdChevDownQ_five_le
    (q := idx.1.characteristic) Nat.prime_five le_rfl S hS hnab hchev _ hα5 Y hcomp'
  have hA6 : IsChevSimple idx.1.characteristic (alternatingGroup (Fin 6)) :=
    CFSG.LocalAnalysis.GLTheoremA.chev_isChevSimple_of_mulEquiv ψ.symm hI
  have h5S : 5 ∣ Nat.card S := by
    rw [← hso]
    exact orderOf_dvd_natCard s
  by_cases hr2 : idx.1.characteristic = 2
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3S
    exact k324Simple_lie_two h2 hS idx e hr2 h3 hx hso hYC hYn hY
  rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop1116Design.alt_chev_cases
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts4.inputAltNotLie_holds hr2 (by norm_num)
      ⟨MulEquiv.refl _⟩ hA6 with ⟨h, -⟩ | ⟨-, hr3⟩
  · omega
  by_cases hsmall : CFSG.AGLEmbeddingD2.IsD2LieCharSmall 3 idx.1
  · obtain ⟨q, hq3, hcases⟩ := hsmall
    obtain ⟨d, hv⟩ := idx
    rcases hcases with ⟨hqe, rfl⟩ | ⟨hqe, rfl | rfl⟩
    ·
      exfalso
      obtain ⟨hst, hdup⟩ := (TauCeti.LieTypeIndex.valid_iff _).mp hv
      have h4' := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp hst).2 rfl
      rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
      have hq : q.card = 3 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq3]
      have he1 := q.exponent_pos
      interval_cases hqe' : q.exponent
      · rw [hq] at h4'
        norm_num at h4'
      · exact hdup (Or.inl ⟨rfl, Or.inr (Or.inr (by rw [hq]; norm_num))⟩)
    ·
      have hL := blueprintLieModel_of_models_classical (CFSG.Models.lieModel_A 2 q hv e)
        (Or.inl rfl) (by norm_num)
      rw [hq3, hqe] at hL
      have hcard := CFSG.ComponentClassification.CatLeafProof.card_eq_lieOrder hL.admissible hL
      rw [hcard] at h5S
      revert h5S
      decide
    ·
      have hL := blueprintLieModel_of_models_classical (CFSG.Models.lieModel_twistedA 2 q hv e)
        (Or.inr rfl) (by norm_num)
      have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
        TauCeti.LieTypeIndex.characteristic_twistedA 2 q
      have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
        TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
      rw [hc, hf, hq3, hqe] at hL
      have hcard := CFSG.ComponentClassification.CatLeafProof.card_eq_lieOrder hL.admissible hL
      rw [hcard] at h5S
      revert h5S
      decide
  · have := CFSG.AGLEmbeddingD2.kFactLieCharRank S idx ⟨e⟩ 3 Nat.prime_three (by norm_num) hr3.symm
      hsmall
    omega

end Lie

section All


theorem k324Simple_of_two
    (h2 : K324Two) : K324Simple := by
  intro S _ _ hS hK h3 h125 s hso Y hYC hYn hY
  obtain ⟨hnab, -, h25, hcomp, hYP⟩ := k324Simple_data hS hso hYC hYn hY
  haveI := hS
  obtain ⟨i, ⟨e⟩⟩ := hK.isCatalogGroup_of_surjective ⊤ hnab
    (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).toMonoidHom
    (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).surjective
  cases i with
  | cyclic p hp =>
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact k324Simple_alt hn e h3 h25
  | sporadic name => exact k324Simple_spor name e h3 h125 h25 hso hcomp hYP
  | lie idx => exact k324Simple_lie h2 hS idx e h3 hso hYC hYn hY

end All

section Final


theorem k324_of_two
    (h2 : K324Two) : K324 :=
  k324_of_simple (k324Simple_of_two h2) kOutP_holds

end Final

end CFSG.LocalAnalysis.UniquenessCase.UCK
