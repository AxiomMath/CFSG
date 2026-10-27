module

public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsGen
public import CFSG.LocalAnalysis.UniquenessCase.UC6K591Cent
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicTits
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankFourTheoremC
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.Blueprint (LieModel)

section Model


theorem lieModel_equiv {X : Type} [Group X] (h : LieModel X .Tits 0 2 1) : Nonempty (X ≃* titsD) :=
  titsModelEquiv X 2 1 (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2

theorem simple_of_lieModel {X : Type} [Group X] (h : LieModel X .Tits 0 2 1) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨e⟩ := lieModel_equiv h
  haveI : IsSimpleGroup titsD := titsD_simple
  haveI : IsSimpleGroup X := e.isSimpleGroup_congr.mpr inferInstance
  haveI : Finite X := Finite.of_equiv titsD e.symm.toEquiv
  have h2 : 2 ∣ Nat.card X := by rw [Nat.card_congr e.toEquiv, card_titsD]; norm_num
  have h3 : 2 < Nat.card X := by rw [Nat.card_congr e.toEquiv, card_titsD]; norm_num
  exact ⟨inferInstance, exists_noncomm_of_simple_of_even h2 h3⟩

end Model

section Iso


theorem isoLie_of_lieModel {X : Type} [Group X] (h : LieModel X .Tits 0 2 1) : IsoLie X .tits := by
  have hv : TauCeti.LieTypeIndex.tits.Valid := by simp
  refine ⟨hv, ?_⟩
  obtain ⟨e₁⟩ := titsModelEquiv X 2 1 (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2
  have hT : CFSG.Blueprint.ReeTitsModel (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 2 1 :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e₂⟩ := titsModelEquiv _ 2 1 hT
  exact ⟨e₁.trans e₂.symm⟩

theorem center_eq_bot {K : Type} [Group K] (hK : IsoLie K .tits) : Subgroup.center K = ⊥ := by
  obtain ⟨hv, ⟨e⟩⟩ := hK
  obtain ⟨eS⟩ := titsModelEquiv K 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  exact center_eq_bot_of_mulEquiv eS titsD_center

theorem card_eq {K : Type} [Group K] (hK : IsoLie K .tits) : Nat.card K = 17971200 := by
  obtain ⟨hv, ⟨e⟩⟩ := hK
  obtain ⟨eS⟩ := titsModelEquiv K 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  rw [Nat.card_congr eS.toEquiv, card_titsD]

theorem factorization_five {K : Type} [Group K] (hK : IsoLie K .tits) : (Nat.card K).factorization 5 = 2 := by
  rw [card_eq hK, show (17971200 : ℕ) = 5 ^ 2 * 718848 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_sylow_eq {K : Type} [Group K] [Finite K] (hK : IsoLie K .tits) (E : Subgroup K)
    (hE : Nat.card E = 5 ^ 2) : ∃ P : Sylow 5 K, (P : Subgroup K) = E := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨Sylow.ofCard E (by rw [hE, factorization_five hK]), rfl⟩

end Iso

section Local


theorem sylowAutSelfCent {K : Type} [Group K] [Finite K] (hK : IsoLie K .tits) : SylowAutSelfCent K 5 := by
  have hcen : Subgroup.center K = ⊥ := center_eq_bot hK
  obtain ⟨hv, ⟨e⟩⟩ := hK
  have hd : (⟨.tits, hv⟩ : TauCeti.ValidLieTypeIndex).1 = .tits := rfl
  intro R
  have h := d2TorusLocalAt_tits _ hd (MulAut K) (MulAut.conj : K →* MulAut K).range
    normal_range_conj (centralizer_range_conj_eq_bot hcen)
    ⟨(mulEquivRangeConj hcen).symm.trans e⟩ 5 rfl R
  exact ⟨h.2.1, h.2.2.2.1⟩

theorem absKC {K : Type} [Group K] [Finite K] (hK : LieModel K .Tits 0 2 1) {r : ℕ} (hr : r = 5)
    (E : Subgroup K) (hE : Nat.card E = 5 ^ 2) : AbsKC K r E := by
  subst hr
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK' := isoLie_of_lieModel hK
  exact AbsKC.of_sylowAutSelfCent (sylowAutSelfCent hK') (center_eq_bot hK') hE

theorem absKInv {K : Type} [Group K] [Finite K] (hK : LieModel K .Tits 0 2 1) (E : Subgroup K)
    (hE : Nat.card E = 5 ^ 2) : AbsKInv K E := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK' := isoLie_of_lieModel hK
  exact AbsKInv.of_sylowAutSelfCent (by norm_num) (sylowAutSelfCent hK') (center_eq_bot hK') hE

end Local

section Sig


theorem absKN {K : Type} [Group K] [Finite K] (hK : LieModel K .Tits 0 2 1) {r : ℕ} (hr : r = 5)
    (isL34 : Prop) (E : Subgroup K) (hE : Nat.card E = 5 ^ 2) : AbsKN K r E isL34 := by
  subst hr
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK' := isoLie_of_lieModel hK
  obtain ⟨P, rfl⟩ := exists_sylow_eq hK' E hE
  exact AbsKN.of_signalizerTrivialOn (signalizerTrivialTits_holds K hK') P isL34

end Sig

end CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Sporadic.Schreier.Tits
open CFSG.Blueprint (LieModel)

section KTits


theorem kTits_holds : KTits := fun _ _ h => CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut.simple_of_lieModel h

end KTits

section KMult


theorem kMult_Tits (J : Type) [Group J] [Finite J] (hq : CFSG.Open.IsQuasisimple J)
    (N : Subgroup J) [N.Normal] (hN : N ≤ center J) (hT : LieModel (J ⧸ N) .Tits 0 2 1)
    (hodd : Odd (Nat.card (center J))) : center J = ⊥ := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut.lieModel_equiv hT
  obtain ⟨hs, a, b, hab⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut.simple_of_lieModel hT
  have hnorm : ((center J).map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hCN : center J = N := by
    haveI := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((center J).map (QuotientGroup.mk' N)) with h | h
    · refine le_antisymm (fun x hx => ?_) hN
      have : QuotientGroup.mk' N x ∈ (center J).map (QuotientGroup.mk' N) := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · exfalso
      have ha : a ∈ (center J).map (QuotientGroup.mk' N) := by rw [h]; exact Subgroup.mem_top a
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
      exact hab (by rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y])
  have e' : J ⧸ center J ≃* titsD := (QuotientGroup.quotientMulEquivOfEq hCN).trans e
  have hdvd := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess (S := titsD) ⟨hq.1⟩ e'
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier titsD) = 1 := by
    obtain ⟨hM'⟩ := (CFSG.LieType.Multipliers.Tits.multiplier_of_mulEquiv_titsD (MulEquiv.refl titsD)).2
    rw [Nat.card_congr hM'.toEquiv]
    simp
  rw [hM, Nat.dvd_one] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ hdvd

end KMult

end CFSG.LocalAnalysis.UniquenessCase.UCK
