module

public import CFSG.Blueprint.Catalog
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.Adapters.ExceptionalCatalogReverse
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.StandardType.ChevTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.Assembly.LowTwoRank

theorem not_namesTag_of_mem_classicalTags {d : LieTypeIndex} {t : StatedLieTag} {p f : ℕ}
    (ht : t ∈ classicalTags) : ¬ CFSG.Models.NamesTag d t p f := by
  cases t <;> simp [classicalTags] at ht <;> cases d <;> simp [CFSG.Models.NamesTag]

theorem blueprintLieModel_of_modelsLieModel {S : Type} [Group S] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : CFSG.Models.LieModel S t n p f) :
    CFSG.Blueprint.LieModel S t n p f := by
  obtain ⟨-, h | ⟨-, d, hd, -⟩⟩ := h
  · exact .inl ⟨ht, h⟩
  · exact absurd hd (not_namesTag_of_mem_classicalTags ht)

theorem card_galoisField_two {f : ℕ} (hf : f ≠ 0) :
    Nat.card (GaloisField 2 f) = 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact GaloisField.card 2 f hf

section Exceptional


theorem untwistedChevalleyModel_of_bridge {S : Type} [Group S] {τ : Tag}
    {c : PrimePower → LieTypeIndex} (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (q : PrimePower) (hv : (c q).Valid) (hp : q.p = 2)
    (e : S ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    UntwistedChevalleyModel S τ (2 ^ q.exponent) := by
  have hK : Nat.card (GaloisField 2 q.exponent) = 2 ^ q.exponent :=
    card_galoisField_two q.exponent_pos.ne'
  obtain ⟨b⟩ := hB q hv (GaloisField 2 q.exponent) (by rw [hK, PrimePower.card_def, hp])
  exact ⟨GaloisField 2 q.exponent, inferInstance, inferInstance, hK, ⟨e.trans b.symm⟩⟩

theorem twistedChevalleyModel_of_bridge {S : Type} [Group S] {t : TwistTag}
    {c : PrimePower → LieTypeIndex} (hB : CFSG.TauCetiBridge.Even.TwistedBridgeAll t c)
    (q : PrimePower) (hv : (c q).Valid) (hp : q.p = 2)
    (e : S ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    TwistedChevalleyModel S t (2 ^ q.exponent) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hto : 0 < t.order := by cases t <;> decide
  let K := GaloisField 2 (q.exponent * t.order)
  have hK : Nat.card K = (2 ^ q.exponent) ^ t.order := by
    rw [card_galoisField_two (Nat.mul_ne_zero q.exponent_pos.ne' hto.ne'), pow_mul]
  let σ : K →+* K := iterateFrobenius K 2 q.exponent
  have hσ : ∀ x : K, σ x = x ^ (2 ^ q.exponent) := fun _ => rfl
  obtain ⟨b⟩ := hB q hv K (by rw [hK, PrimePower.card_def, hp]) σ
    (fun x => by rw [hσ, PrimePower.card_def, hp])
  exact ⟨K, inferInstance, inferInstance, hK, σ, hσ, ⟨e.trans b.symm⟩⟩

theorem suzukiModel_of_valid {S : Type} [Group S] (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩) : SuzukiModel S 2 (2 * m + 1) := by
  have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    card_galoisField_two (by omega)
  exact ⟨rfl, m, hm, GaloisField 2 (2 * m + 1), inferInstance, inferInstance, rfl, hK,
    ⟨e.trans ((CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).trans
      (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).symm)⟩⟩

theorem reeTitsModel_of_reeF4 {S : Type} [Group S] (a : ℕ) (hv : (LieTypeIndex.reeF4 a).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.reeF4 a, hv⟩) : ReeTitsModel S .twistedF4 2 (2 * a + 1) := by
  have ha : 1 ≤ a := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := card_galoisField_two (by omega)
  have : CharP K 2 := CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow hK
  have hhalf : (ReeF4LieIndex.of a hv).toSuzukiReeIndex.halfExponent = a :=
    SuzukiReeIndex.halfExponent_reeF4 a hv
  have hcard : Nat.card K =
      2 ^ (2 * (ReeF4LieIndex.of a hv).toSuzukiReeIndex.halfExponent + 1) := by
    rw [hhalf, hK]
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.reeF4_candidate_equiv_of_card (ReeF4LieIndex.of a hv) hcard
  rw [hhalf] at e₁
  have e₂ : S ≃* CFSG.Blueprint.DerivedCentralQuotient
      (reeFixedGroup .F4 K reeF4Perm fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) :=
    (e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv a).symm
  exact ⟨⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one a, by omega⟩, a, rfl,
    K, inferInstance, inferInstance, hK, ⟨e₂⟩⟩

theorem reeTitsModel_of_tits {S : Type} [Group S] (hv : LieTypeIndex.tits.Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩) : ReeTitsModel S .Tits 2 1 := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.tits_candidate_equiv_of_card TitsLieIndex.of hK
  have e₂ : S ≃* CFSG.Blueprint.DerivedCentralQuotient
      (reeFixedGroup .F4 (ZMod 2) reeF4Perm fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1)) :=
    (e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm
  exact ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, ZMod 2, inferInstance, inferInstance,
    by simp, ⟨e₂⟩⟩

theorem exists_lieModel_two_of_valid {S : Type} [Group S] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (e : S ≃* d.Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel S t n 2 f := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  obtain ⟨d, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_A r q hv e
    rw [hp] at h
    exact ⟨_, _, _, blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h⟩
  | twistedA r q =>
    have h := CFSG.Models.lieModel_twistedA r q hv e
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := hd
    rw [hc] at h
    exact ⟨_, _, _, blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h⟩
  | B r q =>
    have hp : q.p = 2 := by simpa using hd
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · rw [hp] at h
      exact ⟨_, _, _, blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h⟩
    · rw [hp] at h
      exact absurd h.1.2.2.2 (by simp)
  | C r q =>
    have hp : q.p = 2 := by simpa using hd
    exact absurd hp hr.2
  | D r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_D r q hv e
    rw [hp] at h
    exact ⟨_, _, _, blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h⟩
  | twistedD r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_twistedD r q hv e
    rw [hp] at h
    exact ⟨_, _, _, blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h⟩
  | E6 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E6, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.e6 q hv hp e⟩)⟩
  | E7 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E7, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.e7 q hv hp e⟩)⟩
  | E8 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E8, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.e8 q hv hp e⟩)⟩
  | F4 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.F4, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.f4 q hv hp e⟩)⟩
  | G2 q =>
    have hp : q.p = 2 := by simpa using hd
    have h3 : 3 ≤ 2 ^ q.exponent := by
      have h3 : 3 ≤ q.card := hr
      rwa [PrimePower.card_def, hp] at h3
    exact ⟨.G2, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩, untwistedChevalleyModel_of_bridge hB.g2 q hv hp e⟩)⟩
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.twistedE6, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      twistedChevalleyModel_of_bridge hB.twistedE6 q hv hp e⟩)⟩
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.trialityD4, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      twistedChevalleyModel_of_bridge hB.trialityD4 q hv hp e⟩)⟩
  | suzuki m =>
    exact ⟨.twistedB2, 0, 2 * m + 1, .inr (.inr (.inr ⟨rfl, rfl, suzukiModel_of_valid m hv e⟩))⟩
  | reeG2 m =>
    exact absurd hd (by simp)
  | reeF4 a =>
    exact ⟨.twistedF4, 0, 2 * a + 1, .inr (.inr (.inl ⟨rfl, by simp [reeTitsTags],
      reeTitsModel_of_reeF4 a hv e⟩))⟩
  | tits =>
    exact ⟨.Tits, 0, 1, .inr (.inr (.inl ⟨rfl, by simp [reeTitsTags], reeTitsModel_of_tits hv e⟩))⟩

end Exceptional

end CFSG.StandardType.ChevTwo
