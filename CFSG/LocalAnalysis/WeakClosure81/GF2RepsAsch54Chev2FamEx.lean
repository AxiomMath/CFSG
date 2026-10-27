module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2OrbitDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotient
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotientMin
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeE6E7
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeE8
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeF4
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeTwistedE6
public import CFSG.Monster.B.Fischer.Fi22Order
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeG2

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Open

variable {X : Type} [Group X] {n f : ℕ}

theorem exists_borelQuotientModel_g2
    (hm : CFSG.Models.LieModel X .G2 n 2 f) :
    ∃ (π : ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) →* X) (e : ℕ),
      CFSG.AGLEmbedding.ParabHub.BorelQuotient
        (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField 2 f))
        (CFSG.LieType.Chevalley.weylElement .G2 (GaloisField 2 f))
        (CFSG.LieType.Steinberg.Adjoint.torus (τ := .G2) (GaloisField 2 f)) π e := by
  obtain ⟨hadm, hclass | ⟨-, d, hN, ⟨φ⟩⟩⟩ := hm
  · exact hclass.2.elim
  obtain ⟨i, hv⟩ := d
  cases i with
  | G2 q =>
      simp only [CFSG.Models.NamesTag] at hN
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let K := GaloisField 2 f
      have hf1 : 1 ≤ f := hadm.2.1
      have hf0 : f ≠ 0 := by omega
      have hKcard : Nat.card K = 2 ^ f := by
        dsimp [K]
        exact GaloisField.card 2 f hf0
      have hqcard : q.card = 2 ^ f := by
        rw [TauCeti.PrimePower.card_def, hN.1, hN.2]
      have hK : Nat.card K = q.card := hKcard.trans hqcard.symm
      have : CharP K 2 := by
        dsimp [K]
        exact inferInstance
      obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hN.1 K hK
      have hφ := φ.trans b.symm
      exact ⟨_, _, CFSG.AGLEmbedding.ParabHub.borelQuotient_g2 hφ⟩
  | _ => simp only [CFSG.Models.NamesTag] at hN

theorem hasBQRank_g2
    (hm : CFSG.Models.LieModel X .G2 n 2 f) : HasBQRank X 2 := by
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_g2 hm
  have : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) :=
    CFSG.LieType.Chevalley.generated_group_finite .G2 _
  exact ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)), inferInstance,
    inferInstance, CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField 2 f),
    CFSG.LieType.Chevalley.weylElement .G2 (GaloisField 2 f),
    CFSG.LieType.Steinberg.Adjoint.torus (τ := .G2) (GaloisField 2 f), π, e, hbq, rfl⟩

theorem exists_borelQuotientModel_f4
    (hm : CFSG.Models.LieModel X .F4 n 2 f) :
    ∃ (π : ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 f)) →* X) (e : ℕ),
      CFSG.AGLEmbedding.ParabHub.BorelQuotient
        (CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField 2 f))
        (CFSG.LieType.Chevalley.weylElement .F4 (GaloisField 2 f))
        (CFSG.LieType.Steinberg.Adjoint.torus (τ := .F4) (GaloisField 2 f)) π e := by
  obtain ⟨hadm, hclass | ⟨-, d, hN, ⟨φ⟩⟩⟩ := hm
  · exact hclass.2.elim
  obtain ⟨i, hv⟩ := d
  cases i with
  | F4 q =>
      simp only [CFSG.Models.NamesTag] at hN
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let K := GaloisField 2 f
      have hf1 : 1 ≤ f := hadm.2.1
      have hf0 : f ≠ 0 := by omega
      have hKcard : Nat.card K = 2 ^ f := by
        dsimp [K]
        exact GaloisField.card 2 f hf0
      have hqcard : q.card = 2 ^ f := by
        rw [TauCeti.PrimePower.card_def, hN.1, hN.2]
      have hK : Nat.card K = q.card := hKcard.trans hqcard.symm
      have : CharP K 2 := by
        dsimp [K]
        exact inferInstance
      obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hN.1 K hK
      have hφ := φ.trans b.symm
      exact ⟨_, _, CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_f4 hφ⟩
  | _ => simp only [CFSG.Models.NamesTag] at hN

theorem hasBQRank_f4
    (hm : CFSG.Models.LieModel X .F4 n 2 f) : HasBQRank X 4 := by
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_f4 hm
  have : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 f)) :=
    CFSG.LieType.Chevalley.generated_group_finite .F4 _
  exact ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 f)), inferInstance,
    inferInstance, CFSG.LieType.Steinberg.Adjoint.f4Datum (GaloisField 2 f),
    CFSG.LieType.Chevalley.weylElement .F4 (GaloisField 2 f),
    CFSG.LieType.Steinberg.Adjoint.torus (τ := .F4) (GaloisField 2 f), π, e, hbq, rfl⟩

theorem exists_borelQuotientModel_e6
    (hm : CFSG.Models.LieModel X .E6 n 2 f) :
    ∃ (π : ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
        (GaloisField 2 f)) →* X) (e : ℕ),
      CFSG.AGLEmbedding.ParabHub.BorelQuotient
        (CFSG.LieType.Steinberg.Minuscule.e6Datum (GaloisField 2 f))
        (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.nm (GaloisField 2 f))
        (CFSG.LieType.Steinberg.Minuscule.e6Data_valid.torus (GaloisField 2 f)) π e := by
  obtain ⟨hadm, hclass | ⟨-, d, hN, ⟨φ⟩⟩⟩ := hm
  · exact hclass.2.elim
  obtain ⟨i, hv⟩ := d
  cases i with
  | E6 q =>
      simp only [CFSG.Models.NamesTag] at hN
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let K := GaloisField 2 f
      have hf1 : 1 ≤ f := hadm.2.1
      have hf0 : f ≠ 0 := by omega
      have hKcard : Nat.card K = 2 ^ f := by
        dsimp [K]
        exact GaloisField.card 2 f hf0
      have hqcard : q.card = 2 ^ f := by
        rw [TauCeti.PrimePower.card_def, hN.1, hN.2]
      have hK : Nat.card K = q.card := hKcard.trans hqcard.symm
      have : CharP K 2 := by
        dsimp [K]
        exact inferInstance
      obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hN.1 K hK
      have hφ := φ.trans b.symm
      exact ⟨_, _, CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_e6 hφ⟩
  | _ => simp only [CFSG.Models.NamesTag] at hN

theorem hasBQRank_e6
    (hm : CFSG.Models.LieModel X .E6 n 2 f) : HasBQRank X 6 := by
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_e6 hm
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 2 f)) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup
      CFSG.LieType.Steinberg.Minuscule.e6Data_valid _
  exact ⟨↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 2 f)),
    inferInstance, inferInstance, CFSG.LieType.Steinberg.Minuscule.e6Datum (GaloisField 2 f),
    CFSG.LieType.Steinberg.Minuscule.e6Data_valid.nm (GaloisField 2 f),
    CFSG.LieType.Steinberg.Minuscule.e6Data_valid.torus (GaloisField 2 f), π, e, hbq, rfl⟩

theorem exists_borelQuotientModel_e7
    (hm : CFSG.Models.LieModel X .E7 n 2 f) :
    ∃ (π : ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup
        (GaloisField 2 f)) →* X) (e : ℕ),
      CFSG.AGLEmbedding.ParabHub.BorelQuotient
        (CFSG.LieType.Steinberg.Minuscule.e7Datum (GaloisField 2 f))
        (CFSG.LieType.Steinberg.Minuscule.e7Data_valid.nm (GaloisField 2 f))
        (CFSG.LieType.Steinberg.Minuscule.e7Data_valid.torus (GaloisField 2 f)) π e := by
  obtain ⟨hadm, hclass | ⟨-, d, hN, ⟨φ⟩⟩⟩ := hm
  · exact hclass.2.elim
  obtain ⟨i, hv⟩ := d
  cases i with
  | E7 q =>
      simp only [CFSG.Models.NamesTag] at hN
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let K := GaloisField 2 f
      have hf1 : 1 ≤ f := hadm.2.1
      have hf0 : f ≠ 0 := by omega
      have hKcard : Nat.card K = 2 ^ f := by
        dsimp [K]
        exact GaloisField.card 2 f hf0
      have hqcard : q.card = 2 ^ f := by
        rw [TauCeti.PrimePower.card_def, hN.1, hN.2]
      have hK : Nat.card K = q.card := hKcard.trans hqcard.symm
      have : CharP K 2 := by
        dsimp [K]
        exact inferInstance
      obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 q hv hN.1 K hK
      have hφ := φ.trans b.symm
      exact ⟨_, _, CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_e7 hφ⟩
  | _ => simp only [CFSG.Models.NamesTag] at hN

theorem hasBQRank_e7
    (hm : CFSG.Models.LieModel X .E7 n 2 f) :
    HasBQRank X 7 := by
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_e7 hm
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup
      (GaloisField 2 f)) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup
      CFSG.LieType.Steinberg.Minuscule.e7Data_valid _
  exact ⟨↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 f)),
    inferInstance, inferInstance, CFSG.LieType.Steinberg.Minuscule.e7Datum (GaloisField 2 f),
    CFSG.LieType.Steinberg.Minuscule.e7Data_valid.nm (GaloisField 2 f),
    CFSG.LieType.Steinberg.Minuscule.e7Data_valid.torus (GaloisField 2 f), π, e, hbq, rfl⟩

theorem exists_borelQuotientModel_e8
    (hm : CFSG.Models.LieModel X .E8 n 2 f) :
    ∃ (π : ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 f)) →* X) (e : ℕ),
      CFSG.AGLEmbedding.ParabHub.BorelQuotient
        (CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 2 f))
        (CFSG.LieType.Chevalley.weylElement .E8 (GaloisField 2 f))
        (CFSG.LieType.Steinberg.Adjoint.torus (τ := .E8) (GaloisField 2 f)) π e := by
  obtain ⟨hadm, hclass | ⟨-, d, hN, ⟨φ⟩⟩⟩ := hm
  · exact hclass.2.elim
  obtain ⟨i, hv⟩ := d
  cases i with
  | E8 q =>
      simp only [CFSG.Models.NamesTag] at hN
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let K := GaloisField 2 f
      have hf1 : 1 ≤ f := hadm.2.1
      have hf0 : f ≠ 0 := by omega
      have hKcard : Nat.card K = 2 ^ f := by
        dsimp [K]
        exact GaloisField.card 2 f hf0
      have hqcard : q.card = 2 ^ f := by
        rw [TauCeti.PrimePower.card_def, hN.1, hN.2]
      have hK : Nat.card K = q.card := hKcard.trans hqcard.symm
      have : CharP K 2 := by
        dsimp [K]
        exact inferInstance
      obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 q hv hN.1 K hK
      have hφ := φ.trans b.symm
      exact ⟨_, _, CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_e8 hφ⟩
  | _ => simp only [CFSG.Models.NamesTag] at hN

theorem hasBQRank_e8
    (hm : CFSG.Models.LieModel X .E8 n 2 f) : HasBQRank X 8 := by
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_e8 hm
  have : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 f)) :=
    CFSG.LieType.Chevalley.generated_group_finite .E8 _
  exact ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 f)), inferInstance,
    inferInstance, CFSG.LieType.Steinberg.Adjoint.e8Datum (GaloisField 2 f),
    CFSG.LieType.Chevalley.weylElement .E8 (GaloisField 2 f),
    CFSG.LieType.Steinberg.Adjoint.torus (τ := .E8) (GaloisField 2 f), π, e, hbq, rfl⟩

theorem exists_borelQuotientModel_twistedE6
    (hm : CFSG.Models.LieModel X .twistedE6 n 2 f) :
    ∃ (π : ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup (GaloisField 2 (2 * f))
        (iterateFrobenius (GaloisField 2 (2 * f)) 2 f)) →* X) (e : ℕ),
      CFSG.AGLEmbedding.ParabHub.BorelQuotient
        (CFSG.LieType.Steinberg.TwistedE6.twistedDatum (GaloisField 2 (2 * f))
          (iterateFrobenius (GaloisField 2 (2 * f)) 2 f))
        (CFSG.LieType.Steinberg.TwistedE6.nHat
          (iterateFrobenius (GaloisField 2 (2 * f)) 2 f))
        (CFSG.LieType.Steinberg.TwistedE6.hHat (GaloisField 2 (2 * f))
          (iterateFrobenius (GaloisField 2 (2 * f)) 2 f)) π e := by
  obtain ⟨hadm, hclass | ⟨-, d, hN, ⟨φ⟩⟩⟩ := hm
  · exact hclass.2.elim
  obtain ⟨i, hv⟩ := d
  cases i with
  | twistedE6 q =>
      simp only [CFSG.Models.NamesTag] at hN
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let K := GaloisField 2 (2 * f)
      have hf1 : 1 ≤ f := hadm.2.1
      have hf0 : 2 * f ≠ 0 := by omega
      have hKcard : Nat.card K = 2 ^ (2 * f) := by
        dsimp [K]
        exact GaloisField.card 2 (2 * f) hf0
      have hqcard : q.card = 2 ^ f := by
        rw [TauCeti.PrimePower.card_def, hN.1, hN.2]
      have hK : Nat.card K = q.card ^ 2 := by
        rw [hKcard, hqcard, ← pow_mul]
        congr 1
        omega
      have hK4 : 4 ≤ Nat.card K := by
        rw [hKcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : CharP K 2 := by
        dsimp [K]
        exact inferInstance
      let σ : K →+* K := iterateFrobenius K 2 f
      have hσ : ∀ c, σ c = c ^ q.card := by
        intro c
        dsimp [σ]
        rw [hqcard]
        exact iterateFrobenius_def 2 f c
      have hθ : ∀ c, σ (σ c) = c := by
        intro c
        have hc : σ (σ c) = (σ c) ^ q.card := hσ (σ c)
        rw [hc, hσ c, ← pow_mul, ← sq, ← hK]
        have : Fintype K := Fintype.ofFinite K
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card c
      obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6 q hv hN.1 K hK σ hσ
      have hφ := φ.trans b.symm
      exact ⟨_, _, CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.borelQuotient_e6tw
        hθ hK4 hK hσ hφ⟩
  | _ => simp only [CFSG.Models.NamesTag] at hN

theorem hasBQRank_twistedE6
    (hm : CFSG.Models.LieModel X .twistedE6 n 2 f) : HasBQRank X 4 := by
  obtain ⟨π, e, hbq⟩ := exists_borelQuotientModel_twistedE6 hm
  let K := GaloisField 2 (2 * f)
  let σ : K →+* K := iterateFrobenius K 2 f
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup K) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup
      CFSG.LieType.Steinberg.Minuscule.e6Data_valid K
  have : Finite ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup K σ) := Subtype.finite
  exact ⟨↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup K σ), inferInstance, inferInstance,
    CFSG.LieType.Steinberg.TwistedE6.twistedDatum K σ,
    CFSG.LieType.Steinberg.TwistedE6.nHat σ,
    CFSG.LieType.Steinberg.TwistedE6.hHat K σ, π, e, hbq, rfl⟩

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
