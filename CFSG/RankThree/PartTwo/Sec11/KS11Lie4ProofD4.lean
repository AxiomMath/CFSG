module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Chevalley.GraphFixedSchreier
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.RankThree.SteinbergR3EEvenQuadraticSL2Fixed
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate43
public import Certificates.Certificate7233Base

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace KS11Lie4Proof

abbrev d4Outer : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩

@[expose] noncomputable def d4ShortSL2
    (K : Type) [Field K] (σ : K →+* K) :
    Subgroup (graphFixedRootGroup TwistTag.D4 K σ) :=
  (orbitRankOneHom TwistTag.D4 K σ d4Outer).range.comap
    (graphFixedRootGroup TwistTag.D4 K σ).subtype

section Statements


@[expose] def D4ThreeConj : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q : ℕ) (σ : K ≃+* K), Nat.card K = q ^ 3 →
    (∀ c, σ c = c ^ q) → ¬ 3 ∣ q →
    ∀ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, z ^ 3 = 1 → z ≠ 1 →
      ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        g * z * g⁻¹ ∈ d4ShortSL2 K σ.toRingHom ∨
          g * z * g⁻¹ ∈ Subgroup.centralizer ((d4ShortSL2 K σ.toRingHom :
            Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
              Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))

@[expose] def D4ThreeACent : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q : ℕ) (σ : K ≃+* K), Nat.card K = q ^ 3 →
    (∀ c, σ c = c ^ q) → ¬ 3 ∣ q →
    ∀ z ∈ d4ShortSL2 K σ.toRingHom, z ^ 3 = 1 → z ≠ 1 →
      Group.IsSolvable (Subgroup.centralizer ({z} :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ∨
      ∃ N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        N ≤ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
        (∀ x ∈ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          ∀ y ∈ Subgroup.centralizer ({z} :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), x * y * x⁻¹ * y⁻¹ ∈ N) ∧
        CFSG.IsQuasisimple N ∧
        ∃ x ∈ N, (∀ n ∈ N, x * n = n * x) ∧ x ≠ 1 ∧ x ^ 3 = 1

@[expose] def D4ThreeBCent : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q : ℕ) (σ : K ≃+* K), Nat.card K = q ^ 3 →
    (∀ c, σ c = c ^ q) → ¬ 3 ∣ q →
    ∀ z ∈ Subgroup.centralizer ((d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), z ^ 3 = 1 → z ≠ 1 →
      (∀ x ∈ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        ∀ y ∈ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          x * y * x⁻¹ * y⁻¹ ∈ d4ShortSL2 K σ.toRingHom) ∧
      ∀ b ∈ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        b ∈ Subgroup.centralizer ((d4ShortSL2 K σ.toRingHom :
          Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) → b ^ (q ^ 2 - 1) = 1

@[expose] def D4NormCent : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q : ℕ) (σ : K ≃+* K), Nat.card K = q ^ 3 →
    (∀ c, σ c = c ^ q) → ¬ 3 ∣ q →
    ∀ y ∈ d4ShortSL2 K σ.toRingHom, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ 1 →
      ∀ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, g * y * g⁻¹ ∈ Subgroup.zpowers y →
        g ∈ Subgroup.normalizer ((Subgroup.centralizer ((d4ShortSL2 K σ.toRingHom :
          Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
              Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
                Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))

@[expose] def D4ShortOut : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (q : ℕ) (σ : K ≃+* K), Nat.card K = q ^ 3 →
    (∀ c, σ c = c ^ q) → ¬ 3 ∣ q →
    ∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), (∃ k : ℕ, β ^ 3 ^ k = 1) →
      (∀ x ∈ d4ShortSL2 K σ.toRingHom, β x = x) →
        β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range

end Statements

section Model


theorem exists_d4_model {Z : Type} [Group Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ) (σ : K ≃+* K), Nat.card K = q ^ 3 ∧
      (∀ c, σ c = c ^ q) ∧ ¬ 3 ∣ q ∧ σ ^ 3 = 1 ∧
      IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      Nonempty (Z ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨X, _, ⟨q, hq, hp3, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p (3 * q.exponent)
  have hKp : CharP K q.p := inferInstanceAs (CharP (GaloisField q.p (3 * q.exponent)) q.p)
  have hK3 : Nat.card K = q.card ^ 3 := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
      ← pow_mul, mul_comm]
  set σ' : K ≃+* K := iterateFrobeniusEquiv K q.p q.exponent with hσ'def
  have hσ'y : ∀ y : K, σ' y = y ^ q.card := fun y => by
    rw [hσ'def, iterateFrobeniusEquiv_def, TauCeti.PrimePower.card_def]
  have hσ'3 : ∀ y : K, σ' (σ' (σ' y)) = y := by
    intro y
    have : Fintype K := Fintype.ofFinite K
    rw [hσ'y, hσ'y, hσ'y, ← pow_mul, ← pow_mul]
    have h1 : q.card * (q.card * q.card) = Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK3]
      ring
    rw [h1, FiniteField.pow_card]
  have hσRE : σ' ^ 3 = 1 := by
    apply RingEquiv.ext
    intro y
    exact hσ'3 y
  have hK3' : Nat.card K = q.card ^ TwistTag.D4.order := hK3
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hq K hK3'
    σ'.toRingHom hσ'y
  set L := AlgebraicClosure K
  have : CharP L q.p := @charP_of_injective_ringHom K L _ _ (algebraMap K L)
    (algebraMap K L).injective q.p hKp
  obtain ⟨-, -, hTG, hsimple, hnonab⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group q.p q.exponent q.prime_p
      q.exponent_pos K (by rw [hK3, TauCeti.PrimePower.card_def]) L 1 (Or.inl rfl) σ'.toRingHom
      (fun c => by rw [pow_one, ← TauCeti.PrimePower.card_def]; exact hσ'y c)
      (iterateFrobenius L q.p q.exponent) (fun c => iterateFrobenius_def q.p q.exponent c)
  set e3 := MulEquiv.subgroupCongr hTG
  have : IsSimpleGroup (CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K σ'.toRingHom) :=
    MulEquiv.isSimpleGroup e3
  obtain ⟨e2⟩ := KS11Lie3Proof.nonempty_derivedCentralQuotient_mulEquiv
    (CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K σ'.toRingHom) (by
      obtain ⟨x, y, hxy⟩ := hnonab
      refine ⟨e3.symm x, e3.symm y, fun h => hxy ?_⟩
      have := congrArg e3 h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)
  have hXp : Group.IsPerfect X := by
    have := SetUp1118Proof.isPerfect_lie_trialityD4 q hq
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  have h3q : ¬ 3 ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  exact ⟨K, inferInstance, inferInstance, q.card, σ', hK3, hσ'y, h3q, hσRE, hsimple,
    ⟨(e.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv)).trans
      (f.trans (b.symm.trans (e2.trans e3)))⟩⟩

variable {K : Type} [Field K]

theorem mem_orbitField_d4Outer {σ : K ≃+* K} (hσ : σ ^ 3 = 1) (c : K) :
    c ∈ orbitField TwistTag.D4 K σ.toRingHom d4Outer := by
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
    rw [← ringEquiv_pow_three_apply, hσ]
    rfl
  rw [orbitField_D4_zero_eq_top σ h3]
  exact Subfield.mem_top c

theorem nonempty_mulEquiv_d4ShortSL2 {σ : K ≃+* K} (hσ : σ ^ 3 = 1) :
    Nonempty (SL2 (orbitField TwistTag.D4 K σ.toRingHom d4Outer) ≃*
      d4ShortSL2 K σ.toRingHom) := by
  have hinj := orbitRankOneHom_injective_D4 hσ d4Outer
  have hle := range_orbitRankOneHom_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) d4Outer
  exact ⟨(MonoidHom.ofInjective hinj).trans (Subgroup.subgroupOfEquivOfLe hle).symm⟩

theorem natCard_orbitField_d4Outer {σ : K ≃+* K} (hσ : σ ^ 3 = 1) :
    Nat.card (orbitField TwistTag.D4 K σ.toRingHom d4Outer) = Nat.card K :=
  Nat.card_congr (Equiv.subtypeUnivEquiv (mem_orbitField_d4Outer hσ))

theorem isQuasisimple_d4ShortSL2 [Finite K] {σ : K ≃+* K} (hσ : σ ^ 3 = 1)
    (hK4 : 4 ≤ Nat.card K) : CFSG.IsQuasisimple (d4ShortSL2 K σ.toRingHom) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_d4ShortSL2 hσ
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom d4Outer) := Subtype.finite
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (isQuasisimple_sl2 (by rw [natCard_orbitField_d4Outer hσ]; exact hK4))

theorem card_d4ShortSL2 [Finite K] {σ : K ≃+* K} (hσ : σ ^ 3 = 1) :
    Nat.card (d4ShortSL2 K σ.toRingHom) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_d4ShortSL2 hσ
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom d4Outer) := Subtype.finite
  rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    natCard_orbitField_d4Outer hσ]

@[expose] def sl2Three (F : Type) [Field F] : SL2 F :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

theorem sl2Three_pow_three (F : Type) [Field F] : sl2Three F ^ 3 = 1 ∧ sl2Three F ≠ 1 := by
  refine ⟨Subtype.ext ?_, fun h => ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Three, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  · have h1 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [sl2Three] at h1

theorem eq_one_of_central_of_pow_three {F : Type} [Field F] {B : SL2 F} (hB3 : B ^ 3 = 1)
    (hB : ∀ A : SL2 F, A * B = B * A) : B = 1 := by
  have hu' : (B : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] * (B : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F)) (hB (uSL 1))
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    have e : ((uSL 1 : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
    rw [e] at h
    exact h.symm
  have hl' : (B : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] =
      !![1, 0; 1, 1] * (B : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F)) (hB (vSL 1))
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    have e : ((vSL 1 : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl
    rw [e] at h
    exact h.symm
  have hsc := CFSG.RankThree.QuadraticSL2.eq_scalar_of_commute _ hu' hl'
  set c := (B : Matrix (Fin 2) (Fin 2) F) 0 0 with hc
  have hdet : c ^ 2 = 1 := by
    have h := B.2
    rw [Matrix.det_fin_two, hsc] at h
    simpa [Matrix.scalar_apply, Matrix.diagonal, sq] using h
  have h3 : c ^ 3 = 1 := by
    have h := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hB3
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at h
    rw [hsc, ← map_pow] at h
    simpa [Matrix.scalar_apply] using h
  have hc1 : c = 1 := by
    have h := h3
    rw [show c ^ 3 = c * c ^ 2 by ring, hdet, mul_one] at h
    exact h
  apply Subtype.ext
  rw [hsc, hc1, Matrix.SpecialLinearGroup.coe_one, map_one]

variable [Finite K]

open scoped commutatorElement in
theorem not_hasType424_d4 {σ : K ≃+* K} (hσ : σ ^ 3 = 1)
    [IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)] :
    ¬ KS11Lie2Proof.HasType424 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : IsSimpleGroup (⊤ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    MulEquiv.isSimpleGroup Subgroup.topEquiv
  obtain ⟨ι, η, hι, hη, hc⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσ
  obtain ⟨hA3, hA1⟩ := sl2Three_pow_three K
  obtain ⟨hA3', hA1'⟩ := sl2Three_pow_three (CFSG.LieType.Chevalley.fixSubfield σ)
  set u := ι (sl2Three K)
  set v := η (sl2Three (CFSG.LieType.Chevalley.fixSubfield σ))
  have huv : u * v = v * u := hc _ _
  have hcomm : ⁅u, v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr huv
  refine KS11Lie2Proof.not_hasType424_of_simple ⊤ (fun _ _ => Subgroup.mem_top _)
    (Subgroup.mem_top u) (Subgroup.mem_top v) (fun h => hA1 (hι (h.trans (map_one ι).symm)))
    (by rw [← map_pow, hA3, map_one]) (by rw [← map_pow, hA3', map_one])
    (by rw [hcomm]; exact Commute.one_left _) (by rw [hcomm]; exact Commute.one_left _) ?_
  intro hvu
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hvu
  have hcen : ∀ A : SL2 K, A * sl2Three K ^ n = sl2Three K ^ n * A := by
    intro A
    apply hι
    rw [map_mul, map_mul, map_zpow]
    change ι A * u ^ n = u ^ n * ι A
    rw [hn]
    exact hc A _
  have h1 : sl2Three K ^ n = 1 := eq_one_of_central_of_pow_three (by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA3, one_zpow]) hcen
  apply hA1'
  apply hη
  show v = η 1
  rw [map_one, ← hn, ← map_zpow, h1, map_one]

end Model

section Data

theorem mem_centralizer_comap_iff {Z C : Type} [Group Z] [Group C] (e : Z ≃* C)
    (S : Subgroup C) (x : Z) :
    x ∈ Subgroup.centralizer ((S.comap e.toMonoidHom : Subgroup Z) : Set Z) ↔
      e x ∈ Subgroup.centralizer (S : Set C) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    obtain ⟨s', rfl⟩ := e.surjective s
    have h1 := h s' hs
    rw [← map_mul, ← map_mul, h1]
  · intro h s hs
    exact e.injective (by rw [map_mul, map_mul]; exact h (e s) hs)


variable {Z : Type} [Group Z] [Finite Z] {K : Type} [Field K] [Finite K]

theorem threeBAt_d4 (hA : D4ThreeACent) (hB : D4ThreeBCent) {q : ℕ} {σ : K ≃+* K}
    (hK : Nat.card K = q ^ 3) (hσ : ∀ c, σ c = c ^ q) (h3 : ¬ 3 ∣ q) (hσ3 : σ ^ 3 = 1)
    (e : Z ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) {z : Z} (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1)
    (hmem : e z ∈ d4ShortSL2 K σ.toRingHom ∨ e z ∈ Subgroup.centralizer
      ((d4ShortSL2 K σ.toRingHom : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    {J : Subgroup Z} (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) :
    e z ∈ Subgroup.centralizer
      ((d4ShortSL2 K σ.toRingHom : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
      ThreeBAt Z z ((d4ShortSL2 K σ.toRingHom).comap e.toMonoidHom) := by
  have hez3 : e z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hez1 : e z ≠ 1 := fun h => hz1 (e.injective (h.trans (map_one e).symm))
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q <;> simp at hK <;> have := Finite.one_lt_card (α := K) <;> omega
    · exact h
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
  rcases hmem with hzS | hzM
  ·
    exfalso
    have hJ' : J ∈ thetaComponentsIn (Subgroup.centralizer ({z} : Set Z)) := by
      rw [← fixSub_conj_eq_centralizer]
      exact hJ
    rcases hA K q σ hK hσ h3 (e z) hzS hez3 hez1 with hsol | ⟨N, hNC, hcomm, hNq, x, hxN, hxc,
      hx1, hx3⟩
    ·
      have hJC := le_of_mem_thetaComponentsIn hJ'
      let f : J →* Subgroup.centralizer ({e z} :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
        (e.toMonoidHom.comp J.subtype).codRestrict _ fun j => mem_centralizer_map.mpr (hJC j.2)
      have hf : Function.Injective f := fun a b h =>
        Subtype.ext (e.injective (congrArg Subtype.val h))
      have hJs : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective hf
      exact ne_bot_of_mem_thetaComponentsIn hJ'
        (eq_bot_of_isPerfect_of_isSolvable (isPerfect_of_mem_thetaComponentsIn hJ') hJs)
    · have e' : (N.comap e.toMonoidHom : Subgroup Z) ≃* N :=
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _))
      refine false_of_threeA (N := N.comap e.toMonoidHom) (fun y hy => ?_) (fun a ha b hb => ?_)
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm hNq) ⟨e.symm x, ?_, ?_, ?_, ?_⟩ hJ
        hJT
      · exact mem_centralizer_map.mp (hNC hy)
      · have := hcomm _ (mem_centralizer_map.mpr ha) _ (mem_centralizer_map.mpr hb)
        change e (a * b * a⁻¹ * b⁻¹) ∈ N
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        exact this
      · change e (e.symm x) ∈ N
        rwa [MulEquiv.apply_symm_apply]
      · intro n hn
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hxc _ hn
      · intro h
        apply hx1
        rw [← MulEquiv.apply_symm_apply e x, h, map_one]
      · apply e.injective
        rw [map_pow, MulEquiv.apply_symm_apply, hx3, map_one]
  ·
    refine ⟨hzM, ?_, fun s hs => ?_, fun x hx y hy => ?_⟩
    · have e' : ((d4ShortSL2 K σ.toRingHom).comap e.toMonoidHom : Subgroup Z) ≃*
          d4ShortSL2 K σ.toRingHom :=
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _))
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm
        (isQuasisimple_d4ShortSL2 hσ3 hK4)
    · rw [← mem_centralizer_map (e := e)]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hzM (e s) hs)
    · have hx' := (mem_centralizer_map (e := e)).mpr hx
      have hy' := (mem_centralizer_map (e := e)).mpr hy
      have := (hB K q σ hK hσ h3 (e z) hzM hez3 hez1).1 _ hx' _ hy'
      change e (x * y * x⁻¹ * y⁻¹) ∈ d4ShortSL2 K σ.toRingHom
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact this

end Data

section Provers


theorem exists_d4_threeB (hC : D4ThreeConj) (hA : D4ThreeACent) (hB : D4ThreeBCent)
    {Z : Type} [Group Z] [Finite Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X))
    {z : Z} {J : Subgroup Z} (hz3 : MulAut.conj z ^ 3 = 1)
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ) (σ : K ≃+* K), Nat.card K = q ^ 3 ∧
      (∀ c, σ c = c ^ q) ∧ ¬ 3 ∣ q ∧ σ ^ 3 = 1 ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧
      ∃ e : Z ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        e z ∈ Subgroup.centralizer ((d4ShortSL2 K σ.toRingHom :
          Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
        ThreeBAt Z z ((d4ShortSL2 K σ.toRingHom).comap e.toMonoidHom) := by
  have hZ' : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) := by
    obtain ⟨X, _, ⟨q, hq, -, hf⟩, he⟩ := hZ
    exact ⟨X, inferInstance, ⟨q, hq, hf⟩, he⟩
  obtain ⟨K, _, _, q, σ, hK, hσ, h3, hσ3, hsimple, ⟨E⟩⟩ := exists_d4_model hZ
  have hz3' : z ^ 3 = 1 := by
    have h1 := KS11Lie3Proof.mem_center_of_conj_eq_one (x := z ^ 3) (by rw [map_pow, hz3])
    rwa [KS11Lie3Proof.center_eq_bot_d4 Z hZ', Subgroup.mem_bot] at h1
  have hz1 : z ≠ 1 := by
    rintro rfl
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    have hT := KS11Lie2Proof.hasType424_of_mem hJ hJT
    rw [map_one, Item426.fixSub_one] at hT
    exact not_hasType424_d4 hσ3 ((hT.of_mulEquiv Subgroup.topEquiv).of_mulEquiv E)
  have hez3 : E z ^ 3 = 1 := by rw [← map_pow, hz3', map_one]
  have hez1 : E z ≠ 1 := fun h => hz1 (E.injective (h.trans (map_one E).symm))
  obtain ⟨g, hg⟩ := hC K q σ hK hσ h3 (E z) hez3 hez1
  set e' : Z ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := E.trans (MulAut.conj g)
    with he'
  have hmem : e' z ∈ d4ShortSL2 K σ.toRingHom ∨ e' z ∈ Subgroup.centralizer
      ((d4ShortSL2 K σ.toRingHom : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := hg
  obtain ⟨hzM, h⟩ := threeBAt_d4 hA hB hK hσ h3 hσ3 e' hz3' hz1 hmem hJ hJT
  exact ⟨K, inferInstance, inferInstance, q, σ, hK, hσ, h3, hσ3, hz3', hz1, e', hzM, h⟩

theorem thetaCentral119D4Ss_of (hC : D4ThreeConj) (hA : D4ThreeACent) (hB : D4ThreeBCent) :
    ThetaCentral119D4Ss := by
  intro Z _ _ hZ z J hz3 hJ hJT
  obtain ⟨K, _, _, q, σ, -, -, -, -, -, -, e, -, h⟩ := exists_d4_threeB hC hA hB hZ hz3 hJ hJT
  exact h.thetaCentral hJ

theorem centJ119D4Inn_of (hC : D4ThreeConj) (hA : D4ThreeACent) (hB : D4ThreeBCent) :
    CentJ119D4Inn := by
  intro Z _ _ hZ z b J hz3 hb hbz hJ hJT hbJ
  obtain ⟨K, _, _, q, σ, hK, hσ, h3, hσ3, hz3', hz1, e, hez, h⟩ :=
    exists_d4_threeB hC hA hB hZ hz3 hJ hJT
  have hcard : Nat.card ((d4ShortSL2 K σ.toRingHom).comap e.toMonoidHom) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _))).toEquiv]
    exact card_d4ShortSL2 hσ3
  have hm : q ^ 2 - 1 ∣ Nat.card ((d4ShortSL2 K σ.toRingHom).comap e.toMonoidHom) := by
    rw [hcard, hK]
    refine Dvd.dvd.mul_left ?_ _
    have h6 : (q ^ 3) ^ 2 - 1 = (q ^ 2) ^ 3 - 1 ^ 3 := by rw [one_pow, ← pow_mul, ← pow_mul]
    rw [h6]
    exact Nat.sub_dvd_pow_sub_pow _ _ _
  refine h.inn hm (fun x hx hxS => ?_) hJ hb hbz hbJ
  have hx' := (mem_centralizer_map (e := e)).mpr hx
  have hxS' := (mem_centralizer_comap_iff e _ x).mp hxS
  have hez3 : e z ^ 3 = 1 := by rw [← map_pow, hz3', map_one]
  have hez1 : e z ≠ 1 := fun h' => hz1 (e.injective (h'.trans (map_one e).symm))
  have := (hB K q σ hK hσ h3 (e z) hez hez3 hez1).2 _ hx' hxS'
  exact e.injective (by rw [map_pow, this, map_one])

theorem centJ119D4Out_of (hC : D4ThreeConj) (hA : D4ThreeACent) (hB : D4ThreeBCent)
    (hO : D4ShortOut) : CentJ119D4Out := by
  intro Z _ _ hZ z β J hz3 hβ hzβ hJ hJT hβJ
  obtain ⟨K, _, _, q, σ, hK, hσ, h3, -, -, -, e, -, h⟩ := exists_d4_threeB hC hA hB hZ hz3 hJ hJT
  refine h.out (fun γ hγ hγS => ?_) hJ hβ hβJ
  obtain ⟨k, hk⟩ := hγ
  have hγ' : ∃ k : ℕ, MulAut.congr e γ ^ 3 ^ k = 1 := ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨g, hg⟩ := hO K q σ hK hσ h3 (MulAut.congr e γ) hγ' fun x hx => by
    obtain ⟨x', rfl⟩ := e.surjective x
    change e (γ (e.symm (e x'))) = e x'
    rw [MulEquiv.symm_apply_apply, hγS x' hx]
  refine ⟨e.symm g, MulEquiv.ext fun x => e.injective ?_⟩
  have h1 := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =>
    φ (e x)) hg
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem normCentJ1117D4Ss_of (hC : D4ThreeConj) (hA : D4ThreeACent) (hB : D4ThreeBCent)
    (hN : D4NormCent) : NormCentJ1117D4Ss := by
  intro Z _ _ hZ z J y g hz3 hJ hJT hyJ hyk hy3 _ hgy
  obtain ⟨K, _, _, q, σ, hK, hσ, h3, -, -, -, e, -, h⟩ := exists_d4_threeB hC hA hB hZ hz3 hJ hJT
  have hJS := h.eq hJ
  subst hJS
  have hey : e y ∈ d4ShortSL2 K σ.toRingHom := hyJ
  have heyk : ∃ k : ℕ, e y ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hyk
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hey3 : e y ^ 3 ≠ 1 := fun h' => hy3 (e.injective (by rw [map_pow, h', map_one]))
  have hegy : e g * e y * (e g)⁻¹ ∈ Subgroup.zpowers (e y) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgy
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [← map_zpow, hn, map_mul, map_mul, map_inv]
  have heg := hN K q σ hK hσ h3 (e y) hey heyk hey3 (e g) hegy
  rw [Subgroup.mem_normalizer_iff] at heg ⊢
  intro x
  rw [mem_centralizer_comap_iff, mem_centralizer_comap_iff]
  have h1 := heg (e x)
  rw [h1, map_mul, map_mul, map_inv]

end Provers

end KS11Lie4Proof

end CFSG.RankThree.PartTwo.Sec11
