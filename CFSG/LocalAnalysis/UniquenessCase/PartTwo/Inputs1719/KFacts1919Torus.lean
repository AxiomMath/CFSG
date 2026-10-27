module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusSp4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenLevi
public import CFSG.GroupTheory.CoprimeSupPCore
public import CFSG.GroupTheory.CoprimeCentralizerTransport
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusRegular
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open scoped Pointwise commutatorElement

@[expose] def K_19_19_torusQS : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (I A J : Subgroup X) (n p : ℕ), 3 ≤ n → p.Prime → p ≠ 2 →
    ((IsSp4 (Bar2 I) n ∧ Odd n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∧ IsQuasisimple (Bar2 J)) ∨
        IsL2Square (Bar2 I) n ∨
        (S17.IsL2U3Product (Bar2 I) n ∧ IsPowTwo n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)])) →
    A ≤ I → IsZModSq A n → J ≤ I → A ≤ normalizer J → S17.oUpperTwo J = J →
    pRank p J ≤ 1 →
    ((IsPGroup 3 (Bar2 J) ∧ Nat.card (Bar2 J) ∣ 9) ∨ IsQuasisimple (Bar2 J)) →
    3 ∣ Nat.card (Bar2 J) →
    (J : Set X) ⊆ (pCoreOf 2 J : Set X) * (A : Set X) ∨
      (IsL2 (Bar2 J) n ∧ ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧
        IsQuasisimple (Bar2 K) ∧ J ≤ K ∧
        (J ⊔ pCoreOf 2 K = K ∨ IsSp4 (Bar2 K) n ∨ IsU3 (Bar2 K) n))

@[expose] def K_19_19_leviInv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Dsub : Subgroup G),
    IsQuasisimple (Bar2 Dsub) → List19_16_5 (BarInf Dsub) →
      IsNontrivialParabolic (Bar2 Dsub) (barOfInter M Dsub) → pCoreOf 2 Dsub ≤ M →
      ∀ (d : ℕ) (K J : Fin d → Subgroup G), IsDynkinFamilyIn M Dsub d K J →
        ((∀ (k : Fin d) (n' : ℕ), 3 ≤ n' → ¬ IsL2 (Bar2 (J k)) n') →
          ∀ X : Subgroup G, X ≤ normalizer Dsub → X ≤ normalizer (Dsub ⊓ M) →
            Odd (Nat.card X) → ∀ k, X ≤ normalizer (K k)) ∧
        ∀ k, 3 ∣ Nat.card (Bar2 (J k)) ∧
          (IsQuasisimple (Bar2 (J k)) ∨
            (Nonempty (Bar2 (J k) ≃* Multiplicative (ZMod 3)) ∧
              IsLieTypeOver2 (BarInf Dsub)))

private theorem subset_pCore_mul_of_regular {X : Type} [Group X] [Finite X]
    {I A J : Subgroup X} {x : X} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hord : orderOf x = r)
    (hAI : A ≤ I) (hAC : A ≤ Subgroup.centralizer ({x} : Set X))
    (hAodd : Odd (Nat.card A)) (hJI : J ≤ I)
    (hAJ : A ≤ Subgroup.normalizer (J : Set X))
    (hcent : Subgroup.centralizer ({x} : Set X) ⊓ I =
      A ⊔ (Subgroup.centralizer ({x} : Set X) ⊓ pCoreOf 2 I))
    (hjx : ⁅J, Subgroup.zpowers x⁆ ≤ pCoreOf 2 J) :
    (J : Set X) ⊆ (pCoreOf 2 J : Set X) * (A : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime r) := ⟨hr⟩
  set CX : Subgroup X := Subgroup.centralizer ({x} : Set X) with hCXdef
  set C : Subgroup X := CX ⊓ I with hCdef
  set Z : Subgroup X := CX ⊓ pCoreOf 2 I with hZdef
  set Y : Subgroup X := J ⊓ CX with hYdef
  set P : Subgroup X := pCoreOf 2 J with hPdef
  have hCeq : C = A ⊔ Z := hcent
  have hCleI : C ≤ I := inf_le_right
  have hZleCX : Z ≤ CX := inf_le_left
  have hZleI : Z ≤ I := inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
  have hZleC : Z ≤ C := le_inf hZleCX hZleI
  have hYleJ : Y ≤ J := inf_le_left
  have hYleCX : Y ≤ CX := inf_le_right
  have hYleI : Y ≤ I := hYleJ.trans hJI
  have hYleC : Y ≤ C := le_inf hYleCX hYleI
  have hAleC : A ≤ C := le_inf hAC hAI
  have hZ2 : IsPGroup 2 Z :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) I).to_le inf_le_right
  have hYnormZ : Y ≤ Subgroup.normalizer (Z : Set X) := by
    have h1 : Y ≤ Subgroup.normalizer (CX : Set X) := hYleCX.trans Subgroup.le_normalizer
    have h2 : Y ≤ Subgroup.normalizer (pCoreOf 2 I : Set X) :=
      hYleI.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I)
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAnormY : A ≤ Subgroup.normalizer (Y : Set X) := by
    have h1 : A ≤ Subgroup.normalizer (J : Set X) := hAJ
    have h2 : A ≤ Subgroup.normalizer (CX : Set X) := hAC.trans Subgroup.le_normalizer
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAnormZ : A ≤ Subgroup.normalizer (Z : Set X) := by
    have h1 : A ≤ Subgroup.normalizer (CX : Set X) := hAC.trans Subgroup.le_normalizer
    have h2 : A ≤ Subgroup.normalizer (pCoreOf 2 I : Set X) :=
      hAI.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I)
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAZbot : A ⊓ Z = ⊥ := by
    rw [inf_comm]
    exact CFSG.RankThree.OddKernel.inf_eq_bot_of_odd hZ2 hAodd
  have hZlePI : Z ≤ pCoreOf 2 I := inf_le_right
  have hYZleP : Y ⊓ Z ≤ P := by
    have hJP : J ⊓ pCoreOf 2 I ≤ P := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (N := J ⊓ pCoreOf 2 I) (H := J) inf_le_left ?_ ?_
      · exact (le_inf Subgroup.le_normalizer
          (hJI.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I))).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) I).to_le
          (inf_le_right : J ⊓ pCoreOf 2 I ≤ pCoreOf 2 I)
    exact (le_inf ((inf_le_left : Y ⊓ Z ≤ Y).trans hYleJ)
      ((inf_le_right : Y ⊓ Z ≤ Z).trans hZlePI)).trans hJP
  have hAZrel := CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := A) (K := Z) hAnormZ
  have hZrelC : Z.relIndex C = Nat.card A := by
    rw [hCeq, hAZrel.2, hAZbot, Subgroup.relIndex_bot_left]
  have hArelC : A.relIndex C = Nat.card Z := by
    rw [hCeq, hAZrel.1, hAZbot, Subgroup.relIndex_bot_left]
  have hYZleC : Y ⊔ Z ≤ C := sup_le hYleC hZleC
  have hAYleC : A ⊔ Y ≤ C := sup_le hAleC hYleC
  have hd1 : Z.relIndex (Y ⊔ Z) ∣ Nat.card A := by
    have hmul := Subgroup.relIndex_mul_relIndex (H := Z) (K := Y ⊔ Z) (L := C)
      le_sup_right hYZleC
    rw [hZrelC] at hmul
    exact ⟨_, hmul.symm⟩
  have hd2 : A.relIndex (A ⊔ Y) ∣ Nat.card Z := by
    have hmul := Subgroup.relIndex_mul_relIndex (H := A) (K := A ⊔ Y) (L := C)
      le_sup_left hAYleC
    rw [hArelC] at hmul
    exact ⟨_, hmul.symm⟩
  have hZrelY : (Y ⊓ Z).relIndex Y = Z.relIndex (Y ⊔ Z) :=
    (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := Y) (K := Z) hYnormZ).2.symm
  have hArelY : (Y ⊓ A).relIndex Y = A.relIndex (A ⊔ Y) := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := A) (K := Y) hAnormY).1
    rw [inf_comm] at h
    exact h.symm
  have hcardY1 : Nat.card Y = Nat.card ↥(Y ⊓ Z) * (Y ⊓ Z).relIndex Y := by
    have h := Subgroup.relIndex_mul_card (H := Y ⊓ Z) (K := Y)
    have hinf : (Y ⊓ Z) ⊓ Y = Y ⊓ Z := by
      ext y
      simp only [Subgroup.mem_inf]
      tauto
    rw [hinf] at h
    rw [← h, mul_comm]
  have hcardY2 : Nat.card Y = Nat.card ↥(Y ⊓ A) * (Y ⊓ A).relIndex Y := by
    have h := Subgroup.relIndex_mul_card (H := Y ⊓ A) (K := Y)
    have hinf : (Y ⊓ A) ⊓ Y = Y ⊓ A := by
      ext y
      simp only [Subgroup.mem_inf]
      tauto
    rw [hinf] at h
    rw [← h, mul_comm]
  have hv_odd : Odd (Nat.card ↥(Y ⊓ A)) :=
    hAodd.of_dvd_nat (Subgroup.card_dvd_of_le (H := Y ⊓ A) (K := A) inf_le_right)
  have hd1_odd : Odd ((Y ⊓ Z).relIndex Y) := by
    rw [hZrelY]
    exact hAodd.of_dvd_nat hd1
  have hu_pow : ∃ k, Nat.card ↥(Y ⊓ Z) = 2 ^ k :=
    (hZ2.to_le (inf_le_right : Y ⊓ Z ≤ Z)).exists_card_eq
  have hd2_pow : ∃ k, (Y ⊓ A).relIndex Y = 2 ^ k := by
    rw [hArelY]
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hdvd : A.relIndex (A ⊔ Y) ∣ 2 ^ k := by
      rw [← hk]
      exact hd2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have heq : Nat.card ↥(Y ⊓ Z) * (Y ⊓ Z).relIndex Y =
      Nat.card ↥(Y ⊓ A) * (Y ⊓ A).relIndex Y := by
    rw [← hcardY1, ← hcardY2]
  have hu : Nat.card ↥(Y ⊓ Z) = (Y ⊓ A).relIndex Y := by
    obtain ⟨a, ha⟩ := hu_pow
    obtain ⟨b, hb⟩ := hd2_pow
    rw [ha, hb] at heq ⊢
    rw [mul_comm (Nat.card ↥(Y ⊓ A))] at heq
    rw [CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hd1_odd hv_odd heq]
  have hposd2 : 0 < (Y ⊓ A).relIndex Y := by
    have h := Subgroup.relIndex_mul_card (H := Y ⊓ A) (K := Y)
    have hYpos : 0 < Nat.card Y := Nat.card_pos
    by_contra h0
    have hzero : (Y ⊓ A).relIndex Y = 0 := Nat.eq_zero_of_not_pos h0
    rw [hzero, zero_mul] at h
    omega
  have hv : Nat.card ↥(Y ⊓ A) = (Y ⊓ Z).relIndex Y := by
    have h2 : (Y ⊓ A).relIndex Y * Nat.card ↥(Y ⊓ A) =
        (Y ⊓ A).relIndex Y * (Y ⊓ Z).relIndex Y := by
      calc (Y ⊓ A).relIndex Y * Nat.card ↥(Y ⊓ A)
          = Nat.card ↥(Y ⊓ A) * (Y ⊓ A).relIndex Y := mul_comm _ _
        _ = Nat.card ↥(Y ⊓ Z) * (Y ⊓ Z).relIndex Y := heq.symm
        _ = (Y ⊓ A).relIndex Y * (Y ⊓ Z).relIndex Y := by rw [hu]
    exact Nat.eq_of_mul_eq_mul_left hposd2 h2
  have hYcard : Nat.card Y = Nat.card ↥(Y ⊓ Z) * Nat.card ↥(Y ⊓ A) := by
    rw [hcardY1, ← hv]
  have hprod_sub : (((Y ⊓ Z : Subgroup X) : Set X) *
      ((Y ⊓ A : Subgroup X) : Set X)) ⊆ (Y : Set X) := by
    rintro _ ⟨z, hz, a, ha, rfl⟩
    exact Y.mul_mem ((inf_le_left : Y ⊓ Z ≤ Y) hz) ((inf_le_left : Y ⊓ A ≤ Y) ha)
  have hYeq : ((Y ⊓ Z : Subgroup X) : Set X) * ((Y ⊓ A : Subgroup X) : Set X) =
      (Y : Set X) := by
    have hinj : Function.Injective
        (fun p : ↥(Y ⊓ Z) × ↥(Y ⊓ A) => ((p.1 : X) * (p.2 : X))) := by
      rintro ⟨z₁, a₁⟩ ⟨z₂, a₂⟩ h
      have h1 : (z₁ : X)⁻¹ * (z₂ : X) = (a₁ : X) * (a₂ : X)⁻¹ := by
        change (z₁ : X) * (a₁ : X) = (z₂ : X) * (a₂ : X) at h
        have hz₂ : (z₂ : X) = (z₁ : X) * (a₁ : X) * (a₂ : X)⁻¹ := by
          calc (z₂ : X) = (z₂ : X) * (a₂ : X) * (a₂ : X)⁻¹ := by group
            _ = (z₁ : X) * (a₁ : X) * (a₂ : X)⁻¹ := by rw [← h]
        rw [hz₂]
        group
      have hz : (z₁ : X)⁻¹ * (z₂ : X) ∈ Y ⊓ Z :=
        ⟨Y.mul_mem (Y.inv_mem z₁.2.1) z₂.2.1, Z.mul_mem (Z.inv_mem z₁.2.2) z₂.2.2⟩
      have ha : (a₁ : X) * (a₂ : X)⁻¹ ∈ Y ⊓ A :=
        ⟨Y.mul_mem a₁.2.1 (Y.inv_mem a₂.2.1), A.mul_mem a₁.2.2 (A.inv_mem a₂.2.2)⟩
      have hbot : (z₁ : X)⁻¹ * (z₂ : X) = 1 := by
        have hmem : (z₁ : X)⁻¹ * (z₂ : X) ∈ Z ⊓ A := ⟨hz.2, h1 ▸ ha.2⟩
        rw [inf_comm, hAZbot, Subgroup.mem_bot] at hmem
        exact hmem
      have hzz : (z₁ : X) = (z₂ : X) := by
        have h' : (z₁ : X) * ((z₁ : X)⁻¹ * (z₂ : X)) = (z₁ : X) * 1 :=
          congrArg (fun t => (z₁ : X) * t) hbot
        simpa using h'.symm
      have haa : (a₁ : X) = (a₂ : X) := by
        have h2 : (a₁ : X) * (a₂ : X)⁻¹ = 1 := by
          rw [← h1, ← hzz, inv_mul_cancel]
        have h3 := congrArg (fun t => t * (a₂ : X)) h2
        simpa [mul_assoc] using h3
      exact Prod.ext (Subtype.ext hzz) (Subtype.ext haa)
    have hcard : Nat.card (((Y ⊓ Z : Subgroup X) : Set X) *
        ((Y ⊓ A : Subgroup X) : Set X)) = Nat.card Y := by
      let f : ↥(Y ⊓ Z) × ↥(Y ⊓ A) →
          (((Y ⊓ Z : Subgroup X) : Set X) * ((Y ⊓ A : Subgroup X) : Set X)) :=
        fun p => ⟨(p.1 : X) * (p.2 : X), Set.mul_mem_mul p.1.2 p.2.2⟩
      have hf : Function.Bijective f := by
        refine ⟨fun p q h => hinj (congrArg Subtype.val h), ?_⟩
        rintro ⟨y, hy⟩
        obtain ⟨z, hz, a, ha, rfl⟩ := hy
        exact ⟨(⟨z, hz⟩, ⟨a, ha⟩), rfl⟩
      calc Nat.card (((Y ⊓ Z : Subgroup X) : Set X) * ((Y ⊓ A : Subgroup X) : Set X))
          = Nat.card (↥(Y ⊓ Z) × ↥(Y ⊓ A)) :=
            Nat.card_congr (Equiv.ofBijective f hf).symm
        _ = Nat.card ↥(Y ⊓ Z) * Nat.card ↥(Y ⊓ A) := Nat.card_prod _ _
        _ = Nat.card Y := hYcard.symm
    refine Set.eq_of_subset_of_ncard_le hprod_sub ?_
    show Nat.card Y ≤ Nat.card ↥(((Y ⊓ Z : Subgroup X) : Set X) *
      ((Y ⊓ A : Subgroup X) : Set X))
    rw [← hcard]
  have hYlePA : (Y : Set X) ⊆ (P : Set X) * (A : Set X) := by
    intro y hy
    rw [← hYeq] at hy
    obtain ⟨z, hz, a, ha, rfl⟩ := hy
    exact Set.mul_mem_mul (hYZleP hz) ((inf_le_right : Y ⊓ A ≤ A) ha)
  have hJeq : J = P ⊔ Y := by
    have h := CFSG.GroupTheory.inf_centralizer_sup_pCoreOf_eq_of_commutator_le
      (L := J) (A := Subgroup.zpowers x) hr hr2
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one]))
      (by rw [Subgroup.commutator_comm]; exact hjx)
    rw [CFSG.Walter.centralizer_zpowers_eq'] at h
    rw [show J ⊓ CX = Y from hYdef.symm, show pCoreOf 2 J = P from hPdef.symm] at h
    rw [sup_comm] at h
    exact h.symm
  have hYnormP : Y ≤ Subgroup.normalizer (P : Set X) :=
    hYleJ.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J)
  intro j hj
  have hcoe : (J : Set X) = (P : Set X) * (Y : Set X) := by
    rw [hJeq]
    exact Subgroup.coe_mul_of_right_le_normalizer_left P Y hYnormP
  rw [hcoe] at hj
  obtain ⟨p, hp, y, hy, rfl⟩ := hj
  obtain ⟨p', hp', a, ha, rfl⟩ := Set.mem_mul.mp (hYlePA hy)
  change p * (p' * a) ∈ (P : Set X) * (A : Set X)
  rw [← mul_assoc]
  exact Set.mul_mem_mul (P.mul_mem hp hp') ha

theorem subset_pCore_mul_of_regular_three {X : Type} [Group X] [Finite X]
    {I A J : Subgroup X} (hAI : A ≤ I) (hAcomm : IsMulCommutative ↥A)
    (hAodd : Odd (Nat.card A)) (hJI : J ≤ I) (hAJ : A ≤ normalizer (J : Set X))
    (hgroup : IsPGroup 3 (Bar2 J) ∧ Nat.card (Bar2 J) ∣ 9) (h3 : 3 ∣ Nat.card (Bar2 J))
    {r : ℕ} (hpr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (x : ↥A)
    (hxord : orderOf ((x : ↥A) : X) = r)
    (hCzI : Subgroup.centralizer
        ({(QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp (Subgroup.inclusion hAI) x} : Set (Bar2 I)) =
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp (Subgroup.inclusion hAI)).range) :
    (J : Set X) ⊆ (pCoreOf 2 J : Set X) * (A : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime r) := ⟨hpr⟩
  set φ : ↥A →* Bar2 I :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp (Subgroup.inclusion hAI) with hφdef
  have hAC : A ≤ Subgroup.centralizer ({((x : ↥A) : X)} : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun z : ↥A => (z : X)) (hAcomm.is_comm.comm ⟨a, ha⟩ x)
  have hcent : Subgroup.centralizer ({((x : ↥A) : X)} : Set X) ⊓ I =
      A ⊔ (Subgroup.centralizer ({((x : ↥A) : X)} : Set X) ⊓ pCoreOf 2 I) := by
    set xI : ↥I := Subgroup.inclusion hAI x with hxIdef
    have hxI_mk : QuotientGroup.mk' (CFSG.pCore 2 ↥I) xI = φ x := rfl
    have hxIord : orderOf xI = r := by
      rw [← Subgroup.orderOf_coe xI]
      exact hxord
    have hE : IsPGroup r (Subgroup.zpowers xI) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxIord, pow_one])
    have hNr : ¬ r ∣ Nat.card ↥(CFSG.pCore 2 ↥I) := by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
      rw [hk]
      intro h
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp (hpr.dvd_of_dvd_pow h))
    have hcent_eq := CFSG.GroupTheory.CoprimeTransport.centralizer_image_mk_eq
      (G := ↥I) (N := CFSG.pCore 2 ↥I) (s := r) hNr hE
      (S := ({xI} : Set ↥I))
      (by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact Subgroup.mem_zpowers xI)
    rw [Set.image_singleton, hxI_mk, hCzI] at hcent_eq
    have hAbar : φ.range = (A.subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) := by
      ext z
      constructor
      · rintro ⟨a, rfl⟩
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hAI a, a.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
    rw [hAbar] at hcent_eq
    refine le_antisymm ?_ ?_
    · rintro c ⟨hcC, hcI⟩
      have hcπ : QuotientGroup.mk' (CFSG.pCore 2 ↥I) ⟨c, hcI⟩ ∈
          (A.subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) := by
        rw [hcent_eq]
        refine Subgroup.mem_map_of_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hcC)
      obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hcπ
      have hyA : (y : X) ∈ A := hy
      have hyI : (y : X) ∈ I := y.2
      have hsub : (y : X)⁻¹ * c ∈ CFSG.Open.pCoreOf 2 I := by
        have h1 : y⁻¹ * (⟨c, hcI⟩ : ↥I) ∈ CFSG.pCore 2 ↥I :=
          QuotientGroup.eq.mp hyc
        exact (CFSG.mem_openPCoreOf_iff (y⁻¹ * (⟨c, hcI⟩ : ↥I))).mpr h1
      have hZmem' : (y : X)⁻¹ * c ∈
          Subgroup.centralizer ({((x : ↥A) : X)} : Set X) ⊓ pCoreOf 2 I :=
        ⟨(Subgroup.centralizer ({((x : ↥A) : X)} : Set X)).mul_mem
            ((Subgroup.centralizer _).inv_mem (hAC hyA)) hcC, hsub⟩
      have hseq : c = (y : X) * ((y : X)⁻¹ * c) := by group
      rw [hseq]
      exact Subgroup.mul_mem_sup hyA hZmem'
    · have hZle : (Subgroup.centralizer ({((x : ↥A) : X)} : Set X) ⊓ pCoreOf 2 I) ≤
          Subgroup.centralizer ({((x : ↥A) : X)} : Set X) ⊓ I := by
        refine le_inf inf_le_left ?_
        exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
      exact sup_le (le_inf hAC hAI) hZle
  have hjx : ⁅Subgroup.zpowers ((x : ↥A) : X), J⁆ ≤ pCoreOf 2 J := by
    let A' : Subgroup X := Subgroup.zpowers ((x : ↥A) : X)
    have hxJ : ((x : ↥A) : X) ∈ Subgroup.normalizer (J : Set X) := hAJ x.2
    have hA'J : A' ≤ Subgroup.normalizer (J : Set X) := Subgroup.zpowers_le.mpr hxJ
    have : A'.Normalizes J := ⟨hA'J⟩
    have hNinv : CFSG.IsInvariant ↥A' ↥J (CFSG.pCore 2 ↥J) :=
      CFSG.RankThree.GroupTheory.SteinbergBY.isInvariant_of_characteristic
        (A := ↥A') (P := ↥J) (CFSG.pCore 2 ↥J)
    let : MulDistribMulAction ↥A' (Bar2 J) :=
      CFSG.quotientMulDistribMulAction (A := ↥A') (G := ↥J) (CFSG.pCore 2 ↥J) hNinv
    have hA'p : IsPGroup r ↥A' :=
      IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, hxord, pow_one])
    have hmod := hA'p.card_modEq_card_fixedPoints (Bar2 J)
    have hFeq : Nat.card ↥(fixedPointSubgroup ↥A' (Bar2 J)) = Nat.card (Bar2 J) := by
      have hFdvd : Nat.card ↥(fixedPointSubgroup ↥A' (Bar2 J)) ∣ Nat.card (Bar2 J) :=
        Subgroup.card_subgroup_dvd_card _
      obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show Nat.card (Bar2 J) ∣ 3 ^ 2 by simpa using hgroup.2)
      have hFdvd' : Nat.card ↥(fixedPointSubgroup ↥A' (Bar2 J)) ∣ 3 ^ k := by
        rwa [hk] at hFdvd
      obtain ⟨j, hj2, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hFdvd'
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        rw [hk] at h3
        exact absurd h3 (by norm_num)
      have hk12 : k = 1 ∨ k = 2 := by omega
      have hjk : j ≤ k := by omega
      have hle : 3 ^ j ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hjk
      have hmod' : 3 ^ k ≡ 3 ^ j [MOD r] := by
        have hmod1 : Nat.card (Bar2 J) ≡
            Nat.card ↥(fixedPointSubgroup ↥A' (Bar2 J)) [MOD r] := hmod
        rw [show 3 ^ k = Nat.card (Bar2 J) from hk.symm,
          show 3 ^ j = Nat.card ↥(fixedPointSubgroup ↥A' (Bar2 J)) from hj.symm]
        exact hmod1
      have hdvd : r ∣ 3 ^ k - 3 ^ j := (Nat.modEq_iff_dvd' hle).mp hmod'.symm
      have hdiff : 3 ^ k = 3 ^ j := by
        have h0 : 3 ^ k - 3 ^ j = 0 := by
          rcases hk12 with rfl | rfl
          · interval_cases j
            · exfalso
              have h2 : r ∣ 2 := by simpa using hdvd
              exact hr2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp h2)
            · rfl
          · interval_cases j
            · exfalso
              have h8 : r ∣ 8 := by simpa using hdvd
              have h8' : r ∣ 2 ^ 3 := by simpa using h8
              have h2 : r ∣ 2 := hpr.dvd_of_dvd_pow h8'
              exact hr2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp h2)
            · exfalso
              have h6 : r ∣ 6 := by simpa using hdvd
              have h6' : r ∣ 2 * 3 := by simpa using h6
              rcases (Nat.Prime.dvd_mul hpr).mp h6' with h | h
              · exact hr2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp h)
              · exact hr3 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_three).mp h)
            · rfl
        omega
      have hkj : k = j := Nat.pow_right_injective (by norm_num : 1 < 3) hdiff
      calc Nat.card ↥(fixedPointSubgroup ↥A' (Bar2 J)) = 3 ^ j := hj
        _ = 3 ^ k := congrArg (fun t => 3 ^ t) hkj.symm
        _ = Nat.card (Bar2 J) := hk.symm
    have hfix : ∀ (b : ↥A') (y : Bar2 J), b • y = y := by
      intro b y
      have htop : fixedPointSubgroup ↥A' (Bar2 J) = ⊤ :=
        Subgroup.eq_top_of_card_eq _ hFeq
      have hmem : y ∈ fixedPointSubgroup ↥A' (Bar2 J) := by rw [htop]; exact Subgroup.mem_top y
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hmem
      exact hmem b
    rw [Subgroup.commutator_le]
    intro b hb a ha
    have hb' : b ∈ A' := hb
    have h1 : QuotientGroup.mk (s := CFSG.pCore 2 ↥J)
        ((⟨b, hb'⟩ : ↥A') • (⟨a, ha⟩ : ↥J)) =
        QuotientGroup.mk (s := CFSG.pCore 2 ↥J) ⟨a, ha⟩ := by
      rw [← MulAction.Quotient.smul_coe]
      exact hfix ⟨b, hb'⟩ _
    have h2 : (((⟨b, hb'⟩ : ↥A') • (⟨a, ha⟩ : ↥J)) * (⟨a, ha⟩ : ↥J)⁻¹ : ↥J) ∈
        CFSG.pCore 2 ↥J := by
      have hmem : (⟨a, ha⟩ : ↥J)⁻¹ * ((⟨b, hb'⟩ : ↥A') • (⟨a, ha⟩ : ↥J)) ∈
          CFSG.pCore 2 ↥J :=
        QuotientGroup.eq.mp h1.symm
      have hconj : ((⟨b, hb'⟩ : ↥A') • (⟨a, ha⟩ : ↥J)) * (⟨a, ha⟩ : ↥J)⁻¹ =
          ((⟨b, hb'⟩ : ↥A') • (⟨a, ha⟩ : ↥J)) *
            ((⟨a, ha⟩ : ↥J)⁻¹ * ((⟨b, hb'⟩ : ↥A') • (⟨a, ha⟩ : ↥J))) *
            ((⟨b, hb'⟩ : ↥A') • (⟨a, ha⟩ : ↥J))⁻¹ := by group
      rw [hconj]
      exact (CFSG.pCore_normal (p := 2) (G := ↥J)).conj_mem _ hmem _
    have h4 : ((((⟨b, hb'⟩ : ↥A') • (⟨a, ha⟩ : ↥J)) * (⟨a, ha⟩ : ↥J)⁻¹ : ↥J) : X) ∈
        CFSG.Open.pCoreOf 2 J :=
      (CFSG.mem_openPCoreOf_iff
        (((⟨b, hb'⟩ : ↥A') • (⟨a, ha⟩ : ↥J)) * (⟨a, ha⟩ : ↥J)⁻¹)).mpr h2
    have h5 : (((⟨b, hb'⟩ : ↥A') • (⟨a, ha⟩ : ↥J) : ↥J) : X) = b * a * b⁻¹ := by
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have h6 : (b * a * b⁻¹) * a⁻¹ ∈ CFSG.Open.pCoreOf 2 J := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, h5] using h4
    rw [commutatorElement_def]
    exact h6
  exact subset_pCore_mul_of_regular hpr hr2 hxord hAI hAC hAodd hJI hAJ hcent
    (by rw [Subgroup.commutator_comm]; exact hjx)

theorem false_of_isSzSquare_of_three_dvd_bar2 {X : Type} [Group X] [Finite X]
    {I J : Subgroup X} {n : ℕ} (hSz : IsSzSquare (Bar2 I) n) (hJI : J ≤ I)
    (h3 : 3 ∣ Nat.card (Bar2 J)) : False := by
  obtain ⟨Q₁, Q₂, _inst₁, _inst₂, ⟨e⟩, hQ₁, hQ₂⟩ := hSz
  have h3I : 3 ∣ Nat.card (Bar2 I) := by
    have hBJ : Nat.card (Bar2 J) ∣ Nat.card J := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥J)]
      exact dvd_mul_right _ _
    have hJ : 3 ∣ Nat.card I := (h3.trans hBJ).trans (Subgroup.card_dvd_of_le hJI)
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I), ha] at hJ
    exact (Nat.prime_three.dvd_mul.mp hJ).resolve_right fun h =>
      absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  rw [Nat.card_congr e.toEquiv, Nat.card_prod] at h3I
  rcases Nat.prime_three.dvd_mul.mp h3I with h | h
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hQ₁ h
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hQ₂ h

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem k_19_19_torusInv_sp4_three {X : Type} [Group X] [Finite X]
    (I A J : Subgroup X) (n : ℕ) (hn : 3 ≤ n) (hsp : IsSp4 (Bar2 I) n) (hodd : Odd n)
    (hAI : A ≤ I) (hA : IsZModSq A n) (hJI : J ≤ I) (hAJ : A ≤ normalizer J)
    (hgroup : IsPGroup 3 (Bar2 J) ∧ Nat.card (Bar2 J) ∣ 9) (h3 : 3 ∣ Nat.card (Bar2 J)) :
    (J : Set X) ⊆ (pCoreOf 2 J : Set X) * (A : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hFld, hFin, hChar, hKcard, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel
      (n := 2) (f := n) hsp
  have hoddq : Odd (2 ^ n - 1) := by
    have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    exact ⟨2 ^ (n - 1) - 1, by
      rw [h2]
      have hpos : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
      omega⟩
  have hAodd : Odd (Nat.card A) := by
    rw [card_eq_of_isZModSq hA]
    exact hoddq.mul hoddq
  have hAinf : A ⊓ CFSG.Open.pCoreOf 2 I = ⊥ := by
    rw [inf_comm]
    exact CFSG.RankThree.OddKernel.inf_eq_bot_of_odd
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) I) hAodd
  let φ : ↥A →* Bar2 I :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp (Subgroup.inclusion hAI)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥A) : X) ∈ CFSG.Open.pCoreOf 2 I := by
      have h3 : Subgroup.inclusion hAI (a * b⁻¹) ∈ CFSG.pCore 2 ↥I :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hAI (a * b⁻¹))).mp h1
      exact (CFSG.mem_openPCoreOf_iff (Subgroup.inclusion hAI (a * b⁻¹))).mpr h3
    have h3 : ((a * b⁻¹ : ↥A) : X) ∈ A ⊓ CFSG.Open.pCoreOf 2 I := ⟨(a * b⁻¹).2, h2⟩
    rw [hAinf, Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.mp (Subtype.ext h3)
  let T : Subgroup (StatedSp 2 K) := (φ.range).map e.toMonoidHom
  have hT : IsZModSq T n := by
    obtain ⟨eA⟩ := hA
    have e1 : ↥A ≃* ↥(φ.range) := MonoidHom.ofInjective hφinj
    have e2 : ↥(φ.range) ≃* ↥T :=
      Subgroup.equivMapOfInjective (φ.range) e.toMonoidHom e.injective
    exact ⟨e2.symm.trans (e1.symm.trans eA)⟩
  obtain ⟨g, hg⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.exists_conj_eq_torus_of_isZModSq_sp4
      (K := K) hKcard hn hodd hT
  have hK8 : 8 ≤ Nat.card K := by
    rw [hKcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨r, hpr, hrd⟩ := Nat.exists_prime_and_dvd (show Nat.card K - 1 ≠ 1 by omega)
  have : Fact (Nat.Prime r) := ⟨hpr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hnot : ¬ 2 ∣ Nat.card K - 1 := by
      rw [hKcard]
      intro hd
      exact (Nat.not_even_iff_odd.mpr hoddq) (even_iff_two_dvd.mpr hd)
    exact hnot hrd
  have hr3 : r ≠ 3 := by
    rintro rfl
    have hmod : 2 ^ n % 3 = 2 := by
      obtain ⟨k, rfl⟩ := hodd
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have hdiv : 3 ∣ 2 ^ n - 1 := by rwa [hKcard] at hrd
    have h1 : 2 ^ n % 3 = 1 := by
      have h2 : 2 ^ n = (2 ^ n - 1) + 1 := by omega
      rw [h2, Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hdiv, zero_add,
        Nat.mod_eq_of_lt (by omega : 1 < 3)]
    omega
  obtain ⟨y, hyC, hyord⟩ := exists_regular_torus_sp4 hpr hr2 hr3 hrd
  let zT : StatedSp 2 K := g * y * g⁻¹
  have hy_mem : y ∈ torus 2 K := by
    rw [← hyC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzT_mem : zT ∈ T := by
    rw [hg]
    exact Subgroup.mem_map.mpr ⟨y, hy_mem, rfl⟩
  let zI : Bar2 I := e.symm zT
  have hzI_mem : zI ∈ φ.range := by
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hzT_mem
    have hwz' : zI = w := by
      rw [show zI = e.symm zT from rfl, ← hwz]
      exact e.symm_apply_apply w
    rw [hwz']
    exact hw
  obtain ⟨x, hxφ⟩ := MonoidHom.mem_range.mp hzI_mem
  have hCzT : Subgroup.centralizer ({zT} : Set (StatedSp 2 K)) =
      (torus 2 K).map (MulAut.conj g).toMonoidHom := by
    have h := CFSG.GroupTheory.CoprimeTransport.centralizer_image_mulEquiv (MulAut.conj g)
      ({y} : Set (StatedSp 2 K))
    rw [Set.image_singleton] at h
    rw [← hyC]
    exact h
  have hCzI : Subgroup.centralizer ({zI} : Set (Bar2 I)) = φ.range := by
    have h1 := CFSG.GroupTheory.CoprimeTransport.centralizer_image_mulEquiv e
      ({zI} : Set (Bar2 I))
    rw [Set.image_singleton, show e zI = zT from e.apply_symm_apply zT, hCzT, ← hg] at h1
    exact Subgroup.map_injective e.injective h1.symm
  have hzI_ord : orderOf zI = r := by
    calc orderOf zI = orderOf zT := MulEquiv.orderOf_eq e.symm zT
      _ = orderOf (MulAut.conj g y) := by rw [show zT = MulAut.conj g y from rfl]
      _ = orderOf y := MulEquiv.orderOf_eq (MulAut.conj g) y
      _ = r := hyord
  have hxord : orderOf ((x : ↥A) : X) = r := by
    have h1 : orderOf (φ x) = orderOf (x : ↥A) := orderOf_injective φ hφinj x
    calc orderOf ((x : ↥A) : X) = orderOf (x : ↥A) := Subgroup.orderOf_coe x
      _ = orderOf (φ x) := h1.symm
      _ = orderOf zI := by rw [hxφ]
      _ = r := hzI_ord
  have hCx : Subgroup.centralizer ({φ x} : Set (Bar2 I)) = φ.range := by
    rw [hxφ]
    exact hCzI
  exact subset_pCore_mul_of_regular_three hAI (isMulCommutative_of_isZModSq hA) hAodd hJI hAJ
    hgroup h3 hpr hr2 hr3 x hxord hCx

theorem k_19_19_torusInv_of_qs (h : K_19_19_torusQS) :
    ∀ (X : Type) [Group X] [Finite X] (I A J : Subgroup X) (n p : ℕ), 3 ≤ n → p.Prime → p ≠ 2 →
      ((IsSp4 (Bar2 I) n ∧ Odd n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
          IsL2Square (Bar2 I) n ∨ IsSzSquare (Bar2 I) n ∨
          (S17.IsL2U3Product (Bar2 I) n ∧ IsPowTwo n ∧
            (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)])) →
      A ≤ I → IsZModSq A n → J ≤ I → A ≤ normalizer J → S17.oUpperTwo J = J →
      pRank p J ≤ 1 →
      ((IsPGroup 3 (Bar2 J) ∧ Nat.card (Bar2 J) ∣ 9) ∨ IsQuasisimple (Bar2 J)) →
      3 ∣ Nat.card (Bar2 J) →
      (J : Set X) ⊆ (pCoreOf 2 J : Set X) * (A : Set X) ∨
        (IsL2 (Bar2 J) n ∧ ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧
          IsQuasisimple (Bar2 K) ∧ J ≤ K ∧
          (J ⊔ pCoreOf 2 K = K ∨ IsSp4 (Bar2 K) n ∨ IsU3 (Bar2 K) n)) := by
  intro X _ _ I A J n p hn hp hp2 hshape hAI hA hJI hAJ hO hr hgroup h3
  rcases hshape with hsp | hL2sq | hSzsq | hU3
  · by_cases hq : IsQuasisimple (Bar2 J)
    · exact h X I A J n p hn hp hp2 (Or.inl ⟨hsp.1, hsp.2.1, hsp.2.2, hq⟩) hAI hA hJI hAJ hO hr
        hgroup h3
    · exact Or.inl (k_19_19_torusInv_sp4_three I A J n hn hsp.1 hsp.2.1 hAI hA hJI hAJ
        (hgroup.resolve_right hq) h3)
  · exact h X I A J n p hn hp hp2 (Or.inr (Or.inl hL2sq)) hAI hA hJI hAJ hO hr hgroup h3
  · exact (false_of_isSzSquare_of_three_dvd_bar2 hSzsq hJI h3).elim
  · exact h X I A J n p hn hp hp2 (Or.inr (Or.inr hU3)) hAI hA hJI hAJ hO hr hgroup h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
