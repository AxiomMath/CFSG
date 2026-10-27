module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Linear
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Gaps
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
public import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.GroupTheory.LocalCores.Components
public import Certificates.Certificate43
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Card
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Order.Atoms
public import Mathlib.Order.KrullDimension
public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity
public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.GroupTheory.DerivedCentralQuotient
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Levi
public import TauCeti.LinearAlgebra.SymplecticGroup

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Matrix CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL localRank)
open scoped MatrixGroups

noncomputable def quotientComapEquiv {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (M : Subgroup (G ⧸ N)) [M.Normal] [(M.comap (QuotientGroup.mk' N)).Normal] :
    G ⧸ M.comap (QuotientGroup.mk' N) ≃* (G ⧸ N) ⧸ M :=
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp (QuotientGroup.mk' N)) :=
    (QuotientGroup.mk'_surjective M).comp (QuotientGroup.mk'_surjective N)
  have hker : ((QuotientGroup.mk' M).comp (QuotientGroup.mk' N)).ker =
      M.comap (QuotientGroup.mk' N) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)

noncomputable def slMapEquivN (n : ℕ) {F F' : Type} [Field F] [Field F'] (φ : F ≃+* F') :
    SL(n, F) ≃* SL(n, F') :=
  MonoidHom.toMulEquiv (SpecialLinearGroup.map (φ : F →+* F'))
    (SpecialLinearGroup.map (φ.symm : F' →+* F))
    (by ext A i j; simp)
    (by ext A i j; simp)

noncomputable def sl3EquivProjSL : SL(3, ZMod 3) ≃* projSL 3 (GaloisField 3 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ZMod 3 ≃+* GaloisField 3 1 := (GaloisField.equivZmodP 3).toRingEquiv.symm
  let e := slMapEquivN 3 φ
  have hc : Subgroup.center SL(3, GaloisField 3 1) = ⊥ := by
    rw [← Subgroup.map_center_eq e, center_SL3_three, Subgroup.map_bot]
  exact e.trans ((QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)).trans (pslEquivProjSL 3 (GaloisField 3 1)))

theorem pRank_le_pRank_top {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (H : Subgroup X) : CFSG.pRank p H ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact CFSG.RankThreeEvenClassification.Helpers.pRank_mono p hp le_top

theorem pRank_quotient_pCore_two {G : Type*} [Group G] [Finite G] (hO2 : pCore 2 G ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (G ⧸ pCore 2 G)) = localRank p G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (pCore 2 G) := pCore_isPGroup
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hO2 (Subgroup.eq_bot_of_card_eq _ hk)
  have hpN : ¬ p ∣ Nat.card (pCore 2 G) := by
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have heven : Even (Nat.card (pCore 2 G)) := by
    rw [hk]
    exact (Nat.even_pow' hk0).mpr even_two
  have : (pCore 2 G).Normal := pCore_normal
  obtain ⟨h1, h2⟩ := CFSG.RankThree.Classical2.localRank_eq_pRank_of_even hp hp2 (pCore 2 G) hpN
    heven
  exact (h1.trans h2).symm

section Three

variable {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
  [IsSimpleGroup (X ⧸ K)]

omit [Group.IsPerfect X] [K.Normal] [IsSimpleGroup (X ⧸ K)] in
theorem pPrimeCore_le_centralizer_pCore (p : ℕ) [Fact p.Prime] :
    pPrimeCore p X ≤ Subgroup.centralizer (pCore p X : Set X) := by
  have : (pCore p X).Normal := pCore_normal
  have : (pPrimeCore p X).Normal := pPrimeCore_normal
  have hinf : pPrimeCore p X ⊓ pCore p X = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup p (pCore p X)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (pPrimeCore_coprime_card (p := p) (G := X)).symm
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : t * x * t⁻¹ * x⁻¹ ∈ pPrimeCore p X := by
    have : x * t⁻¹ * x⁻¹ ∈ pPrimeCore p X :=
      Subgroup.Normal.conj_mem inferInstance _ (inv_mem ht) x
    have := mul_mem ht this
    simpa [mul_assoc] using this
  have h2 : t * x * t⁻¹ * x⁻¹ ∈ pCore p X :=
    mul_mem (Subgroup.Normal.conj_mem inferInstance x hx t) (inv_mem hx)
  have h3 : t * x * t⁻¹ * x⁻¹ ∈ pPrimeCore p X ⊓ pCore p X := ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot] at h3
  calc x * t = t * x * t⁻¹ * x⁻¹ * (x * t) := by rw [h3, one_mul]
    _ = t * x := by group

omit [Group.IsPerfect X] [K.Normal] [IsSimpleGroup (X ⧸ K)] in
theorem centralizer_pCore_three_le (hK : Group.IsSolvable K)
    (h3S : Subgroup.centralizer (pCore 3 X : Set X) ≤ K) :
    Subgroup.centralizer (pCore 3 (X ⧸ pPrimeCore 3 X) : Set (X ⧸ pPrimeCore 3 X)) ≤
      pCore 3 (X ⧸ pPrimeCore 3 X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := pPrimeCore 3 X with hTdef
  have : T.Normal := pPrimeCore_normal
  set Q := pCore 3 (X ⧸ T) with hQdef
  have : Q.Normal := pCore_normal
  have : (pCore 3 X).Normal := pCore_normal
  set C := Subgroup.centralizer (Q : Set (X ⧸ T)) with hCdef
  have hTO : T ⊓ pCore 3 X = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 3 (pCore 3 X)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (pPrimeCore_coprime_card (p := 3) (G := X)).symm
  have hQhat : (pCore 3 X).map (QuotientGroup.mk' T) ≤ Q :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective T),
      pCore_isPGroup.map _⟩
  have hCK : C ≤ K.map (QuotientGroup.mk' T) := by
    intro c hc
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨y, h3S ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ (hQhat ⟨x, hx, rfl⟩)
    change (QuotientGroup.mk x : X ⧸ T) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk x at h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    have h2 : (x * y)⁻¹ * (y * x) ∈ pCore 3 X := by
      have hyx : y * x * y⁻¹ ∈ pCore 3 X := Subgroup.Normal.conj_mem inferInstance x hx y
      have : (x * y)⁻¹ * (y * x) = y⁻¹ * (x⁻¹ * (y * x * y⁻¹)) * y := by group
      rw [this]
      exact Subgroup.Normal.conj_mem' inferInstance _
        (mul_mem (inv_mem hx) hyx) y
    have h3 : (x * y)⁻¹ * (y * x) ∈ T ⊓ pCore 3 X := ⟨h1, h2⟩
    rw [hTO, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact h3
  have hCsol : Group.IsSolvable C := by
    have : Group.IsSolvable (K.map (QuotientGroup.mk' T)) := by
      have := hK
      exact Group.isSolvable_of_surjective ((QuotientGroup.mk' T).subgroupMap_surjective K)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCK)
  have hFY : fittingSubgroup (X ⧸ T) ≤ Q := by
    rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun q => ?_
    have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
    have : Fact (q : ℕ).Prime := ⟨hq⟩
    by_cases hq3 : (q : ℕ) = 3
    · rw [hq3]
    · have hle : pCore (q : ℕ) (X ⧸ T) ≤ pPrimeCore 3 (X ⧸ T) := by
        refine le_sSup ⟨pCore_normal, ?_⟩
        obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup (q : ℕ) (pCore (q : ℕ) (X ⧸ T))).exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hq).mpr (Ne.symm hq3))
      rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3] at hle
      exact hle.trans bot_le
  have hFC : (fittingSubgroup C).map C.subtype ≤ Q :=
    (le_sSup ⟨inferInstance, Group.nilpotent_of_surjective (C.subtype.subgroupMap
      (fittingSubgroup C)) (C.subtype.subgroupMap_surjective _)⟩ :
        _ ≤ fittingSubgroup (X ⧸ T)).trans hFY
  have hCC := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hCsol
  intro c hc
  have hmem : (⟨c, hc⟩ : C) ∈ Subgroup.centralizer (fittingSubgroup C : Set C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc (f : X ⧸ T) (hFC ⟨f, hf, rfl⟩)
  exact hFC ⟨⟨c, hc⟩, hCC hmem, rfl⟩

theorem linearOutcome_three (h3 : PrimeThreeLinear) (hK : Group.IsSolvable K)
    (h3S : Subgroup.centralizer (pCore 3 X : Set X) ≤ K)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) :
    ∃ (N : Subgroup X) (_ : N.Normal), LinearOutcome X 3 N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := pPrimeCore 3 X with hTdef
  have : T.Normal := pPrimeCore_normal
  set Q := pCore 3 (X ⧸ T) with hQdef
  have : Q.Normal := pCore_normal
  have hN : (Q.comap (QuotientGroup.mk' T)).Normal := Subgroup.Normal.comap inferInstance _
  have hC := centralizer_pCore_three_le hK h3S
  have hT3 : ¬ 3 ∣ Nat.card T :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp pPrimeCore_coprime_card
  have hrankY : CFSG.pRank 3 (X ⧸ T) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_quotient_eq T hT3]
    exact hrank
  have hTK : T ≤ K := (pPrimeCore_le_centralizer_pCore 3).trans h3S
  have hQtop : Q ≠ ⊤ := by
    intro hQ
    have hpg : IsPGroup 3 (X ⧸ T) := fun y => by
      have hy : y ∈ Q := by
        rw [hQ]
        exact Subgroup.mem_top y
      obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 3 Q) ⟨y, hy⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have : Group.IsNilpotent (X ⧸ T) := hpg.isNilpotent
    by_cases hnt : Nontrivial (X ⧸ T)
    · exact Group.IsPerfect.not_isSolvable (X ⧸ T) inferInstance
    · have hTtop : T = ⊤ := by
        by_contra h
        exact hnt (QuotientGroup.nontrivial_iff.mpr h)
      have hKtop : K = ⊤ := top_le_iff.mp (hTtop ▸ hTK)
      exact (QuotientGroup.nontrivial_iff.mp inferInstance) hKtop
  have hcop : ∀ y ∈ Q.comap (QuotientGroup.mk' T), Nat.Coprime (orderOf y) 3 →
      ∀ x ∈ pCore 3 X, y * x = x * y := by
    intro y hy hy3 x hx
    have hyT : y ∈ T := by
      obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 3 Q) ⟨_, hy⟩
      have h1 : orderOf (QuotientGroup.mk y : X ⧸ T) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
      have h2 : orderOf (QuotientGroup.mk y : X ⧸ T) ∣ orderOf y :=
        orderOf_map_dvd (QuotientGroup.mk' T) y
      have h3' : orderOf (QuotientGroup.mk y : X ⧸ T) = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k hy3) h2 h1
      rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3'
      exact h3'
    exact (Subgroup.mem_centralizer_iff.mp (pPrimeCore_le_centralizer_pCore 3 hyT) x hx).symm
  rcases h3 (X ⧸ T) inferInstance hC hrankY hQtop with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact ⟨_, hN, hcop, Or.inr (Or.inr ⟨rfl, ⟨(quotientComapEquiv T Q).trans e⟩⟩)⟩
  · exact ⟨_, hN, hcop, Or.inr (Or.inl ⟨(quotientComapEquiv T Q).trans e⟩)⟩

end Three

theorem rank3II_4_4_partOne (h3 : PrimeThreeLinear) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) [Group.IsPerfect G] {K : Subgroup G} [K.Normal]
    (hK : Group.IsSolvable K) [IsSimpleGroup (G ⧸ K)] (hO2 : pCore 2 G ≠ ⊥) :
    IsQuasisimple (G ⧸ pCore 2 G) ∨
      Nonempty (G ⧸ oTwoFitting G ≃* SL(2, ZMod 5)) ∨
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧ Nonempty (G ⧸ oTwoP p G ≃* SL(2, ZMod p))) ∨
      (Nonempty (G ⧸ oTwoP 3 G ≃* projSL 3 (GaloisField 3 1)) ∨
        IsExtOf (G ⧸ oTwoP 3 G) (alternatingGroup (Fin 5)) Q8D8) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCore 2 G with hPdef
  have : P.Normal := pCore_normal
  have hPK : P ≤ K := pCore_le 2
  set KX := K.map (QuotientGroup.mk' P) with hKXdef
  have : KX.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective P)
  have hKX : Group.IsSolvable KX := by
    have := hK
    exact Group.isSolvable_of_surjective ((QuotientGroup.mk' P).subgroupMap_surjective K)
  have : IsSimpleGroup ((G ⧸ P) ⧸ KX) :=
    (QuotientGroup.quotientQuotientEquivQuotient P K hPK).isSimpleGroup
  by_cases hq : IsQuasisimple (G ⧸ P)
  · exact Or.inl hq
  obtain ⟨p₀, hp₀, hS₀⟩ := exists_centralizer_pCore_le hKX hq
  have hO2X : pCore 2 (G ⧸ P) = ⊥ := ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hlin : ∀ p : ℕ, p.Prime → Subgroup.centralizer (pCore p (G ⧸ P) : Set (G ⧸ P)) ≤ KX →
      ∃ (N : Subgroup (G ⧸ P)) (_ : N.Normal), LinearOutcome (G ⧸ P) p N := by
    intro p hp hpS
    have : Fact p.Prime := ⟨hp⟩
    have hPne : pCore p (G ⧸ P) ≠ ⊥ := by
      intro h
      have htop : (⊤ : Subgroup (G ⧸ P)) ≤
          Subgroup.centralizer (pCore p (G ⧸ P) : Set (G ⧸ P)) := by
        intro g _
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [h] at hx
        rw [(Subgroup.mem_bot).mp hx, one_mul, mul_one]
      exact (QuotientGroup.nontrivial_iff.mp inferInstance) (top_le_iff.mp (htop.trans hpS))
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hPne hO2X
    rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
    · refine linearOutcome_three h3 hKX hpS ?_
      rw [pRank_quotient_pCore_two hO2 hp hp2]
      exact SectionFourHyp.localRank_three_le hG
    · obtain ⟨D, hD⟩ := exists_criticalAt hp2 hPne
      have hrank : CFSG.pRank p D ≤ 2 := by
        have h1 := pRank_le_pRank_top hp D
        rw [pRank_quotient_pCore_two hO2 hp hp2] at h1
        have h2 := hG.localRank_lt p hp hp3
        omega
      exact linearOutcome_of_criticalAt hKX hp3 hpS hD hrank
  rcases linear_endgame hKX hO2X hp₀ hS₀ hlin with ⟨⟨e⟩⟩ | ⟨p, hp, hp3, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inr (Or.inl ⟨(quotientComapEquiv P (fittingSubgroup (G ⧸ P))).trans e⟩)
  · have : Fact p.Prime := ⟨hp⟩
    exact Or.inr (Or.inr (Or.inl ⟨p, hp, hp3,
      ⟨(quotientComapEquiv P (pCore p (G ⧸ P))).trans e⟩⟩))
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨((quotientComapEquiv P (pCore 3 (G ⧸ P))).trans e).trans sl3EquivProjSL⟩)))

end CFSG.RankThree.PartTwo.Sec4.Census
