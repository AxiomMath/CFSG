module

public import CFSG.Sporadic.SuzRecog.ModelGroups
public import CFSG.Sporadic.SuzRecog.C1ModelNorm
public import CFSG.Sporadic.SuzRecog.GluingProof
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.Sporadic.SuzRecog.C1ModelCent
public import CFSG.Sporadic.SuzRecog.ChartGluing
public import Certificates.Certificate15088Base
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

public section

namespace CFSG.Sporadic.SuzRecog.B0Gluing

open Subgroup CFSG.Sporadic.SuzOddCore

section IndexTwo

variable {N G : Type*} [Group N] [Group G]

theorem exists_hom_of_index_two {K : Subgroup N} {τ : N} (hτK : τ ∉ K) (hτ : τ * τ = 1)
    (hnorm : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K) (hcov : ∀ n : N, n ∈ K ∨ n * τ ∈ K) (φ : K →* G)
    (τ' : G) (hτ' : τ' * τ' = 1)
    (hcompat : ∀ k (hk : k ∈ K), φ ⟨τ * k * τ⁻¹, hnorm k hk⟩ = τ' * φ ⟨k, hk⟩ * τ'⁻¹) :
    ∃ ψ : N →* G, (∀ k (hk : k ∈ K), ψ k = φ ⟨k, hk⟩) ∧ ψ τ = τ' := by
  classical
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hmτ : ∀ n, n ∉ K → n * τ ∈ K := fun n hn => (hcov n).resolve_left hn
  have hconj : ∀ k ∈ K, τ * k * τ ∈ K := fun k hk => by
    have := hnorm k hk
    rwa [hτi] at this
  let φ' : N → G := fun n => if h : n ∈ K then φ ⟨n, h⟩ else 1
  have φ'_eq : ∀ n (h : n ∈ K), φ' n = φ ⟨n, h⟩ := fun n h => dite_eq_left h
  have φ'_mul : ∀ a b, a ∈ K → b ∈ K → φ' (a * b) = φ' a * φ' b := fun a b ha hb => by
    rw [φ'_eq _ (mul_mem ha hb), φ'_eq a ha, φ'_eq b hb, ← map_mul]
    rfl
  have hcomm : ∀ k, k ∈ K → τ' * φ' k = φ' (τ * k * τ) * τ' := by
    intro k hk
    have h := hcompat k hk
    rw [φ'_eq k hk, φ'_eq _ (hconj k hk)]
    have e : (⟨τ * k * τ, hconj k hk⟩ : K) = ⟨τ * k * τ⁻¹, hnorm k hk⟩ := by
      apply Subtype.ext
      show τ * k * τ = τ * k * τ⁻¹
      rw [hτi]
    rw [e, h, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
  let f : N → G := fun n => if n ∈ K then φ' n else φ' (n * τ) * τ'
  have f_in : ∀ n, n ∈ K → f n = φ' n := fun n h => ite_eq_left h
  have f_out : ∀ n, n ∉ K → f n = φ' (n * τ) * τ' := fun n h => ite_eq_right h
  have f_mul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    by_cases ha : a ∈ K <;> by_cases hb : b ∈ K
    · rw [f_in _ (mul_mem ha hb), f_in a ha, f_in b hb, φ'_mul a b ha hb]
    · have hab : a * b ∉ K := fun h => hb (by simpa using mul_mem (inv_mem ha) h)
      rw [f_out _ hab, f_in a ha, f_out b hb, mul_assoc a b τ, φ'_mul a _ ha (hmτ b hb),
        mul_assoc]
    · have hab : a * b ∉ K := fun h => ha (by simpa using mul_mem h (inv_mem hb))
      have e : a * b * τ = a * τ * (τ * b * τ) := by
        calc a * b * τ = a * (τ * τ) * b * τ := by rw [hτ, mul_one]
          _ = a * τ * (τ * b * τ) := by group
      rw [f_out _ hab, f_out a ha, f_in b hb, e, φ'_mul _ _ (hmτ a ha) (hconj b hb),
        mul_assoc (φ' (a * τ)) τ' (φ' b), hcomm b hb, ← mul_assoc]
    · have hτb : τ * b ∈ K := by
        have := hconj _ (hmτ b hb)
        rwa [mul_assoc, mul_assoc, hτ, mul_one] at this
      have hab : a * b ∈ K := by
        have := mul_mem (hmτ a ha) hτb
        rwa [mul_assoc, ← mul_assoc τ, hτ, one_mul] at this
      have e : a * b = a * τ * (τ * (b * τ) * τ) := by
        calc a * b = a * (τ * τ) * b * (τ * τ) := by rw [hτ, mul_one, mul_one]
          _ = a * τ * (τ * (b * τ) * τ) := by group
      rw [f_in _ hab, f_out a ha, f_out b hb, e, φ'_mul _ _ (hmτ a ha) (hconj _ (hmτ b hb)),
        mul_assoc (φ' (a * τ)) τ' (φ' (b * τ) * τ'), ← mul_assoc τ' (φ' (b * τ)) τ',
        hcomm _ (hmτ b hb), mul_assoc (φ' (τ * (b * τ) * τ)) τ' τ', hτ', mul_one]
  let ψ : N →* G :=
    { toFun := f
      map_one' := by
        rw [f_in 1 (one_mem K), φ'_eq 1 (one_mem K)]
        exact map_one φ
      map_mul' := f_mul }
  refine ⟨ψ, fun k hk => (f_in k hk).trans (φ'_eq k hk), ?_⟩
  show f τ = τ'
  rw [f_out τ hτK, hτ, φ'_eq 1 (one_mem K)]
  have e : (⟨1, one_mem K⟩ : K) = 1 := rfl
  rw [e, map_one, one_mul]

end IndexTwo

section Identities

variable {P : Type*} [Group P]

theorem conj_mem_centralizer {S : Subgroup P} {c g : P} (hc : c ∈ normalizer (S : Set P))
    (hg : g ∈ centralizer (S : Set P)) : c * g * c⁻¹ ∈ centralizer (S : Set P) := by
  rw [mem_centralizer_iff]
  intro s hs
  have hs' : c⁻¹ * s * c ∈ S := by
    have := (mem_normalizer_iff.1 (inv_mem hc) s).1 hs
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 hg _ hs'
  calc s * (c * g * c⁻¹) = c * ((c⁻¹ * s * c) * g) * c⁻¹ := by group
    _ = c * (g * (c⁻¹ * s * c)) * c⁻¹ := by rw [e]
    _ = c * g * c⁻¹ * s := by group

theorem conj_commute_of_inverts {t x r : P} (ht : t * r * t⁻¹ = r⁻¹) (hx : Commute x r) :
    Commute (t * x * t⁻¹) r := by
  have ht' : t * r⁻¹ * t⁻¹ = r := by
    rw [show t * r⁻¹ * t⁻¹ = (t * r * t⁻¹)⁻¹ by group, ht, inv_inv]
  have hxi : Commute x r⁻¹ := hx.inv_right
  have e1 : r = t * r⁻¹ * t⁻¹ := ht'.symm
  calc t * x * t⁻¹ * r = t * x * t⁻¹ * (t * r⁻¹ * t⁻¹) := by rw [← e1]
    _ = t * (x * r⁻¹) * t⁻¹ := by group
    _ = t * (r⁻¹ * x) * t⁻¹ := by rw [hxi.eq]
    _ = t * r⁻¹ * t⁻¹ * (t * x * t⁻¹) := by group
    _ = r * (t * x * t⁻¹) := by rw [ht']

theorem conj_mul_conj (t a b : P) : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by
  group

theorem conj_conj_of_mul_self {t h : P} (ht : t * t = 1) : t * (t * h * t⁻¹) * t⁻¹ = h := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [hti, ← mul_assoc, ← mul_assoc, ht, one_mul, mul_assoc, ht, mul_one]

theorem mul_mul_conj_of_mul_self {t a b : P} (ht : t * t = 1) :
    a * t * (t * b * t) = a * b * t := by
  calc a * t * (t * b * t) = a * (t * t) * b * t := by group
    _ = a * b * t := by rw [ht, mul_one]

theorem mul_mul_conj_mul_of_mul_self {t a b : P} (ht : t * t = 1) :
    a * t * (t * (b * t) * t) = a * b := by
  calc a * t * (t * (b * t) * t) = a * (t * t) * b * (t * t) := by group
    _ = a * b := by rw [ht, mul_one, mul_one]

theorem conj_inv_mul_of_mul_self {t a : P} (ht : t * t = 1) : t * (a * t)⁻¹ * t = a⁻¹ * t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [mul_inv_rev, hti, ← mul_assoc, ht, one_mul]

end Identities

section Base

local notation "τ₀" => C1Model.tau0

theorem tau0_conj_mem_J0 {x : Equiv.Perm (Fin 1782)} (hx : x ∈ C1Model.J0) :
    τ₀ * x * τ₀⁻¹ ∈ C1Model.J0 := by
  have hC := conj_mem_centralizer (mem_inf.1 C1Model.tau0_mem_B0).2
    (C1Model.J0_le_centralizer_R0 hx)
  have hρ : Commute (τ₀ * x * τ₀⁻¹) Model.rho1 :=
    conj_commute_of_inverts C1Model.tau0_conj_rho1 (C1Model.mem_J0_iff.1 hx).2.2.1
  have hw := mem_centralizer_iff.1 hC _ C1Model.w0_mem_R0
  have hr := mem_centralizer_iff.1 hC _ C1Model.r1_mem_R0
  exact C1Model.mem_J0_iff.2 ⟨hw.symm, hr.symm, hρ.eq,
    mul_mem (mul_mem ModelGroups.tau0_mem_suzM (C1Model.J0_le_suzM hx))
      (inv_mem ModelGroups.tau0_mem_suzM)⟩

theorem tau0_mem_normalizer_J0 :
    τ₀ ∈ normalizer (C1Model.J0 : Set (Equiv.Perm (Fin 1782))) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => tau0_conj_mem_J0 hh, fun hh => ?_⟩
  have := tau0_conj_mem_J0 hh
  rwa [conj_conj_of_mul_self C1Model.tau0_mul_self] at this

theorem tau0_conj_mem_A40 {x : Equiv.Perm (Fin 1782)} (hx : x ∈ C1Model.A40) :
    τ₀ * x * τ₀⁻¹ ∈ C1Model.A40 :=
  mem_inf.2 ⟨conj_mem_centralizer tau0_mem_normalizer_J0 (mem_inf.1 hx).1,
    mul_mem (mul_mem ModelGroups.tau0_mem_suzM (mem_inf.1 hx).2)
      (inv_mem ModelGroups.tau0_mem_suzM)⟩

theorem J0_le_NR0 : C1Model.J0 ≤ Model.NR0 := fun _ hx =>
  ModelGroups.mem_NR0.2 ⟨C1Model.J0_le_suzM hx,
    ModelGroups.mem_normalizer_R0_of_mem_centralizer (C1Model.J0_le_centralizer_R0 hx)⟩

@[expose] noncomputable def tauN : ↥Model.NR0 := ⟨τ₀, ModelGroups.tau0_mem_NR0⟩

theorem tauN_mul_self : tauN * tauN = 1 := Subtype.ext C1Model.tau0_mul_self

theorem tauN_inv : tauN⁻¹ = tauN := inv_eq_of_mul_eq_one_right tauN_mul_self

section A40

theorem w0_mem_A40 : Model.w0 ∈ C1Model.A40 :=
  C1Model.closure_le_A40 (subset_closure (Set.mem_insert _ _))

theorem rho1_mem_A40 : Model.rho1 ∈ C1Model.A40 :=
  C1Model.closure_le_A40 (subset_closure (Set.mem_insert_of_mem _ rfl))

theorem A40_le_NR0 : C1Model.A40 ≤ Model.NR0 := by
  rw [C1Model.A40_eq, closure_le]
  rintro x (rfl | rfl)
  · exact ModelGroups.w0_mem_NR0
  · exact ModelGroups.rho1_mem_NR0

@[expose] noncomputable def mulMap : ↥C1Model.J0 × ↥C1Model.A40 →* ↥Model.NR0 :=
  (inclusion J0_le_NR0).noncommCoprod (inclusion A40_le_NR0) fun j a => by
    apply Subtype.ext
    show (j : Equiv.Perm (Fin 1782)) * a = a * j
    exact mem_centralizer_iff.1 (mem_inf.1 a.2).1 _ j.2

theorem coe_mulMap (p : ↥C1Model.J0 × ↥C1Model.A40) :
    ((mulMap p : ↥Model.NR0) : Equiv.Perm (Fin 1782)) =
      (p.1 : Equiv.Perm (Fin 1782)) * (p.2 : Equiv.Perm (Fin 1782)) :=
  rfl

theorem tauN_conj_mulMap (p : ↥C1Model.J0 × ↥C1Model.A40) :
    tauN * mulMap p * tauN⁻¹ =
      mulMap (⟨τ₀ * p.1 * τ₀⁻¹, tau0_conj_mem_J0 p.1.2⟩,
        ⟨τ₀ * p.2 * τ₀⁻¹, tau0_conj_mem_A40 p.2.2⟩) := by
  apply Subtype.ext
  show τ₀ * ((p.1 : Equiv.Perm (Fin 1782)) * p.2) * τ₀⁻¹ =
    (τ₀ * p.1 * τ₀⁻¹) * (τ₀ * p.2 * τ₀⁻¹)
  exact conj_mul_conj _ _ _

theorem tauN_conj_mem_range {k : ↥Model.NR0} (hk : k ∈ mulMap.range) :
    tauN * k * tauN⁻¹ ∈ mulMap.range := by
  obtain ⟨p, rfl⟩ := hk
  exact ⟨_, (tauN_conj_mulMap p).symm⟩

theorem mem_range_or_mul_tauN (n : ↥Model.NR0) :
    n ∈ mulMap.range ∨ n * tauN ∈ mulMap.range := by
  set K := mulMap.range
  have hτK : tauN * tauN ∈ K := by rw [tauN_mul_self]; exact one_mem K
  have hconj : ∀ k ∈ K, tauN * k * tauN ∈ K := fun k hk => by
    have := tauN_conj_mem_range hk
    rwa [tauN_inv] at this
  have hJ : ∀ x (hx : x ∈ C1Model.J0), (⟨x, J0_le_NR0 hx⟩ : ↥Model.NR0) ∈ K := fun x hx =>
    ⟨(⟨x, hx⟩, 1), Subtype.ext (by rw [coe_mulMap]; exact mul_one x)⟩
  have hA : ∀ x (hx : x ∈ C1Model.A40), (⟨x, A40_le_NR0 hx⟩ : ↥Model.NR0) ∈ K := fun x hx =>
    ⟨(1, ⟨x, hx⟩), Subtype.ext (by rw [coe_mulMap]; exact one_mul x)⟩
  have hgen : (n : Equiv.Perm (Fin 1782)) ∈
      closure {suzInv 1, C1Model.zJ0, Model.w0, Model.rho1, τ₀} := by
    rw [← ModelGroups.NR0_eq_closure]
    exact n.2
  suffices h : ∀ x (hx : x ∈ closure {suzInv 1, C1Model.zJ0, Model.w0, Model.rho1, τ₀})
      (hN : x ∈ Model.NR0), (⟨x, hN⟩ : ↥Model.NR0) ∈ K ∨ ⟨x, hN⟩ * tauN ∈ K from h _ hgen n.2
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    intro hN
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (hJ _ C1Model.suzInv_one_mem_J0)
    · exact Or.inl (hJ _ C1Model.zJ0_mem_J0)
    · exact Or.inl (hA _ w0_mem_A40)
    · exact Or.inl (hA _ rho1_mem_A40)
    · exact Or.inr hτK
  | one => exact fun _ => Or.inl (one_mem K)
  | mul x y hx hy ihx ihy =>
    intro hN
    have hxN : x ∈ Model.NR0 := by rw [ModelGroups.NR0_eq_closure]; exact hx
    have hyN : y ∈ Model.NR0 := by rw [ModelGroups.NR0_eq_closure]; exact hy
    have e : (⟨x * y, hN⟩ : ↥Model.NR0) = ⟨x, hxN⟩ * ⟨y, hyN⟩ := rfl
    rw [e]
    rcases ihx hxN with ha | ha <;> rcases ihy hyN with hb | hb
    · exact Or.inl (mul_mem ha hb)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem ha hb)
    · refine Or.inr ?_
      have := mul_mem ha (hconj _ hb)
      rwa [mul_mul_conj_of_mul_self tauN_mul_self] at this
    · refine Or.inl ?_
      have := mul_mem ha (hconj _ hb)
      rwa [mul_mul_conj_mul_of_mul_self tauN_mul_self] at this
  | inv x hx ihx =>
    intro hN
    have hxN : x ∈ Model.NR0 := by rw [ModelGroups.NR0_eq_closure]; exact hx
    have e : (⟨x⁻¹, hN⟩ : ↥Model.NR0) = (⟨x, hxN⟩ : ↥Model.NR0)⁻¹ := rfl
    rw [e]
    rcases ihx hxN with ha | ha
    · exact Or.inl (inv_mem ha)
    · refine Or.inr ?_
      have := hconj _ (inv_mem ha)
      rwa [conj_inv_mul_of_mul_self tauN_mul_self] at this

theorem card_range_mulMap : Nat.card mulMap.range = 241920 := by
  set K := mulMap.range
  have hle : Nat.card K ≤ 241920 := by
    have h := Nat.card_le_card_of_surjective _ mulMap.rangeRestrict_surjective
    rwa [Nat.card_prod, C1Model.card_J0, C1Model.card_A40] at h
  have hge : 483840 ≤ 2 * Nat.card K := by
    let f : K ⊕ K → ↥Model.NR0 := Sum.elim (fun k => k) (fun k => k * tauN)
    have hf : Function.Surjective f := by
      intro n
      rcases mem_range_or_mul_tauN n with h | h
      · exact ⟨Sum.inl ⟨n, h⟩, rfl⟩
      · refine ⟨Sum.inr ⟨n * tauN, h⟩, ?_⟩
        show n * tauN * tauN = n
        rw [mul_assoc, tauN_mul_self, mul_one]
    have h := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_sum, ModelGroups.card_NR0] at h
    omega
  omega

theorem mulMap_injective : Function.Injective mulMap := by
  have hb := mulMap.rangeRestrict_surjective.bijective_of_nat_card_le (by
    rw [Nat.card_prod, C1Model.card_J0, C1Model.card_A40, card_range_mulMap])
  intro p q h
  exact hb.1 (Subtype.ext h)

theorem tauN_not_mem_range : tauN ∉ mulMap.range := by
  intro h
  have htop : mulMap.range = ⊤ := by
    rw [eq_top_iff]
    intro n _
    rcases mem_range_or_mul_tauN n with hn | hn
    · exact hn
    · have := mul_mem hn (inv_mem h)
      rwa [mul_inv_cancel_right] at this
  have := card_range_mulMap
  rw [htop, Subgroup.card_top, ModelGroups.card_NR0] at this
  exact absurd this (by norm_num)

theorem exists_hom_NR0 {G : Type*} [Group G]
    (α : ↥C1Model.J0 →* G) (β : ↥C1Model.A40 →* G) (τ' : G)
    (hcomm : ∀ j : ↥C1Model.J0, ∀ a : ↥C1Model.A40, α j * β a = β a * α j)
    (hτ2 : τ' * τ' = 1)
    (hτα : ∀ x (hx : x ∈ C1Model.J0) (hx' : C1Model.tau0 * x * C1Model.tau0⁻¹ ∈ C1Model.J0),
      α ⟨_, hx'⟩ = τ' * α ⟨x, hx⟩ * τ'⁻¹)
    (hτβ : ∀ x (hx : x ∈ C1Model.A40) (hx' : C1Model.tau0 * x * C1Model.tau0⁻¹ ∈ C1Model.A40),
      β ⟨_, hx'⟩ = τ' * β ⟨x, hx⟩ * τ'⁻¹) :
    ∃ ψ : ↥Model.NR0 →* G,
      (∀ x (hx : x ∈ C1Model.J0) (hxN : x ∈ Model.NR0), ψ ⟨x, hxN⟩ = α ⟨x, hx⟩) ∧
      (∀ x (hx : x ∈ C1Model.A40) (hxN : x ∈ Model.NR0), ψ ⟨x, hxN⟩ = β ⟨x, hx⟩) ∧
      ∀ hN : C1Model.tau0 ∈ Model.NR0, ψ ⟨C1Model.tau0, hN⟩ = τ' := by
  set K := mulMap.range
  let e : ↥C1Model.J0 × ↥C1Model.A40 ≃* K := MonoidHom.ofInjective mulMap_injective
  let φ₀ : ↥C1Model.J0 × ↥C1Model.A40 →* G := α.noncommCoprod β fun j a => hcomm j a
  let φ : K →* G := φ₀.comp e.symm.toMonoidHom
  have hφ : ∀ p, φ ⟨mulMap p, ⟨p, rfl⟩⟩ = α p.1 * β p.2 := by
    intro p
    have : e.symm ⟨mulMap p, ⟨p, rfl⟩⟩ = p := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (MonoidHom.ofInjective_apply mulMap_injective).symm
    show φ₀ (e.symm _) = _
    rw [this]
    rfl
  have hcompat : ∀ k (hk : k ∈ K), φ ⟨tauN * k * tauN⁻¹, tauN_conj_mem_range hk⟩ =
      τ' * φ ⟨k, hk⟩ * τ'⁻¹ := by
    rintro _ ⟨p, rfl⟩
    have e1 : (⟨tauN * mulMap p * tauN⁻¹, tauN_conj_mem_range ⟨p, rfl⟩⟩ : K) =
        ⟨mulMap _, ⟨_, rfl⟩⟩ := Subtype.ext (tauN_conj_mulMap p)
    rw [e1, hφ, hφ, hτα _ p.1.2, hτβ _ p.2.2]
    group
  obtain ⟨ψ, hψ, hψτ⟩ := exists_hom_of_index_two tauN_not_mem_range tauN_mul_self
    (fun k hk => tauN_conj_mem_range hk) mem_range_or_mul_tauN φ τ' hτ2 hcompat
  refine ⟨ψ, fun x hx hxN => ?_, fun x hx hxN => ?_, fun hN => hψτ⟩
  · have hk : (⟨x, hxN⟩ : ↥Model.NR0) = mulMap (⟨x, hx⟩, 1) :=
      Subtype.ext (by simp [coe_mulMap])
    rw [hk, hψ _ ⟨_, rfl⟩, hφ, map_one, mul_one]
  · have hk : (⟨x, hxN⟩ : ↥Model.NR0) = mulMap (1, ⟨x, hx⟩) :=
      Subtype.ext (by simp [coe_mulMap])
    rw [hk, hψ _ ⟨_, rfl⟩, hφ, map_one, one_mul]

end A40

end Base

section Agree

theorem b0Agree_of {G : Type} [Group G] {M : Subgroup G} (σ : M ≃* invE 1)
    (ψ : ↥Model.NR0 →* G)
    (hT : ∀ i < 4, ∀ (h1 : C1Model.t0Gen i ∈ invE 1) (h2 : C1Model.t0Gen i ∈ Model.NR0),
      ψ ⟨_, h2⟩ = (σ.symm ⟨_, h1⟩ : G))
    (hw : ∀ (h1 : Model.w0 ∈ invE 1) (h2 : Model.w0 ∈ Model.NR0),
      ψ ⟨_, h2⟩ = (σ.symm ⟨_, h1⟩ : G))
    (hr : ∀ (h1 : Model.rho1 ∈ invE 1) (h2 : Model.rho1 ∈ Model.NR0),
      ψ ⟨_, h2⟩ = (σ.symm ⟨_, h1⟩ : G))
    (ht : ∀ (h1 : C1Model.tau0 ∈ invE 1) (h2 : C1Model.tau0 ∈ Model.NR0),
      ψ ⟨_, h2⟩ = (σ.symm ⟨_, h1⟩ : G)) :
    B0Agree σ ψ := by
  intro x hx hxN
  have hB : x ∈ Model.B0 := mem_inf.2 ⟨hx, (ModelGroups.mem_NR0.1 hxN).2⟩
  have hB1 : ∀ y, y ∈ Model.B0 → y ∈ invE 1 := fun y hy => (mem_inf.1 hy).1
  have hBN : ∀ y, y ∈ Model.B0 → y ∈ Model.NR0 := fun y hy =>
    ModelGroups.mem_NR0.2 ⟨C1Model.invE_le_suzM (mem_inf.1 hy).1, (mem_inf.1 hy).2⟩
  rw [C1Model.B0_eq] at hB
  suffices h : ∀ y (hy : y ∈ closure ({g | ∃ i < 4, C1Model.t0Gen i = g} ∪
      {Model.w0, Model.rho1, C1Model.tau0})) (h1 : y ∈ invE 1) (h2 : y ∈ Model.NR0),
      ψ ⟨y, h2⟩ = (σ.symm ⟨y, h1⟩ : G) from h x hB hx hxN
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    intro h1 h2
    rcases hy with ⟨i, hi, rfl⟩ | hy
    · exact hT i hi h1 h2
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact hw h1 h2
      · exact hr h1 h2
      · exact ht h1 h2
  | one =>
    intro h1 h2
    have e1 : (⟨1, h2⟩ : ↥Model.NR0) = 1 := rfl
    have e2 : (⟨1, h1⟩ : ↥(invE 1)) = 1 := rfl
    rw [e1, e2, map_one, map_one, Subgroup.coe_one]
  | mul y z hy hz ihy ihz =>
    intro h1 h2
    have hyB : y ∈ Model.B0 := by rw [C1Model.B0_eq]; exact hy
    have hzB : z ∈ Model.B0 := by rw [C1Model.B0_eq]; exact hz
    have e1 : (⟨y * z, h2⟩ : ↥Model.NR0) = ⟨y, hBN y hyB⟩ * ⟨z, hBN z hzB⟩ := rfl
    have e2 : (⟨y * z, h1⟩ : ↥(invE 1)) = ⟨y, hB1 y hyB⟩ * ⟨z, hB1 z hzB⟩ := rfl
    rw [e1, e2, map_mul, map_mul, Subgroup.coe_mul, ihy, ihz]
  | inv y hy ihy =>
    intro h1 h2
    have hyB : y ∈ Model.B0 := by rw [C1Model.B0_eq]; exact hy
    have e1 : (⟨y⁻¹, h2⟩ : ↥Model.NR0) = (⟨y, hBN y hyB⟩ : ↥Model.NR0)⁻¹ := rfl
    have e2 : (⟨y⁻¹, h1⟩ : ↥(invE 1)) = (⟨y, hB1 y hyB⟩ : ↥(invE 1))⁻¹ := rfl
    rw [e1, e2, map_inv, map_inv, Subgroup.coe_inv, ihy]

end Agree

end CFSG.Sporadic.SuzRecog.B0Gluing
