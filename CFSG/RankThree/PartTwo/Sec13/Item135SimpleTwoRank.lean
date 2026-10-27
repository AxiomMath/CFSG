module

public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.RankThree.PartTwo.Census.DoubleCoverLift
import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwoX
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
import CFSG.RankThree.PartTwo.Sec13.Item134Arg128FailHJ
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofPrime
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeCover
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import Certificates.Certificate10019
import Certificates.Certificate10019Base
import Certificates.Certificate3139

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree (isoLThreePi_of_mulEquiv)
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift (E8Datum)

@[expose] def KS135TwoRankCover : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsPGroup 2 (Subgroup.center J) →
    Subgroup.center J ≠ ⊥ →
    (Nonempty (J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      ∃ f : ℕ, 1 ≤ f ∧ Sec4.IsoLThreePi (J ⧸ Subgroup.center J) 2 f) →
    3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup J)

section M22

variable {J X : Type*} [Group J] [Finite J] [Group X]

theorem three_le_pRank_of_e8Datum {φ : J →* X} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) {a₁ a₂ a₃ n : X} (h : E8Datum a₁ a₂ a₃ n) :
    3 ≤ CFSG.pRank 2 J := by
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, s₁, s₂, s₃, c₁₂, c₁₃, c₂₃⟩ := h.exists_lift hφ hker
  refine Sec4.Census.three_le_pRank_of_involutions (by rw [← sq]; exact s₁)
    (by rw [← sq]; exact s₂) (by rw [← sq]; exact s₃) c₁₂.eq c₁₃.eq c₂₃.eq ?_
  intro a b d hprod
  by_contra hne
  have himg := congrArg φ hprod
  simp only [map_mul, map_pow, map_one, hb₁, hb₂, hb₃] at himg
  refine h.prod_ne_one a b d ?_ himg
  intro h0
  exact hne ⟨congrArg Prod.fst h0, congrArg (fun x => x.2.1) h0, congrArg (fun x => x.2.2) h0⟩

theorem three_le_pRank_of_m22 (e : J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.M22) :
    3 ≤ CFSG.pRank 2 J := by
  refine three_le_pRank_of_e8Datum (φ := e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_
    Sec4.Census.DoubleCoverRanks.m22_e8Datum
  intro x hx
  have h1 : e (QuotientGroup.mk' (Subgroup.center J) x) = 1 := hx
  rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end M22

section S3A4

@[expose] def s3a4X : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4) :=
  (Equiv.swap 0 1, 1)

@[expose] def s3a4Y : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4) :=
  (1, ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩)

@[expose] def s3a4C : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4) :=
  (1, ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩)

theorem three_le_pRank_of_injective_s3a4 {J : Type*} [Group J] [Finite J]
    (ψ : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4) →* J) (hψ : Function.Injective ψ) :
    3 ≤ CFSG.pRank 2 J := by
  have hx : s3a4X * s3a4X = 1 := by decide
  have hy : s3a4Y * s3a4Y = 1 := by decide
  have hc : s3a4C * s3a4C = 1 := by decide
  have hxy : s3a4X * s3a4Y = s3a4Y * s3a4X := by decide
  have hxc : s3a4X * s3a4C = s3a4C * s3a4X := by decide
  have hyc : s3a4Y * s3a4C = s3a4C * s3a4Y := by decide
  have hind : ∀ a b d : ZMod 2, s3a4X ^ a.val * s3a4Y ^ b.val * s3a4C ^ d.val = 1 →
      a = 0 ∧ b = 0 ∧ d = 0 := by decide
  refine Sec4.Census.three_le_pRank_of_involutions (x := ψ s3a4X) (y := ψ s3a4Y) (c := ψ s3a4C)
    (by rw [← map_mul, hx, map_one]) (by rw [← map_mul, hy, map_one])
    (by rw [← map_mul, hc, map_one]) (by rw [← map_mul, hxy, map_mul])
    (by rw [← map_mul, hxc, map_mul]) (by rw [← map_mul, hyc, map_mul]) ?_
  intro a b d h
  refine hind a b d (hψ ?_)
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, h, map_one]

variable {J : Type} [Group J] [Finite J]

theorem exists_mem_not_mem_center_of_isHeisThree {P A : Subgroup J} (hP : Sec4.IsHeisThree P)
    (hA9 : Nat.card A = 9) :
    ∃ a ∈ A, a ∉ P ⊓ Subgroup.centralizer (P : Set J) := by
  by_contra h
  push Not at h
  have hle := Subgroup.card_le_of_le (show A ≤ P ⊓ Subgroup.centralizer (P : Set J) from h)
  rw [hA9, Item134Arg128Fail.card_inf_centralizer_of_heis hP] at hle
  omega

theorem three_le_pRank_of_m12 (h414 : Sec4.Item4_14_local)
    (e : J ≃* CFSG.Blueprint.NativeSporadic.M12) : 3 ≤ CFSG.pRank 2 J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 J) := inferInstance
  obtain ⟨hH, -, E, F, A, t, -, -, hΔ, -, -, -, hN⟩ := h414 J ⟨e⟩ P
  have hA : A ∈ {B : Subgroup J | B ≤ P ∧ Nat.card B = 9} := by
    rw [hΔ]
    simp
  obtain ⟨a, haA, haZ⟩ := exists_mem_not_mem_center_of_isHeisThree hH hA.2
  obtain ⟨φ⟩ := hN a haA haZ
  exact three_le_pRank_of_injective_s3a4
    ((Subgroup.normalizer (Subgroup.zpowers a : Set J)).subtype.comp φ.symm.toMonoidHom)
    (Subtype.val_injective.comp φ.symm.injective)

theorem three_le_pRank_of_j2 (h415 : Sec4.Item4_15) (e : J ≃* CFSG.Blueprint.NativeSporadic.J2) :
    3 ≤ CFSG.pRank 2 J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 J) := inferInstance
  have h := h415 J ⟨e⟩ P _ rfl _ rfl
  have hH := h.1.1
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := (P : Subgroup J)) 3 (n := 2)
    (by rw [hH.2.1]; norm_num)
  have hAP : A₀.map (P : Subgroup J).subtype ≤ P := Subgroup.map_subtype_le _
  have hA9 : Nat.card (A₀.map (P : Subgroup J).subtype) = 9 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hA₀]
    norm_num
  obtain ⟨a, haA, haZ⟩ := exists_mem_not_mem_center_of_isHeisThree hH hA9
  obtain ⟨-, ⟨φ⟩, -⟩ := h.2.2.2.1 _ ⟨hAP, hA9⟩ a haA haZ
  exact three_le_pRank_of_injective_s3a4
    ((Subgroup.normalizer (Subgroup.zpowers a : Set J)).subtype.comp φ.symm.toMonoidHom)
    (Subtype.val_injective.comp φ.symm.injective)

end S3A4

section Unitary

open Matrix

variable (f : ℕ)

@[expose] noncomputable def traceQ2 : GaloisField 2 (2 * f) →+ GaloisField 2 (2 * f) where
  toFun a := a + a ^ 2 ^ f
  map_zero' := by rw [zero_pow (pow_ne_zero _ two_ne_zero), add_zero]
  map_add' a b := by rw [add_pow_char_pow]; ring

theorem traceQ2_apply (a : GaloisField 2 (2 * f)) : traceQ2 f a = a + a ^ 2 ^ f := rfl

theorem mem_ker_traceQ2 {a : GaloisField 2 (2 * f)} :
    a ∈ (traceQ2 f).ker ↔ a ^ 2 ^ f = a := by
  rw [AddMonoidHom.mem_ker, traceQ2_apply]
  constructor
  · intro h
    have h' : a ^ 2 ^ f = -a := by linear_combination h
    rw [h', CharTwo.neg_eq]
  · intro h
    rw [h, CharTwo.add_self_eq_zero]

theorem le_card_ker_traceQ2 (hf : 1 ≤ f) : 2 ^ f ≤ Nat.card (traceQ2 f).ker := by
  have hle : (traceQ2 f).range ≤ (traceQ2 f).ker := by
    rintro _ ⟨a, rfl⟩
    rw [mem_ker_traceQ2, traceQ2_apply, add_pow_char_pow]
    have h2 : (a ^ 2 ^ f) ^ 2 ^ f = a := Sec4.Census.frobQ_frobQ hf a
    rw [h2, add_comm]
  have hcard := AddSubgroup.card_mul_index (traceQ2 f).ker
  rw [AddSubgroup.index_ker, GaloisField.card 2 (2 * f) (by omega)] at hcard
  have h1 := AddSubgroup.card_le_of_le hle
  have h3 : (2 ^ f) ^ 2 ≤ Nat.card (traceQ2 f).ker ^ 2 := by
    calc (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
      _ = Nat.card (traceQ2 f).ker * Nat.card (traceQ2 f).range := hcard.symm
      _ ≤ Nat.card (traceQ2 f).ker * Nat.card (traceQ2 f).ker := Nat.mul_le_mul_left _ h1
      _ = Nat.card (traceQ2 f).ker ^ 2 := (sq _).symm
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h3

@[expose] noncomputable def isoLineMat : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f)) :=
  !![1, 1, 0; 1, 1, 0; 0, 0, 0]

@[expose] noncomputable def radU3 :
    (traceQ2 f).ker →+ Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f)) where
  toFun c := (c : GaloisField 2 (2 * f)) • isoLineMat f
  map_zero' := by rw [AddSubgroup.coe_zero, zero_smul]
  map_add' a b := by rw [AddSubgroup.coe_add, add_smul]

theorem radU3_injective : Function.Injective (radU3 f) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
  have h00 := congrFun (congrFun hc 0) 0
  simp [radU3, isoLineMat] at h00
  exact h00

theorem radU3_mul (v w : (traceQ2 f).ker) : radU3 f v * radU3 f w = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radU3, isoLineMat, mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem det_one_add_radU3 (c : (traceQ2 f).ker) : (1 + radU3 f c).det = 1 := by
  have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharTwo.two_eq_zero
  rw [det_fin_three]
  simp [radU3, isoLineMat]
  linear_combination (c : GaloisField 2 (2 * f)) * h2

theorem unitary_one_add_radU3 (c : (traceQ2 f).ker) :
    ((1 + radU3 f c).map (· ^ 2 ^ f))ᵀ * (1 + radU3 f c) = 1 := by
  have hc : (c : GaloisField 2 (2 * f)) ^ 2 ^ f = c := (mem_ker_traceQ2 f).mp c.2
  have h0 : (0 : GaloisField 2 (2 * f)) ^ 2 ^ f = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have h1c : (1 + (c : GaloisField 2 (2 * f))) ^ 2 ^ f = 1 + c := by
    rw [add_pow_char_pow, one_pow, hc]
  have hmap : (1 + radU3 f c).map (· ^ 2 ^ f) = 1 + radU3 f c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [radU3, isoLineMat, hc, h0, h1c]
  have hT : (1 + radU3 f c)ᵀ = 1 + radU3 f c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [radU3, isoLineMat]
  have h2 : radU3 f c + radU3 f c = 0 := by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  rw [hmap, hT]
  calc (1 + radU3 f c) * (1 + radU3 f c) =
        1 + (radU3 f c + radU3 f c) + radU3 f c * radU3 f c := by noncomm_ring
    _ = 1 := by rw [h2, radU3_mul, add_zero, add_zero]

theorem le_pRank_projSU_three {k : ℕ} (hk : Nat.card (traceQ2 f).ker = 2 ^ k) :
    k ≤ CFSG.pRank 2 (projSU 3 2 f) := by
  refine Sec4.Census.le_pRank_of_sqZero (radU3 f) (radU3_injective f) (radU3_mul f)
    (fun c => Subtype.ext ?_) (projSU 3 2 f) (fun c => ?_) hk
  · rw [AddSubgroup.coe_nsmul, two_nsmul, CharTwo.add_self_eq_zero, AddSubgroup.coe_zero]
  · refine ⟨Sec4.Census.sqZeroUnit (radU3 f) (radU3_mul f) c,
      Subgroup.subset_closure ⟨?_, ?_⟩, rfl⟩
    · apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, Units.val_one]
      exact det_one_add_radU3 f c
    · exact unitary_one_add_radU3 f c

end Unitary

section Assembly

variable {J : Type} [Group J] [Finite J]

theorem three_le_pRank_of_isoLThreePi_two (hq : IsQuasisimple J) {f : ℕ} (hf : 1 ≤ f)
    (h : Sec4.IsoLThreePi J 2 f) : 3 ≤ CFSG.pRank 2 J := by
  rcases h with ⟨h3, ⟨φ⟩⟩ | ⟨h3, ⟨φ⟩⟩
  · have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      norm_num at h3
    have : Finite (projSL 3 (GaloisField 2 f)) := Finite.of_equiv J φ.toEquiv
    have hle := Sec17.HeadProof.two_mul_le_pRank_projSL_three (GaloisField 2 f) (p := 2)
      (k := f) (GaloisField.card 2 f (by omega))
    rw [pRank_congr_mulEquiv one_lt_two φ]
    omega
  · by_cases hf1 : f = 1
    · subst hf1
      exfalso
      have hs := isSolvable_projSU_two
      have hsJ : Group.IsSolvable J :=
        Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hq
      have : Group.IsPerfect J := hq.1
      exact Group.IsPerfect.not_isSolvable J hsJ
    · have hf3 : 3 ≤ f := by
        by_contra hlt
        obtain rfl : f = 2 := by omega
        norm_num at h3
      have hdvd := AddSubgroup.card_addSubgroup_dvd_card (traceQ2 f).ker
      rw [GaloisField.card 2 (2 * f) (by omega)] at hdvd
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hle := le_card_ker_traceQ2 f hf
      rw [hk] at hle
      have hfk : f ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
      have : Finite (projSU 3 2 f) := Finite.of_equiv J φ.toEquiv
      have hr := le_pRank_projSU_three f hk
      rw [pRank_congr_mulEquiv one_lt_two φ]
      omega

theorem ks135TwoRank_of_cover (hC : KS135TwoRankCover) (h414 : Sec4.Item4_14_local)
    (h415 : Sec4.Item4_15) : KS135TwoRank := by
  intro J _ _ hq hZ2 htype
  rcases htype with hM | hJ | hM22 | hL
  · by_cases hZ : Subgroup.center J = ⊥
    · obtain ⟨φ⟩ := hM
      let e0 : J ≃* J ⧸ Subgroup.center J :=
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact three_le_pRank_of_m12 h414 (e0.trans φ)
    · exact hC J hq hZ2 hZ (Or.inl hM)
  · by_cases hZ : Subgroup.center J = ⊥
    · obtain ⟨φ⟩ := hJ
      let e0 : J ≃* J ⧸ Subgroup.center J :=
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact three_le_pRank_of_j2 h415 (e0.trans φ)
    · exact hC J hq hZ2 hZ (Or.inr (Or.inl hJ))
  · obtain ⟨φ⟩ := hM22
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact three_le_pRank_of_m22 φ
  · by_cases hZ : Subgroup.center J = ⊥
    · obtain ⟨f, hf, hLf⟩ := hL
      let e0 : J ≃* J ⧸ Subgroup.center J :=
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact three_le_pRank_of_isoLThreePi_two hq hf (isoLThreePi_of_mulEquiv e0 hLf)
    · exact hC J hq hZ2 hZ (Or.inr (Or.inr hL))

end Assembly

end CFSG.RankThree.PartTwo.Sec13
