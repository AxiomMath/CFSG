module

public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofModels
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import Certificates.Certificate8093
public import Certificates.Certificate8095
public import Certificates.Certificate6103
public import Certificates.Certificate15042
public import Certificates.Certificate15043
public import Certificates.Certificate8023
public import Certificates.Certificate2082
public import Certificates.Certificate2168
public import Certificates.Certificate2177
public import Certificates.Certificate3084
public import Certificates.Certificate3017
public import Certificates.Certificate9123
public import Certificates.Certificate9215
public import Certificates.Certificate9250
public import Certificates.Certificate9251
public import Certificates.Certificate9252
public import Certificates.Certificate9253
public import Certificates.Certificate9254
public import Certificates.Certificate9255
public import Certificates.Certificate9256
public import Certificates.Certificate9257
public import Certificates.Certificate9258
public import Certificates.Certificate9259
public import Certificates.Certificate9260
public import Certificates.Certificate9261
public import Certificates.Certificate9262
public import Certificates.Certificate9263
public import Certificates.Certificate9264
public import Certificates.Certificate9265
public import Certificates.Certificate9266
public import Certificates.Certificate9267
public import CFSG.RankThree.PartTwo.Census.DoubleCoverLift
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleTwoRank
public import CFSG.RankThree.PartTwo.Sec13.KS135TwoRankCover
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofHe
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofExc
import CFSG.RankThree.PartTwo.Census.TransitiveLift
import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks
import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksL34
import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverM23
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverJ3
import CFSG.RankThree.PartTwo.Sec4.Census.TwoCoverCensusResidual
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwoX
import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofPrime
import CFSG.Sporadic.Recognition.HeMultiplierCert
import CFSG.Sporadic.Recognition.J4Multiplier
import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4CoverCert
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Sporadic.GLQ.J4TwoRank
import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.Sporadic.Presentation.M24Exact
public import Certificates.Certificate3168
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import Certificates.Certificate8026Base

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

namespace Item21Early2Proof

@[expose] def TwoRankGood (S : Type) [Group S] : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → IsPGroup 2 (Subgroup.center J) →
    Nonempty (J ⧸ Subgroup.center J ≃* S) → 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup J)

theorem TwoRankGood.of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : TwoRankGood T) : TwoRankGood S :=
  fun J _ _ hq hZ ⟨f⟩ => h J hq hZ ⟨f.trans e⟩

@[expose] noncomputable def quotMap {J S : Type*} [Group J] [Group S]
    (e : J ⧸ Subgroup.center J ≃* S) : J →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))

theorem quotMap_surjective {J S : Type*} [Group J] [Group S] (e : J ⧸ Subgroup.center J ≃* S) :
    Function.Surjective (quotMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem quotMap_ker {J S : Type*} [Group J] [Group S] (e : J ⧸ Subgroup.center J ≃* S) :
    (quotMap e).ker = Subgroup.center J := by
  ext x
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk x) = 1 ↔ _
  rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]

theorem twoRankGood_of_e8Datum {S : Type} [Group S] {a₁ a₂ a₃ n : S}
    (h : Sec4.Census.DoubleCoverLift.E8Datum a₁ a₂ a₃ n) : TwoRankGood S := by
  intro J _ _ _ _ ⟨e⟩
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact Sec13.three_le_pRank_of_e8Datum (quotMap_surjective e) (quotMap_ker e).le h

theorem twoRankGood_of_e16Datum {S : Type} [Group S] {a₁ a₂ a₃ a₄ n : S}
    (h : Sec4.Census.SporadicTwoCover.E16Datum a₁ a₂ a₃ a₄ n) : TwoRankGood S := by
  intro J _ _ _ _ ⟨e⟩
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  obtain ⟨b₁, b₂, b₃, -, hb₁, hb₂, hb₃, -, s₁, s₂, s₃, -, c₁₂, c₁₃, -, c₂₃, -, -⟩ :=
    h.exists_lift (quotMap_surjective e) (quotMap_ker e).le
  refine Sec4.Census.three_le_pRank_of_involutions (by rw [← sq]; exact s₁)
    (by rw [← sq]; exact s₂) (by rw [← sq]; exact s₃) c₁₂.eq c₁₃.eq c₂₃.eq ?_
  intro a b d hprod
  by_contra hne
  have himg := congrArg (quotMap e) hprod
  simp only [map_mul, map_pow, map_one, hb₁, hb₂, hb₃] at himg
  refine h.prod_ne_one ![a, b, d, 0] ?_ ?_
  · intro h0
    exact hne ⟨congrFun h0 0, congrFun h0 1, congrFun h0 2⟩
  · have h3 : (![a, b, d, 0] : Fin 4 → Fin 2) 3 = 0 := rfl
    rw [Sec4.Census.SporadicTwoCover.e16Prod, h3]
    simp only [Fin.val_zero, pow_zero, mul_one]
    exact himg

theorem twoRankGood_of_center {S : Type} [Group S] [Finite S]
    (hZ : ∀ (J : Type) [Group J] [Finite J], ¬ Sec4.Census.IsTwoCover J S)
    (hS : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S)) : TwoRankGood S := by
  intro J _ _ hq hZ2 ⟨e⟩
  have hbot : Subgroup.center J = ⊥ := by
    by_contra hne
    exact hZ J ⟨hq, hZ2, (Subgroup.nontrivial_iff_ne_bot _).mpr hne, ⟨e⟩⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
    ((quotCenterEquivOfBot hbot).symm.trans e)]
  exact hS

section M24

open Equiv Sec4.Census.DoubleCoverLift

@[expose] def m24α : Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
    List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] *
    List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] *
    List.formPerm [19, 23] * List.formPerm [21, 22]

@[expose] def m24β : Perm (Fin 24) :=
  List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]

theorem m24α_mem : m24α ∈ NativeSporadic.M24 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem m24β_mem : m24β ∈ NativeSporadic.M24 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def m24Word : List Char → Perm (Fin 24)
  | [] => 1
  | c :: w => (if c = 'a' then m24α else if c = 'b' then m24β else m24β⁻¹) * m24Word w

theorem m24Word_mem : ∀ w, m24Word w ∈ NativeSporadic.M24
  | [] => Subgroup.one_mem _
  | c :: w => by
    unfold m24Word
    refine Subgroup.mul_mem _ ?_ (m24Word_mem w)
    split_ifs
    · exact m24α_mem
    · exact m24β_mem
    · exact Subgroup.inv_mem _ m24β_mem

@[expose] def m24N : Perm (Fin 24) :=
  List.formPerm [0, 11, 6, 15, 7, 12, 2] * List.formPerm [1, 13, 21, 16, 3, 4, 14] *
    List.formPerm [5, 17, 19, 9, 18, 10, 23]

@[expose] def m24X : Perm (Fin 24) :=
  swap 0 13 * swap 1 2 * swap 3 15 * swap 4 7 * swap 6 16 * swap 11 21 * swap 12 14 * swap 20 22

@[expose] def m24G : Perm (Fin 24) :=
  swap 0 21 * List.formPerm [1, 2, 15, 7, 4, 20] * swap 3 22 *
    List.formPerm [6, 11, 12, 14, 13, 16] * List.formPerm [9, 17, 19] * List.formPerm [10, 18, 23]

@[expose] def m24T : Perm (Fin 24) :=
  swap 0 22 * swap 1 16 * swap 2 6 * swap 3 21 * swap 4 14 * swap 7 12 * swap 11 15 * swap 13 20

theorem m24N_eq : m24N = m24Word "aBaBaBabaBB".toList ^ 2 := by
  decide +kernel

theorem m24X_eq : m24X = m24Word "BaBabababa".toList ^ 7 := by
  decide +kernel

theorem m24G_eq : m24G = m24Word "aBabababaBaBaBab".toList := by
  decide +kernel

theorem m24T_eq : m24T = (m24G * m24X * m24G⁻¹)⁻¹ * (m24N * (m24G * m24X * m24G⁻¹) * m24N⁻¹) := by
  decide +kernel

theorem m24N_mem : m24N ∈ NativeSporadic.M24 :=
  m24N_eq ▸ Subgroup.pow_mem _ (m24Word_mem _) 2

theorem m24T_mem : m24T ∈ NativeSporadic.M24 := by
  have hX : m24X ∈ NativeSporadic.M24 := m24X_eq ▸ Subgroup.pow_mem _ (m24Word_mem _) 7
  have hG : m24G ∈ NativeSporadic.M24 := m24G_eq ▸ m24Word_mem _
  have hY : m24G * m24X * m24G⁻¹ ∈ NativeSporadic.M24 :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hG hX) (Subgroup.inv_mem _ hG)
  rw [m24T_eq]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hY)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ m24N_mem hY) (Subgroup.inv_mem _ m24N_mem))

theorem m24_perm_e8Datum : E8Datum m24T (m24N * m24T * m24N⁻¹)
    (m24N * (m24N * m24T * m24N⁻¹) * m24N⁻¹) m24N where
  ne_one := by decide +kernel
  sq := by decide +kernel
  comm₁₂ := (by decide +kernel : m24T * (m24N * m24T * m24N⁻¹) = (m24N * m24T * m24N⁻¹) * m24T)
  comm₁₃ := (by decide +kernel : m24T * (m24N * (m24N * m24T * m24N⁻¹) * m24N⁻¹) =
    (m24N * (m24N * m24T * m24N⁻¹) * m24N⁻¹) * m24T)
  conj₁ := rfl
  conj₂ := rfl
  conj₃ := by decide +kernel

theorem m24_e8Datum :
    E8Datum (⟨m24T, m24T_mem⟩ : NativeSporadic.M24)
      (⟨m24N, m24N_mem⟩ * ⟨m24T, m24T_mem⟩ * ⟨m24N, m24N_mem⟩⁻¹)
      (⟨m24N, m24N_mem⟩ * (⟨m24N, m24N_mem⟩ * ⟨m24T, m24T_mem⟩ * ⟨m24N, m24N_mem⟩⁻¹) *
        ⟨m24N, m24N_mem⟩⁻¹) ⟨m24N, m24N_mem⟩ :=
  E8Datum.of_map NativeSporadic.M24.subtype Subtype.val_injective m24_perm_e8Datum

end M24

section SL

open Matrix Sec4.Census.DoubleCoverLift Sec4.Census.RankOmegaF4

@[expose] def sl4A₁ : GL (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide +kernel, by decide +kernel⟩

@[expose] def sl4A₂ : GL (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1], by decide +kernel, by decide +kernel⟩

@[expose] def sl4A₃ : GL (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1], by decide +kernel, by decide +kernel⟩

@[expose] def sl4N : GL (Fin 4) (ZMod 2) :=
  ⟨!![0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
    !![1, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1], by decide +kernel, by decide +kernel⟩

theorem sl4_gl_e8Datum : E8Datum sl4A₁ sl4A₂ sl4A₃ sl4N where
  ne_one := by decide +kernel
  sq := by decide +kernel
  comm₁₂ := (by decide +kernel : sl4A₁ * sl4A₂ = sl4A₂ * sl4A₁)
  comm₁₃ := (by decide +kernel : sl4A₁ * sl4A₃ = sl4A₃ * sl4A₁)
  conj₁ := by decide +kernel
  conj₂ := by decide +kernel
  conj₃ := by decide +kernel

@[expose] def sl5A₁ : GL (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    by decide +kernel, by decide +kernel⟩

@[expose] def sl5A₂ : GL (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    by decide +kernel, by decide +kernel⟩

@[expose] def sl5A₃ : GL (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    by decide +kernel, by decide +kernel⟩

@[expose] def sl5N : GL (Fin 5) (ZMod 2) :=
  ⟨!![0, 0, 1, 0, 0; 1, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    by decide +kernel, by decide +kernel⟩

theorem sl5_gl_e8Datum : E8Datum sl5A₁ sl5A₂ sl5A₃ sl5N where
  ne_one := by decide +kernel
  sq := by decide +kernel
  comm₁₂ := (by decide +kernel : sl5A₁ * sl5A₂ = sl5A₂ * sl5A₁)
  comm₁₃ := (by decide +kernel : sl5A₁ * sl5A₃ = sl5A₃ * sl5A₁)
  conj₁ := by decide +kernel
  conj₂ := by decide +kernel
  conj₃ := by decide +kernel

theorem projF2_mem_projSL {m : ℕ} {M : GL (Fin m) (ZMod 2)}
    (hM : (M : Matrix (Fin m) (Fin m) (ZMod 2)).det = 1) :
    projF2 M ∈ projSL m (GaloisField 2 1) := by
  refine ⟨toF2 M, ?_, rfl⟩
  change toF2 M ∈ (Matrix.GeneralLinearGroup.det : GL (Fin m) (GaloisField 2 1) →* _).ker
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_toF2, Units.val_one,
    ← RingEquiv.coe_toRingHom f2, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hM, map_one]

theorem projF2_injective' {m : ℕ} : Function.Injective (projF2 (ι := Fin m)) :=
  Sec4.Census.DoubleCoverRanks.projF2_injective

theorem sl4_e8Datum : E8Datum
    (⟨projF2 sl4A₁, projF2_mem_projSL (by decide +kernel)⟩ : projSL 4 (GaloisField 2 1))
    ⟨projF2 sl4A₂, projF2_mem_projSL (by decide +kernel)⟩
    ⟨projF2 sl4A₃, projF2_mem_projSL (by decide +kernel)⟩
    ⟨projF2 sl4N, projF2_mem_projSL (by decide +kernel)⟩ :=
  E8Datum.of_map (projSL 4 (GaloisField 2 1)).subtype Subtype.val_injective
    (sl4_gl_e8Datum.map projF2 projF2_injective')

theorem sl5_e8Datum : E8Datum
    (⟨projF2 sl5A₁, projF2_mem_projSL (by decide +kernel)⟩ : projSL 5 (GaloisField 2 1))
    ⟨projF2 sl5A₂, projF2_mem_projSL (by decide +kernel)⟩
    ⟨projF2 sl5A₃, projF2_mem_projSL (by decide +kernel)⟩
    ⟨projF2 sl5N, projF2_mem_projSL (by decide +kernel)⟩ :=
  E8Datum.of_map (projSL 5 (GaloisField 2 1)).subtype Subtype.val_injective
    (sl5_gl_e8Datum.map projF2 projF2_injective')

end SL

section U54

open Matrix

local notation "𝕂" => GaloisField 2 (2 * 2)

@[expose] noncomputable def isoMatU5₁ : Matrix (Fin 5) (Fin 5) 𝕂 :=
  !![1, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]

@[expose] noncomputable def isoMatU5₂ : Matrix (Fin 5) (Fin 5) 𝕂 :=
  !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 0]

@[expose] noncomputable def radU5 :
    (Sec13.traceQ2 2).ker × (Sec13.traceQ2 2).ker →+ Matrix (Fin 5) (Fin 5) 𝕂 where
  toFun v := (v.1 : 𝕂) • isoMatU5₁ + (v.2 : 𝕂) • isoMatU5₂
  map_zero' := by simp
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, add_smul]
    abel

theorem radU5_injective : Function.Injective radU5 := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  have h00 := congrFun (congrFun hv 0) 0
  have h22 := congrFun (congrFun hv 2) 2
  simp [radU5, isoMatU5₁, isoMatU5₂] at h00 h22
  exact Prod.ext h00 h22

theorem radU5_mul (v w : (Sec13.traceQ2 2).ker × (Sec13.traceQ2 2).ker) :
    radU5 v * radU5 w = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radU5, isoMatU5₁, isoMatU5₂, mul_apply, Fin.sum_univ_five, CharTwo.add_self_eq_zero]

theorem eq_one_of_sq_eq_one_char_two {x : 𝕂} (h : x ^ 2 = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (x + 1) ^ 2 = 0 := by
    rw [add_pow_char, h, one_pow, CharTwo.add_self_eq_zero]
  have h3 : x + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
  calc x = x + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h3, zero_add]

theorem det_one_add_radU5 (v : (Sec13.traceQ2 2).ker × (Sec13.traceQ2 2).ker) :
    (1 + radU5 v).det = 1 := by
  have hsq : (1 + radU5 v) * (1 + radU5 v) = 1 := by
    have h2 : radU5 v + radU5 v = 0 := by
      ext i j
      simp [CharTwo.add_self_eq_zero]
    calc (1 + radU5 v) * (1 + radU5 v) = 1 + (radU5 v + radU5 v) + radU5 v * radU5 v := by
          noncomm_ring
      _ = 1 := by rw [h2, radU5_mul, add_zero, add_zero]
  apply eq_one_of_sq_eq_one_char_two
  rw [sq, ← Matrix.det_mul, hsq, Matrix.det_one]

theorem unitary_one_add_radU5 (v : (Sec13.traceQ2 2).ker × (Sec13.traceQ2 2).ker) :
    ((1 + radU5 v).map (· ^ 2 ^ 2))ᵀ * (1 + radU5 v) = 1 := by
  have hc₁' : (v.1 : 𝕂) ^ 2 ^ 2 = v.1 := (Sec13.mem_ker_traceQ2 2).mp v.1.2
  have hc₂' : (v.2 : 𝕂) ^ 2 ^ 2 = v.2 := (Sec13.mem_ker_traceQ2 2).mp v.2.2
  have h1c₁' : (1 + (v.1 : 𝕂)) ^ 2 ^ 2 = 1 + v.1 := by rw [add_pow_char_pow, one_pow, hc₁']
  have h1c₂' : (1 + (v.2 : 𝕂)) ^ 2 ^ 2 = 1 + v.2 := by rw [add_pow_char_pow, one_pow, hc₂']
  have hc₁ : (v.1 : 𝕂) ^ 4 = v.1 := hc₁'
  have hc₂ : (v.2 : 𝕂) ^ 4 = v.2 := hc₂'
  have h1c₁ : (1 + (v.1 : 𝕂)) ^ 4 = 1 + v.1 := h1c₁'
  have h1c₂ : (1 + (v.2 : 𝕂)) ^ 4 = 1 + v.2 := h1c₂'
  have h0 : (0 : 𝕂) ^ 4 = 0 := zero_pow (by norm_num)
  have hmap : (1 + radU5 v).map (· ^ 2 ^ 2) = 1 + radU5 v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [radU5, isoMatU5₁, isoMatU5₂, hc₁, hc₂, h0, h1c₁, h1c₂]
  have hT : (1 + radU5 v)ᵀ = 1 + radU5 v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [radU5, isoMatU5₁, isoMatU5₂]
  have h2 : radU5 v + radU5 v = 0 := by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  rw [hmap, hT]
  calc (1 + radU5 v) * (1 + radU5 v) = 1 + (radU5 v + radU5 v) + radU5 v * radU5 v := by
        noncomm_ring
    _ = 1 := by rw [h2, radU5_mul, add_zero, add_zero]

theorem four_le_pRank_projSU_five_two [Finite (projSU 5 2 2)] :
    4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (projSU 5 2 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := Sec13.le_card_ker_traceQ2 2 (by norm_num)
  have hdvd : Nat.card (Sec13.traceQ2 2).ker ∣ 2 ^ 4 := by
    have h := AddSubgroup.card_addSubgroup_dvd_card (Sec13.traceQ2 2).ker
    rwa [GaloisField.card 2 (2 * 2) (by norm_num)] at h
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcard : Nat.card ((Sec13.traceQ2 2).ker × (Sec13.traceQ2 2).ker) = 2 ^ (k + k) := by
    rw [Nat.card_prod, hk, pow_add]
  have hr := Sec4.Census.le_pRank_of_sqZero radU5 radU5_injective radU5_mul
    (fun v => Prod.ext (Subtype.ext (by
      rw [Prod.smul_fst, AddSubgroup.coe_nsmul, two_nsmul, CharTwo.add_self_eq_zero,
        Prod.fst_zero, AddSubgroup.coe_zero]))
      (Subtype.ext (by
      rw [Prod.smul_snd, AddSubgroup.coe_nsmul, two_nsmul, CharTwo.add_self_eq_zero,
        Prod.snd_zero, AddSubgroup.coe_zero])))
    (projSU 5 2 2) (fun v => ⟨Sec4.Census.sqZeroUnit radU5 radU5_mul v,
      Subgroup.subset_closure ⟨by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
        exact det_one_add_radU5 v, unitary_one_add_radU5 v⟩, rfl⟩) hcard
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  omega

end U54

theorem twoRankGood_projSL_three {n : ℕ} (hn : 2 ≤ n) :
    TwoRankGood (projSL 3 (GaloisField 2 n)) := by
  intro J _ _ hq hZ2 ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hq4 : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  by_cases hbot : Subgroup.center J = ⊥
  · have h2n := Sec17.HeadProof.two_mul_le_pRank_projSL_three (K := GaloisField 2 n) (p := 2) hK
    have : Finite (projSL 3 (GaloisField 2 n)) := Finite.of_equiv J
      ((quotCenterEquivOfBot hbot).symm.trans e).toEquiv
    rw [CFSG.RankThree.PartTwo.pRank_congr_mulEquiv one_lt_two
      ((quotCenterEquivOfBot hbot).symm.trans e)]
    omega
  · have hZnt : Nontrivial (Subgroup.center J) := (Subgroup.nontrivial_iff_ne_bot _).mpr hbot
    set φ := quotMap e with hφdef
    have hφ := quotMap_surjective e
    have hk : φ.ker ≤ Subgroup.center J := (quotMap_ker e).le
    have hK3 : 3 ≤ Nat.card (GaloisField 2 n) := by rw [hK]; omega
    obtain ⟨A, hA, hcard⟩ := Sec4.Census.TransitiveLift.exists_isElementaryAbelian_card hφ hk
      (W := (Sec4.Census.DoubleCoverRanksTwo.rootHom (K := GaloisField 2 n)).range)
      (fun y y' hy hy' => Sec4.Census.DoubleCoverRanksTwo.commute_lift_rootHom hφ hk hy hy')
      (fun y hy => by
        obtain ⟨a, ha⟩ := hy
        exact Sec4.Census.DoubleCoverRanksTwo.exists_sq_eq_sq_E hφ hk hK3
          (ha ▸ Sec4.Census.DoubleCoverRanksTwo.rootHom_mem_range_uHom a))
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2
      (Sec4.Census.two_dvd_card_center hZ2 hZnt)
    have hz1 : (z : J) ≠ 1 := by
      intro h1
      rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hz2 : (z : J) ^ 2 = 1 := by
      rw [← Subgroup.orderOf_coe] at hz
      rw [← hz]
      exact pow_orderOf_eq_one _
    have hzk : φ z = 1 := by rw [← MonoidHom.mem_ker, quotMap_ker]; exact z.2
    have hΩ : 2 ≤ Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} := by
      have : Nontrivial {c : J // φ c = 1 ∧ c ^ 2 = 1} :=
        ⟨⟨⟨1, map_one φ, one_pow 2⟩, ⟨z, hzk, hz2⟩, fun h => hz1 (congrArg Subtype.val h).symm⟩⟩
      exact Finite.one_lt_card_iff_nontrivial.mpr this
    refine Sec4.Census.TransitiveLift.le_pRank_of_card hA ?_
    rw [hcard, Sec4.Census.DoubleCoverRanksTwo.card_range_rootHom, hK]
    calc 2 ^ 3 = 4 * 2 := by norm_num
      _ ≤ 2 ^ n * Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} := Nat.mul_le_mul hq4 hΩ

theorem three_le_pRank_of_J4
    {K : Type} [Group K] [Finite K] (e : K ≃* NativeSporadic.J4) :
    3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup K) := by
  have h := (CFSG.Sporadic.GLQ.j4_two_rank_at_least_eleven K ⟨e⟩).2
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  omega

theorem not_isTwoCover_projSp_two (hGA : GriessMultipliersAllModels) {n : ℕ} (hn : 2 ≤ n)
    (J : Type) [Group J] [Finite J] : ¬ Sec4.Census.IsTwoCover J (projSp 2 (GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq4 : 4 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  refine Sec4.Census.not_isTwoCover_of_odd_tableOrder hGA (Sec4.Census.lieModel_projSp
    ⟨Nat.prime_two, by omega, le_rfl, fun h => ?_⟩) (Sec4.Census.odd_tableOrder_psp_two_even
      (by omega))
  simp only [Prod.mk.injEq] at h
  omega

theorem not_isTwoCover_projSU_four (hGA : GriessMultipliersAllModels) {n : ℕ} (hn : 2 ≤ n)
    (J : Type) [Group J] [Finite J] : ¬ Sec4.Census.IsTwoCover J (projSU 4 2 n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Sec4.Census.not_isTwoCover_of_odd_tableOrder hGA (Sec4.Census.lieModel_projSU
    ⟨Nat.prime_two, by omega, by norm_num, fun h => ?_⟩)
    (Sec4.Census.odd_tableOrder_psu_four_even hn)
  simp only [Prod.mk.injEq] at h
  omega

theorem not_isTwoCover_projSU_five (hGA : GriessMultipliersAllModels) (J : Type) [Group J]
    [Finite J] : ¬ Sec4.Census.IsTwoCover J (projSU 5 2 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Sec4.Census.not_isTwoCover_of_odd_tableOrder hGA (Sec4.Census.lieModel_projSU
    ⟨Nat.prime_two, by norm_num, by norm_num, fun h => ?_⟩) ?_
  · simp only [Prod.mk.injEq] at h
    omega
  · refine Sec4.Census.odd_tableOrder (by decide) odd_one ?_
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all

theorem not_isTwoCover_He
    (J : Type) [Group J] [Finite J] : ¬ Sec4.Census.IsTwoCover J NativeSporadic.He := by
  rintro ⟨hq, -, hZnt, he⟩
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hZnt
    (CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate J hq he)

theorem not_isTwoCover_J4
    (J : Type) [Group J] [Finite J] : ¬ Sec4.Census.IsTwoCover J NativeSporadic.J4 :=
  Sec4.Census.SporadicTwoCover.not_isTwoCover_of_noPerfectDoubleCover
    (CFSG.Sporadic.Recognition.J4Multiplier.noPerfectDoubleCover_J4
      CFSG.ComponentClassification.RankTwoSporadic.J4.j4_foxCert
      CFSG.ComponentClassification.RankTwoSporadic.J4.j4_formCert)

end Item21Early2Proof

open Item21Early2Proof

theorem ks213TwoRank_of
    (hGA : GriessMultipliersAllModels) : KS213TwoRank := by
  intro X _ _ hX J _ _ hq hZ2 ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK135 : Sec13.KS135TwoRank := Sec13.ks135TwoRank_of_cover Sec13.ks135TwoRankCover
    Sec4.Sporadic.rank3II_4_14_local Sec4.Sporadic.rank3II_4_15
  have hY := bar211Quot_of_isBar211 hX
  unfold Bar211Quot at hY
  rcases hY with h | h | h | h | h | h | h | h | h |
      ⟨n, hn, he, h⟩ | ⟨n, hn, he, hG | hD⟩ | ⟨n, hn, he, h⟩ | ⟨n, hn, h⟩ | h |
      h | h | h
  · obtain ⟨f⟩ := h
    exact twoRankGood_of_e8Datum Sec4.Census.DoubleCoverRanks.m22_e8Datum J hq hZ2 ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    exact twoRankGood_of_e8Datum Sec4.Census.SporadicTwoCover.m23_e8Datum J hq hZ2
      ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    obtain ⟨a₁, a₂, a₃, m, hd⟩ := Sec4.Census.DoubleCoverRanks.hs_e8Datum
    exact twoRankGood_of_e8Datum (S := NativeSporadic.HS) hd J hq hZ2 ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    exact twoRankGood_of_e8Datum m24_e8Datum J hq hZ2 ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    have h5 := five_le_pRank_He
    exact twoRankGood_of_center (S := NativeSporadic.He) not_isTwoCover_He (by omega) J hq hZ2
      ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    exact hK135 J hq hZ2 (Or.inr (Or.inl ⟨e.trans f⟩))
  · obtain ⟨f⟩ := h
    obtain ⟨a₁, a₂, a₃, m, hd⟩ := Sec4.Census.DoubleCoverRanks.ru_e8Datum
    exact twoRankGood_of_e8Datum (S := NativeSporadic.Ru) hd J hq hZ2 ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    have hbot : Subgroup.center J = ⊥ := by
      by_contra hne
      exact not_isTwoCover_J4 J ⟨hq, hZ2, (Subgroup.nontrivial_iff_ne_bot _).mpr hne,
        ⟨e.trans f⟩⟩
    exact three_le_pRank_of_J4 ((quotCenterEquivOfBot hbot).symm.trans (e.trans f))
  · obtain ⟨f⟩ := h
    obtain ⟨a₁, a₂, a₃, a₄, m, hd⟩ := Sec4.Census.SporadicTwoCover.j3_e16Datum
    exact twoRankGood_of_e16Datum (S := NativeSporadic.J3) hd J hq hZ2 ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    exact twoRankGood_projSL_three hn J hq hZ2 ⟨e.trans f⟩
  · exact three_le_pRank_of_excModel hGA hq hZ2 hn (Or.inl (chevalleyG2_of_mulEquiv e hG))
  · exact three_le_pRank_of_excModel hGA hq hZ2 hn (Or.inr (chevalleyD4_of_mulEquiv e hD))
  · obtain ⟨f⟩ := h
    have : Finite (projSp 2 (GaloisField 2 n)) := Finite.of_equiv _ f.toEquiv
    have hb := Sec4.Census.le_pRank_projSp_two (GaloisField 2 n) (p := 2)
      (GaloisField.card 2 n (by omega))
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hb
    exact twoRankGood_of_center (not_isTwoCover_projSp_two hGA hn) (by omega) J hq hZ2
      ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    have : Finite (projSU 4 2 n) := Finite.of_equiv _ f.toEquiv
    have hb := Sec4.Census.le_pRank_projSU_four (p := 2) (f := n) (by omega)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hb
    exact twoRankGood_of_center (not_isTwoCover_projSU_four hGA hn) (by omega) J hq hZ2
      ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    have : Finite (projSU 5 2 2) := Finite.of_equiv _ f.toEquiv
    have hb := four_le_pRank_projSU_five_two
    exact twoRankGood_of_center (not_isTwoCover_projSU_five hGA) (by omega) J hq hZ2
      ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    exact twoRankGood_of_e8Datum sl4_e8Datum J hq hZ2 ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    exact twoRankGood_of_e8Datum sl5_e8Datum J hq hZ2 ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    exact twoRankGood_of_e8Datum Sec4.Census.DoubleCoverRanks.sp62_e8Datum J hq hZ2 ⟨e.trans f⟩

theorem ks213TwoRank :
    KS213TwoRank :=
  ks213TwoRank_of CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end CFSG.RankThree.PartTwo.Sec21
