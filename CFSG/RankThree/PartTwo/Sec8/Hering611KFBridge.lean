module

public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
import CFSG.RankThree.PartTwo.Sec8.Hering611K
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofMem
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigidProof
public import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec11.Notation
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec8.Hering611Defs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Bridge


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem nonempty_sec11K_quot_alt6 (C : Cfg611 G A c L E T d S K) :
    Nonempty (Sec11.sec11K L d ⧸ aschbacherSolvableCore 3 (Sec11.sec11K L d) ≃*
      alternatingGroup (Fin 6)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := C.mem_S.1.1
  have hdA : d ∈ A := C.mem_E.2 C.d_mem.1
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  obtain ⟨φ⟩ := C.iso_L
  obtain ⟨hdN, hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta L C.d_field (by decide)
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩) with hα
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hcard : Nat.card (GaloisField 3 (3 * 2)) = (3 ^ 2) ^ 3 := by
    rw [GaloisField.card 3 (3 * 2) (by omega), ← pow_mul, mul_comm]
  have hq : 4 ≤ 3 ^ 2 := by norm_num
  set ψ := φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2))) with hψ
  obtain ⟨hZ, hQ, -, -⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2 ψ hq hcard hα3 hnot
  set β := MulAut.congr ψ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := by rwa [hβ, KFacts.isInnerAut_congr]
  obtain ⟨σ, hσ3, ⟨e⟩⟩ := KFacts.exists_eqLocus_mulEquiv_psl2 hβ3 hβout
  have hσcard : Nat.card (GH74.GLS.IVK.fixedField σ) = 3 ^ 2 :=
    KFacts.card_fixedField_of_orderOf_eq_three hσ3 hcard
  obtain ⟨e1⟩ := Sec11.nonempty_sec11K_quotient_mulEquiv hdN hd3 hQ hZ
  obtain ⟨e2⟩ := Sec11.fieldCent_nonempty_eqLocus_congr ψ α
  haveI : Fintype (GH74.GLS.IVK.fixedField σ) := Fintype.ofFinite _
  have hK9 : Fintype.card (GH74.GLS.IVK.fixedField σ) = 9 := by
    rw [← Nat.card_eq_fintype_card, hσcard]
    norm_num
  obtain ⟨e6⟩ := ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
    (GH74.GLS.IVK.fixedField σ) hK9
  exact ⟨(e1.trans (e2.trans e)).trans e6⟩

theorem exists_bridge_image (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K) :
    ∃ hcN : c ∈ Subgroup.normalizer (K : Set G),
      Item426.thetaAut K hcN ^ 3 = 1 ∧ Item426.thetaAut K hcN ≠ 1 ∧
      ((Sec11.sec11K L d).subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) ∈
        thetaComponentsIn (Item426.fixSub (Item426.thetaAut K hcN)) ∧
      Nonempty (((Sec11.sec11K L d).subgroupOf K).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) ⧸
        aschbacherSolvableCore 3 (((Sec11.sec11K L d).subgroupOf K).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) ≃* alternatingGroup (Fin 6)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := C.standing
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := C.mem_S.1.1
  have hcA := C.c_mem
  have hdE : d ∈ E := C.d_mem.1
  have hdA : d ∈ A := C.mem_E.2 hdE
  have hd1 : d ≠ 1 := fun h => C.d_not_mem (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c C.mem_L
  have hKd : K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d C.mem_K
  obtain ⟨φ⟩ := C.iso_L
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hdA hd1 K hKd
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hAK hcA
  obtain ⟨hdN, hQ, hZ⟩ := Sec6.Hering611.fieldCent_facts_two φ C.d_field hd3
  have hY : Sec11.sec11K L d ∈ thetaComponentsIn
      (Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Sec6.Res611Res7.sec11K_mem_thetaComponentsIn_centralizer hLc hdN hd3 hQ hZ
  have hDK : Sec11.sec11K L d ≤ K := C.perf_le
  have hLcC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hKdC : K ≤ Subgroup.centralizer ({d} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hKd
  have hD : Sec11.sec11K L d ∈ thetaComponentsIn (K ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Sec15.Y4Core.mem_thetaComponentsIn_mid hY (le_inf hDK ((Sec11.sec11K_le L d).trans hLcC))
      (inf_le_inf_right _ hKdC)
  refine ⟨hcN, Item426.thetaAut_pow_eq_one K hcN hc3, ?_,
    Item426.map_mem_thetaComponentsIn_fixSub K hcN hc3 hD, ?_⟩
  · intro h1
    exact C.c_not_cent ((Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hcN).mpr h1)
  · obtain ⟨e⟩ := nonempty_sec11K_quot_alt6 C
    obtain ⟨e'⟩ := Item426.nonempty_quotTheta_map_equiv K hDK
    exact ⟨e'.symm.trans e⟩

theorem exists_bridge (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K) :
    ∃ hcN : c ∈ Subgroup.normalizer (K : Set G),
      Item426.thetaAut K hcN ^ 3 = 1 ∧ Item426.thetaAut K hcN ≠ 1 ∧
      ∃ P : Subgroup (K ⧸ aschbacherSolvableCore 3 K),
        P ∈ thetaComponentsIn (Item426.fixSub (Item426.thetaAut K hcN)) ∧
        Nonempty (P ⧸ aschbacherSolvableCore 3 P ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hcN, h3, h1, hP, hq⟩ := exists_bridge_image h45 C
  exact ⟨hcN, h3, h1, _, hP, hq⟩

end Bridge

end CFSG.RankThree.PartTwo.Sec8.Hering611
