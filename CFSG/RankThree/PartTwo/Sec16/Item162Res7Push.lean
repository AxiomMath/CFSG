module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec14.Item1446
import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.NormalizerChain
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_mem_sup_of_centralizes {A : Subgroup G} {c : G} {K T : Subgroup G}
    (hcA : c ∈ A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (hc : ∀ y ∈ K, c * y * c⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hKT : CFSG.Open.pCoreOf 2 K ≤ T) :
    ∀ z ∈ K ⊔ T, ∀ g ∈ Subgroup.zpowers c, z * g * z⁻¹ * g⁻¹ ∈ T := by
  let O2K : Subgroup G := CFSG.Open.pCoreOf 2 K
  let C : Subgroup G := CFSG.SignalizerFunctorTheorem.McBride.sectionCentralizer O2K K
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.prop.1.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    (mem_scriptQ_iff.mp hT.prop.1.1).2.1
  have hNK_O : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (O2K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  have hcK : c ∈ Subgroup.normalizer (K : Set G) := hAK hcA
  have hcO : c ∈ Subgroup.normalizer (O2K : Set G) := hNK_O hcK
  have hcC : c ∈ C := by
    refine ⟨hcO, hcK, fun y hy => ?_⟩
    simpa [commutatorElement_def] using hc y hy
  have hzpC : Subgroup.zpowers c ≤ C := Subgroup.zpowers_le.mpr hcC
  have hconjC : ∀ g ∈ C, ∀ s ∈ T, s * g * s⁻¹ ∈ C := by
    intro g hg s hs
    have hsK : s ∈ Subgroup.normalizer (K : Set G) := hTK hs
    have hsO : s ∈ Subgroup.normalizer (O2K : Set G) := hNK_O hsK
    obtain ⟨hgO, hgK, hgcomm⟩ := hg
    refine ⟨?_, ?_, ?_⟩
    · exact mul_mem (mul_mem hsO hgO) (inv_mem hsO)
    · exact mul_mem (mul_mem hsK hgK) (inv_mem hsK)
    · intro y hy
      have hy' : s⁻¹ * y * s ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hsK) y).mp hy
        simpa using this
      have h1 := (Subgroup.mem_normalizer_iff.mp hsO _).mp (hgcomm _ hy')
      have e : ⁅s * g * s⁻¹, y⁆ = s * ⁅g, s⁻¹ * y * s⁆ * s⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact h1
  intro z hz g hg
  have hgC : g ∈ C := hzpC hg
  have hgA : g ∈ A := Subgroup.zpowers_le.mpr hcA hg
  have hgNT : g ∈ Subgroup.normalizer (T : Set G) := hAT hgA
  have hz' : z ∈ (K : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K T hTK]
    exact hz
  obtain ⟨y, hy, s, hs, hys⟩ := hz'
  rw [← hys]
  have hdecomp : (y * s) * g * (y * s)⁻¹ * g⁻¹ =
      (y * (s * g * s⁻¹ * g⁻¹) * y⁻¹) * (y * g * y⁻¹ * g⁻¹) := by
    group
  rw [hdecomp]
  have hgs : g * s⁻¹ * g⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp hgNT s⁻¹).mp (T.inv_mem hs)
  have huT : s * g * s⁻¹ * g⁻¹ ∈ T := by
    have := T.mul_mem hs hgs
    simpa [mul_assoc] using this
  have huC : s * g * s⁻¹ * g⁻¹ ∈ C :=
    C.mul_mem (hconjC g hgC s hs) (C.inv_mem hgC)
  have hucomm :
      ⁅(s * g * s⁻¹ * g⁻¹)⁻¹, y⁆ ∈ O2K :=
    (show (s * g * s⁻¹ * g⁻¹)⁻¹ ∈ C from C.inv_mem huC).2.2 y hy
  have hOy : (s * g * s⁻¹ * g⁻¹)⁻¹ * y * (s * g * s⁻¹ * g⁻¹) * y⁻¹ ∈ O2K := by
    simpa [commutatorElement_def] using hucomm
  have hcomp1 : y * (s * g * s⁻¹ * g⁻¹) * y⁻¹ ∈ T := by
    have hEq : y * (s * g * s⁻¹ * g⁻¹) * y⁻¹ =
        (s * g * s⁻¹ * g⁻¹) *
          ((s * g * s⁻¹ * g⁻¹)⁻¹ * y * (s * g * s⁻¹ * g⁻¹) * y⁻¹) := by
      group
    rw [hEq]
    exact T.mul_mem huT (hKT hOy)
  have hgy : g * y * g⁻¹ * y⁻¹ ∈ O2K := by
    have := (show g ∈ C from hgC).2.2 y hy
    simpa [commutatorElement_def] using this
  have hcomp2 : y * g * y⁻¹ * g⁻¹ ∈ T := by
    refine hKT ?_
    have hEq : y * g * y⁻¹ * g⁻¹ = (g * y * g⁻¹ * y⁻¹)⁻¹ := by group
    rw [hEq]
    exact O2K.inv_mem hgy
  exact T.mul_mem hcomp1 hcomp2

private theorem commutator_le_zpowers_of_commutator_mem {A : Subgroup G} {c : G}
    {L : Subgroup G} {K T W : Subgroup G}
    (h : Sec14Std G A c L)
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hcW : ∀ w ∈ W, c * w * c⁻¹ * w⁻¹ ∈ T) :
    ⁅W, Subgroup.zpowers c⁆ ≤ T := by
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.toSec13Data.zpowers_mem_omegaA).1
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    (mem_scriptQ_iff.mp hT.prop.1.1).2.1
  let C : Subgroup G := CFSG.SignalizerFunctorTheorem.McBride.sectionCentralizer T W
  have hcC : c ∈ C := by
    refine ⟨hAT hcA, hAW hcA, fun w hw => ?_⟩
    simpa [commutatorElement_def] using hcW w hw
  have hzpC : Subgroup.zpowers c ≤ C := Subgroup.zpowers_le.mpr hcC
  rw [Subgroup.commutator_le]
  intro x hx g hg
  have hcomm : ⁅g, x⁆ ∈ T := (show g ∈ C from hzpC hg).2.2 x hx
  change x * g * x⁻¹ * g⁻¹ ∈ T
  have e : x * g * x⁻¹ * g⁻¹ = ⁅g, x⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact T.inv_mem hcomm

private theorem exists_centralizer_factorization {A : Subgroup G} {c : G} {L : Subgroup G}
    {K T W : Subgroup G}
    (h : Sec14Std G A c L) (h142 : Concl142 A (lB A))
    (hW : IsPGroup 2 W) (hWK : W ≤ Subgroup.normalizer (K : Set G))
    (hWT : W ≤ Subgroup.normalizer (T : Set G))
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) :
    ∃ U : Subgroup G, U ∈ scriptQPi A (lB A)
        (Subgroup.normalizer (K : Set G)) (piOf 2) ∧
      U ≤ Subgroup.normalizer (T : Set G) ∧
      W = ⁅W, Subgroup.zpowers c⁆ ⊔ U := by
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.toSec13Data.zpowers_mem_omegaA).1
  have hWcard : ¬ 3 ∣ Nat.card W := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hW
    rw [hn]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2))
  have hzp3 : IsPGroup 3 (Subgroup.zpowers c) :=
    hA.isPGroup.to_le (Subgroup.zpowers_le.mpr hcA)
  have hzp_NW : Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.zpowers_le.mpr hcA).trans hAW
  let U : Subgroup G := W ⊓ Subgroup.centralizer (Subgroup.zpowers c : Set G)
  have hfactor : W = ⁅W, Subgroup.zpowers c⁆ ⊔ U :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three (Subgroup.zpowers c) W hzp3 hWcard hzp_NW
  have hU2 : IsPGroup 2 U := hW.to_le inf_le_left
  have hU_NK : U ≤ Subgroup.normalizer (K : Set G) := inf_le_left.trans hWK
  have hU_NT : U ≤ Subgroup.normalizer (T : Set G) := inf_le_left.trans hWT
  have hA_Czp : A ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
    haveI : IsMulCommutative A := hA.1.1
    refine (Subgroup.le_centralizer (H := A)).trans (Subgroup.centralizer_le ?_)
    intro x hx
    exact Subgroup.zpowers_le.mpr hcA hx
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    (le_inf hAW (hA_Czp.trans
      (Subgroup.le_normalizer (H := Subgroup.centralizer
        (Subgroup.zpowers c : Set G))))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf
        (H := W) (K := Subgroup.centralizer (Subgroup.zpowers c : Set G)))
  have hU3' : ¬ 3 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU2
    rw [hn]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2))
  have hU_le_Nzp : U ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    (inf_le_right : U ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hUinv : U ∈ invariantPiSubgroups
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piCompl 3) :=
    ⟨hU_le_Nzp, (isPiSubgroup_piCompl_iff Nat.prime_three U).mpr hU3', hAU⟩
  have hUscriptQ : U ∈ scriptQ A (lB A) := by
    obtain ⟨Q', hQ', hUQ'⟩ := exists_le_mem_maxInvariantPiSubgroups hUinv
    exact mem_scriptQ_of_le (h142 c h.toSec13Data.zpowers_mem_omegaA Q' hQ').1 hUQ' hAU
  have hUpi : U ∈ scriptQPi A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2) :=
    ⟨⟨hUscriptQ, hU_NK⟩, (isPiSubgroup_piOf_iff Nat.prime_two U).mpr hU2⟩
  exact ⟨U, hUpi, hU_NT, hfactor⟩

theorem eq_of_commutator_mem {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    {K T W : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (hW : IsPGroup 2 W) (hTW : T ≤ W) (hWK : W ≤ Subgroup.normalizer (K : Set G))
    (hWT : W ≤ Subgroup.normalizer (T : Set G)) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hcW : ∀ w ∈ W, c * w * c⁻¹ * w⁻¹ ∈ T) : W = T := by
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hcomm_le_T := commutator_le_zpowers_of_commutator_mem h hT hAW hcW
  obtain ⟨U, hUpi, hU_NT, hfactor⟩ :=
    exists_centralizer_factorization h h142 hW hWK hWT hAW
  have hUT : U ⊔ T ∈ scriptQPi A (lB A)
      (Subgroup.normalizer (K : Set G)) (piOf 2) :=
    sup_mem_scriptQPi_of_item146 hA h146 hUpi hT.prop hU_NT
  have hUleT : U ≤ T := le_sup_left.trans (hT.2 hUT le_sup_right)
  refine le_antisymm ?_ hTW
  rw [hfactor]
  exact sup_le hcomm_le_T hUleT

private theorem false_of_not_pCoreOf_le {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    {K T : Subgroup G} (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (hStepA : ∀ z ∈ K ⊔ T, ∀ g ∈ Subgroup.zpowers c, z * g * z⁻¹ * g⁻¹ ∈ T)
    (hQ : ¬ CFSG.Open.pCoreOf 2 (K ⊔ T) ≤ T) : False := by
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 (K ⊔ T)
  let P : Subgroup G := Q ⊔ T
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.prop.1.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    (mem_scriptQ_iff.mp hT.prop.1.1).2.1
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ T)
  have hQ_le : Q ≤ K ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 (K ⊔ T)
  have hT_le_NQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T))
  have hP2 : IsPGroup 2 P := IsPGroup.to_sup_of_normal_left' hQ2 hT2 hT_le_NQ
  have hP_le_KT : P ≤ K ⊔ T := sup_le hQ_le le_sup_right
  have hP_le_NK : P ≤ Subgroup.normalizer (K : Set G) :=
    hP_le_KT.trans (sup_le Subgroup.le_normalizer hTK)
  have hTP : T < P := lt_of_le_of_ne le_sup_right (by
    intro hEq
    exact hQ (le_sup_left.trans (le_of_eq hEq.symm)))
  let K' : Subgroup G := Subgroup.normalizer (T : Set G) ⊓ P
  have hK'lt : T < K' := lt_normalizer_inf_of_isPGroup hP2 le_sup_right hTP
  have hK'2 : IsPGroup 2 K' := hP2.to_le inf_le_right
  have hK'_le_NK : K' ≤ Subgroup.normalizer (K : Set G) :=
    (inf_le_right : K' ≤ P).trans hP_le_NK
  have hK'_le_NT : K' ≤ Subgroup.normalizer (T : Set G) := inf_le_left
  have hA_NNT : A ≤ Subgroup.normalizer
      (Subgroup.normalizer (T : Set G) : Set G) :=
    hAT.trans Subgroup.le_normalizer
  have hA_KT : A ≤ Subgroup.normalizer (K ⊔ T : Subgroup G) :=
    (le_inf hAK hAT).trans (Subgroup.inf_normalizer_le_normalizer_sup K T)
  have hA_Q : A ≤ Subgroup.normalizer (Q : Set G) :=
    hA_KT.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ T))
  have hA_P : A ≤ Subgroup.normalizer (P : Set G) :=
    (le_inf hA_Q hAT).trans (Subgroup.inf_normalizer_le_normalizer_sup Q T)
  have hA_K' : A ≤ Subgroup.normalizer (K' : Set G) :=
    (le_inf hA_NNT hA_P).trans (Subgroup.inf_normalizer_le_normalizer_inf
      (H := Subgroup.normalizer (T : Set G)) (K := P))
  have hK'_le_KT : K' ≤ K ⊔ T := (inf_le_right : K' ≤ P).trans hP_le_KT
  have hcK' : ∀ w ∈ K', c * w * c⁻¹ * w⁻¹ ∈ T := by
    intro w hw
    have h := hStepA w (hK'_le_KT hw) c (Subgroup.mem_zpowers c)
    have e : c * w * c⁻¹ * w⁻¹ = (w * c * w⁻¹ * c⁻¹)⁻¹ := by group
    rw [e]
    exact T.inv_mem h
  have hK'eqT : K' = T :=
    eq_of_commutator_mem h h146 h142 hT hK'2 hK'lt.1 hK'_le_NK hK'_le_NT hA_K' hcK'
  exact hK'lt.ne hK'eqT.symm

theorem pCoreOf_sup_le_of_centralizes {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    {K T : Subgroup G} (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (hc : ∀ y ∈ K, c * y * c⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hKT : CFSG.Open.pCoreOf 2 K ≤ T) :
    CFSG.Open.pCoreOf 2 (K ⊔ T) ≤ T := by
  by_contra hQ
  exact false_of_not_pCoreOf_le h h146 h142 hAK hT
    (commutator_mem_sup_of_centralizes
      (zpowers_mem_omegaA_iff.mp h.toSec13Data.zpowers_mem_omegaA).1 hAK hT hc hKT) hQ

end CFSG.RankThree.PartTwo.Sec16
