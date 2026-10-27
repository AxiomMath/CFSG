module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGB36LemmaRT
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueTypeInner
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

private theorem am2ab_card_le_9_of_mulAut_projectiveSL {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (B : Subgroup (MulAut (projectiveSL 4 K))) (hB : IsElemAbelian 3 B) :
    Nat.card B ≤ 3 ^ 2 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hdvd := card_mulAut_projectiveSL_dvd (n := 4) (f := 1) (by norm_num) hK'
  have hGL : Nat.card (GL (Fin 4) K) = 20160 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_GL_eq, hK]
    norm_num [Finset.prod_Icc_succ_top]
  rw [hGL, mul_one] at hdvd
  have hBdvd : Nat.card B ∣ 2 * 20160 := (Subgroup.card_subgroup_dvd_card B).trans hdvd
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (TableB.isPGroup_of_isElemAbelian hB)
  rw [hj] at hBdvd ⊢
  have hj2 : j ≤ 2 := by
    have h40320 : (2 * 20160 : ℕ) = 3 ^ 2 * 4480 := by norm_num
    have h4480 : (4480 : ℕ).factorization 3 = 0 := by
      rw [Nat.factorization_eq_zero_of_not_dvd]
      norm_num
    have hle : j ≤ (2 * 20160 : ℕ).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num)).mp hBdvd
    rw [h40320, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, h4480] at hle
    rw [Nat.Prime.factorization_self Nat.prime_three] at hle
    omega
  calc 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj2
    _ = 9 := by norm_num

private theorem am2ab_rank_linear_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (A : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 4) K))))
    (hA : IsElemAbelian 3 A) : Nat.card A ≤ 3 ^ 2 := by
  have h9 := am2ab_card_le_9_of_mulAut_projectiveSL (K := K) hK
    (A.map (MulAut.congr (TypeA.recipeEquiv 4 K)).toMonoidHom)
    (CFSG.SectionRank.isElemAbelian_map hA (MulAut.congr (TypeA.recipeEquiv 4 K)).toMonoidHom)
  rwa [Subgroup.card_map_of_injective (MulAut.congr (TypeA.recipeEquiv 4 K)).injective] at h9

private theorem am2ab_aut_A3 {J : Type} [Group J] [Finite J] (hperf : commutator J = ⊤)
    (hlab : GGHasLabel ⟨.A, 3, 1⟩ (J ⧸ Subgroup.center J)) :
    ∀ E : Subgroup (MulAut J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 := by
  intro E hE
  unfold GGHasLabel at hlab
  dsimp only [LargeEvenRawDatum] at hlab
  unfold LargeEvenRecipeLinear at hlab
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hlab
  have hK2 : Nat.card K = 2 := by rw [hKcard]; norm_num
  have hb := am2ab_rank_linear_two (K := K) hK2
    (E.map (ggInducedAut e))
    (CFSG.SectionRank.isElemAbelian_map hE (ggInducedAut e))
  have hinj : Function.Injective (ggInducedAut e) :=
    ggInducedAut_injective_of_perfect hperf e
  have hcard : Nat.card (E.map (ggInducedAut e)) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  rwa [hcard] at hb

theorem ggAm2Ab_card_le {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)}
    {σ : MulAut X} {J : Subgroup X} {n : ℕ} {S : ℕ → LargeEvenLabel → Prop}
    (hd : GGTPNBasicB 3 n S A Ab σ J)
    (hhJ : GGHasLabel ⟨.A, 3, 1⟩ (↥J ⧸ Subgroup.center ↥J)) : Nat.card Ab ≤ 3 ^ 3 := by
  obtain ⟨hlocCore, hflat, -, hrank, -, -, -, hmarked⟩ := hd
  obtain ⟨hAbA, hσAb, -, hkerAb⟩ := hflat
  have hnormA : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := hlocCore.2.2.2.2
  have hperfJ : commutator ↥J = ⊤ := hlocCore.2.2.2.1.2.2.1
  have hAbab : IsElemAbelian 3 Ab := by
    obtain ⟨hc, hp⟩ := hlocCore.1
    haveI : IsMulCommutative A := hc
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
    · apply Subtype.ext
      exact Subgroup.mul_comm_of_mem_isMulCommutative A (hAbA u.2) (hAbA v.2)
    · exact hp z (hAbA hz)
  have hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J := fun a ha j hj => hnormA a (hAbA ha) j hj
  have hAut : ∀ E : Subgroup (MulAut ↥J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 :=
    am2ab_aut_A3 hperfJ hhJ
  have h := B36.card_le_of_kernel_le_zpowers (p := 3) (by norm_num) hAbab hσAb hnorm hkerAb
    (k := 2) hAut
  simpa using h

end CFSG.StandardType

end
