module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec119OmegaModel
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeN
public import CFSG.ClassicalGroups.Orthogonal.Models
import CFSG.ClassicalGroups.Orthogonal.RootInvolutionModels
import CFSG.GroupTheory.WeirSylow.OrthogonalTypes

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
open CFSG.LieType.Universal.Spin CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

theorem ne_zero_of_forall_sq_add_mul_add_ne_zero {K : Type*} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  exact hirr r (by rw [hr, zero_mul, add_zero, ← _root_.sq, CharTwo.add_self_eq_zero])

theorem minusThreeFrame_quadMinus {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    MinusThreeFrame (quadMinus 3 K b c)
      (minusPair K b c ⟨0, by norm_num⟩).e (minusPair K b c ⟨0, by norm_num⟩).f
      (minusPair K b c ⟨1, by norm_num⟩).e (minusPair K b c ⟨1, by norm_num⟩).f
      (Pi.single (Sum.inr (Sum.inr 0)) 1) (Pi.single (Sum.inr (Sum.inr 1)) 1) := by
  set u : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 0)) 1 with hu
  set v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 1)) 1 with hv
  have hQu : quadMinus 3 K b c u = 1 := by
    rw [quadMinus_apply]
    simp [hu]
  have hQv : quadMinus 3 K b c v = c := by
    rw [quadMinus_apply]
    simp [hv]
  have huv : polar (quadMinus 3 K b c) u v = b := by
    rw [polar, quadMinus_apply, quadMinus_apply, quadMinus_apply]
    simp [hu, hv]
    ring
  have hperp : ∀ (i : Fin (3 - 1)) (w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K),
      (w = u ∨ w = v) → w ∈ (minusPair K b c i).perp := by
    rintro i w (rfl | rfl)
    all_goals
      refine HypPair.mem_perp.mpr ⟨?_, ?_⟩
      · rw [minusPair_e, polar_single_inl_quadMinus]
        simp [hu, hv]
      · rw [minusPair_f, polar_single_inr_quadMinus]
        simp [hu, hv]
  have hdim : finrank K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) = 6 :=
    CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (m := 3) (by norm_num)
  exact exists_minusThreeFrame hdim (fun i : Fin 2 => minusPair K b c ⟨i, by omega⟩)
    (minusPair_orth (by simp)) (fun i => ⟨hperp _ _ (Or.inl rfl), hperp _ _ (Or.inr rfl)⟩) hQu
    (by rw [huv]; exact ne_zero_of_forall_sq_add_mul_add_ne_zero hirr)
    (by rw [huv, hQv]; exact hirr)

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.exists_omega_model_psu (hc : Ctx M Q Z B) {x : ℕ} (hx : 2 ≤ x)
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' 2) (N : Type)
      (_ : AddCommGroup N) (_ : Module K' N) (_ : FiniteDimensional K' N)
      (QN : QuadraticForm K' N), Nat.card K' = 2 ^ x ∧ (polarBilin QN).Nondegenerate ∧
        finrank K' N = 2 * 3 ∧ (∃ e f p p' u v : N, MinusThreeFrame QN e f p p' u v) ∧
        ∃ ψ : ↥(Xbar M Q Z B) ≃* ↥(elementaryGroup QN),
          ∀ t : ↥(Xbar M Q Z B), (t : Mbar M Q) ∈ Ebar M Q Z B →
            IsOrthA2 QN ((ψ t : ↥(elementaryGroup QN)) : N ≃ₗ[K'] N) := by
  obtain ⟨K, _, _, _, b, c, hK, hirr, ⟨e⟩⟩ :=
    exists_mulEquiv_elementaryGroup_of_lieModel_PSU_four hU
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
  have hdim : finrank K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) = 2 * 3 :=
    CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (by norm_num)
  obtain ⟨ψ, hψ⟩ := hc.exists_mulEquiv_isOrthA2_of_model
    (hc.center_Xbar_eq_bot_of_omega hx (m := 3) (Or.inr (Or.inr ⟨rfl, hU⟩))) hQ hdim le_rfl e
  exact ⟨K, inferInstance, inferInstance, inferInstance, _, inferInstance, inferInstance,
    inferInstance, quadMinus 3 K b c, hK, hQ, hdim,
    ⟨_, _, _, _, _, _, minusThreeFrame_quadMinus hirr⟩, ψ, hψ⟩

end CFSG.RankThree.GF2n.Stroth80
