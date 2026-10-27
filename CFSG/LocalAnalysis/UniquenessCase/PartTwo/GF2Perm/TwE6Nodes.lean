module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneTorus
public import CFSG.ClassicalInvolution.Models.TwistedPairs.Unitary
import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.LieType.Steinberg.TwistedE6 CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
open CFSG.ClassicalInvolution.Models.TwistedPairs (fixedField)
open CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Steinberg

variable {k : Type} [Field k] [Finite k] [CharP k 2] {θ : k →+* k}

omit [Finite k] [CharP k 2] in
theorem hasSL2Node_twE6_zero :
    HasSL2Node (twistedDatum k θ) (nf 0) (fixedField θ) := by
  have h0 : orbitMap (nd 1) = nf 0 := by decide
  refine ⟨nodeHom0 θ, rFixed_injective θ (nd 1) rfl, fun c => ?_, fun c => ?_⟩
  · rw [← CFSG.Timmesfeld.LevisExtras.tv01_eq_sl2Upper]
    exact rFixed_upper θ (nd 1) rfl h0 c
  · rw [← CFSG.Timmesfeld.LevisExtras.tv10_eq_sl2Lower]
    exact rFixed_lower θ (nd 1) rfl h0 c

omit [CharP k 2] in
theorem hasTorusSL2_twE6_three
    (hθ : ∀ c, θ (θ c) = c) (hK4 : 4 ≤ Nat.card k) :
    HasTorusSL2 (twistedDatum k θ) (hHat k θ) (nf 3) k := by
  have hab : (nd 0 = nd 2 ∧ nd 5 = nd 4) ∨ (nd 0 = nd 0 ∧ nd 5 = nd 5) :=
    Or.inr ⟨rfl, rfl⟩
  have h3 : orbitMap (nd 0) = nf 3 := by decide
  obtain ⟨a, ha0, ha2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card k hK4
  set t : kˣ := Units.mk0 a ha0 with ht
  have ht2 : (t : k) ^ 2 ≠ 1 := by simpa [ht] using ha2
  have hnc : torusHom k t * sl2Upper (1 : k) ≠ sl2Upper (1 : k) * torusHom k t := by
    intro hc
    have h01 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) k =>
      (A : Matrix (Fin 2) (Fin 2) k) 0 1) hc
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h01
    rw [coe_torusHom] at h01
    simp [sl2Upper, Matrix.mul_apply, Fin.sum_univ_two] at h01
    apply ht2
    field_simp at h01
    linear_combination h01
  refine ⟨nodeHom3 θ hθ, slOrbitHom_injective θ hθ hab, fun c => ?_, fun c => ?_,
    le_of_eq (rankOne_twistedE6_three θ hθ), torusHom k t, sl2Upper 1, hnc, ?_⟩
  · rw [← CFSG.Timmesfeld.LevisExtras.tv01_eq_sl2Upper]
    exact slOrbitHom_upper_mem θ hθ hab h3 c
  · rw [← CFSG.Timmesfeld.LevisExtras.tv10_eq_sl2Lower]
    exact slOrbitHom_lower_mem θ hθ hab h3 c
  · rw [hHat, Subgroup.mem_subgroupOf, slOrbitHom_torusHom θ hθ hab]
    exact ⟨t, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
