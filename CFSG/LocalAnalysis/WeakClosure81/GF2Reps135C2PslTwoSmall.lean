module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRep
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusLine
import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2Fac
public import CFSG.LinearAlgebra.LinearGroups.PSL2NineCoverKernelAction
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Layer

private theorem c2sltwo_center_specialLinear_eq_bot {K : Type} [Field K] [CharP K 2] :
    Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  have hmem : A ∈ ({1, -1} : Set (SpecialLinearGroup (Fin 2) K)) := by
    rw [← CFSG.LinearGroups.center_specialLinearGroup_two]
    exact hA
  rcases hmem with h1 | hneg
  · exact h1
  · rw [hneg]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    rw [Matrix.neg_apply, CharTwo.neg_eq]

private theorem c2sltwo_binPsi_eq_mulAutLinear {W : Type} [CommGroup W]
    [Module (ZMod 2) (Additive W)] (a : MulAut W) (w : Additive W) :
    binPsi ((MulEquiv.multiplicativeAdditive W).symm) a w = mulAutLinear a w := by
  rw [binPsi_apply, mulAutLinear_apply]
  simp

theorem w135c2_psl_two_small {W : Type} [CommGroup W] [Finite W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2 ^ f) (φ : SpecialLinearGroup (Fin 2) K →* ↥L)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 2) K))
    (hirr : (pslRep φ).IsIrreducible) (hne : ∃ x, pslRep φ x ≠ 1)
    (hW : Nat.card W < 2 ^ (4 * f)) :
    Chev2Natural W L ∨ ∃ l, f = 3 * l ∧ Nat.card W = 2 ^ (8 * l) := by
  classical
  have hkerbot : φ.ker = ⊥ :=
    le_bot_iff.mp (hker.trans (le_of_eq c2sltwo_center_specialLinear_eq_bot))
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  let ψ : ↥L ≃* SpecialLinearGroup (Fin 2) K :=
    (MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm
  let θ : W ≃* Multiplicative (Additive W) := (MulEquiv.multiplicativeAdditive W).symm
  have hθ : θ = (MulEquiv.multiplicativeAdditive W).symm := rfl
  have hrep : B45L2.repOf θ ψ = pslRep φ := by
    rw [hθ]
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro w
    rw [B45L2.repOf_apply, pslRep_apply, c2sltwo_binPsi_eq_mulAutLinear]
    rfl
  haveI : Fact (B45L2.repOf θ ψ).IsIrreducible := ⟨by rw [hrep]; exact hirr⟩
  have hnt : ∃ g, (B45L2.repOf θ ψ) g ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by rw [hrep]; exact hx⟩
  have hF' : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK]
  have hA2 : ∀ a ∈ K147L2Fac.rootSub K, a * a = 1 :=
    fun _ hu => K147L2Fac.mul_self_of_mem_rootSub hu
  have hA : Nat.card (K147L2Fac.rootSub K) = 2 ^ f := K147L2Fac.natCard_rootSub.trans hK
  rcases CFSG.RankThree.GF2n.Tim81.Sec2.isNaturalModule_or_isOrthModule_or_of_card_lt
      hf hK (B45L2.repOf θ ψ) hnt (K147L2Fac.rootSub K) hA2 hA hW with
    hnat | ⟨l, hl, hnl, horth⟩ | ⟨l, hl3, hcardW, _⟩
  · refine Or.inl (Or.inl ⟨2, f, Or.inl ⟨?_, ?_⟩⟩)
    · exact ⟨K, inferInstance, inferInstance, hF',
        ⟨ψ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)⟩⟩
    · exact binaryNaturalSL_of_isNaturalModule hF' θ ψ hnat
  · have hl1 : 1 ≤ l := by omega
    have hNat := natOmegaMinus_of_isOrthModule hl1 hl θ ψ horth
    exact Or.inl (Or.inl ⟨4, l, Or.inr (Or.inr (Or.inr
      ⟨isOmegaMinus_of_natOmegaMinus_four hNat, hNat⟩))⟩)
  · exact Or.inr ⟨l, hl3, hcardW⟩

end CFSG.LocalAnalysis.WeakClosure81
