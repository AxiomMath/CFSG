module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRep
public import CFSG.LieType.SpecialLinear.BinaryDescent.ExteriorTwist
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Klein
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.LieType.SpecialLinear
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open CFSG.QuasithinUnique.Setup.Layer

private theorem c2slo6_center_specialLinear_four {K : Type} [Field K] [Fintype K] [CharP K 2] :
    Subgroup.center (SpecialLinearGroup (Fin 4) K) = ⊥ := by
  refine eq_bot_iff.mpr fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr' : r ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 from rfl]
    exact hr
  have hr1 : r = 1 := by
    have h1 : (r - 1) ^ 2 ^ 2 = 0 := by
      rw [sub_pow_char_pow, hr', one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

private theorem c2slo6_binPsi_eq_mulAutLinear {W : Type} [CommGroup W]
    [Module (ZMod 2) (Additive W)] (a : MulAut W) (w : Additive W) :
    binPsi ((MulEquiv.multiplicativeAdditive W).symm) a w = mulAutLinear a w := by
  rw [binPsi_apply, mulAutLinear_apply]
  simp

theorem w135c2_psl_orth_six {W : Type} [CommGroup W] [Finite W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {f : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2 ^ f) (φ : SpecialLinearGroup (Fin 4) K →* ↥L)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 4) K))
    {j r : ℕ} (hj : j = 2) (β : Additive W ≃+ (Set.powersetCard (Fin 4) j → K))
    (hβ : ∀ g w, β (pslRep φ g w) = extTwist 4 j r K g *ᵥ β w) : Chev2Natural W L := by
  classical
  subst hj
  have hcenter : Subgroup.center (SpecialLinearGroup (Fin 4) K) = ⊥ :=
    c2slo6_center_specialLinear_four
  have hkerbot : φ.ker = ⊥ := le_bot_iff.mp (hker.trans (le_of_eq hcenter))
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  let ψ : ↥L ≃* SpecialLinearGroup (Fin 4) K :=
    (MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm
  have hψ : ∀ l : ↥L, φ (ψ l) = l := fun _ =>
    MulEquiv.ofBijective_apply_symm_apply φ ⟨hinj, hφ⟩
  let θ : W ≃* Multiplicative (Additive W) := (MulEquiv.multiplicativeAdditive W).symm
  have hβ' : ∀ (l : ↥L) (w : Additive W),
      β (binPsi θ (l : MulAut W) w) = extTwist 4 2 r K (ψ l) *ᵥ β w := by
    intro l w
    have h1 : binPsi θ (l : MulAut W) w = mulAutLinear (l : MulAut W) w :=
      c2slo6_binPsi_eq_mulAutLinear (l : MulAut W) w
    have h2 : ((φ (ψ l) : ↥L) : MulAut W) = (l : MulAut W) := congrArg Subtype.val (hψ l)
    rw [h1, ← hβ (ψ l) w, pslRep_apply, h2]
  have hF' : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK]
  have hreal := realizes_natOmegaPlus_of_extTwist_two θ ψ r β hβ'
  have hnat : NatOmegaPlus L ⊤ ⊥ 6 f :=
    ⟨by decide, K, inferInstance, inferInstance, hF', hreal⟩
  have hiso : IsOmegaPlus ↥L 6 f := isOmegaPlus_six_of_mulEquiv hF' ψ
  exact Or.inl ⟨6, f, Or.inr (Or.inr (Or.inl ⟨hiso, hnat⟩))⟩

end CFSG.LocalAnalysis.WeakClosure81
