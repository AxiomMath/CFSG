module

public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGTBWNormNbr
public import CFSG.Mathlib.GroupTheory.PerfectCentralAut
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSpAut
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSp)
open CFSG.Open (StatedLieAdmissible)
open CFSG.SeitzReduction.SporadicRefine

theorem ggTorusWNormSC_of_equiv_sp_two {m : ℕ} (hm : 3 ≤ m)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {p : ℕ} {R : Type} [Group R] (e : R ≃* StatedProj (StatedSp m K))
    (I : Set (MulAut R)) : GGTorusWNormSC p R I := by
  have hK' : Nat.card K = 2 ^ 1 := by simpa using hK
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hK'
  have : NeZero m := ⟨by omega⟩
  have hZ : Subgroup.center R = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [TableBSymp.center_spProj_eq_bot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
  have hinner : ∀ β : MulAut R, ∃ r : R, β = MulAut.conj r :=
    allInner_of_mulEquiv e (allInner_statedProjSp_of_card_two hm hK)
  apply ggTorusWNormSC_of_forall_mulAut_eq_conj
  intro L' _ _ ψ hψ hker hperf
  exact forall_mulAut_eq_conj_of_forall_mulAut_eq_conj hperf ψ hψ hker hZ hinner

theorem largeEvenLabelAll_wnorm_symplectic_two {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (hm : 3 ≤ lab.rank) (hn : lab.n = 1) {p : ℕ} :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, m, n⟩
  dsimp only at htag hm hn ⊢
  subst hn
  rcases htag with rfl | rfl
  · intro Q hQ
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_of_equiv_sp_two hm (by simpa using hK) (MulEquiv.refl _) _
  · intro Q hQ
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_of_equiv_sp_two hm (by simpa using hK) (MulEquiv.refl _) _

end CFSG.StandardType
