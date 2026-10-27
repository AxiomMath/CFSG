module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKNatOmegaMap
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltOverlap
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B5FinPerm
import CFSG.Quasithin.Background.B5FinTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltOverlap
open scoped Matrix

private noncomputable def s16k_phi :
    G6.PermMod 5 →* Multiplicative (SmallOmegaFour.ι4 → ZMod 2) where
  toFun x := Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i • SmallOmegaFour.sing i)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => add_smul _ _ _

private theorem s16k_phi_inj_on_core :
    ∀ x : Fin 5 → ZMod 2, (∑ i, x i = 0) →
      (∑ i, x i • SmallOmegaFour.sing i = 0) → x = 0 :=
  singSum_ker

private theorem s16k_phi_surj_aux :
    ∀ v : SmallOmegaFour.ι4 → ZMod 2, ∃ x : Fin 5 → ZMod 2,
      (∑ i, x i = 0) ∧ (∑ i, x i • SmallOmegaFour.sing i = v) :=
  singSum_surj

private noncomputable def s16k_phi0 :
    ↥(G6.coreMod 5) →* ↥(⊤ : Subgroup (Multiplicative (SmallOmegaFour.ι4 → ZMod 2))) :=
  (s16k_phi.comp (G6.coreMod 5).subtype).codRestrict ⊤ fun _ => Subgroup.mem_top _

private theorem s16k_phi0_surjective : Function.Surjective s16k_phi0 := by
  intro y
  obtain ⟨x, hx, hv⟩ := s16k_phi_surj_aux (Multiplicative.toAdd y.1)
  refine ⟨⟨Multiplicative.ofAdd x, G6.mem_coreMod.mpr hx⟩, ?_⟩
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  change (∑ i, x i • SmallOmegaFour.sing i) = Multiplicative.toAdd y.1
  exact hv

private theorem s16k_phi_eq_one_iff (x : ↥(G6.coreMod 5)) :
    s16k_phi (x : G6.PermMod 5) = 1 ↔ (x : G6.PermMod 5) = 1 := by
  constructor
  · intro hx
    have h0 : ∑ i, Multiplicative.toAdd (x : G6.PermMod 5) i • SmallOmegaFour.sing i = 0 := by
      have h := congrArg Multiplicative.toAdd hx
      simpa [s16k_phi] using h
    have hz := s16k_phi_inj_on_core (Multiplicative.toAdd (x : G6.PermMod 5))
      (G6.mem_coreMod.mp x.2) h0
    apply Multiplicative.toAdd.injective
    simpa using hz
  · intro hx
    rw [hx, map_one]

private theorem s16k_allOnes_five_not_mem_coreMod : G6.allOnes 5 ∉ G6.coreMod 5 := by
  rw [G6.mem_coreMod]
  decide +kernel

private theorem s16k_altDn_five_ker : (FFModel.altDn 5).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  rcases B5FinPerm.mem_zpowers_allOnes_iff.mp hz1 with h | h
  · exact h
  · exact absurd (h ▸ hz2) s16k_allOnes_five_not_mem_coreMod

private theorem s16k_thetaFour_symm_mulVec_sing (σ : ↥(alternatingGroup (Fin 5))) (i : Fin 5) :
    ((thetaFour.symm σ : ↥(StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1))) :
      GL SmallOmegaFour.ι4 (ZMod 2)).1 *ᵥ SmallOmegaFour.sing i =
        SmallOmegaFour.sing ((σ : Equiv.Perm (Fin 5)) i) := by
  have h := omegaPerm4_spec (thetaFour.symm σ) i
  have hσ : omegaPerm4 (thetaFour.symm σ) = (σ : Equiv.Perm (Fin 5)) := by
    have h2 := thetaFour_apply (thetaFour.symm σ)
    rw [MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  rwa [hσ] at h

private theorem s16k_permAct_apply_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : G6.PermMod n)
    (i : Fin n) :
    Multiplicative.toAdd (G6.permAct n σ x) i = Multiplicative.toAdd x (σ.symm i) :=
  G6.permAct_apply n σ x i

private theorem s16k_natAct_theta_phi (σ : ↥(alternatingGroup (Fin 5))) (x : G6.PermMod 5) :
    natAct (StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1)) (thetaFour.symm σ) (s16k_phi x) =
      s16k_phi (G6.permAct 5 (σ : Equiv.Perm (Fin 5)) x) := by
  apply Multiplicative.toAdd.injective
  show ((thetaFour.symm σ : ↥(StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1))) :
      GL SmallOmegaFour.ι4 (ZMod 2)).1 *ᵥ
        (∑ i, Multiplicative.toAdd x i • SmallOmegaFour.sing i) =
    ∑ i, Multiplicative.toAdd (G6.permAct 5 (σ : Equiv.Perm (Fin 5)) x) i •
      SmallOmegaFour.sing i
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, s16k_thetaFour_symm_mulVec_sing]
  have hR : (∑ i, Multiplicative.toAdd (G6.permAct 5 (σ : Equiv.Perm (Fin 5)) x) i •
      SmallOmegaFour.sing i) =
      ∑ i, (fun j => Multiplicative.toAdd x j • SmallOmegaFour.sing ((σ : Equiv.Perm (Fin 5)) j))
        ((σ : Equiv.Perm (Fin 5)).symm i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [s16k_permAct_apply_symm, Equiv.apply_symm_apply]
  rw [hR]
  exact (Equiv.sum_comp (σ : Equiv.Perm (Fin 5)).symm
    (fun j => Multiplicative.toAdd x j • SmallOmegaFour.sing ((σ : Equiv.Perm (Fin 5)) j))).symm

theorem s16k_alternatingNatural_five_of_natOmegaMinus_zmod {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {I Z : Subgroup W}
    (h : (FFModel.nat (StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1))).Realizes H I Z) :
    AlternatingNatural H I Z 5 := by
  obtain ⟨π, hπ⟩ := h
  refine ⟨π.comp thetaFour.symm.toMonoidHom, ?_⟩
  refine FFModel.RealizesVia.of_surjHom (FFModel.altDn_isActionModel 5) hπ
    thetaFour.symm.toMonoidHom thetaFour.symm.surjective s16k_phi0 s16k_phi0_surjective ?_ ?_
  · intro σ m _
    exact (s16k_natAct_theta_phi σ m.1).symm
  · intro m
    rw [s16k_altDn_five_ker]
    exact s16k_phi_eq_one_iff m

theorem s16k_alternatingNatural_five_of_natOmegaMinus_four {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {I Z : Subgroup W} (h : NatOmegaMinus H I Z 4 1) :
    AlternatingNatural H I Z 5 :=
  s16k_alternatingNatural_five_of_natOmegaMinus_zmod (s16k_natOmegaMinus_zmod h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
