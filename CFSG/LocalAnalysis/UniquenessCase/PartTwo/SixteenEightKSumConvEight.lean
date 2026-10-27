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

private noncomputable def s16k_eightToSixFun (m : ↥(G6.coreMod 8)) :
    Multiplicative (SmallOmegaSix.ι6 → ZMod 2) :=
  Multiplicative.ofAdd (SmallOmegaSix.Tm *ᵥ Multiplicative.toAdd (m : G6.PermMod 8))

private noncomputable def s16k_eightToSix :
    ↥(G6.coreMod 8) →* ↥(⊤ : Subgroup (Multiplicative (SmallOmegaSix.ι6 → ZMod 2))) where
  toFun m := ⟨s16k_eightToSixFun m, Subgroup.mem_top _⟩
  map_one' := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    simp [s16k_eightToSixFun]
  map_mul' m n := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    simp [s16k_eightToSixFun, Matrix.mulVec_add]

private theorem s16k_eightToSix_coe (m : ↥(G6.coreMod 8)) :
    (s16k_eightToSix m : Multiplicative (SmallOmegaSix.ι6 → ZMod 2)) = s16k_eightToSixFun m :=
  rfl

private theorem s16k_eightToSix_surjective : Function.Surjective s16k_eightToSix := by
  intro y
  refine ⟨⟨Multiplicative.ofAdd (SmallOmegaSix.Fm *ᵥ Multiplicative.toAdd
    (y : Multiplicative (SmallOmegaSix.ι6 → ZMod 2))), G6.mem_coreMod.mpr ?_⟩, ?_⟩
  · rw [toAdd_ofAdd]
    exact SmallOmegaSix.F_even _
  · apply Subtype.ext
    apply Multiplicative.toAdd.injective
    rw [s16k_eightToSix_coe, s16k_eightToSixFun]
    simp only [toAdd_ofAdd]
    rw [Matrix.mulVec_mulVec, SmallOmegaSix.TF, Matrix.one_mulVec]

private theorem s16k_thetaSix_coe (σ : ↥(alternatingGroup (Fin 8))) :
    (((thetaSix.symm σ : ↥(StatedOmega SmallOmegaSix.Q6)) : GL SmallOmegaSix.ι6 (ZMod 2)) :
      Matrix SmallOmegaSix.ι6 SmallOmegaSix.ι6 (ZMod 2)) =
      SmallOmegaSix.Mm (σ : Equiv.Perm (Fin 8)) := by
  have h1 : omegaPerm6 (thetaSix.symm σ) = (σ : Equiv.Perm (Fin 8)) := by
    have h2 := thetaSix_apply (thetaSix.symm σ)
    rw [MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  have h3 : ((thetaSix.symm σ : ↥(StatedOmega SmallOmegaSix.Q6)) : GL SmallOmegaSix.ι6 (ZMod 2)) =
      SmallOmegaSix.psi (omegaPerm6 (thetaSix.symm σ)) :=
    (psi_omegaPerm6 (thetaSix.symm σ)).symm
  rw [h3, SmallOmegaSix.psi_val, h1]

private theorem s16k_eightToSix_act (σ : ↥(alternatingGroup (Fin 8))) (m : ↥(G6.coreMod 8))
    (hm : G6.permAct 8 (σ : Equiv.Perm (Fin 8)) (m : G6.PermMod 8) ∈ G6.coreMod 8) :
    s16k_eightToSix ⟨G6.permAct 8 (σ : Equiv.Perm (Fin 8)) (m : G6.PermMod 8), hm⟩ =
      natAct (StatedOmega SmallOmegaSix.Q6) (thetaSix.symm σ) (s16k_eightToSix m) := by
  have hw : ∑ k, Multiplicative.toAdd (m : G6.PermMod 8) k = 0 := G6.mem_coreMod.mp m.2
  have hL : Multiplicative.toAdd (G6.permAct 8 (σ : Equiv.Perm (Fin 8)) (m : G6.PermMod 8)) =
      SmallOmegaSix.Pm (σ : Equiv.Perm (Fin 8)) *ᵥ Multiplicative.toAdd (m : G6.PermMod 8) := by
    rw [SmallOmegaSix.Pm_mulVec]
    funext i
    exact G6.permAct_apply 8 (σ : Equiv.Perm (Fin 8)) (m : G6.PermMod 8) i
  apply Multiplicative.toAdd.injective
  simp only [s16k_eightToSix_coe, s16k_eightToSixFun, natAct, toAdd_ofAdd]
  rw [hL, s16k_thetaSix_coe, SmallOmegaSix.Mm_mulVec]
  rcases SmallOmegaSix.FT (Multiplicative.toAdd (m : G6.PermMod 8)) hw with h | h
  · rw [h]
  · rw [h, Matrix.mulVec_add, SmallOmegaSix.Pm_one8, Matrix.mulVec_add, SmallOmegaSix.T_one,
      add_zero]

private theorem s16k_eightToSix_ker (m : ↥(G6.coreMod 8)) :
    ((s16k_eightToSix m : ↥(⊤ : Subgroup (Multiplicative (SmallOmegaSix.ι6 → ZMod 2)))) :
        Multiplicative (SmallOmegaSix.ι6 → ZMod 2)) ∈
      (⊥ : Subgroup (Multiplicative (SmallOmegaSix.ι6 → ZMod 2))) ↔
    (m : G6.PermMod 8) ∈ Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8 := by
  have hw : ∑ k, Multiplicative.toAdd (m : G6.PermMod 8) k = 0 := G6.mem_coreMod.mp m.2
  constructor
  · intro hm
    rw [Subgroup.mem_bot] at hm
    have hzero : SmallOmegaSix.Tm *ᵥ Multiplicative.toAdd (m : G6.PermMod 8) = 0 := by
      have h := congrArg Multiplicative.toAdd hm
      rwa [s16k_eightToSix_coe, s16k_eightToSixFun, toAdd_ofAdd,
        toAdd_one] at h
    refine Subgroup.mem_inf.mpr ⟨?_, m.2⟩
    rw [B5FinPerm.mem_zpowers_allOnes_iff]
    rcases Tm_ker _ hw hzero with h | h
    · left
      apply Multiplicative.toAdd.injective
      rw [h, toAdd_one]
    · right
      apply Multiplicative.toAdd.injective
      rw [h]
      rfl
  · intro hm
    have hz := (Subgroup.mem_inf.mp hm).1
    rw [Subgroup.mem_bot]
    have hzero : SmallOmegaSix.Tm *ᵥ Multiplicative.toAdd (m : G6.PermMod 8) = 0 := by
      rcases B5FinPerm.mem_zpowers_allOnes_iff.mp hz with h | h
      · have hm1 : m = 1 := Subtype.ext (by simpa using h)
        rw [hm1]
        simp
      · rw [h]
        rw [show Multiplicative.toAdd (G6.allOnes 8) = SmallOmegaSix.one8 from rfl,
          SmallOmegaSix.T_one]
    rw [s16k_eightToSix_coe, s16k_eightToSixFun]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, hzero, toAdd_one]

theorem s16k_alternatingNatural_eight_of_natOmegaPlus_zmod {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {I Z : Subgroup W}
    (h : (FFModel.nat (StatedOmega (StatedQuadPlus 3 (ZMod 2)))).Realizes H I Z) :
    AlternatingNatural H I Z 8 := by
  obtain ⟨π, hπ⟩ := h
  refine ⟨π.comp thetaSix.symm.toMonoidHom, ?_⟩
  refine FFModel.RealizesVia.of_surjHom (FFModel.altDn_isActionModel 8) hπ
    thetaSix.symm.toMonoidHom thetaSix.symm.surjective s16k_eightToSix s16k_eightToSix_surjective
    ?_ ?_
  · intro σ m hm
    exact s16k_eightToSix_act σ m hm
  · intro m
    exact s16k_eightToSix_ker m

theorem s16k_alternatingNatural_eight_of_natOmegaPlus_six {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {I Z : Subgroup W} (h : NatOmegaPlus H I Z 6 1) :
    AlternatingNatural H I Z 8 :=
  s16k_alternatingNatural_eight_of_natOmegaPlus_zmod (s16k_natOmegaPlus_zmod h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
