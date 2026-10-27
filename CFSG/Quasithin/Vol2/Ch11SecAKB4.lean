module

public import CFSG.Quasithin.Vol2.Ch11SecAKB3
public import CFSG.Quasithin.Vol2.KGNatSL3Par

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)

open PointStab in
theorem factRadicalInnerSL3_holds : Ch11.SecA.FactRadicalInnerSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  rw [eq_U1_of_isFlagW hW hf hg hU]
  intro τ hτ2 hτZ hτH hτP hτc
  obtain ⟨a, b, hab⟩ := exists_uMat_of_centralizes hSL hf g hτ2 hτZ hτH hτP hτc
  obtain ⟨y, hy, hyeq⟩ := radical_mem_pCore hSL hf g a b
  refine ⟨y, hy, fun h hh => ?_⟩
  have hyH : (y : MulAut W) ∈ H := by
    rw [hyeq]
    exact (rho3 π _).2
  have hτv : ∀ v, f (τ v) = f ((y : MulAut W) v) := fun v => by
    rw [hyeq, hf.act3, gconj_mulVec, coe_uSL, ← hab, g_ginv_mulVec]
  have hc : ∀ w, f (((y : MulAut W)⁻¹ * τ) w) = f w := by
    intro w
    have h1 : ((g * uSL a b 0 * g⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ f (((y : MulAut W)⁻¹ * τ) w) =
          ((g * uSL a b 0 * g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            f w := by
      rw [← hf.act3, ← hf.act3, ← hyeq, MulAut.mul_apply, MulAut.apply_inv_self, hτv]
    have h2 := congrArg (fun v => (((g * uSL a b 0 * g⁻¹)⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) h1
    simpa only [ginv_g_mulVec] using h2
  have hcN : ∀ x ∈ H, ((y : MulAut W)⁻¹ * τ) * x * ((y : MulAut W)⁻¹ * τ)⁻¹ ∈ H := by
    intro x hx
    rw [show ((y : MulAut W)⁻¹ * τ) * x * ((y : MulAut W)⁻¹ * τ)⁻¹ =
      (y : MulAut W)⁻¹ * (τ * x * τ⁻¹) * (y : MulAut W) by group]
    exact H.mul_mem (H.mul_mem (H.inv_mem hyH) (hτH x hx)) hyH
  have h1 := commute_of_trivial_mod hf hcN hc h hh
  calc τ * h * τ⁻¹ = (y : MulAut W) * (((y : MulAut W)⁻¹ * τ) * h) * τ⁻¹ := by group
    _ = (y : MulAut W) * (h * ((y : MulAut W)⁻¹ * τ)) * τ⁻¹ := by rw [h1]
    _ = (y : MulAut W) * h * (y : MulAut W)⁻¹ := by group

end CFSG.Quasithin.Vol2.KGNat
