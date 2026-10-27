module

public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeWeylLift
public import CFSG.LocalAnalysis.StandardType.GGF4N2CalibrationC1

public section

namespace CFSG.StandardType.F4Over

open CFSG.Open CFSG.StandardType.N2KCoordinate CFSG.LieType.Steinberg.Minuscule

variable {G : Type} [Group G]

theorem conj_comp_markedRankOne_of_ne_three
    (Ψ : ↥(e6Data_valid.minGroup (GaloisField 2 2)) →* G) (ψ₁ : SL6F4 →* G)
    (hsl6 : Ψ.comp (CFSG.SeitzReduction.F4Pilot.slToE6Sc (GaloisField 2 2)) = ψ₁)
    {c : G} (hc : c ∈ Subgroup.centralizer (ψ₁.range : Set G))
    (ρθ : SL2F4 →* ↥(e6Data_valid.minGroup (GaloisField 2 2))) {k : Fin 4} (hk : k ≠ 3)
    (s : SL2F4) :
    ((MulAut.conj c).toMonoidHom.comp Ψ) (N2E6Native.markedRankOne ρθ k s) = ψ₁ (blk k s) := by
  have hslk : ∀ (h : 2 * k.val < 5),
      Ψ (CFSG.SeitzReduction.F4Pilot.slToE6Sc (GaloisField 2 2)
        (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 2) 5 ⟨2 * k.val, h⟩ s)) =
        ψ₁ (blk k s) := by
    intro h
    rw [← blockSL2_eq_blk hk h s, ← hsl6]
    rfl
  have hcomm : ∀ z ∈ ψ₁.range, c * z * c⁻¹ = z := by
    intro z hz
    rw [← Subgroup.mem_centralizer_iff.mp hc z hz, mul_inv_cancel_right]
  have hmem : ψ₁ (blk k s) ∈ ψ₁.range := ⟨_, rfl⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hcomm _ hmem]
  congr 2
  fin_cases k
  · exact hslk (by decide)
  · exact hslk (by decide)
  · exact hslk (by decide)
  · exact absurd rfl hk

theorem conj_comp_markedRankOne_three
    (Ψ : ↥(e6Data_valid.minGroup (GaloisField 2 2)) →* G) (c : G)
    (ρθ : SL2F4 →* ↥(e6Data_valid.minGroup (GaloisField 2 2))) (s : SL2F4) :
    ((MulAut.conj c).toMonoidHom.comp Ψ) (N2E6Native.markedRankOne ρθ 3 s) =
      c * Ψ (ρθ s) * c⁻¹ :=
  rfl

theorem kappa_eq_conj_comp_markedRankOne
    (Ψ : ↥(e6Data_valid.minGroup (GaloisField 2 2)) →* G) (ψ₁ : SL6F4 →* G)
    (hsl6 : Ψ.comp (CFSG.SeitzReduction.F4Pilot.slToE6Sc (GaloisField 2 2)) = ψ₁)
    {c : G} (hc : c ∈ Subgroup.centralizer (ψ₁.range : Set G))
    (ρθ : SL2F4 →* ↥(e6Data_valid.minGroup (GaloisField 2 2))) (t : SL2F4) {Bs : Subgroup G}
    (κ : V5 ≃* ↥Bs) (hκ : ∀ k : Fin 4, k ≠ 3 → ((κ (e5 k) : ↥Bs) : G) = ψ₁ (blk k t))
    (hκ3 : ((κ (e5 3) : ↥Bs) : G) = c * Ψ (ρθ t) * c⁻¹) :
    ∀ k, ((κ (e5 k) : ↥Bs) : G) =
      ((MulAut.conj c).toMonoidHom.comp Ψ) (N2E6Native.markedRankOne ρθ k t) := by
  intro k
  by_cases hk : k = 3
  · subst hk
    rw [conj_comp_markedRankOne_three]
    exact hκ3
  · rw [conj_comp_markedRankOne_of_ne_three Ψ ψ₁ hsl6 hc ρθ hk t]
    exact hκ k hk

end CFSG.StandardType.F4Over

end
