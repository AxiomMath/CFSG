module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRep
public import CFSG.LargeExtraspecial.SL4ModEmbed
import CFSG.LargeExtraspecial.SL4ModMain
import CFSG.CGT.T75N.L29Transport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

theorem w135c2_psl_l42_isIrredGen {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]
    {L : Subgroup (MulAut W)} {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2)
    (φ : Matrix.SpecialLinearGroup (Fin 4) K →* ↥L) (hirr : (pslRep φ).IsIrreducible) :
    ∃ ρ : CFSG.LargeExtraspecial.SL4Mod.SL4 →* (Additive W ≃ₗ[ZMod 2] Additive W),
      CFSG.LargeExtraspecial.SL4Mod.IsIrredGen ρ := by
  have hZ : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  let e : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (hK.trans hZ.symm)
  let σ : CFSG.LargeExtraspecial.SL4Mod.SL4 ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
    CFSG.CGT.T75N.slRingEquiv 4 e.symm
  have h := (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff (pslRep φ)).1 hirr
  let ψ : CFSG.LargeExtraspecial.SL4Mod.SL4 →* ↥L := φ.comp σ.toMonoidHom
  let ρ : CFSG.LargeExtraspecial.SL4Mod.SL4 →* (Additive W ≃ₗ[ZMod 2] Additive W) :=
    { toFun := fun x => mulAutLinearEquiv ((ψ x : ↥L) : MulAut W)
      map_one' := LinearEquiv.ext fun v => by
        show mulAutLinear ((ψ 1 : ↥L) : MulAut W) v = v
        rw [map_one]
        rfl
      map_mul' := fun x y => LinearEquiv.ext fun v => by
        show mulAutLinear ((ψ (x * y) : ↥L) : MulAut W) v =
          mulAutLinear ((ψ x : ↥L) : MulAut W) (mulAutLinear ((ψ y : ↥L) : MulAut W) v)
        rw [map_mul]
        rfl }
  refine ⟨ρ, fun W' hW' => h.2 W' fun g u hu => ?_⟩
  have hmem : ρ (σ.symm g) u ∈ W' :=
    CFSG.LargeExtraspecial.SL4Mod.forall_mem_of_gen ρ hW' (σ.symm g) u hu
  have hψ : ψ (σ.symm g) = φ g := by
    show φ (σ (σ.symm g)) = φ g
    rw [σ.apply_symm_apply]
  have hrep : pslRep φ g = ρ (σ.symm g) := by
    apply LinearMap.ext
    intro v
    rw [pslRep_apply]
    show mulAutLinear ((φ g : ↥L) : MulAut W) v =
      mulAutLinear ((ψ (σ.symm g) : ↥L) : MulAut W) v
    rw [hψ]
  simpa [hrep] using hmem

end CFSG.LocalAnalysis.WeakClosure81
