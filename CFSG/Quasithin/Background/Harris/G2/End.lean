module

public import CFSG.Quasithin.Background.Harris.G2.Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.QuasithinUnique.Setup.SL2Modules

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem endIsField_of_natCard [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) {n : ℕ}
    (hcard : Nat.card (endCommutant L) = 2 ^ n) : EndIsField L n := by
  classical
  have := CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_nontrivial hL
  have := CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_noZeroDivisors hL
  have : IsDomain (endCommutant L) := NoZeroDivisors.to_isDomain _
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  have : Finite (endCommutant L) := Subtype.finite
  let alg : Algebra (ZMod 2) (endCommutant L) := inferInstance
  let _ : Field (endCommutant L) := (Finite.isDomain_to_isField (endCommutant L)).toField
  let _ : Algebra (ZMod 2) (endCommutant L) := alg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨GaloisField.algEquivGaloisField 2 n hcard⟩

theorem natCard_endCommutant_eq {F : Type} [Field F] (L : Subgroup (GLV V))
    (e : ↥L ≃* ↥(cayleyGroup F)) :
    Nat.card (endCommutant L) = Nat.card (EndRing (repC L e)) := by
  have hmem : ∀ f : Module.End (ZMod 2) V,
      f ∈ endCommutant L ↔ ∀ g v, f (repC L e g v) = repC L e g (f v) := by
    intro f
    constructor
    · intro hf g v
      rw [repC_apply, repC_apply]
      exact CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_apply_comm hf
        (e.symm g).2 v
    · intro hf
      rw [endCommutant, Subalgebra.mem_centralizer_iff]
      rintro _ ⟨h, hh, rfl⟩
      ext v
      have := hf (e ⟨h, hh⟩) v
      rw [repC_apply, repC_apply, MulEquiv.symm_apply_apply] at this
      simpa [Module.End.mul_apply] using this.symm
  have hmem' := mem_endRing_iff (repC L e)
  let toEnd : EndRing (repC L e) → endCommutant L := fun ψ =>
    ⟨ψ.restrictScalars (ZMod 2), (hmem _).2 ((hmem' _).1 ⟨ψ, rfl⟩)⟩
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective toEnd ⟨fun a b hab => ?_, fun f => ?_⟩
  · apply LinearMap.ext
    intro v
    exact congrArg (fun f : endCommutant L => (f : Module.End (ZMod 2) V) v) hab
  · obtain ⟨ψ, hψ⟩ := (hmem' f.1).2 ((hmem _).1 f.2)
    refine ⟨ψ, Subtype.ext (LinearMap.ext fun v => ?_)⟩
    exact congrFun hψ v

end CFSG.Quasithin.G11.Harris.G2
