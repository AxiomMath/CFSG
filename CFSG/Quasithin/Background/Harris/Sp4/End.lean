module

public import CFSG.Quasithin.Background.Harris.Sp4.Setup
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd

public section

namespace CFSG.Quasithin.G11.Harris.Sp4

open CFSG.Open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.SL2Modules

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
    (φ : ↥L ≃* antiSp F) :
    Nat.card (endCommutant L) =
      Nat.card (EndRing (CFSG.Quasithin.B42Sp4.repOf (piOf L φ))) := by
  set ρ := CFSG.Quasithin.B42Sp4.repOf (piOf L φ) with hρ
  have hρapply : ∀ g v, ρ g v = ((φ.symm g : ↥L) : GLV V) v := fun g v => rfl
  have hmem : ∀ f : Module.End (ZMod 2) V,
      f ∈ endCommutant L ↔ ∀ g v, f (ρ g v) = ρ g (f v) := by
    intro f
    constructor
    · intro hf g v
      rw [hρapply, hρapply]
      exact CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_apply_comm hf
        (φ.symm g).2 v
    · intro hf
      rw [endCommutant, Subalgebra.mem_centralizer_iff]
      rintro _ ⟨h, hh, rfl⟩
      ext v
      have := hf (φ ⟨h, hh⟩) v
      rw [hρapply, hρapply, MulEquiv.symm_apply_apply] at this
      simpa [Module.End.mul_apply] using this.symm
  have hmem' := mem_endRing_iff ρ
  let toEnd : EndRing ρ → endCommutant L := fun ψ =>
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

theorem finrank_eq_mul_of_card {D : Type*} [Field D] [Module D V] [Finite V]
    {d : ℕ} (hD : Nat.card D = 2 ^ d) : Module.finrank (ZMod 2) V = d * Module.finrank D V := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : Module.Finite D V := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  have h2 := Module.natCard_eq_pow_finrank (K := D) (V := V)
  rw [Nat.card_zmod] at h1
  rw [hD, ← pow_mul] at h2
  rw [h1] at h2
  exact Nat.pow_right_injective le_rfl h2

end CFSG.Quasithin.G11.Harris.Sp4
