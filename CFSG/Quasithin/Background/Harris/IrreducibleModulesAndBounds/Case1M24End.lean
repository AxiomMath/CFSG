module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin.G11 CFSG.Quasithin.Background.Harris.OrdinaryProofs

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem endIsField_one_of_prime_finrank {H : Subgroup (GLV V)} (hH : IsIrr H ⊤)
    (hp : (Module.finrank (ZMod 2) V).Prime) (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) :
    EndIsField H 1 := by
  classical
  haveI := endCommutant_nontrivial hH
  haveI := endCommutant_noZeroDivisors hH
  haveI : IsDomain (endCommutant H) := NoZeroDivisors.to_isDomain _
  haveI : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  haveI : Finite (endCommutant H) := Subtype.finite
  have hVnt : Nontrivial V := by
    obtain ⟨v, -, hv⟩ := (Submodule.ne_bot_iff _).mp (ne_of_lt hH.2.1).symm
    exact ⟨v, 0, hv⟩
  letI : Field (endCommutant H) := (Finite.isDomain_to_isField _).toField
  letI : Module (endCommutant H) V := Module.compHom V (Subalgebra.val (endCommutant H)).toRingHom
  haveI : Module.Finite (endCommutant H) V := inferInstance
  have hcardV : Nat.card V = Nat.card (endCommutant H) ^ Module.finrank (endCommutant H) V :=
    Module.natCard_eq_pow_finrank
  have hcardK : Nat.card (endCommutant H) = 2 ^ Module.finrank (ZMod 2) (endCommutant H) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := endCommutant H)
    rwa [Nat.card_zmod] at this
  have hcardV2 : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod] at this
  have hrs : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (endCommutant H) * Module.finrank (endCommutant H) V := by
    rw [hcardK, ← pow_mul, hcardV2] at hcardV
    exact Nat.pow_right_injective (le_refl 2) hcardV
  rw [hrs] at hp
  rcases Nat.prime_mul_iff.1 hp with ⟨-, hs⟩ | ⟨-, hr⟩
  ·
    exfalso
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hone := (finrank_eq_one_iff_of_nonzero' (K := endCommutant H) v hv).1 hs
    have hcl : ∀ g ∈ H, ∃ c : endCommutant H, ∀ w, (c : Module.End (ZMod 2) V) w = (g : GLV V) w := by
      intro g hg
      obtain ⟨c, hc⟩ := hone ((g : GLV V) v)
      refine ⟨c, fun w => ?_⟩
      obtain ⟨c', rfl⟩ := hone w
      have hc' : (c : Module.End (ZMod 2) V) v = (g : GLV V) v := hc
      have h1 := endCommutant_apply_comm c'.2 hg v
      have h2 : ((c * c' : endCommutant H) : Module.End (ZMod 2) V) v =
          ((c' * c : endCommutant H) : Module.End (ZMod 2) V) v := by rw [mul_comm]
      simp only [Subalgebra.coe_mul, Module.End.mul_apply] at h2
      show (c : Module.End (ZMod 2) V) ((c' : Module.End (ZMod 2) V) v) = (g : GLV V) ((c' : Module.End (ZMod 2) V) v)
      calc (c : Module.End (ZMod 2) V) ((c' : Module.End (ZMod 2) V) v)
          = (c' : Module.End (ZMod 2) V) ((c : Module.End (ZMod 2) V) v) := h2
        _ = (c' : Module.End (ZMod 2) V) ((g : GLV V) v) := by rw [hc']
        _ = (g : GLV V) ((c' : Module.End (ZMod 2) V) v) := h1
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    obtain ⟨ca, hca⟩ := hcl a ha
    obtain ⟨cb, hcb⟩ := hcl b hb
    apply hab
    ext x
    have h2 : ((ca * cb : endCommutant H) : Module.End (ZMod 2) V) x =
        ((cb * ca : endCommutant H) : Module.End (ZMod 2) V) x := by rw [mul_comm]
    simp only [Subalgebra.coe_mul, Module.End.mul_apply] at h2
    show (a : GLV V) ((b : GLV V) x) = (b : GLV V) ((a : GLV V) x)
    calc (a : GLV V) ((b : GLV V) x) = (a : GLV V) ((cb : Module.End (ZMod 2) V) x) := by
          rw [hcb]
      _ = (ca : Module.End (ZMod 2) V) ((cb : Module.End (ZMod 2) V) x) := (hca _).symm
      _ = (cb : Module.End (ZMod 2) V) ((ca : Module.End (ZMod 2) V) x) := h2
      _ = (cb : Module.End (ZMod 2) V) ((a : GLV V) x) := by rw [hca]
      _ = (b : GLV V) ((a : GLV V) x) := hcb _
  ·
    have hK : Nat.card (endCommutant H) = 2 ^ 1 := by rw [hcardK, hr]
    exact ⟨GaloisField.algEquivGaloisField 2 1 hK⟩

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
