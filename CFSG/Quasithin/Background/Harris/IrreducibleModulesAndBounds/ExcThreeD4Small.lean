module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4Final
public import CFSG.Quasithin.Background.SmithB45TorD4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


theorem trialityD4_dim_bound {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (W : Type) [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    (τ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* MulAut W) (hτ : Function.Injective τ) :
    2 ^ (24 * f) ≤ Nat.card W := by
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
  let L : Subgroup (MulAut W) := τ.range
  let e0 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* L := MonoidHom.ofInjective hτ
  have hZL : Subgroup.center L = ⊥ := center_eq_bot_of_mulEquiv_generic e0.symm hZ
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    ((QuotientGroup.quotientMulEquivOfEq hZL).trans (QuotientGroup.quotientBot (G := ↥L))).trans
      e0.symm
  exact CFSG.Quasithin.B45Tor.two_pow_le_card hf hK σ hσ hW L hZL e

theorem false_of_trialityD4_small {f : ℕ} (hf : f = 1 ∨ f = 2)
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f) : False := by
  have hf1 : 1 ≤ f := by omega
  exact false_of_trialityD4_of_dim hf1 (ρ := 24 * f) (by omega)
    (fun K _ _ hK σ hσ W _ _ hW τ hτ => trialityD4_dim_bound hf1 K hK σ hσ W hW τ hτ) h hX

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
