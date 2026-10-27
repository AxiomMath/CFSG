module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthPolar
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

structure GGOrthSetup
    {G : Type} [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (𝒦 : Finset (Subgroup G))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V) (ι : Additive ↥Bs ≃+ V) : Prop where
  cfg : GGSecFiveRouteCfg' 3 B Bs x L D J 𝒦
  split : GGSplitLie 3 L
  fixA : ∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1
  nondeg : PolarNondeg3 Q
  dim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5
  orth : ∀ g : V ≃ₗ[ZMod 3] V, (∃ a ∈ ggAInf 3 B Bs x L D J, ggLin (p := 3) ι a = g) ↔ ∀ v, Q (g v) = Q v

@[expose] def GGOrthPres
    {G : Type} [Group G] (L : Subgroup G) (t : StatedLieTag) (n : ℕ) : Prop :=
  ∃ (f : ℕ) (ψ : (ggU t n f).K →* G), StatedLieAdmissible t n 2 f ∧ 3 ≤ bnRank t n ∧
    ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = L ∧ 3 ∣ 2 ^ f - 1

end CFSG.StandardType.OrthF3

end
