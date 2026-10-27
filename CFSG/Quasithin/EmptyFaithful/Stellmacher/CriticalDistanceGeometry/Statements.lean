module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.SitSigma
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom

section At

variable {G : Type} [Group G] [Finite G]

@[expose] def Hss26AAt (H M : Subgroup G) : Prop :=
  1 < bMin H M → ∀ (δ μ : Geo H M) (U : Subgroup G), F53.SitSigma δ μ U → Qv μ ≤ U →
    Zv δ ≤ centerOf (stab δ)

@[expose] def Hss27S3At (H M : Subgroup G) : Prop :=
  2 ≤ bMin H M → ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → vtype α = true →
    bAt α = bMin H M →
    stab α ≤ Subgroup.normalizer ((Zv α ⊔ Zv β : Subgroup G) : Set G) →
    Zv β ≤ centerOf (stab β)

omit [Finite G] in
theorem Hss27S3At_of_Hss27At {H M : Subgroup G} (h : Hss27At H M) : Hss27S3At H M :=
  fun hb α β hαβ _ hα hn => h hb α β hαβ hα hn

@[expose] def Hss31At (H M : Subgroup G) : Prop :=
  ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → vtype α = true → bAt α = bMin H M →
    bMin H M < bAt β → Zv β ≤ centerOf (stab β)

@[expose] def Hss28ModAt (H M : Subgroup G) : Prop :=
  ∀ δ ν : Geo H M, ν ∈ nbrs δ → vtype δ = false → Qv δ ≤ Qv ν → ¬ thompsonJ (Qv ν) ≤ Qv δ →
    stab δ ⊓ Subgroup.centralizer ((quasithinOmegaOneCenter (Qv δ) : Subgroup G) : Set G) =
      Qv δ →
    (∀ g ∈ Qv ν, g ^ 2 ∈ Qv δ) ∧
      ¬ quasithinOmegaOneCenter (stab δ ⊓ stab ν) ≤ centerOf (stab δ)

end At

@[expose] def Hss26A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S → Hss26AAt H M

end F53.Stellmacher

end CFSG.Quasithin
