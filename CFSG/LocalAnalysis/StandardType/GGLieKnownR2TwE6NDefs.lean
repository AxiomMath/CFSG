module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad
public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Steinberg.BruhatWeyl
public import CFSG.LieType.Steinberg.CentralExt.BorelIndex
public import CFSG.LieType.Steinberg.TwistedE6.Clause0
public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.Steinberg.TwistedE6.Generation

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
open scoped commutatorElement

theorem twE6_hct
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    IsCTGroupDatum (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem
      (weylAction (twistedDatum k θ).isFiniteType) (twistedDatum k θ).roots
      (twistedDatum k θ).rootGroup (nHat θ) (hHat k θ) :=
  twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)

abbrev twE6W
    (k : Type) [Field k] (θ : k →+* k) : Type :=
  (coxeterMatrix (twistedDatum k θ).isFiniteType).Group

@[expose] noncomputable def twE6N
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (w : twE6W k θ) :
    fixedGroup k θ :=
  nrep (twE6_hct θ hθ) w

noncomputable abbrev twE6RA
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  (twistedDatum k θ).rootGroup twE6Alpha

noncomputable abbrev twE6NA
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  Subgroup.normalizer ((twE6RA θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ))

noncomputable abbrev twE6PosUnip
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  posUnipotent (twistedDatum k θ)

noncomputable abbrev twE6Borel
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  borel (twistedDatum k θ) (hHat k θ)

noncomputable abbrev twE6Cj
    {k : Type} [Field k] {θ : k →+* k} (g : fixedGroup k θ) (H : Subgroup (fixedGroup k θ)) :
    Subgroup (fixedGroup k θ) :=
  H.map (MulAut.conj g).toMonoidHom

@[expose] def twE6A : Set (Fin (Tag.rank .F4) → ℤ) :=
  {![1, 2, 4, 2], ![1, 3, 4, 2], ![2, 3, 4, 2]}

@[expose] noncomputable def twE6V
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  ggSub (twistedDatum k θ) twE6A

@[expose] noncomputable def twE6Va
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  ggSub (twistedDatum k θ) (insert twE6Alpha twE6A)

@[expose] def twE6LongPos0 : Set (Fin (Tag.rank .F4) → ℤ) :=
  {![0, 1, 0, 0], ![0, 1, 2, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 2, 0], ![1, 2, 2, 0]}

@[expose] noncomputable def twE6UM
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  ggSub (twistedDatum k θ) twE6LongPos0

@[expose] def twE6Psi : Set (Fin (Tag.rank .F4) → ℤ) :=
  {γ | 1 ≤ γ twE6Last ∨ γ ∈ twE6LongPos0}

@[expose] noncomputable def twE6W0L
    (k : Type) [Field k] (θ : k →+* k) : twE6W k θ :=
  (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.wordProd
    [nf 0, nf 1, nf 2, nf 0, nf 1, nf 2, nf 0, nf 1, nf 2]

@[expose] def TorusRegularAlpha3
    {k : Type} [Field k] (θ : k →+* k) : Prop :=
  ∀ y ∈ (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1),
    (∀ t ∈ (⨆ i, hHat k θ i : Subgroup (fixedGroup k θ)), t * y * t⁻¹ = y) → y = 1

@[expose] noncomputable def twE6V3
    (k : Type) [Field k] (θ : k →+* k) : twE6W k θ :=
  (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2) * twE6W0L k θ

end CFSG.StandardType.LieKnownR2.Short
