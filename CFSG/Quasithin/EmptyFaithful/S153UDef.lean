module

public import CFSG.Quasithin.EmptyFaithful.S153TDef

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def InputC61S3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I T T₀ : Subgroup G),
    IsSQTKTC I → CharTwo I → IsSylowTwoOf T₀ I → IsPGroup 2 T → T₀ ≤ T → T₀.relIndex T = 2 →
    T ⊓ I = T₀ →
    (∀ C : Subgroup G, C ≤ T₀ → C ≠ ⊥ → T ≤ Subgroup.normalizer (C : Set G) →
      I ⊓ Subgroup.normalizer (C : Set G) ≤ T₀) →
    (pCoreOf 2 I).relIndex T₀ = 2 →
    (∀ x ∈ pCoreOf 2 I, ∀ y ∈ pCoreOf 2 I, x * y = y * x) ∧ Nat.card (pCoreOf 2 I) ≤ 8

theorem InputC61S3.toAbel (h : InputC61S3) : Input1463FourAbel :=
  fun G _ _ I T T₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 => (h G I T T₀ h1 h2 h3 h4 h5 h6 h7 h8 h9).1

end CFSG.Quasithin
