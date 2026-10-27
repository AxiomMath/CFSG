module

public import CFSG.Quasithin.Background.G10FifteenTwist
public import CFSG.Quasithin.Background.G10FifteenInputs
public import CFSG.Quasithin.Background.G10FifteenIso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem three_of_isotropic (hOut : OuterGLInput) (h10 : G1010Concl Γ v₁ X L)
    (h11 : G1011Concl Γ v₁ X L) (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) (hiso : Isotropic B I) :
    ¬ AutAll (normalClosure Γ L) I ∨ Module.finrank (ZMod 2) I = 4 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hAut, hfr⟩ := hcon
  have hfaith := hyp.faithfulOn_of_isotropic h10 h11 h12 hI hfix hx hne hiso
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hn : ¬ HIso (normalClosure Γ L) I (conjSub x I) := fun h => hne (hfix x hx h)
  obtain ⟨α, P, hαP, hαα, hel, hreal⟩ := hyp.twist_package hx hI.1 hfaith
  have hK : ∀ g : GLV ↥I, g ∈ restrictRange (normalClosure Γ L) I hI.1 := by
    intro g
    obtain ⟨k, hk, hkg⟩ := hAut g
    exact ⟨⟨k, hk⟩, LinearEquiv.ext fun i => Subtype.ext (hkg i)⟩
  have h3 : 3 ≤ Module.finrank (ZMod 2) ↥I := hyp.two_lt_finrank hirr
  obtain ⟨s, hs, t, ht, hnot⟩ := hOut ↥I (restrictRange (normalClosure Γ L) I hI.1) hK h3 hfr α P
    hαP hαα (fun hc => hn (hreal hc))
  exact hnot (hel s hs t ht)

end G108Hyp

end G11

end CFSG.Quasithin
