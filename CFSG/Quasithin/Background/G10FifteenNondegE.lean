module

public import CFSG.Quasithin.Background.G10FifteenNondegD
public import CFSG.Quasithin.Background.G10FifteenNondegC
public import CFSG.Quasithin.Background.G10FifteenTwist

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem nondeg_data (hq : IsQuotientOfSQTKTauCeti ↥Γ) (hSQT : SectionSQTInput)
    (h1212 : G1212Stmt) (hSimple : InspectSimple) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I) {i : V} (hi : i ∈ I ⊓ perp B v₁) (hi0 : i ≠ 0)
    (hFT : FullTransvections (stabilizerOf X I) (I ⊓ perp B v₁) i hi)
    (hnd : NondegOn B I) (hnle : ¬ I ≤ perp B v₁) :
    ∃ f : LinearMap.BilinForm (ZMod 2) ↥I,
      G121Data f (restrictRange (normalClosure Γ L) I hI.1 ⊔
          restrictRange (stabilizerOf X I) I (invariant_stabilizerOf X I))
        (restrictRange (normalClosure Γ L) I hI.1)
        (restrictRange (stabilizerOf X I) I (invariant_stabilizerOf X I)) ⟨i, hi.1⟩ ∧
      IsSimpleGroup ↥(restrictRange (normalClosure Γ L) I hI.1) ∧
      CFSG.IsStronglyQuasithin ↥(restrictRange (normalClosure Γ L) I hI.1) := by
  obtain ⟨f, hD⟩ := hyp.apply_h1212 h1212 hI hi hi0 hFT hnd hnle
  have hsimp := hSimple ↥I f _ _ _ _ hD
  have hqH : IsQuotientOfSQTKTauCeti ↥(normalClosure Γ L) := hq.of_le hyp.H_le
  have hqK : IsQuotientOfSQTKTauCeti ↥(restrictRange (normalClosure Γ L) I hI.1) :=
    isQuotientOfSQTKTauCeti_restrictRange hI.1 hqH
  have hnab : ∃ a b : ↥(restrictRange (normalClosure Γ L) I hI.1), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative ↥(restrictRange (normalClosure Γ L) I hI.1) :=
      ⟨⟨fun a b => hcon a b⟩⟩
    have : Group.IsPerfect ↥(restrictRange (normalClosure Γ L) I hI.1) := hD.K_perf
    exact Group.IsPerfect.not_isMulCommutative _ hcomm
  exact ⟨f, hD, hsimp, isStronglyQuasithin_of_simple hSQT hqK hsimp hnab⟩

theorem faithful_absurd (hq : IsQuotientOfSQTKTauCeti ↥Γ) (hSQT : SectionSQTInput)
    (h1212 : G1212Stmt) (hSimple : InspectSimple) (hOuter : InspectOuter)
    {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) {i : V} (hi : i ∈ I ⊓ perp B v₁) (hi0 : i ≠ 0)
    (hFT : FullTransvections (stabilizerOf X I) (I ⊓ perp B v₁) i hi)
    (hnd : NondegOn B I) (hnle : ¬ I ≤ perp B v₁)
    (hfaith : FaithfulOn (normalClosure Γ L) I) : False := by
  obtain ⟨f, hD, -, hqK⟩ := hyp.nondeg_data hq hSQT h1212 hSimple hI hi hi0 hFT hnd hnle
  obtain ⟨α, P, hαP, hαα, hel, hreal⟩ := hyp.twist_package hx hI.1 hfaith
  obtain ⟨g, hg⟩ := hOuter ↥I f _ _ _ _ hD hqK α P hαP hαα hel
  exact hne (hfix x hx (hreal ⟨g, hg⟩))

end G108Hyp

end G11

end CFSG.Quasithin
