module

public import CFSG.Timmesfeld.ARS.CaseHBasic
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Steinberg.G2.Extras
public import CFSG.LieType.Steinberg.TwistedD4.Defs
public import CFSG.LieType.Steinberg.Exceptional.Fields

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Blueprint.Chevalley

inductive NSLType : (r : ℕ) → Matrix (Fin r) (Fin r) ℤ → Fin r → Prop
  | symplectic {n : ℕ} (hn : 3 ≤ n) (i₀ : Fin n) (hi₀ : i₀.val + 1 < n) :
      NSLType n (Symplectic.cartanC n) i₀
  | orthogonal {m : ℕ} (hm : 3 ≤ m) (i₀ : Fin m) (hi₀ : i₀.val + 1 < m) :
      NSLType m (Spin.cartanB m) i₀
  | g2 (i₀ : Fin (Tag.rank .G2)) (hi₀ : i₀.val = 0) : NSLType (Tag.rank .G2) (Tag.cartan .G2) i₀
  | f4 (i₀ : Fin (Tag.rank .F4)) (hi₀ : i₀.val < 2) : NSLType (Tag.rank .F4) (Tag.cartan .F4) i₀

class inductive NSLConcrete : {K : Type} → [Group K] → UniversalRootDatum K → Prop
  | symplectic (n : ℕ) (F : Type) [Field F] : NSLConcrete (Symplectic.rootDatum n F)
  | minus (n : ℕ) {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
      NSLConcrete (Spin.Twisted.minusDatum n hirr)
  | g2 (K : Type) [Field K] : NSLConcrete (Adjoint.g2Datum K)
  | twistedD4 (f : ℕ) [Fact (1 ≤ f)] :
      NSLConcrete (TwistedD4.twistedDatum (iterateFrobenius (GaloisField 2 (3 * f)) 2 f))
  | f4 (K : Type) [Field K] : NSLConcrete (Adjoint.f4Datum K)
  | twistedE6 (f : ℕ) [Fact (1 ≤ f)] : NSLConcrete (Exceptional.twistedE6Datum 2 f)

attribute [instance] NSLConcrete.symplectic NSLConcrete.minus NSLConcrete.g2
  NSLConcrete.twistedD4 NSLConcrete.f4 NSLConcrete.twistedE6

structure NSLFrameData (G : Type) [Group G] (R : Set (Subgroup G)) where
  K : Type
  [group : Group K]
  D : UniversalRootDatum K
  n : Fin D.rank → K
  H : Fin D.rank → Subgroup K
  hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H
  hext : SteinbergExtras D n H
  hdiv : D.divisible = ∅
  i₀ : Fin D.rank
  type : NSLType D.rank D.cartan i₀
  pgroup : ∀ γ ∈ D.roots, IsPGroup 2 ↥(D.rootGroup γ)
  Ψ : K →* G
  surj : Function.Surjective Ψ
  ker : Ψ.ker ≤ Subgroup.center K
  mem : (D.rootGroup (Pi.single i₀ 1)).map Ψ ∈ R
  opp : Opposite ((D.rootGroup (Pi.single i₀ 1)).map Ψ) ((D.rootGroup (-Pi.single i₀ 1)).map Ψ)
  comm : D.cartan = Symplectic.cartanC D.rank → ∀ i j, D.cartan i j = -2 →
    Commuting (D.rootGroup (Pi.single i 1)) (D.rootGroup (Pi.single i 1 + Pi.single j 1))
  conc : NSLConcrete D

attribute [instance] NSLFrameData.group

@[expose] def NSLFrame (G : Type) [Group G] (R : Set (Subgroup G)) : Prop :=
  Nonempty (NSLFrameData G R)

@[expose] def NSLData (G : Type) [Group G] (R : Set (Subgroup G)) : Prop :=
  SigmaEqLambda R ∨ NSLFrame G R

theorem NSLData.of_frame {G : Type} [Group G] {R : Set (Subgroup G)} (F : NSLFrameData G R) :
    NSLData G R :=
  Or.inr ⟨F⟩

theorem NSLData.of_sigmaEqLambda {G : Type} [Group G] {R : Set (Subgroup G)}
    (h : SigmaEqLambda R) : NSLData G R :=
  Or.inl h

theorem NSLType.symplecticDatum {n : ℕ} (hn : 3 ≤ n) (F : Type) [Field F] :
    NSLType (Symplectic.rootDatum n F).rank (Symplectic.rootDatum n F).cartan ⟨0, by
      change 0 < n; omega⟩ :=
  NSLType.symplectic hn ⟨0, by omega⟩ (by simp only; omega)

theorem NSLType.minusDatum {n : ℕ} (hn : 4 ≤ n) {K : Type*} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    NSLType (Spin.Twisted.minusDatum n hirr).rank (Spin.Twisted.minusDatum n hirr).cartan ⟨0, by
      change 0 < n - 1; omega⟩ :=
  NSLType.orthogonal (m := n - 1) (by omega) ⟨0, by omega⟩ (by simp only; omega)

theorem NSLType.g2Datum (K : Type) [Field K] (i₀ : Fin (Adjoint.g2Datum K).rank)
    (hi₀ : i₀.val = 0) : NSLType (Adjoint.g2Datum K).rank (Adjoint.g2Datum K).cartan i₀ :=
  NSLType.g2 i₀ hi₀

theorem NSLType.twistedD4Datum {K : Type} [Field K] (σ : K →+* K)
    (i₀ : Fin (TwistedD4.twistedDatum σ).rank) (hi₀ : i₀.val = 0) :
    NSLType (TwistedD4.twistedDatum σ).rank (TwistedD4.twistedDatum σ).cartan i₀ :=
  NSLType.g2 i₀ hi₀

theorem NSLType.f4Datum (K : Type) [Field K] (i₀ : Fin (Adjoint.f4Datum K).rank)
    (hi₀ : i₀.val < 2) : NSLType (Adjoint.f4Datum K).rank (Adjoint.f4Datum K).cartan i₀ :=
  NSLType.f4 i₀ hi₀

theorem NSLType.twistedE6Datum (k : Type*) [Field k] (θ : k →+* k)
    (i₀ : Fin (TwistedE6.twistedDatum k θ).rank) (hi₀ : i₀.val < 2) :
    NSLType (TwistedE6.twistedDatum k θ).rank (TwistedE6.twistedDatum k θ).cartan i₀ :=
  NSLType.f4 i₀ hi₀

end CFSG.Timmesfeld.ARS
