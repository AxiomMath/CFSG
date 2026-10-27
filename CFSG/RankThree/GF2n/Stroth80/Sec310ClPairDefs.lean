module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

@[expose] def ElPts (F : LinearMap.BilinForm K V) (H : Subgroup (V ≃ₗ[K] V)) : Set V :=
  {e | e ≠ 0 ∧ ElationFull F ((H : Set _) ∩ pointRad F e) e}

@[expose] def PairForm (F : LinearMap.BilinForm K V) (H : Subgroup (V ≃ₗ[K] V)) (e f : V)
    (Q : QuadraticForm K V) : Prop :=
  Q.polarBilin = F ∧ Q e = 0 ∧ Q f = 0 ∧ H ⊓ pointRadSubgroup F e ≤ orthSubgroup Q ∧
    H ⊓ pointRadSubgroup F f ≤ orthSubgroup Q

@[expose] def AData (F : LinearMap.BilinForm K V) (H : Subgroup (V ≃ₗ[K] V)) (e f : V)
    (a : V → K) : Prop :=
  (∀ w, F w e = 0 → F w f = 0 → ∃ g ∈ H ⊓ pointRadSubgroup F e, g f - f = w + a w • e) ∧
  (∀ (c : K) (w : V), F w e = 0 → F w f = 0 → a (c • w) = c ^ 2 * a w) ∧
  (∀ w w' : V, F w e = 0 → F w f = 0 → F w' e = 0 → F w' f = 0 →
    a (w + w') = a w + a w' + F w w') ∧
  (∀ g ∈ H ⊓ pointRadSubgroup F e, ∀ (w : V) (c : K), F w e = 0 → F w f = 0 →
    g f - f = w + c • e → c = a w) ∧
  (∀ g ∈ H ⊓ pointRadSubgroup F f, ∀ (w : V) (c : K), F w e = 0 → F w f = 0 →
    g e - e = w + c • f → c = a w)

end CFSG.RankThree.GF2n.Stroth80.Classify
