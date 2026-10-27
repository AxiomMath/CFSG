module

public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix commutatorElement

structure D36Norm {W : Type} [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W) : Prop where
  std : D3Std M Mp T L V
  lt : V < orbSup T V
  tT : t ∈ T
  tn : t ∉ Subgroup.normalizer (L : Set (MulAut W))
  Mp_eq : Mp = L ⊔ conjAutSub t L
  triv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v

@[expose] def D35Five {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) (V : Subgroup W) : Prop :=
  (∃ n, BinaryNaturalSL L V (V ⊓ fixV L) 3 n) ∨ (∃ n, BinaryNaturalSp4 L V (V ⊓ fixV L) n) ∨
    AlternatingNatural L V (V ⊓ fixV L) 6 ∨ BinaryNaturalSL L V (V ⊓ fixV L) 4 1 ∨
    BinaryNaturalSL L V (V ⊓ fixV L) 5 1 ∨ A7Four L V (V ⊓ fixV L)

@[expose] def D35Concl {W : Type} [CommGroup W] [Finite W] (Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) : Prop :=
  Mp = L ∧
  (∃ t ∈ T, t ∉ stabSub V) ∧
  (∀ t ∈ T, t ∉ stabSub V →
    (∀ s ∈ T, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V) ∧
      IsSumMod (orbSup T V ⊓ fixV L) V (V.map t.toMonoidHom) (orbSup T V)) ∧
  D35Five L V

@[expose] def D35 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → V < orbSup T V →
    (∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g) → D35Concl Mp T L V

@[expose] def D36Acts : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    ∀ A : Subgroup (MulAut W), A ≤ T →
      autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) →
      A ≤ stabSub (commSub (orbSup T V) L)

@[expose] def D36A38 : Prop :=
  ∀ (W : Type) [CommGroup W] (L : Subgroup (MulAut W)) (V : Subgroup W),
    A38Types ↥L → D35Five L V → IsPSL 3 2 1 ↥L ∧ BinaryNaturalSL L V (V ⊓ fixV L) 3 1

@[expose] def D3L38 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      Mp = L ⊔ conjAutSub t L →
      A38Types ↥L ∧ ⁅L, conjAutSub t L⁆ = ⊥ ∧ L ⊓ conjAutSub t L = ⊥ ∧
        ∀ s ∈ T, conjAutSub s L = L ∨ conjAutSub s L = conjAutSub t L

end CFSG.Quasithin
