module

public import CFSG.Quasithin.H13.L32NItems143

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

structure Hyp147 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) : Prop where
  hyp : Hyp14_3_1One G T L
  fsu : FSU G T L V
  abelian : IsMulCommutative ↥(fsuU T V)

namespace L32A

variable {G : Type} [Group G]

abbrev hz (T V : Subgroup G) : Subgroup G := Subgroup.centralizer (fsuV1 T V : Set G)

abbrev kz (T V : Subgroup G) : Subgroup G := oTwoUpper (hz T V)

abbrev sL (T L V : Subgroup G) : Subgroup G := conjClosure (fsuU T V) L

abbrev l1 (T L V : Subgroup G) : Subgroup G :=
  oTwoUpper (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G))

abbrev m1 (T L V : Subgroup G) : Subgroup G := hz T V ⊓ Subgroup.normalizer (L : Set G)

@[expose] def IsHz (T L V H : Subgroup G) : Prop :=
  InH (l1 T L V ⊔ T) H ∧ ¬ H ≤ Subgroup.normalizer (L : Set G) ∧
    H ≤ Subgroup.normalizer (fsuV1 T V : Set G)

@[expose] def IsElemSection (X Y : Subgroup G) : Prop :=
  Y ≤ X ∧ ∀ x ∈ X, ∀ x' ∈ X, x * x' * x⁻¹ * x'⁻¹ ∈ Y ∧ x ^ 2 ∈ Y

@[expose] def IsL24Section (K X Y : Subgroup G) : Prop :=
  K ≤ Subgroup.normalizer (X : Set G) ∧
    ∃ (π : K →* Matrix.SpecialLinearGroup (Fin 2) RuType.F4)
      (β : X →* Multiplicative (Fin 2 → RuType.F4)),
      Function.Surjective π ∧ π.ker = (pCoreOf 2 K).subgroupOf K ∧
      Function.Surjective β ∧ β.ker = Y.subgroupOf X ∧
      ∀ (k : K) (x x' : X), (x' : G) = k * x * (k : G)⁻¹ →
        β x' = Multiplicative.ofAdd (((π k : Matrix.SpecialLinearGroup (Fin 2) RuType.F4) :
          Matrix (Fin 2) (Fin 2) RuType.F4).mulVec (Multiplicative.toAdd (β x)))

@[expose] def IsSteinbergSection (L S V : Subgroup G) : Prop :=
  ∀ θ : L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective θ →
    θ.ker = S.subgroupOf L →
    ∃ χ : S →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)),
      χ.ker = V.subgroupOf S ∧ (∀ s, RuType.IsTraceZero (Multiplicative.toAdd (χ s))) ∧
      (∀ A, RuType.IsTraceZero A → ∃ s, χ s = Multiplicative.ofAdd A) ∧
      ∀ (l : L) (s t : S), (t : G) = l * s * (l : G)⁻¹ →
        χ t = Multiplicative.ofAdd (RuType.stAct (θ l) (Multiplicative.toAdd (χ s)))

end L32A

end CFSG.Quasithin.H13
