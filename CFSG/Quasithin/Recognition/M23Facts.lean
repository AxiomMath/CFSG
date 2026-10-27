module

public import CFSG.Quasithin.Recognition.UniquenessSystemPairs
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Quasithin.Recognition.UniquenessSystemRecognition

public section

namespace CFSG.Quasithin.Asc94

open MulAction CFSG.Blueprint

theorem m23_four_transitive
    : IsMultiplyPretransitive ↥NativeSporadic.M23 (Fin 23) 4 := by
  rw [Sporadic.Mathieu.nativeM23_eq]
  exact CFSG.M23.M23Group.four_pretransitive

theorem m23_isUniquenessSystem
    {a b c d : Fin 23} (habcd : [a, b, c, d].Nodup) :
    IsUniquenessSystem (pairGraph (Fin 23)) (quadStab ↥NativeSporadic.M23 a b c d)
      (pairSubgraph ↥NativeSporadic.M23 habcd) (xbar habcd) (ybar habcd) :=
  pairSystem_isUniquenessSystem habcd m23_four_transitive

theorem m23_isBase
    {a b c d : Fin 23} (habcd : [a, b, c, d].Nodup) :
    IsBase ↥NativeSporadic.M23 (pairGraph (Fin 23)) (pairSubgraph ↥NativeSporadic.M23 habcd) :=
  pairSystem_isBase habcd m23_four_transitive

theorem m23_recognition
    {G : Type*} [Group G] {X : Type*} [MulAction G X] {Γ : SimpleGraph X}
    {I : Subgroup G} {ΓI : Γ.Subgraph} {x y : X} (hU : IsUniquenessSystem Γ I ΓI x y)
    {a b c d : Fin 23} (habcd : [a, b, c, d].Nodup)
    {β : stabilizer G x ≃* stabilizer ↥NativeSporadic.M23 (xbar habcd)}
    {ζ : I ≃* quadStab ↥NativeSporadic.M23 a b c d}
    (he : IsEquivalence I x y (quadStab ↥NativeSporadic.M23 a b c d) (xbar habcd) (ybar habcd)
      β ζ) :
    ∃ φ : G ≃* ↥NativeSporadic.M23, (∀ g : stabilizer G x, φ g = β g) ∧ ∀ i : I, φ i = ζ i :=
  recognition hU (m23_isUniquenessSystem habcd) he (m23_isBase habcd)
    Sporadic.Mathieu.fam_m23_simplicity.2.2

end CFSG.Quasithin.Asc94
