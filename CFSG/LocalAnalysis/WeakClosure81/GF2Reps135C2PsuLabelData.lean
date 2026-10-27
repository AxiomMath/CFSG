module

public import CFSG.LieType.Universal.Unitary.BinaryModel.CurtisType
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.ScalarCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Finset Matrix
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.HardMathSupport.GuralnickMalle
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.RootSystem
open CFSG.LieType.SpecialLinear.ExteriorModel CFSG.Quasithin.SmithCurtis
open scoped MonoidAlgebra TensorProduct

@[expose] def HasUnitaryLabel {m f : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W) [ρ.IsIrreducible]
    (ε : Fin f → Finset (Fin m)) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : CharP k 2)
    (_ : Algebra (Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m))
      ρ.asModule) k) (φ₀ : K →+* k)
    (ζ : traceZero (unitaryInvolution K 2 f)) (hζ : (ζ : K) ≠ 0)
    (y : k ⊗[Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m))
      ρ.asModule] ρ.asModule)
    (χ : SU (unitaryInvolution K 2 f) m → k) (μ : Fin (m / 2) → k),
    (curtisDatum hK m hm ζ hζ).IsCurtisType
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y χ μ ∧
      (∀ r, (⟨0, by omega⟩ : Fin m) ∉ ε r) ∧
      (∀ h ∈ (curtisDatum hK m hm ζ hζ).H, χ h = chiEps φ₀ ε h) ∧
      ∃ β : (k ⊗[Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m))
          ρ.asModule] ρ.asModule) ≃ₗ[k] BModel k ε,
        ∀ (g : SU (unitaryInvolution K 2 f) m) v,
          β (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g v) =
            suRep φ₀ m ε g (β v)

theorem exists_hasUnitaryLabel {m f : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W) [ρ.IsIrreducible]
    (hne : ∃ g, ρ g ≠ 1) :
    ∃ ε : Fin f → Finset (Fin m), HasUnitaryLabel hm hK ρ ε ∧ ∃ r, ε r ≠ ∅ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E := End (ZMod 2)[SU (unitaryInvolution K 2 f) m] ρ.asModule
  haveI : CharP E 2 := endField_charP ρ 2
  let k := AlgebraicClosure E
  obtain ⟨φ₀⟩ := nonempty_ringHom_algebraicClosure (K := E) (F₀ := K) (p := 2)
  letI : Algebra K k := φ₀.toAlgebra
  haveI : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) :=
    isSimpleRep_extendScalars_endFieldRep (ρ := ρ) (k := k)
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero (p := 2) hK
  let D := curtisDatum hK m hm ζ hζ
  have hsplit : SplitOver k D.H := curtisDatum_splitOver hK m hm ζ hζ k
  have : Finite (coxeterMatrix (isFiniteType_cartan m)).Group :=
    finite_group (isFiniteType_cartan m)
  obtain ⟨y, χ, μ, htype⟩ := D.exists_isCurtisType hsplit hsimp
  obtain ⟨ε, h0, hχ, -, β, hβ⟩ := exists_iso_suRep hK hm ζ hζ φ₀ hsimp htype
  refine ⟨ε, ⟨k, inferInstance, inferInstance, inferInstance, φ₀, ζ, hζ, y, χ, μ, htype, h0, hχ,
    β, hβ⟩, ?_⟩
  by_contra hall
  push Not at hall
  obtain ⟨g, hg⟩ := hne
  apply hg
  have h1 := suRep_eq_one_of_forall_eq_empty φ₀ hall g
  exact (extendScalars_endFieldRep_eq_one_iff (ρ := ρ) (k := k) g).mp
    ((eq_one_iff_of_equiv β hβ g).mpr h1)

end CFSG.LocalAnalysis.WeakClosure81
