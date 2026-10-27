module

public import CFSG.Quasithin.H13.A6S1384b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

@[expose] def wedgePair : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

@[expose] def wedge2 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  fun p q => A (wedgePair p).1 (wedgePair q).1 * A (wedgePair p).2 (wedgePair q).2 +
    A (wedgePair p).1 (wedgePair q).2 * A (wedgePair p).2 (wedgePair q).1

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

@[expose] def HatData (K : Subgroup G) (ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)) : Prop :=
  S.G1 ≤ Subgroup.normalizer (K : Set G) ∧ K ⊔ T = S.G1 ∧ S.L1 ≤ K ∧
    (∀ h ∈ S.G1, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 S.G1) → h ∈ pCoreOf 2 S.G1) ∧
    IsHatA6 L ∧ Function.Surjective ρ ∧ (∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) ∧
    Function.Surjective β ∧ (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
    ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) =
        ((ρ h : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (β u))

theorem exists_hatData (hst : S.Struct13827) (hhat : IsHatA6 L) :
    ∃ (K : Subgroup G) (ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
      (β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)), S.HatData K ρ β := by
  obtain ⟨K, hKN, hKT, hL1K, hFs, hcase, -⟩ := hst
  rcases hcase with ⟨hn, -⟩ | ⟨-, ρ, hρs, hker, β, hβs, hβk, hβe⟩
  · exact absurd hhat hn
  · exact ⟨K, ρ, β, hKN, hKT, hL1K, hFs, hhat, hρs, hker, hβs, hβk, hβe⟩

end Setting4

end CFSG.Quasithin.H13.A6

