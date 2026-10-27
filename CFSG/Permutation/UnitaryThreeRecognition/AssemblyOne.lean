module

public import CFSG.Permutation.UnitaryThreeRecognition.BridgeMain
public import CFSG.Permutation.UnitaryThreeRecognition.EndgameMain

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

theorem coordHyp_of {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω}
    {j s : G} {p f d : ℕ} (S : StdHyp G Q a b j s p f d) {K : Type*} [Field K]
    {J : HermitianForm 3 K} (φ : Q ≃* Coord J)
    (h1 : ∀ t (ht : t ∈ pairStab G a b), ∃ k : Kˣ, ∀ x : Q,
      φ ⟨t * x * t⁻¹, S.root.normal t ht.1 x x.2⟩ = hermitianTorusAction J k (φ x))
    (h2 : ∀ k : Kˣ, ∃ t, ∃ ht : t ∈ pairStab G a b, ∀ x : Q,
      φ ⟨t * x * t⁻¹, S.root.normal t ht.1 x x.2⟩ = hermitianTorusAction J k (φ x))
    (h3 : ∀ z : Q, (z : G) ∈ centQ Q j ↔ (φ z : K × K).1 = 0) : CoordHyp Q a b j J φ where
  torus t ht := by
    obtain ⟨k, hk⟩ := h1 t ht
    exact ⟨k, fun x _ => hk x⟩
  torus_surj k := by
    obtain ⟨t, ht, hk⟩ := h2 k
    exact ⟨t, ht, fun x _ => hk x⟩
  center := h3

theorem statedClassicalModel_of_coordHyp_coprime {G Ω : Type} [Group G] [Finite G]
    [IsSimpleGroup G] [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]
    (h2 : IsMultiplyPretransitive G Ω 2) {Q : Subgroup G} {a b : Ω} {j s : G} {p f d : ℕ}
    (S : StdHyp G Q a b j s p f d) (hQ1 : Q ≠ ⊥) {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hK : Nat.card K = (p ^ f) ^ 2) (hconj : ∀ x : K, J.conj x = x ^ (p ^ f))
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) {φ : Q ≃* Coord J}
    (C : CoordHyp Q a b j J φ) (hcop : Nat.Coprime 3 (p ^ f + 1)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f := by
  obtain ⟨s', hs'2, hs'a, hs'⟩ := C.exists_point_weyl_of_coprime S hK hconj hcop
  exact S.root.statedClassicalModel_of_sMap_eq_weyl h2 hQ1 S.hb hs'a hs'2 p f S.hpp S.hpodd S.hf
    J hJ hK hfix φ hs'

end CFSG.UnitaryThreeRecognition
