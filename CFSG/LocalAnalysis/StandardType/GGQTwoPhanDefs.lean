module

public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagUnitary
public import CFSG.LocalAnalysis.StandardType.GGPhanSuBridge
public import CFSG.ClassicalInvolution.Phan.Assembly
public import CFSG.ClassicalInvolution.Phan.Universal

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan
open CFSG.StandardType
open CFSG.Open
open CFSG.LieType.Universal

@[expose] def AdjacentTripleFourMarked (K : Type) [Field K] [Finite K] [CharP K 2] {X : Type}
    [Group X] {n : ℕ} (U : Fin n → Subgroup X) (W : Fin n → Fin n → Subgroup X) : Prop :=
  ∀ i j k : Fin n, (j : ℕ) = i + 1 → (k : ℕ) = j + 1 →
    ∃ θ : Su K 2 1 4 →* X, Function.Injective θ ∧ θ.range = W i j ⊔ W j k ∧
      (blockEmb2 K 2 1 3 0).range.map θ = U i ∧ (blockEmb2 K 2 1 3 1).range.map θ = U j ∧
      (blockEmb2 K 2 1 3 2).range.map θ = U k ∧
      (blockEmb3 K 2 1 3 0 (by norm_num)).range.map θ = W i j ∧
      (blockEmb3 K 2 1 3 1 (by norm_num)).range.map θ = W j k

structure QTwoWeakPhanSystem (K : Type) [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] (n : ℕ) (H : Subgroup G)
    (U : Fin n → Subgroup G) (W : Fin n → Fin n → Subgroup G) : Prop where
  card_four : Nat.card K = 4
  four_le : 4 ≤ n
  iso : ∀ i, Nonempty (Su K 2 1 2 ≃* U i)
  join : ∀ i j : Fin n, i < j → (i : ℕ) + 1 < (j : ℕ) → W i j = U i ⊔ U j
  comm : ∀ i j : Fin n, i < j → (i : ℕ) + 1 < (j : ℕ) →
    ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x
  pair : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 →
    UnitaryBlockStandardPair K 2 1 (W i j) (U i) (U j)
  gen : (⨆ (i : Fin n) (j : Fin n) (_ : i < j), W i j) = H
  adj : AdjacentTripleFourMarked K U W
  farNodeEdge : ∀ i j k : Fin n, (k : ℕ) = (j : ℕ) + 1 →
    ((i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 2 < (i : ℕ)) →
    ∀ x ∈ U i, ∀ y ∈ W j k, x * y = y * x
  farEdgeEdge : ∀ i j k l : Fin n, (k : ℕ) = (i : ℕ) + 1 → (l : ℕ) = (j : ℕ) + 1 →
    ((i : ℕ) + 2 < (j : ℕ) ∨ (j : ℕ) + 2 < (i : ℕ)) →
    ∀ x ∈ W i k, ∀ y ∈ W j l, x * y = y * x

def BSCompletion : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) {G : Type} [Group G] [Finite G]
    (H : Subgroup G) (U : Fin n → Subgroup G) (W : Fin n → Fin n → Subgroup G),
    5 ≤ n → QTwoWeakPhanSystem K n H U W →
    ∃ ψ : Su K 2 1 (n + 1) →* G,
      ψ.range = H ∧ ψ.ker ≤ Subgroup.center (Su K 2 1 (n + 1))

private theorem admissible_PSU_one {N : ℕ} (hN : 6 ≤ N) :
    StatedLieAdmissible .PSU N 2 1 := by
  refine ⟨Nat.prime_two, by norm_num, by omega, ?_⟩
  intro h
  have h' : N = 3 := (Prod.mk.inj h).1
  omega

private theorem bnRank_PSU_three {N : ℕ} (hN : 6 ≤ N) : 3 ≤ bnRank .PSU N := by
  rw [bnRank]
  omega

section Glue

theorem ggSecFiveData_of_psi_PSU_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L D J : Subgroup G} {N : ℕ} (hN : 6 ≤ N)
    (ψ : (ggU .PSU N 1).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSU N 1).K)
    (hrange : ψ.range = ggG0 p B x L D J) :
    GGSecFiveData p B x L D J :=
  Or.inr (Or.inr ⟨.PSU, N, 1,
    ggSecFivePres_of_psi_PSU (admissible_PSU_one hN) (bnRank_PSU_three hN) ψ hker hrange⟩)

theorem ggSecFiveData_of_psi_PSU_su {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {N : ℕ} (hK : Nat.card K = 4) (hN : 6 ≤ N)
    (ψ : Su K 2 1 N →* G)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 1 N))
    (hrange : ψ.range = ggG0 p B x L D J) :
    GGSecFiveData p B x L D J := by
  obtain ⟨e⟩ := nonempty_su_equiv_lieUniversalPSU (p := 2) (f := 1) Nat.prime_two K
    (by simpa using hK) N
  have hrange' : (ψ.comp e.symm.toMonoidHom).range = ggG0 p B x L D J := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, Subgroup.map_top]
    exact hrange
  have hker' : (ψ.comp e.symm.toMonoidHom).ker ≤
      Subgroup.center (lieUniversal .PSU N 2 1 Nat.prime_two).K := by
    intro g hg
    have h1 : e.symm g ∈ Subgroup.center (Su K 2 1 N) := hker hg
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro h
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h1 (e.symm h)
  exact ggSecFiveData_of_psi_PSU_one (p := p) (B := B) (x := x) (L := L) (D := D) (J := J)
    hN (ψ.comp e.symm.toMonoidHom) hker' hrange'

theorem ggSecFiveData_of_qTwoWeakPhanSystem {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (H : Subgroup G) (U : Fin n → Subgroup G) (W : Fin n → Fin n → Subgroup G)
    (hSys : QTwoWeakPhanSystem K n H U W) (hH : H = ggG0 p B x L D J)
    (hBS : BSCompletion) :
    GGSecFiveData p B x L D J := by
  obtain ⟨ψ, hrange, hker⟩ := hBS K n H U W hn hSys
  exact ggSecFiveData_of_psi_PSU_su hSys.card_four (by omega) ψ hker
    (by rw [hrange, hH])

end Glue

end CFSG.StandardType.QTwo

end
