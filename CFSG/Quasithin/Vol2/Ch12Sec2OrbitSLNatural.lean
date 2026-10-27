module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitCount

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Assembly.LowTwoRank
open scoped Matrix LinearAlgebra.Projectivization

theorem units_eq_one_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) (c : Kˣ) : c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  classical
  have h1 : Fintype.card Kˣ = 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.1 h1.le
  exact Subsingleton.elim _ _

theorem exists_SL_mulVec_eq {K : Type} [Field K] (hK : Nat.card K = 2) {n : ℕ}
    {x y : Fin n → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) K, (g : Matrix (Fin n) (Fin n) K) *ᵥ x = y := by
  have h1 : MulAction.IsPretransitive (Matrix.SpecialLinearGroup (Fin n) K) (ℙ K (Fin n → K)) :=
    inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin n) K)
    (Projectivization.mk K x hx) (Projectivization.mk K y hy)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hg
  obtain ⟨c, hc⟩ := hg
  refine ⟨g, ?_⟩
  rw [units_eq_one_of_card_two hK c, one_smul] at hc
  exact hc.symm

theorem orbitSLNatural :
    ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (n : ℕ),
      (n = 3 ∨ n = 4 ∨ n = 5) → BinaryNaturalSL H ⊤ ⊥ n 1 →
        OrbitLengthsIn H [2 ^ n - 1] ∧ OrbitsSeparated H := by
  intro V _ _ H n _ hH
  obtain ⟨K, _, _, hK, hR⟩ := hH
  obtain ⟨π, β, hR⟩ := (realizes_iff _ H ⊤ ⊥).1 hR
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ g ∈ H, (g : MulAut V) v = w := by
    intro v w hv hw
    refine exists_eq_of_transitive hR (fun m _ m' _ hm hm' => ?_) hv hw
    have hm1 : Multiplicative.toAdd (α := Fin n → K) m ≠ 0 := fun h => hm (by
      rw [show m = 1 from Multiplicative.toAdd.injective h]
      exact Subgroup.one_mem _)
    have hm1' : Multiplicative.toAdd (α := Fin n → K) m' ≠ 0 := fun h => hm' (by
      rw [show m' = 1 from Multiplicative.toAdd.injective h]
      exact Subgroup.one_mem _)
    obtain ⟨g, hg⟩ := exists_SL_mulVec_eq hK2 hm1 hm1'
    have hgS : Matrix.SpecialLinearGroup.toGL g ∈ StatedSL n K :=
      Subgroup.subset_closure (by simp)
    refine ⟨⟨_, hgS⟩, 1, Subgroup.one_mem _, ?_⟩
    rw [mul_one]
    change Multiplicative.ofAdd
      (((Matrix.SpecialLinearGroup.toGL g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        Multiplicative.toAdd (α := Fin n → K) m) = m'
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hg]
    rfl
  have h := orbits_of_transitive H htrans
  have hcard : Nat.card V = 2 ^ n := by
    have h1 := card_eq_of_realizesBy hR
    have h2 : Nat.card ↥(FFModel.nat (StatedSL n K)).ker = 1 := Subgroup.card_bot
    have h3 : Nat.card ↥(FFModel.nat (StatedSL n K)).sec = 2 ^ n := by
      change Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin n → K))) = 2 ^ n
      rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, hK2]
    rw [h2, mul_one, h3] at h1
    exact h1
  rwa [hcard] at h

end CFSG.Quasithin.H13.Orbit
