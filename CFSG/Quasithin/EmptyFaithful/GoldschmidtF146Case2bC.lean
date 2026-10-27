module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bB
public import CFSG.Quasithin.Background.GoldschmidtS146RLat

public section

namespace CFSG.Quasithin.F146Field.Case2b

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.GoldS146R
open scoped MatrixGroups


theorem levi_of_mulEquiv {A B : Type*} [Group A] [Group B] {F : Type} [Field F] (e : A ≃* B)
    (b : A →* SL(2, F)) (hb : Function.Surjective b) (hk : IsPGroup 2 b.ker) :
    ∃ g : B →* SL(2, F), Function.Surjective g ∧ IsPGroup 2 g.ker := by
  refine ⟨b.comp e.symm.toMonoidHom, hb.comp e.symm.surjective, ?_⟩
  have h : (b.comp e.symm.toMonoidHom).ker = b.ker.map e.toMonoidHom := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨e.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [h]
  exact hk.map _

section L3a

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem levi_model_three {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) (j : Fin 2) :
    ∃ g : ↥(perfectCore ((Q3 K j).map (proj 3 K))) →* SL(2, K),
      Function.Surjective g ∧ IsPGroup 2 g.ker := by
  have hK' : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨m, hK⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hinj : ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j),
      proj 3 K x = proj 3 K y → x = y := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ (proj 3 K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hzN : x⁻¹ * y ∈ perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
    have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ ((ker_proj 3 K).le hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  exact levi_of_mulEquiv (perfectCoreMapEquiv (proj 3 K) (Q3 K j) hinj) (blk3 j)
    (blk3_surjective hK4 j) (blk3_ker_isPGroup hK' j)

end L3a


theorem levi_transport {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (f : X →* Y)
    (hf : Function.Injective f) (P : Subgroup X) {F : Type} [Field F]
    (g : ↥(perfectCore P) →* SL(2, F)) (hg : Function.Surjective g) (hk : IsPGroup 2 g.ker) :
    ∃ g' : ↥(perfectCore (P.map f)) →* SL(2, F), Function.Surjective g' ∧ IsPGroup 2 g'.ker :=
  levi_of_mulEquiv (perfectCoreMapEquiv f P fun _ _ _ _ h => hf h) g hg hk

section L3

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem parabolics_of_isPSL_three {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 2 ≤ m)
    (hX : IsPSL 3 2 m X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (P : Fin 2 → Subgroup X),
      Nat.card F = 2 ^ m ∧ ResidualOvergroupsAt X U P ∧
      (∀ j, Subgroup.normalizer (U : Set X) ≤ P j) ∧ (∀ j, U ≤ perfectCore (P j)) ∧
      ∀ j, ∃ g : ↥(perfectCore (P j)) →* SL(2, F), Function.Surjective g ∧ IsPGroup 2 g.ker := by
  obtain ⟨K, hF, hFin, hcp, φ, hcard, hφ, hres, -⟩ := even_rank_two_residual_linear hX hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨K, hF, hFin, fun j : Fin 2 => ((Q3 K j).map (proj 3 K)).map φ.symm.toMonoidHom, hcard,
    hres, fun j x hx => ?_, fun j => ?_, fun j => ?_⟩
  · have h1 : φ x ∈ Subgroup.normalizer (projUnitriangular 3 K : Set _) := by
      rw [← hφ, GoldS146R.normalizer_map_equiv]
      exact ⟨x, hx, rfl⟩
    rw [normalizer_projUnitriangular 2] at h1
    exact ⟨φ x, Subgroup.map_mono (upperTriangular_le_Q3 j) h1, by simp⟩
  · have hU' : U = (projUnitriangular 3 K).map φ.symm.toMonoidHom := by
      rw [← hφ]
      simpa using (map_map_symm' φ.symm U).symm
    have h1 : projUnitriangular 3 K ≤ perfectCore ((Q3 K j).map (proj 3 K)) := by
      rw [← map_perfectCore]
      exact Subgroup.map_mono (unitriangular_le_perfectCore_Q3 hK4 j)
    rw [hU', ← map_perfectCore]
    exact Subgroup.map_mono h1
  · obtain ⟨g, hg, hk⟩ := levi_model_three hm hcard j
    exact levi_transport φ.symm.toMonoidHom φ.symm.injective _ g hg hk

end L3


section Sp4

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem levi_model_sp {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) (j : Fin 2) :
    ∃ g : ↥(perfectCore ((Q2 K j).map (proj 2 K))) →* SL(2, K),
      Function.Surjective g ∧ IsPGroup 2 g.ker := by
  have hK' : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨m, hK⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact levi_of_mulEquiv (perfectCoreMapEquiv (proj 2 K) (Q2 K j)
    fun _ _ _ _ h => proj_injective_charTwo h) (blkN j) (blkN_surjective hK4 j)
    (blkN_ker_isPGroup hK' j)

theorem parabolics_of_isPSp_four {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 2 ≤ m)
    (hX : IsPSp4 2 m X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (P : Fin 2 → Subgroup X),
      Nat.card F = 2 ^ m ∧ ResidualOvergroupsAt X U P ∧
      (∀ j, Subgroup.normalizer (U : Set X) ≤ P j) ∧ (∀ j, U ≤ perfectCore (P j)) ∧
      ∀ j, ∃ g : ↥(perfectCore (P j)) →* SL(2, F), Function.Surjective g ∧ IsPGroup 2 g.ker := by
  obtain ⟨K, hF, hFin, hcp, φ, hcard, hφ, hres, -⟩ := even_rank_two_residual_symplectic hX hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨K, hF, hFin, fun j : Fin 2 => ((Q2 K j).map (proj 2 K)).map φ.symm.toMonoidHom, hcard,
    hres, fun j x hx => ?_, fun j => ?_, fun j => ?_⟩
  · have h1 : φ x ∈ Subgroup.normalizer (projUnipotent 2 K : Set _) := by
      rw [← hφ, GoldS146R.normalizer_map_equiv]
      exact ⟨x, hx, rfl⟩
    rw [normalizer_projUnipotent (r := 2) 2 (by norm_num)] at h1
    exact ⟨φ x, Subgroup.map_mono (borelSubgroup_le_Q2 j) h1, by simp⟩
  · have hU' : U = (projUnipotent 2 K).map φ.symm.toMonoidHom := by
      rw [← hφ]
      simpa using (map_map_symm' φ.symm U).symm
    have h1 : projUnipotent 2 K ≤ perfectCore ((Q2 K j).map (proj 2 K)) := by
      rw [← map_perfectCore]
      exact Subgroup.map_mono (unipotent_le_perfectCore_Q2 hK4 j)
    rw [hU', ← map_perfectCore]
    exact Subgroup.map_mono h1
  · obtain ⟨g, hg, hk⟩ := levi_model_sp hm hcard j
    exact levi_transport φ.symm.toMonoidHom φ.symm.injective _ g hg hk

end Sp4

end CFSG.Quasithin.F146Field.Case2b
