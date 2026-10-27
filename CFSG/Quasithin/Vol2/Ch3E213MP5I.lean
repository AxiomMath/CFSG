module

public import CFSG.Quasithin.Vol2.Ch3E213MP5H
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Vol2.Ch3E213MP5F

public section

namespace CFSG.Quasithin.Ch3E213M.P5

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {A : Type} [Group A] [Finite A] {K : Subgroup A} [K.Normal]

theorem model_of_setting {S B E : Subgroup A} {n : ℕ}
    (hS : IsSylowTwoOf S ⊤) (hC : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1)
    (hPSL : IsPSL 3 2 n ↥K)
    (hdiag : ∀ P : Subgroup A, IsMaxParabolic2 K P →
      K ⊓ Subgroup.normalizer ((S ⊓ K : Subgroup A) : Set A) ≤ P →
        ¬ S ≤ Subgroup.normalizer (P : Set A))
    (hBorel : ∃ S₀ : Subgroup A, IsSylowTwoOf S₀ K ∧
      B ⊓ K = K ⊓ Subgroup.normalizer (S₀ : Set A))
    (hSB : S ≤ B) (hES : E ≤ S) (hSE : S ≤ Subgroup.normalizer (E : Set A))
    (hE2 : ∀ x ∈ E, x * x = 1) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (θ : ↥K ≃* projectiveSL 3 k),
      Nat.card k = 2 ^ n ∧
      ((S ⊓ K).subgroupOf K).map θ.toMonoidHom = projUnitriangular 3 k ∧
      ((B ⊓ K).subgroupOf K).map θ.toMonoidHom = projUpperTriangular 3 k ∧
      E ≤ ((pzz k).map θ.symm.toMonoidHom).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : IsSylowTwoOf (S ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hS le_top (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  obtain ⟨k, _, _, _, θ, hk, hθ, hR, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_linear hPSL
      (isSylowTwoOf_subgroupOf_top hSK)
  have hk' : ∃ m : ℕ, Nat.card k = 2 ^ m := ⟨n, hk⟩
  have hNθ : (Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K)).map
      θ.toMonoidHom = projUpperTriangular 3 k := by
    rw [Subgroup.map_equiv_normalizer_eq, hθ, normalizer_projUnitriangular 2]
  obtain ⟨S₀, hS₀, hB⟩ := hBorel
  have hBK := inf_normalizer_eq_of_borel hSK hS₀ hB (le_inf (inf_le_left.trans hSB) inf_le_right)
  have hBθ : ((B ⊓ K).subgroupOf K).map θ.toMonoidHom = projUpperTriangular 3 k := by
    rw [subgroupOf_eq_normalizer hBK, hNθ]
  set P₀ : Subgroup K := (projStabilizer (flagSpace 3 k 1)).map θ.symm.toMonoidHom with hP₀
  have hcov : P₀ ⋖ ⊤ := (hR.2.2.1 _ (hR.2.1 0)).2 ⟨0, rfl⟩
  have hNP : Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K) ≤ P₀ :=
    calc Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K)
        = ((Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup K) : Set K)).map
            θ.toMonoidHom).map θ.symm.toMonoidHom := (map_symm_map θ _).symm
      _ = (projUpperTriangular 3 k).map θ.symm.toMonoidHom := by rw [hNθ]
      _ ≤ P₀ := Subgroup.map_mono (projUpperTriangular_le_projStabilizer 1)
  obtain ⟨hmax, hle⟩ := isMaxParabolic2_of_isCoatom hSK hcov hNP
  obtain ⟨t, htS, ht⟩ := Set.not_subset.mp (hdiag _ hmax hle)
  exact ⟨k, inferInstance, inferInstance, inferInstance, θ, hk, hθ, hBθ,
    le_pzz_of_core hk' θ hθ hC ⟨t, htS, map_conjModel_ne θ ht⟩ hES hSE hE2⟩

end CFSG.Quasithin.Ch3E213M.P5
