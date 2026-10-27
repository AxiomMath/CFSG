module

public import CFSG.Quasithin.Background.E2TwoProofAS
public import CFSG.Quasithin.Background.E2TwoProofA6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.Quasithin.SteinbergBSLinearThreeRoot
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

namespace E2P

theorem inf_projStabilizer_le_linear {F : Type} [Field F] [Finite F] [CharP F 2] :
    LinearFlag.projStabilizer (LinearFlag.flagSpace 3 F 1) ⊓
        LinearFlag.projStabilizer (LinearFlag.flagSpace 3 F 2) ≤
      Subgroup.normalizer
        (LinearFlag.projUnitriangular 3 F : Set (LinearFlag.projectiveSL 3 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SteinbergBS.projStabilizer_inf_eq_projUpperTriangular,
    LinearFlag.normalizer_projUnitriangular 2]

theorem inf_projStabilizer_le_symplectic {F : Type} [Field F] [Finite F] [CharP F 2] :
    SymplecticHigher.projStabilizer 2 F (SymplecticFlag.flag 2 F 1) ⊓
        SymplecticHigher.projStabilizer 2 F (SymplecticFlag.flag 2 F 2) ≤
      Subgroup.normalizer (SymplecticFlag.projUnipotent 2 F :
        Set (StatedProj (StatedSp 2 F))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SymplecticHigher.normalizer_projUnipotent 2 (by norm_num)]
  rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
  have hz : t⁻¹ * s ∈ SymplecticHigher.spScalars 2 F := by
    rw [← SymplecticHigher.ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hts, inv_mul_cancel]
  have hs2 : s ∈ SymplecticFlag.stabilizer 2 F (SymplecticFlag.flag 2 F 2) := by
    have e : s = t * (t⁻¹ * s) := by group
    rw [e]
    exact mul_mem ht (SymplecticHigher.spScalars_le_stabilizer _ hz)
  refine ⟨s, ?_, rfl⟩
  show s ∈ SymplecticFlag.borelSubgroup 2 F
  rw [SymplecticFlag.mem_borelSubgroup]
  intro i hi hi2
  rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
  · exact hs
  · exact hs2

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem ASHyp.isSylow_subgroupOf (hX : ASHyp K T M) :
    IsSylowTwoOf ((T ⊓ K).subgroupOf K) (⊤ : Subgroup ↥K) := by
  have h := isSylowTwoOf_map_top_equiv (MulEquiv.refl ↥K) hX.isSylow_inf
  have e : (MulEquiv.refl ↥K).toMonoidHom = MonoidHom.id ↥K := rfl
  rwa [e, Subgroup.map_id] at h

theorem ASHyp.rankTwo_of_residual (hX : ASHyp K T M) {P : Fin 2 → Subgroup ↥K}
    (hRes : Setup.X6.ResidualOvergroupsAt ↥K ((T ⊓ K).subgroupOf K) P)
    (hB : P 0 ⊓ P 1 ≤ Subgroup.normalizer (((T ⊓ K).subgroupOf K : Subgroup ↥K) : Set ↥K)) :
    E2.IsDiagramNontrivial T K (T ⊓ K) ∧ E2.IsBorelIn K (M ⊓ K) := by
  obtain ⟨hne, hUP, hmax, -⟩ := hRes
  refine hX.rankTwo (MulEquiv.refl ↥K) hX.isSylow_subgroupOf (hUP 0) (hUP 1) hne
    (fun Y hY => ?_) hB
  rw [← covBy_top_iff, hmax Y hY, Fin.exists_fin_two]

theorem ASHyp.l3 (hX : ASHyp K T M) {n : ℕ} (h : IsPSL 3 2 n ↥K) :
    E2.IsDiagramNontrivial T K (T ⊓ K) ∧ E2.IsBorelIn K (M ⊓ K) := by
  obtain ⟨F, hF, hFin, hCh, φ, -, hφ, hRes, -⟩ :=
    Setup.X7a.even_rank_two_residual_linear h hX.isSylow_subgroupOf
  refine hX.rankTwo_of_residual hRes ?_
  have h1 := Subgroup.map_mono (f := φ.symm.toMonoidHom) (inf_projStabilizer_le_linear (F := F))
  rw [Subgroup.map_inf _ _ _ φ.symm.injective, Subgroup.map_equiv_normalizer_eq, ← hφ,
    Subgroup.map_map] at h1
  have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  rw [e, Subgroup.map_id] at h1
  exact h1

theorem ASHyp.sp4 (hX : ASHyp K T M) {n : ℕ} (h : IsPSp4 2 n ↥K) :
    E2.IsDiagramNontrivial T K (T ⊓ K) ∧ E2.IsBorelIn K (M ⊓ K) := by
  obtain ⟨F, hF, hFin, hCh, φ, -, hφ, hRes, -⟩ :=
    Setup.X7a.even_rank_two_residual_symplectic h hX.isSylow_subgroupOf
  refine hX.rankTwo_of_residual hRes ?_
  have h1 := Subgroup.map_mono (f := φ.symm.toMonoidHom)
    (inf_projStabilizer_le_symplectic (F := F))
  rw [Subgroup.map_inf _ _ _ φ.symm.injective, Subgroup.map_equiv_normalizer_eq, ← hφ,
    Subgroup.map_map] at h1
  have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  rw [e, Subgroup.map_id] at h1
  exact h1

theorem e22L3Sp4Fam : E22L3Sp4Fam := by
  intro X _ _ K T M hX n hn h
  rcases h with h | h
  · exact hX.l3 h
  · by_cases hn1 : n = 1
    · subst hn1
      obtain ⟨e⟩ := isSp4Prime_one_iff.mp h
      exact hX.a6 e
    · exact hX.sp4 ((isSp4Prime_of_ne hn1).mp h)

end E2P

end CFSG.Quasithin
