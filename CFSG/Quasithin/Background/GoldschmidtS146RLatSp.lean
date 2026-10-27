module

public import CFSG.Quasithin.Background.GoldschmidtS146RLatGen
public import CFSG.Quasithin.EmptyFaithful.SzN2Sp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X7a
open CFSG.QuasithinUnique.Setup.X6 (ResidualOvergroupsAt)

section Sp4

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem latShape_statedProj_sp_two {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    LatShape (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K))
      ((unipotent 2 K).map (proj 2 K)) := by
  have hK' : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨n, hK⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hres : ResidualOvergroupsAt
      (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) := symplectic_two_residualOvergroupsAt hK'
  have hk : Group.IsSolvable (proj 2 K).ker := by
    rw [ker_proj, spScalars_eq_bot]
    infer_instance
  have hsolv : ∀ Y : Subgroup (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K)),
      (unipotent 2 K).map (proj 2 K) ≤ Y →
      Group.IsSolvable ↥Y →
      Y ≤ Subgroup.normalizer (((unipotent 2 K).map (proj 2 K) : Subgroup _) : Set _) :=
    fun Y hVY hY => solvable_overgroup_of_cover (proj 2 K)
      (proj_surjective (r := 2) (K := K)) hk
      (fun Y' hY' hs => by
        rw [normalizer_unipotent]
        exact CFSG.Quasithin.SzN2.sp4_le_borel_of_solvable hK4 hY' hs) hVY hY
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q2 K j), ∀ y ∈ perfectCore (Q2 K j),
      proj 2 K x = proj 2 K y → x = y := fun j x _ y _ h => proj_injective_charTwo h
  let eN : ∀ j : Fin 2, ↥(perfectCore (Q2 K j)) ≃* ↥(perfectCore ((Q2 K j).map (proj 2 K))) :=
    fun j => perfectCoreMapEquiv (proj 2 K) (Q2 K j) (hinj j)
  refine latShape_of_rank_two hres hsolv hn hK (fun j => (blkN j).comp (eN j).symm.toMonoidHom)
    (fun j => (blkN_surjective hK4 j).comp (eN j).symm.surjective) fun j z => ?_
  obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK' j ⟨(eN j).symm z.1, z.2⟩
  have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ (eN j).symm.injective).mp this

theorem latShape_of_isPSp_four {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsPSp4 2 n X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : LatShape X U := by
  obtain ⟨K, hF, hFin, hcp, φ, hcard, hφ, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_symplectic hX hU
  have h2 := (latShape_statedProj_sp_two hn hcard).map φ.symm
  have e : ((unipotent 2 K).map (proj 2 K)).map φ.symm.toMonoidHom = U := by
    have h3 : (U.map φ.toMonoidHom).map φ.symm.toMonoidHom = U := by
      simpa using map_map_symm' φ.symm U
    rw [← h3, hφ]
    rfl
  rwa [e] at h2

end Sp4

end CFSG.Quasithin.GoldS146R
