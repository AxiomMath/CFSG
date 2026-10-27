module

public import CFSG.Quasithin.Background.GoldschmidtS146RLatGen
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X7a

section L3

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem latShape_projectiveSL_three {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    LatShape (projectiveSL 3 K) ((unitriangular 3 K).map (proj 3 K)) := by
  have hK' : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨n, hK⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hres := linear_three_residual_of_cover hK' (proj 3 K) (proj_surjective 3 K)
    (ker_proj 3 K).le
  have hk : Group.IsSolvable (proj 3 K).ker := by
    rw [ker_proj, scalars_eq_center]
    infer_instance
  have hsolv : ∀ Y : Subgroup (projectiveSL 3 K), (unitriangular 3 K).map (proj 3 K) ≤ Y →
      Group.IsSolvable ↥Y →
      Y ≤ Subgroup.normalizer (((unitriangular 3 K).map (proj 3 K) : Subgroup _) : Set _) :=
    fun Y hVY hY => solvable_overgroup_of_cover (proj 3 K) (proj_surjective 3 K) hk
      (fun Y' hY' hs => by
        rw [normalizer_unitriangular]
        exact CFSG.Quasithin.SzN2.sl3_le_upperTriangular_of_solvable hK4 hY' hs) hVY hY
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j),
      proj 3 K x = proj 3 K y → x = y := by
    intro j x hx y hy hxy
    have hz : x⁻¹ * y ∈ (proj 3 K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hzN : x⁻¹ * y ∈ perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
    have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ ((ker_proj 3 K).le hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  let eN : ∀ j : Fin 2, ↥(perfectCore (Q3 K j)) ≃* ↥(perfectCore ((Q3 K j).map (proj 3 K))) :=
    fun j => perfectCoreMapEquiv (proj 3 K) (Q3 K j) (hinj j)
  refine latShape_of_rank_two hres hsolv hn hK (fun j => (blk3 j).comp (eN j).symm.toMonoidHom)
    (fun j => (blk3_surjective hK4 j).comp (eN j).symm.surjective) fun j z => ?_
  obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK' j ⟨(eN j).symm z.1, z.2⟩
  have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ (eN j).symm.injective).mp this

end L3

theorem latShape_of_isPSL_three {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsPSL 3 2 n X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : LatShape X U := by
  obtain ⟨K, hF, hFin, hcp, φ, hcard, hφ, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_linear hX hU
  have h2 := (latShape_projectiveSL_three hn hcard).map φ.symm
  have e : ((unitriangular 3 K).map (proj 3 K)).map φ.symm.toMonoidHom = U := by
    have h3 : (U.map φ.toMonoidHom).map φ.symm.toMonoidHom = U := by
      simpa using map_map_symm' φ.symm U
    rw [← h3, hφ]
    rfl
  rwa [e] at h2

end CFSG.Quasithin.GoldS146R
