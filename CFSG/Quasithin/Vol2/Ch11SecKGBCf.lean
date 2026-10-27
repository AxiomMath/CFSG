module

public import CFSG.Quasithin.Vol2.Ch11SecKGBCc
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroupSp

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.C10KG

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K]

theorem torusHom_eq_lam_mul (t : Fin 2 → Kˣ) :
    torusHom t = lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1)) := by
  rw [lam_sl2Diag, lam_sl2Diag, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp

theorem lam_conj_sl2W (a : Kˣ) :
    lam (0 : Fin 2) sl2W * lam 0 (sl2Diag a) * (lam 0 sl2W)⁻¹ =
      (lam (0 : Fin 2) (sl2Diag a) : StatedSp 2 K)⁻¹ := by
  rw [← map_inv (lam 0) sl2W, ← map_mul, ← map_mul, sl2W_mul_sl2Diag, mul_inv_cancel_right,
    ← map_inv (lam 0), ← map_inv sl2Diag]

variable [Finite K] [CharP K 2]

theorem isPGroup_commutator_sp4 {Y : Type} [Group Y] [Finite Y]
    (φ : Y →* StatedProj (StatedSp 2 K)) (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker))
    (Q : Sylow 2 (StatedProj (StatedSp 2 K))) :
    IsPGroup 2 ↥⁅(Subgroup.normalizer ((Q : Subgroup (StatedProj (StatedSp 2 K))) :
        Set (StatedProj (StatedSp 2 K)))).comap φ,
      (Subgroup.normalizer ((Q : Subgroup (StatedProj (StatedSp 2 K))) :
        Set (StatedProj (StatedSp 2 K)))).comap φ⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hNU : Subgroup.normalizer ((U : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))) = projBorel 2 K := by
    rw [hU]
    exact (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.sylow_normalizers
      (K := K) (r := 2) 2 (by norm_num)).2.1
  refine isPGroup_commutator_of_weyl_data φ hφ hZ hodd U
    (A₁ := ((proj 2 K).comp ((lam (0 : Fin 2)).comp sl2Diag)).range)
    (A₂ := ((proj 2 K).comp ((lam (1 : Fin 2)).comp sl2Diag)).range)
    (w := proj 2 K (lam 0 sl2W)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ Q
  · intro x hx
    rw [hNU] at hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨u, hu, t, ⟨s, rfl⟩, rfl⟩ := CFSG.QuasithinUnique.Setup.X7a.exists_unipotent_mul_torus hb
    refine ⟨proj 2 K u, hU ▸ Subgroup.mem_map_of_mem _ hu, proj 2 K (torusHom s), ?_,
      map_mul _ _ _⟩
    rw [torusHom_eq_lam_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨s 0, rfl⟩)
      (Subgroup.mem_sup_right ⟨s 1, rfl⟩)
  · rw [hNU]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      refine Subgroup.mem_map_of_mem _ (torus_le_borelSubgroup ?_)
      simp only [MonoidHom.comp_apply]
      rw [lam_sl2Diag]
      exact torusHom_mem_torus _
    · rintro _ ⟨a, rfl⟩
      refine Subgroup.mem_map_of_mem _ (torus_le_borelSubgroup ?_)
      simp only [MonoidHom.comp_apply]
      rw [lam_sl2Diag]
      exact torusHom_mem_torus _
  · exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  · exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, (commute_lam_lam (by decide) _ _).eq]
  · rintro _ ⟨a, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, lam_conj_sl2W, map_inv]
  · rintro _ ⟨b, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, (commute_lam_lam (by decide) _ _).eq,
      mul_inv_cancel_right]

end CFSG.Quasithin.Vol2.Ch11.SecB.C10KG
