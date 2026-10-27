module

public import CFSG.Quasithin.H13.NQCatKG68Singer
public import CFSG.Quasithin.H13.NQCatLieCartanL3
public import CFSG.Quasithin.H13.NQCatLieCentralL3

public section

namespace CFSG.Quasithin.H13.KG68.Singer.L3

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.H13.KG4413 CFSG.Quasithin.H13.NQCat
  CFSG.Quasithin.H13.NQCat.SL3

variable {K : Type} [Field K]

theorem cartanSingerCover_l3 [Finite K] [CharP K 2] : CartanSingerCover (projectiveSL 3 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  set z : K → projectiveSL 3 K := fun c => proj 3 K (tv (show (0 : Fin 3) ≠ 2 by decide) c)
    with hz
  have htv0 : tv (show (0 : Fin 3) ≠ 2 by decide) (0 : K) = 1 :=
    Subtype.ext (by rw [coe_tv]; simp [transvection])
  have hcomm : ∀ c, ∀ t ∈ projUnitriangular 3 K, z c * t = t * z c := by
    intro c t ht
    obtain ⟨v, hv, rfl⟩ := ht
    have h01 : ((tv (show (0 : Fin 3) ≠ 2 by decide) c : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
      rw [coe_tv]
      simp [transvection]
    have h12 : ((tv (show (0 : Fin 3) ≠ 2 by decide) c : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
      rw [coe_tv]
      simp [transvection]
    have h := LieCentral.L3.commute_of_entries_eq_zero
      (tv_mem_unitriangular (show (0 : Fin 3) < 2 by decide) c) hv h01 h12
    rw [hz]
    simp only
    rw [← map_mul, ← map_mul, h]
  have hact : ∀ h ∈ dL3 K, ∃ u : Kˣ, ActsBy z h u := by
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨s.1 * (s.1 * s.2), fun c => ?_⟩
    rw [hz]
    simp only
    rw [← map_inv, ← map_mul, ← map_mul, LieCartan.L3.dg3_conj_tv]
    simp only [Units.val_mul]
  refine cartanSingerCover_of_rootCenter Q (z := z)
    (fun c c' h => LieCartan.L3.eq_of_proj_tv_eq h) (by rw [hz]; simp only; rw [htv0, map_one])
    (fun g hg hgc => ?_) (fun n hn => ?_) (fun u => ?_)
  ·
    rw [hQ] at hg hgc
    obtain ⟨u, hu, rfl⟩ := hg
    have hc : ∀ {a b : Fin 3} (hab : a < b),
        proj 3 K (tv hab.ne 1) * proj 3 K u = proj 3 K u * proj 3 K (tv hab.ne 1) := by
      intro a b hab
      exact (hgc _ ⟨tv hab.ne 1, tv_mem_unitriangular hab 1, rfl⟩).symm
    obtain ⟨h01, h12⟩ := LieMult.entries_eq_zero_of_commute hu
      (hc (show (0 : Fin 3) < 1 by decide)) (hc (show (1 : Fin 3) < 2 by decide))
    refine ⟨(u : Matrix (Fin 3) (Fin 3) K) 0 2, ?_⟩
    have e0 : ∀ {a b : Fin 3} (hab : a ≠ b), tv hab (0 : K) = 1 := fun hab =>
      Subtype.ext (by rw [coe_tv]; simp [transvection])
    have hu' := eq_tv_mul_of_mem_unitriangular hu
    rw [h01, h12, mul_zero, sub_zero, e0, e0, one_mul, mul_one] at hu'
    rw [hz]
    exact (congrArg (proj 3 K) hu').symm
  ·
    rw [hQ, normalizer_projUnitriangular 2] at hn
    have hn' := projUpperTriangular_le hn
    rw [sup_comm] at hn'
    exact exists_actsBy_of_mem_sup hcomm hact hn'
  · refine ⟨proj 3 K (dg3 (1, u)), ?_, ?_⟩
    · rw [hQ]
      exact dL3_le_normalizer ⟨_, ⟨(1, u), rfl⟩, rfl⟩
    · obtain ⟨v, hv⟩ := hact _ ⟨_, ⟨(1, u), rfl⟩, rfl⟩
      have hvu : v = u := by
        have h1 := hv 1
        rw [hz] at h1
        simp only at h1
        rw [← map_inv, ← map_mul, ← map_mul, LieCartan.L3.dg3_conj_tv] at h1
        have h2 := LieCartan.L3.eq_of_proj_tv_eq h1
        rw [mul_one, mul_one] at h2
        exact Units.ext (by rw [← h2]; simp)
      rwa [hvu] at hv

end CFSG.Quasithin.H13.KG68.Singer.L3
