module

public import CFSG.Quasithin.AppendixH.H9.H92.RadCard
public import CFSG.Quasithin.AppendixH.H9.H92.Gamma.GammaCheckOfOrbit
public import CFSG.Quasithin.AppendixH.H9.H92.Gamma.RadOrbits

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem gammaCheck_three_eq_top_of_le_radV1 (D : Subgroup (PairN 5)) (hD : D ≤ V1n 5)
    (hr : rk ↥D = 2 ∨ rk ↥D = 3) (A : Subgroup (MulAut (PairN 5))) (hA : A ≤ RadV1 5 D) :
    E3.gammaCheck 3 A = ⊤ := by
  have hP : IsPGroup 2 ↥A := fun g => ⟨1, Subtype.ext (by
    rw [pow_one]
    exact (isElemAbelian2_radV1 5 D).2 g.1 (hA g.2))⟩
  have hdim : Module.finrank (ZMod 2) (v1Space 5 D) = 2 ∨
      Module.finrank (ZMod 2) (v1Space 5 D) = 3 := by
    rw [finrank_v1Space_eq_rk D hD]
    exact hr
  have hdual := finrank_dotPerp_add 5 (v1Space 5 D)
  have hpow : ∀ d : ℕ, d ≤ 3 → 2 ^ d ≤ 2 ^ 3 := fun d hd => Nat.pow_le_pow_right (by norm_num) hd
  have h1 : ∀ a : Fin 5 → ZMod 2, pairVec a 0 ∈ E3.gammaCheck 3 A := fun a =>
    mem_gammaCheck_of_orbit_subset hP
      (S := (fun e => pairVec (a + e) 0) '' (v1Space 5 D : Set (Fin 5 → ZMod 2)))
      (fun g hg => by
        obtain ⟨e, he, hge⟩ := radV1_apply_pairVec_natural (hA hg) a
        exact ⟨e, he, hge.symm⟩)
      ((ncard_image_submodule_le_two_pow_finrank _ _).trans (hpow _ (by omega)))
  have h2 : ∀ b : Fin 5 → ZMod 2, pairVec 0 b ∈ E3.gammaCheck 3 A := fun b =>
    mem_gammaCheck_of_orbit_subset hP
      (S := (fun e => pairVec 0 (b + e)) '' (dotPerp 5 (v1Space 5 D) : Set (Fin 5 → ZMod 2)))
      (fun g hg => by
        obtain ⟨e, he, hge⟩ := radV1_apply_pairVec_dual (hA hg) b
        exact ⟨e, he, hge.symm⟩)
      ((ncard_image_submodule_le_two_pow_finrank _ _).trans (hpow _ (by omega)))
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  have hx : pairVec a b = pairVec a 0 * pairVec 0 b := by
    rw [pairVec_mul, add_zero, zero_add]
  rw [hx]
  exact Subgroup.mul_mem _ (h1 a) (h2 b)

end CFSG.ASVolI.ChH
