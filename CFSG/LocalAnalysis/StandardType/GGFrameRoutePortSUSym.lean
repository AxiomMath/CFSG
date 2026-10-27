module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortRankSym
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortSUSymTorus
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortSUSymGens

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly
open CFSG.StandardType.FrameRoute.SUSix

variable {K : Type} [Field K]

private lemma map_permH_swap_pow (hK : Nat.card K = 4) (a b : Fin 6) :
    (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
      (permH hK (Equiv.swap a b))) ^ 2 ^ 1 = 1 := by
  simpa using map_permH_sq hK (Equiv.swap a b)
    (by rw [pow_two, Equiv.swap_mul_self])

private noncomputable def s0 (hK : Nat.card K = 4) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2) :=
  LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
    (permH hK (Equiv.swap 2 3))

private noncomputable def s1 (hK : Nat.card K = 4) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2) :=
  LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
    (permH hK (Equiv.swap 4 5))

private lemma e0_inv_s0 (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : ω ^ 3 = 1) :
    s0 hK * e hK ω 0 * (s0 hK)⁻¹ =
      (e hK ω 0)⁻¹ :=
  conj_inv_of hK ω (Equiv.swap 2 3) 0
    (d0 ω) (d0_prod hK ω)
    (E_single_zero hK ω)
    (fun j => congrFun (d0_swap23 hω) j)

private lemma e1_fix_s0 (hK : Nat.card K = 4) (ω : Kˣ) :
    s0 hK * e hK ω 1 * (s0 hK)⁻¹ =
      e hK ω 1 :=
  conj_fix_of hK ω (Equiv.swap 2 3) 1
    (d1 ω) (d1_prod hK ω)
    (E_single_one hK ω)
    (fun j => congrFun (swap_fix (d := d1 ω) (by simp [d1])) j)

private lemma e2_fix_s0 (hK : Nat.card K = 4) (ω : Kˣ) :
    s0 hK * e hK ω 2 * (s0 hK)⁻¹ =
      e hK ω 2 :=
  conj_fix_of hK ω (Equiv.swap 2 3) 2
    (d2 ω) (d2_prod hK ω)
    (E_single_two hK ω)
    (fun j => congrFun (swap_fix (d := d2 ω) (by simp [d2])) j)

private lemma e1_inv_s1 (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : ω ^ 3 = 1) :
    s1 hK * e hK ω 1 * (s1 hK)⁻¹ =
      (e hK ω 1)⁻¹ :=
  conj_inv_of hK ω (Equiv.swap 4 5) 1
    (d1 ω) (d1_prod hK ω)
    (E_single_one hK ω)
    (fun j => congrFun (d1_swap45 hω) j)

private lemma e2_fix_s1 (hK : Nat.card K = 4) (ω : Kˣ) :
    s1 hK * e hK ω 2 * (s1 hK)⁻¹ =
      e hK ω 2 :=
  conj_fix_of hK ω (Equiv.swap 4 5) 2
    (d2 ω) (d2_prod hK ω)
    (E_single_two hK ω)
    (fun j => congrFun (swap_fix (d := d2 ω) (by simp [d2])) j)

private lemma e_pair (hK : Nat.card K = 4) (ω : Kˣ) (hω : ω ^ 3 = 1)
    {i j : Fin 3} (hij : i ≠ j) :
    ∃ s : LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2),
      (∃ k : ℕ, s ^ 2 ^ k = 1) ∧
        ((s * e hK ω i * s⁻¹ = e hK ω i ∧
            s * e hK ω j * s⁻¹ = (e hK ω j)⁻¹) ∨
          (s * e hK ω i * s⁻¹ = (e hK ω i)⁻¹ ∧
            s * e hK ω j * s⁻¹ = e hK ω j)) := by
  fin_cases i
  · fin_cases j
    · exact absurd rfl hij
    · exact ⟨s0 hK,
        ⟨1, map_permH_swap_pow hK 2 3⟩,
        Or.inr ⟨e0_inv_s0 hK hω,
          e1_fix_s0 hK ω⟩⟩
    · exact ⟨s0 hK,
        ⟨1, map_permH_swap_pow hK 2 3⟩,
        Or.inr ⟨e0_inv_s0 hK hω,
          e2_fix_s0 hK ω⟩⟩
  · fin_cases j
    · exact ⟨s0 hK,
        ⟨1, map_permH_swap_pow hK 2 3⟩,
        Or.inl ⟨e1_fix_s0 hK ω,
          e0_inv_s0 hK hω⟩⟩
    · exact absurd rfl hij
    · exact ⟨s1 hK,
        ⟨1, map_permH_swap_pow hK 4 5⟩,
        Or.inr ⟨e1_inv_s1 hK hω,
          e2_fix_s1 hK ω⟩⟩
  · fin_cases j
    · exact ⟨s0 hK,
        ⟨1, map_permH_swap_pow hK 2 3⟩,
        Or.inl ⟨e2_fix_s0 hK ω,
          e0_inv_s0 hK hω⟩⟩
    · exact ⟨s1 hK,
        ⟨1, map_permH_swap_pow hK 4 5⟩,
        Or.inl ⟨e2_fix_s1 hK ω,
          e1_inv_s1 hK hω⟩⟩
    · exact absurd rfl hij

theorem rank3SymGens_largeEvenProjSU_six {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2)) = ⊥) :
    Rank3SymGens (LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2)) 3 := by
  obtain ⟨ω, hω1⟩ := exists_unit_ne_one hK
  have hω3 : ω ^ 3 = 1 := unit_cube hK ω
  have hωord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  refine ⟨e hK ω, e_pow hK hω3,
    e_commute hK ω, ?_, ?_, ?_, ?_, ?_⟩
  · exact e_card hK hωord
  · exact e_inter_center hK ω hZ
  · exact exists_t hK ω hZ
  · exact fun i => inverts hK hω3 i
  · exact fun i j hij => e_pair hK ω hω3 hij

end CFSG.StandardType.FrameRoute

end
