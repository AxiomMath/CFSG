module

public import CFSG.LocalAnalysis.StandardType.GGSpTwoPlaneTorus
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConjCompanion
import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs

public section

namespace CFSG.StandardType

namespace TwoThree

open CFSG.LieType.SteinbergBR.EvenSp CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

section Helpers

variable {K : Type} [Field K]

private theorem planeMat_eq_pairMat {r : ℕ} (i : Fin r) (g : Matrix (Fin 2) (Fin 2) K) :
    planeMat (Pi.mulSingle (M := fun _ : Fin r => Matrix (Fin 2) (Fin 2) K) i g) =
      pairMat (Sum.inl i) (Sum.inr i) g := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hab : a = b <;>
    simp_all [planeMat, pairMat, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne, Matrix.one_apply]

private theorem spCompanion_one_eq [CharP K 2] :
    CFSG.StandardType.SpJoin.spCompanion (1 : K) =
      (⟨((tGL (K := K)) : Matrix (Fin 2) (Fin 2) K), det_tGL (K := K)⟩ :
        Matrix.SpecialLinearGroup (Fin 2) K) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.StandardType.SpJoin.coe_spCompanion, tGL, CharTwo.neg_eq]

private theorem toGL_spCompanion_one [CharP K 2] :
    Matrix.SpecialLinearGroup.toGL (CFSG.StandardType.SpJoin.spCompanion (1 : K)) =
      tGL (K := K) := by
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, spCompanion_one_eq]

private theorem toGL_spPlaneZetaCompanion_one [CharP K 2]
    (ht : CFSG.StandardType.SpJoin.spCompanion (1 : K) ^ 3 = 1)
    (a : Multiplicative (ZMod 3)) :
    Matrix.SpecialLinearGroup.toGL
        (CFSG.StandardType.SpJoin.spPlaneZetaCompanion (1 : K) ht a) = tPow (K := K) a := by
  have ha : a = Multiplicative.ofAdd ((Multiplicative.toAdd a).val : ZMod 3) := by
    rw [ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [ha]
  simp only [CFSG.StandardType.SpJoin.spPlaneZetaCompanion, tPow,
    CFSG.StandardType.TableBSymp.zmodPowHom_natCast]
  rw [map_pow, toGL_spCompanion_one]

private theorem coe_spPlaneZetaCompanion_one [CharP K 2]
    (ht : CFSG.StandardType.SpJoin.spCompanion (1 : K) ^ 3 = 1)
    (a : Multiplicative (ZMod 3)) :
    ((CFSG.StandardType.SpJoin.spPlaneZetaCompanion (1 : K) ht a :
        Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((tPow (K := K) a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  simpa using congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
    (toGL_spPlaneZetaCompanion_one ht a)

private theorem spPlaneTorus_coe_apply [CharP K 2] {r : ℕ}
    (f : Fin r → Multiplicative (ZMod 3)) :
    (((spPlaneTorus (K := K) (r := r)) f : CFSG.Open.StatedSp r K) :
        GL (Fin r ⊕ Fin r) K) = planeHom (fun j => tPow (f j)) := rfl

private theorem spPlaneTorus_eq_spJoin [CharP K 2] {r : ℕ}
    (ht : CFSG.StandardType.SpJoin.spCompanion (1 : K) ^ 3 = 1) :
    (spPlaneTorus (K := K) (r := r)) =
      CFSG.StandardType.SpJoin.spPlaneTorus r
        (CFSG.StandardType.SpJoin.spPlaneZetaCompanion (1 : K) ht) := by
  apply MonoidHom.pi_ext
  intro i a
  rw [CFSG.StandardType.SpJoin.spPlaneTorus_mulSingle]
  apply Subtype.ext
  rw [spPlaneTorus_coe_apply]
  apply Units.ext
  have hfun : (fun j => ((tPow (K := K) (Pi.mulSingle
      (M := fun _ : Fin r => Multiplicative (ZMod 3)) i a j) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) =
      Pi.mulSingle (M := fun _ : Fin r => Matrix (Fin 2) (Fin 2) K) i
        ((tPow (K := K) a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Pi.mulSingle_eq_of_ne h]
  rw [planeHom_val, coe_lam, hfun, planeMat_eq_pairMat, coe_spPlaneZetaCompanion_one ht a]

end Helpers

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}

theorem exists_conj_eq_range_spPlaneTorus (hK : Nat.card K = 2)
    {A : Subgroup (CFSG.Open.StatedSp r K)} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hcard : Nat.card A = 3 ^ r) :
    ∃ g : CFSG.Open.StatedSp r K,
      A.map (MulAut.conj g).toMonoidHom = (spPlaneTorus (K := K)).range := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hirr : Irreducible
      (Polynomial.X ^ 2 + Polynomial.C (1 : K) * Polynomial.X + 1 : Polynomial K) := by
    simpa using
      CFSG.HardMathSupport.Curtis.Coordinator.irreducible_X_sq_add_X_add_one_of_card_eq_two hK
  have hcyclo : Polynomial.cyclotomic 3 K = Polynomial.X ^ 2 + Polynomial.X + 1 := by
    rw [Polynomial.cyclotomic_prime]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
    ring
  have hgd : (Polynomial.X ^ 2 + Polynomial.C (1 : K) * Polynomial.X + 1 : Polynomial K) ∣
      Polynomial.cyclotomic 3 K := by
    rw [hcyclo]
    simp
  have ht : CFSG.StandardType.SpJoin.spCompanion (1 : K) ^ 3 = 1 :=
    CFSG.StandardType.SpJoin.spCompanion_pow_eq_one Nat.prime_three hgd
  have hpq : 3 ∣ Nat.card K + 1 := by
    rw [hK]
  obtain ⟨g, hg⟩ := CFSG.StandardType.SpJoin.spPlaneConj_companion (F := K) (p := 3) h2
    Nat.prime_three (by norm_num) hpq hirr hgd ht r A hA (le_of_eq hcard.symm)
  exact ⟨g, by rw [hg, ← spPlaneTorus_eq_spJoin (K := K) (r := r) ht]⟩

end TwoThree

end CFSG.StandardType
