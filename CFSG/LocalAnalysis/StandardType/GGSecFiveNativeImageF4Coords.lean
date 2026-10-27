module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import Mathlib.GroupTheory.Coxeter.Matrix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

private abbrev V4 (p : ℕ) := Fin 4 → Multiplicative (ZMod p)

private def e3 (p : ℕ) : V4 p :=
  Pi.mulSingle (3 : Fin 4) (ofAdd (1 : ZMod p) : Multiplicative (ZMod p))

private lemma pow_of_involutions_inv {G : Type*} [Group G] {u v : G} (hu : u * u = 1)
    (hv : v * v = 1) (n : ℕ) (h : (u * v) ^ n = 1) : (v * u) ^ n = 1 := by
  have h1 : v * u = (u * v)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hv, inv_eq_of_mul_eq_one_right hu]
  rw [h1, inv_pow, h, inv_one]

private lemma b3_sq0 (p : ℕ) :
    (SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) : MulAut (V4 p)) *
      SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) = 1 := by
  simpa [pow_two] using SpCoord.permAut_swap_sq (p := p) (0:Fin 4) 1

private lemma b3_sq1 (p : ℕ) :
    (SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) : MulAut (V4 p)) *
      SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) = 1 := by
  simpa [pow_two] using SpCoord.permAut_swap_sq (p := p) (1:Fin 4) 2

private lemma b3_sq2 (p : ℕ) :
    (SpCoord.sgnAut (p := p) (2:Fin 4) : MulAut (V4 p)) * SpCoord.sgnAut (p := p) (2:Fin 4) = 1 := by
  simpa [pow_two] using SpCoord.sgnAut_sq (p := p) (2:Fin 4)

private lemma b3_r01 (p : ℕ) :
    (((SpCoord.permAut (p := p) ((Equiv.swap (0:Fin 4) 1)) : MulAut (V4 p)) *
      SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2)) ^ 3) = 1 := by
  change (((ggSpSigned_permAutHom p 4) (Equiv.swap (0:Fin 4) 1) : MulAut (V4 p)) *
      (ggSpSigned_permAutHom p 4) (Equiv.swap (1:Fin 4) 2)) ^ 3 = 1
  rw [← MonoidHom.map_mul, ← MonoidHom.map_pow]
  rw [show ((Equiv.swap (0:Fin 4) 1) * (Equiv.swap (1:Fin 4) 2)) ^ 3 = 1 by decide]
  exact map_one _

private lemma b3_r10 (p : ℕ) :
    (((SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p)) *
      SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1)) ^ 3) = 1 :=
  pow_of_involutions_inv (b3_sq0 p) (b3_sq1 p) 3 (b3_r01 p)

private lemma b3_r02 (p : ℕ) :
    (((SpCoord.permAut (p := p) ((Equiv.swap (0:Fin 4) 1)) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (2:Fin 4)) ^ 2) = 1 := by
  have hcomm : (SpCoord.permAut (p := p) ((Equiv.swap (0:Fin 4) 1)) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (2:Fin 4) =
      SpCoord.sgnAut (p := p) (2:Fin 4) *
      SpCoord.permAut (p := p) ((Equiv.swap (0:Fin 4) 1)) := by
    have hu : ∀ f i, toAdd ((SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) :
        MulAut (V4 p)) f ((Equiv.swap (0:Fin 4) 1) i)) = (1 : ZMod p) * toAdd (f i) := by
      intro f i
      rw [SpCoord.permAut_apply]
      simp
    have h := SpCoord.IsSignedPerm.mul_sgnAut (p := p) (k := 4)
      (u := SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1))
      (π := Equiv.swap (0:Fin 4) 1) (ε := fun _ => 1) hu (2:Fin 4)
    rw [show (Equiv.swap (0:Fin 4) 1) 2 = 2 from by decide] at h
    rw [h]
  have hsq : (((SpCoord.permAut (p := p) ((Equiv.swap (0:Fin 4) 1)) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (2:Fin 4)) ^ 2) =
      (SpCoord.permAut (p := p) ((Equiv.swap (0:Fin 4) 1)) : MulAut (V4 p)) *
      ((SpCoord.sgnAut (p := p) (2:Fin 4)) *
      (SpCoord.permAut (p := p) ((Equiv.swap (0:Fin 4) 1)) : MulAut (V4 p))) *
      SpCoord.sgnAut (p := p) (2:Fin 4) := by
    rw [pow_two]
    group
  rw [hsq, ← hcomm, ← mul_assoc, show (SpCoord.permAut (p := p) ((Equiv.swap (0:Fin 4) 1)) : MulAut (V4 p)) *
      SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) = 1 from b3_sq0 p, one_mul,
    show (SpCoord.sgnAut (p := p) (2:Fin 4) : MulAut (V4 p)) * SpCoord.sgnAut (p := p) (2:Fin 4) = 1 from b3_sq2 p]

private lemma b3_r20 (p : ℕ) :
    (((SpCoord.sgnAut (p := p) (2:Fin 4) : MulAut (V4 p)) *
      SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1)) ^ 2) = 1 :=
  pow_of_involutions_inv (b3_sq0 p) (b3_sq2 p) 2 (b3_r02 p)

private lemma b3_r12 (p : ℕ) :
    (((SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (2:Fin 4)) ^ 4) = 1 := by
  have hu : ∀ f i, toAdd ((SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) :
      MulAut (V4 p)) f ((Equiv.swap (1:Fin 4) 2) i)) = (1 : ZMod p) * toAdd (f i) := by
    intro f i
    rw [SpCoord.permAut_apply]
    simp
  have h2 := SpCoord.IsSignedPerm.mul_sgnAut (p := p) (k := 4)
    (u := SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2))
    (π := Equiv.swap (1:Fin 4) 2) (ε := fun _ => 1) hu (2:Fin 4)
  have h1 := SpCoord.IsSignedPerm.mul_sgnAut (p := p) (k := 4)
    (u := SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2))
    (π := Equiv.swap (1:Fin 4) 2) (ε := fun _ => 1) hu (1:Fin 4)
  rw [show (Equiv.swap (1:Fin 4) 2) 2 = 1 from by decide] at h2
  rw [show (Equiv.swap (1:Fin 4) 2) 1 = 2 from by decide] at h1
  have hsq : (((SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (2:Fin 4)) ^ 2) =
      SpCoord.sgnAut (p := p) (1:Fin 4) * SpCoord.sgnAut (p := p) (2:Fin 4) := by
    calc (((SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p)) *
        SpCoord.sgnAut (p := p) (2:Fin 4)) ^ 2)
        = (SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p)) *
          ((SpCoord.sgnAut (p := p) (2:Fin 4)) *
           (SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p))) *
          SpCoord.sgnAut (p := p) (2:Fin 4) := by
            rw [pow_two]; group
      _ = (SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p)) *
          ((SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p)) *
           SpCoord.sgnAut (p := p) (1:Fin 4)) *
          SpCoord.sgnAut (p := p) (2:Fin 4) := by rw [← h1]
      _ = SpCoord.sgnAut (p := p) (1:Fin 4) * SpCoord.sgnAut (p := p) (2:Fin 4) := by
            rw [← mul_assoc, show (SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p)) *
              SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) = 1 from b3_sq1 p, one_mul]
  have hsq2 : (SpCoord.sgnAut (p := p) (1:Fin 4) *
      SpCoord.sgnAut (p := p) (2:Fin 4)) ^ 2 = 1 := by
    have hc : SpCoord.sgnAut (p := p) (1:Fin 4) * SpCoord.sgnAut (p := p) (2:Fin 4) =
        SpCoord.sgnAut (p := p) (2:Fin 4) * SpCoord.sgnAut (p := p) (1:Fin 4) :=
      SpCoord.sgnAut_mul_comm (p := p) (1:Fin 4) (2:Fin 4)
    calc (SpCoord.sgnAut (p := p) (1:Fin 4) * SpCoord.sgnAut (p := p) (2:Fin 4)) ^ 2
        = SpCoord.sgnAut (p := p) (1:Fin 4) *
          (SpCoord.sgnAut (p := p) (2:Fin 4) * SpCoord.sgnAut (p := p) (1:Fin 4)) *
          SpCoord.sgnAut (p := p) (2:Fin 4) := by rw [pow_two]; group
      _ = SpCoord.sgnAut (p := p) (1:Fin 4) *
          (SpCoord.sgnAut (p := p) (1:Fin 4) * SpCoord.sgnAut (p := p) (2:Fin 4)) *
          SpCoord.sgnAut (p := p) (2:Fin 4) := by rw [hc]
      _ = 1 := by
            rw [← mul_assoc,
              show (SpCoord.sgnAut (p := p) (1:Fin 4) : MulAut (V4 p)) *
                SpCoord.sgnAut (p := p) (1:Fin 4) = 1 from (by
                  simpa [pow_two] using SpCoord.sgnAut_sq (p := p) (1:Fin 4)),
              one_mul,
              show (SpCoord.sgnAut (p := p) (2:Fin 4) : MulAut (V4 p)) *
                SpCoord.sgnAut (p := p) (2:Fin 4) = 1 from b3_sq2 p]
  calc (((SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (2:Fin 4)) ^ 4)
      = (((SpCoord.permAut (p := p) ((Equiv.swap (1:Fin 4) 2)) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (2:Fin 4)) ^ 2) ^ 2 := by group
    _ = (SpCoord.sgnAut (p := p) (1:Fin 4) * SpCoord.sgnAut (p := p) (2:Fin 4)) ^ 2 := by rw [hsq]
    _ = 1 := hsq2

private lemma b3_r21 (p : ℕ) :
    (((SpCoord.sgnAut (p := p) (2:Fin 4) : MulAut (V4 p)) *
      SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2)) ^ 4) = 1 :=
  pow_of_involutions_inv (b3_sq1 p) (b3_sq2 p) 4 (b3_r12 p)

private lemma b3_liftable (p : ℕ) :
    (CoxeterMatrix.B 3).IsLiftable
      (![SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1),
         SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2),
         SpCoord.sgnAut (p := p) (2:Fin 4)] : Fin 3 → MulAut (V4 p)) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [CoxeterMatrix.B, b3_sq0, b3_sq1, b3_sq2, b3_r01, b3_r10, b3_r02, b3_r20,
      b3_r12, b3_r21]

private def d3s0 (p : ℕ) : MulAut (V4 p) := SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1)
private def d3s1 (p : ℕ) : MulAut (V4 p) := SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2)
private def d3s2 (p : ℕ) : MulAut (V4 p) :=
  SpCoord.sgnAut (p := p) (0:Fin 4) * SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) *
    (SpCoord.sgnAut (p := p) (0:Fin 4))⁻¹

private lemma sgn_inv (p : ℕ) (i : Fin 4) :
    (SpCoord.sgnAut (p := p) i : MulAut (V4 p))⁻¹ = SpCoord.sgnAut (p := p) i := by
  have h : (SpCoord.sgnAut (p := p) i : MulAut (V4 p)) * SpCoord.sgnAut (p := p) i = 1 := by
    simpa [pow_two] using SpCoord.sgnAut_sq (p := p) i
  exact inv_eq_of_mul_eq_one_right h

private lemma perm_inv (p : ℕ) (a b : Fin 4) :
    (SpCoord.permAut (p := p) (Equiv.swap a b) : MulAut (V4 p))⁻¹ =
      SpCoord.permAut (p := p) (Equiv.swap a b) := by
  have h : (SpCoord.permAut (p := p) (Equiv.swap a b) : MulAut (V4 p)) *
      SpCoord.permAut (p := p) (Equiv.swap a b) = 1 := by
    simpa [pow_two] using SpCoord.permAut_swap_sq (p := p) a b
  exact inv_eq_of_mul_eq_one_right h

private lemma d3_s2sq (p : ℕ) : d3s2 p * d3s2 p = 1 := by
  have hconj : d3s2 p = MulAut.conj (SpCoord.sgnAut (p := p) (0:Fin 4))
      (SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1)) := by
    rw [d3s2, MulAut.conj_apply]
  rw [hconj, ← map_mul]
  have ht : (SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) : MulAut (V4 p)) *
      SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) = 1 := by
    simpa [pow_two] using SpCoord.permAut_swap_sq (p := p) (0:Fin 4) 1
  rw [ht, map_one]

private lemma d3_r02 (p : ℕ) : (d3s0 p * d3s2 p) ^ 2 = 1 := by
  have hconj := ggSpSigned_conj_permAut_sgnAut p 4 (Equiv.swap (0:Fin 4) 1) (0:Fin 4)
  rw [perm_inv p (0:Fin 4) 1] at hconj
  rw [show (Equiv.swap (0:Fin 4) 1) 0 = 1 from by decide] at hconj
  have heq : d3s0 p * d3s2 p = SpCoord.sgnAut (p := p) (1:Fin 4) *
      SpCoord.sgnAut (p := p) (0:Fin 4) := by
    rw [d3s0, d3s2, ← mul_assoc, ← mul_assoc, hconj, sgn_inv]
  rw [heq]
  have hc : (SpCoord.sgnAut (p := p) (0:Fin 4) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (1:Fin 4) =
      SpCoord.sgnAut (p := p) (1:Fin 4) * SpCoord.sgnAut (p := p) (0:Fin 4) :=
    SpCoord.sgnAut_mul_comm (p := p) (0:Fin 4) (1:Fin 4)
  have h0 : (SpCoord.sgnAut (p := p) (0:Fin 4) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (0:Fin 4) = 1 := by
    simpa [pow_two] using SpCoord.sgnAut_sq (p := p) (0:Fin 4)
  have h1 : (SpCoord.sgnAut (p := p) (1:Fin 4) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (1:Fin 4) = 1 := by
    simpa [pow_two] using SpCoord.sgnAut_sq (p := p) (1:Fin 4)
  calc (SpCoord.sgnAut (p := p) (1:Fin 4) * SpCoord.sgnAut (p := p) (0:Fin 4)) ^ 2
      = SpCoord.sgnAut (p := p) (1:Fin 4) *
        (SpCoord.sgnAut (p := p) (0:Fin 4) * SpCoord.sgnAut (p := p) (1:Fin 4)) *
        SpCoord.sgnAut (p := p) (0:Fin 4) := by rw [pow_two]; group
    _ = SpCoord.sgnAut (p := p) (1:Fin 4) *
        (SpCoord.sgnAut (p := p) (1:Fin 4) * SpCoord.sgnAut (p := p) (0:Fin 4)) *
        SpCoord.sgnAut (p := p) (0:Fin 4) := by rw [← hc]
    _ = 1 := by rw [← mul_assoc, h1, one_mul, h0]

private lemma d3_r12 (p : ℕ) : (d3s1 p * d3s2 p) ^ 3 = 1 := by
  have h2 : d3s2 p = SpCoord.sgnAut (p := p) (0:Fin 4) *
      SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) *
      SpCoord.sgnAut (p := p) (0:Fin 4) := by
    rw [d3s2, sgn_inv]
  refine MulEquiv.ext fun f => ?_
  funext i
  rw [h2]
  fin_cases i <;>
    simp [d3s1, MulAut.mul_apply, SpCoord.permAut_apply, SpCoord.sgnAut_apply,
      Equiv.swap_apply_def, Function.update_apply, pow_succ, pow_two]

private lemma d3_sq0 (p : ℕ) : d3s0 p * d3s0 p = 1 := by
  simpa [d3s0, pow_two] using SpCoord.permAut_swap_sq (p := p) (0:Fin 4) 1

private lemma d3_sq1 (p : ℕ) : d3s1 p * d3s1 p = 1 := by
  simpa [d3s1, pow_two] using SpCoord.permAut_swap_sq (p := p) (1:Fin 4) 2

private lemma d3_r01 (p : ℕ) : (d3s0 p * d3s1 p) ^ 3 = 1 := by
  simpa [d3s0, d3s1] using b3_r01 p

private lemma d3_r10 (p : ℕ) : (d3s1 p * d3s0 p) ^ 3 = 1 :=
  pow_of_involutions_inv (d3_sq0 p) (d3_sq1 p) 3 (d3_r01 p)

private lemma d3_r20 (p : ℕ) : (d3s2 p * d3s0 p) ^ 2 = 1 :=
  pow_of_involutions_inv (d3_sq0 p) (d3_s2sq p) 2 (d3_r02 p)

private lemma d3_r21 (p : ℕ) : (d3s2 p * d3s1 p) ^ 3 = 1 :=
  pow_of_involutions_inv (d3_sq1 p) (d3_s2sq p) 3 (d3_r12 p)

private lemma d3_liftable (p : ℕ) :
    (CoxeterMatrix.A 3).IsLiftable (![d3s0 p, d3s1 p, d3s2 p] : Fin 3 → MulAut (V4 p)) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [CoxeterMatrix.A, d3_sq0, d3_sq1, d3_s2sq, d3_r01, d3_r10, d3_r02, d3_r20,
      d3_r12, d3_r21]

private lemma permAut_swap_rev (p : ℕ) (a b : Fin 4) :
    (SpCoord.permAut (p := p) (Equiv.swap a b) : MulAut (V4 p)) =
      SpCoord.permAut (p := p) (Equiv.swap b a) := by
  rw [Equiv.swap_comm]

private lemma negT_rev (p : ℕ) (a b : Fin 4) :
    (SpCoord.sgnAut (p := p) a * SpCoord.permAut (p := p) (Equiv.swap a b) *
      (SpCoord.sgnAut (p := p) a)⁻¹ : MulAut (V4 p)) =
    SpCoord.sgnAut (p := p) b * SpCoord.permAut (p := p) (Equiv.swap b a) *
      (SpCoord.sgnAut (p := p) b)⁻¹ := by
  refine MulEquiv.ext fun f => ?_
  funext i
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    simp [sgn_inv, MulAut.mul_apply, SpCoord.permAut_apply, SpCoord.sgnAut_apply, negTrans_apply,
      Equiv.swap_apply_def, Function.update_apply]

private lemma d3_neg02 (p : ℕ) :
    (SpCoord.sgnAut (p := p) (0:Fin 4) * SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 2) *
      (SpCoord.sgnAut (p := p) (0:Fin 4))⁻¹ : MulAut (V4 p)) =
    d3s1 p * d3s2 p * d3s1 p := by
  refine MulEquiv.ext fun f => ?_
  funext i
  fin_cases i <;>
    simp [d3s1, d3s2, sgn_inv, MulAut.mul_apply, SpCoord.permAut_apply, SpCoord.sgnAut_apply,
      negTrans_apply, Equiv.swap_apply_def, Function.update_apply]

private lemma d3_neg12 (p : ℕ) :
    (SpCoord.sgnAut (p := p) (1:Fin 4) * SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) *
      (SpCoord.sgnAut (p := p) (1:Fin 4))⁻¹ : MulAut (V4 p)) =
    d3s0 p *
      (SpCoord.sgnAut (p := p) (0:Fin 4) * SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 2) *
        (SpCoord.sgnAut (p := p) (0:Fin 4))⁻¹) * d3s0 p := by
  refine MulEquiv.ext fun f => ?_
  funext i
  fin_cases i <;>
    simp [d3s0, sgn_inv, MulAut.mul_apply, SpCoord.permAut_apply, SpCoord.sgnAut_apply,
      negTrans_apply, Equiv.swap_apply_def, Function.update_apply]

theorem card_bCoordinateBlock_four_le {p : ℕ} (hp : p.Prime) :
    Nat.card ↥(bCoordinateBlock 4 p 3) ≤ 48 := by
  classical
  let f : Fin 3 → MulAut (V4 p) :=
    ![SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1),
      SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2),
      SpCoord.sgnAut (p := p) (2:Fin 4)]
  have hf : (CoxeterMatrix.B 3).IsLiftable f := b3_liftable p
  let φ : (CoxeterMatrix.B 3).Group →* MulAut (V4 p) :=
    (CoxeterMatrix.B 3).toCoxeterSystem.lift ⟨f, hf⟩
  have hφ0 : φ ((CoxeterMatrix.B 3).toCoxeterSystem.simple 0) =
      SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) := by
    rw [show φ ((CoxeterMatrix.B 3).toCoxeterSystem.simple 0) = f 0 from
      (CoxeterMatrix.B 3).toCoxeterSystem.lift_apply_simple hf 0]
    rfl
  have hφ1 : φ ((CoxeterMatrix.B 3).toCoxeterSystem.simple 1) =
      SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) := by
    rw [show φ ((CoxeterMatrix.B 3).toCoxeterSystem.simple 1) = f 1 from
      (CoxeterMatrix.B 3).toCoxeterSystem.lift_apply_simple hf 1]
    rfl
  have hφ2 : φ ((CoxeterMatrix.B 3).toCoxeterSystem.simple 2) = SpCoord.sgnAut (p := p) (2:Fin 4) := by
    rw [show φ ((CoxeterMatrix.B 3).toCoxeterSystem.simple 2) = f 2 from
      (CoxeterMatrix.B 3).toCoxeterSystem.lift_apply_simple hf 2]
    rfl
  have hφ_le : φ.range ≤ bCoordinateBlock 4 p 3 := by
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ Subgroup.closure (Set.range (CoxeterMatrix.B 3).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.B 3).toCoxeterSystem.subgroup_closure_range_simple]
      exact Subgroup.mem_top w
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        fin_cases i
        · change φ ((CoxeterMatrix.B 3).toCoxeterSystem.simple 0) ∈
            bCoordinateBlock 4 p 3
          rw [hφ0]
          exact Subgroup.subset_closure (Or.inr ⟨0, 1, by decide, by decide, by decide, rfl⟩)
        · change φ ((CoxeterMatrix.B 3).toCoxeterSystem.simple 1) ∈
            bCoordinateBlock 4 p 3
          rw [hφ1]
          exact Subgroup.subset_closure (Or.inr ⟨1, 2, by decide, by decide, by decide, rfl⟩)
        · change φ ((CoxeterMatrix.B 3).toCoxeterSystem.simple 2) ∈
            bCoordinateBlock 4 p 3
          rw [hφ2]
          exact Subgroup.subset_closure (Or.inl ⟨2, by decide, rfl⟩)
    | one => simpa using Subgroup.one_mem (bCoordinateBlock 4 p 3)
    | mul x y hx hy ihx ihy =>
        rw [map_mul]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
        rw [map_inv]
        exact Subgroup.inv_mem _ ih
  have ht01 : (SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) : MulAut (V4 p)) ∈ φ.range :=
    ⟨(CoxeterMatrix.B 3).simple 0, hφ0⟩
  have ht12 : (SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) : MulAut (V4 p)) ∈ φ.range :=
    ⟨(CoxeterMatrix.B 3).simple 1, hφ1⟩
  have hc2 : (SpCoord.sgnAut (p := p) (2:Fin 4) : MulAut (V4 p)) ∈ φ.range :=
    ⟨(CoxeterMatrix.B 3).simple 2, hφ2⟩
  have hc1 : (SpCoord.sgnAut (p := p) (1:Fin 4) : MulAut (V4 p)) ∈ φ.range := by
    have heq : (SpCoord.sgnAut (p := p) (1:Fin 4) : MulAut (V4 p)) =
        SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) *
          SpCoord.sgnAut (p := p) (2:Fin 4) *
          SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) := by
      have hconj := ggSpSigned_conj_permAut_sgnAut p 4 (Equiv.swap (1:Fin 4) 2) (2:Fin 4)
      rw [perm_inv, show (Equiv.swap (1:Fin 4) 2) 2 = 1 from by decide] at hconj
      exact hconj.symm
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht12 hc2) ht12
  have hc0 : (SpCoord.sgnAut (p := p) (0:Fin 4) : MulAut (V4 p)) ∈ φ.range := by
    have heq : (SpCoord.sgnAut (p := p) (0:Fin 4) : MulAut (V4 p)) =
        SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) *
          SpCoord.sgnAut (p := p) (1:Fin 4) *
          SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) := by
      have hconj := ggSpSigned_conj_permAut_sgnAut p 4 (Equiv.swap (0:Fin 4) 1) (1:Fin 4)
      rw [perm_inv, show (Equiv.swap (0:Fin 4) 1) 1 = 0 from by decide] at hconj
      exact hconj.symm
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht01 hc1) ht01
  have ht02 : (SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 2) : MulAut (V4 p)) ∈ φ.range := by
    have heq : (SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 2) : MulAut (V4 p)) =
        SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) *
          SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) *
          SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) := by
      change ((ggSpSigned_permAutHom p 4) (Equiv.swap (0:Fin 4) 2) : MulAut (V4 p)) =
        (ggSpSigned_permAutHom p 4) (Equiv.swap (0:Fin 4) 1) *
          (ggSpSigned_permAutHom p 4) (Equiv.swap (1:Fin 4) 2) *
          (ggSpSigned_permAutHom p 4) (Equiv.swap (0:Fin 4) 1)
      rw [← MonoidHom.map_mul, ← MonoidHom.map_mul]
      congr 1
      decide
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht01 ht12) ht01
  have hle_range : bCoordinateBlock 4 p 3 ≤ φ.range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro r (⟨i, hi, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩)
    · fin_cases i
      · exact hc0
      · exact hc1
      · exact hc2
      · exact absurd rfl hi
    · fin_cases a <;> fin_cases b <;>
        first
        | exact ht01
        | exact ht12
        | exact ht02
        | (exfalso; exact hab rfl)
        | (exfalso; exact ha rfl)
        | (exfalso; exact hb rfl)
        | (rw [permAut_swap_rev p]; exact ht01)
        | (rw [permAut_swap_rev p]; exact ht12)
        | (rw [permAut_swap_rev p]; exact ht02)
  have hrange : φ.range = bCoordinateBlock 4 p 3 := le_antisymm hφ_le hle_range
  haveI : Finite (CoxeterMatrix.B 3).Group := by
    refine Nat.finite_of_card_ne_zero ?_
    have h := SpFrame.card_coxeterB_ge 3 (by norm_num)
    norm_num [Nat.factorial] at h
    omega
  have hsurj : Function.Surjective
      (fun w => (⟨φ w, ⟨w, rfl⟩⟩ : ↥φ.range)) := by
    rintro ⟨y, ⟨w, hw⟩⟩
    exact ⟨w, Subtype.ext hw⟩
  have hcard_range : Nat.card ↥φ.range ≤ Nat.card (CoxeterMatrix.B 3).Group :=
    Nat.card_le_card_of_surjective _ hsurj
  calc Nat.card ↥(bCoordinateBlock 4 p 3) = Nat.card ↥φ.range := by rw [hrange]
    _ ≤ Nat.card (CoxeterMatrix.B 3).Group := hcard_range
    _ ≤ 48 := by
        have h := card_coxeterB_le 3
        norm_num [Nat.factorial] at h
        exact h

theorem card_dCoordinateBlock_four_le {p : ℕ} (hp : p.Prime) :
    Nat.card ↥(dCoordinateBlock 4 p 3) ≤ 24 := by
  classical
  let f : Fin 3 → MulAut (V4 p) := ![d3s0 p, d3s1 p, d3s2 p]
  have hf : (CoxeterMatrix.A 3).IsLiftable f := d3_liftable p
  let φ : (CoxeterMatrix.A 3).Group →* MulAut (V4 p) :=
    (CoxeterMatrix.A 3).toCoxeterSystem.lift ⟨f, hf⟩
  have hφ0 : φ ((CoxeterMatrix.A 3).toCoxeterSystem.simple 0) =
      SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) := by
    rw [show φ ((CoxeterMatrix.A 3).toCoxeterSystem.simple 0) = f 0 from
      (CoxeterMatrix.A 3).toCoxeterSystem.lift_apply_simple hf 0]
    rfl
  have hφ1 : φ ((CoxeterMatrix.A 3).toCoxeterSystem.simple 1) =
      SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) := by
    rw [show φ ((CoxeterMatrix.A 3).toCoxeterSystem.simple 1) = f 1 from
      (CoxeterMatrix.A 3).toCoxeterSystem.lift_apply_simple hf 1]
    rfl
  have hφ2 : φ ((CoxeterMatrix.A 3).toCoxeterSystem.simple 2) =
      SpCoord.sgnAut (p := p) (0:Fin 4) *
        SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) *
        (SpCoord.sgnAut (p := p) (0:Fin 4))⁻¹ := by
    rw [show φ ((CoxeterMatrix.A 3).toCoxeterSystem.simple 2) = f 2 from
      (CoxeterMatrix.A 3).toCoxeterSystem.lift_apply_simple hf 2]
    rfl
  have hφ_le : φ.range ≤ dCoordinateBlock 4 p 3 := by
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ Subgroup.closure (Set.range (CoxeterMatrix.A 3).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A 3).toCoxeterSystem.subgroup_closure_range_simple]
      exact Subgroup.mem_top w
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        fin_cases i
        · change φ ((CoxeterMatrix.A 3).toCoxeterSystem.simple 0) ∈
            dCoordinateBlock 4 p 3
          rw [hφ0]
          exact Subgroup.subset_closure (Or.inl ⟨0, 1, by decide, by decide, by decide, rfl⟩)
        · change φ ((CoxeterMatrix.A 3).toCoxeterSystem.simple 1) ∈
            dCoordinateBlock 4 p 3
          rw [hφ1]
          exact Subgroup.subset_closure (Or.inl ⟨1, 2, by decide, by decide, by decide, rfl⟩)
        · change φ ((CoxeterMatrix.A 3).toCoxeterSystem.simple 2) ∈
            dCoordinateBlock 4 p 3
          rw [hφ2]
          exact Subgroup.subset_closure (Or.inr ⟨0, 1, by decide, by decide, by decide, rfl⟩)
    | one => simpa using Subgroup.one_mem (dCoordinateBlock 4 p 3)
    | mul x y hx hy ihx ihy =>
        rw [map_mul]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
        rw [map_inv]
        exact Subgroup.inv_mem _ ih
  have hs0 : d3s0 p ∈ φ.range := ⟨(CoxeterMatrix.A 3).simple 0, hφ0⟩
  have hs1 : d3s1 p ∈ φ.range := ⟨(CoxeterMatrix.A 3).simple 1, hφ1⟩
  have hs2 : d3s2 p ∈ φ.range := ⟨(CoxeterMatrix.A 3).simple 2, hφ2⟩
  have ht02 : (SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 2) : MulAut (V4 p)) ∈ φ.range := by
    have heq : (SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 2) : MulAut (V4 p)) =
        SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) *
          SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) *
          SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 1) := by
      change ((ggSpSigned_permAutHom p 4) (Equiv.swap (0:Fin 4) 2) : MulAut (V4 p)) =
        (ggSpSigned_permAutHom p 4) (Equiv.swap (0:Fin 4) 1) *
          (ggSpSigned_permAutHom p 4) (Equiv.swap (1:Fin 4) 2) *
          (ggSpSigned_permAutHom p 4) (Equiv.swap (0:Fin 4) 1)
      rw [← MonoidHom.map_mul, ← MonoidHom.map_mul]
      congr 1
      decide
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs0 hs1) hs0
  have hneg02 : (SpCoord.sgnAut (p := p) (0:Fin 4) *
      SpCoord.permAut (p := p) (Equiv.swap (0:Fin 4) 2) *
      (SpCoord.sgnAut (p := p) (0:Fin 4))⁻¹ : MulAut (V4 p)) ∈ φ.range := by
    rw [d3_neg02 p]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs1 hs2) hs1
  have hneg12 : (SpCoord.sgnAut (p := p) (1:Fin 4) *
      SpCoord.permAut (p := p) (Equiv.swap (1:Fin 4) 2) *
      (SpCoord.sgnAut (p := p) (1:Fin 4))⁻¹ : MulAut (V4 p)) ∈ φ.range := by
    rw [d3_neg12 p]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs0 hneg02) hs0
  have hle_range : dCoordinateBlock 4 p 3 ≤ φ.range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro r (⟨a, b, hab, ha, hb, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩)
    · fin_cases a <;> fin_cases b <;>
        first
        | exact hs0
        | exact hs1
        | exact ht02
        | (exfalso; exact hab rfl)
        | (exfalso; exact ha rfl)
        | (exfalso; exact hb rfl)
        | (rw [permAut_swap_rev p]; exact hs0)
        | (rw [permAut_swap_rev p]; exact hs1)
        | (rw [permAut_swap_rev p]; exact ht02)
    · fin_cases a <;> fin_cases b <;>
        first
        | exact hs2
        | exact hneg02
        | exact hneg12
        | (exfalso; exact hab rfl)
        | (exfalso; exact ha rfl)
        | (exfalso; exact hb rfl)
        | (rw [negT_rev]; exact hs2)
        | (rw [negT_rev]; exact hneg02)
        | (rw [negT_rev]; exact hneg12)
  have hrange : φ.range = dCoordinateBlock 4 p 3 := le_antisymm hφ_le hle_range
  haveI : Finite (CoxeterMatrix.A 3).Group := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [l05nK3a_card_coxeterA 3]
    norm_num
  have hsurj : Function.Surjective
      (fun w => (⟨φ w, ⟨w, rfl⟩⟩ : ↥φ.range)) := by
    rintro ⟨y, ⟨w, hw⟩⟩
    exact ⟨w, Subtype.ext hw⟩
  have hcard_range : Nat.card ↥φ.range ≤ Nat.card (CoxeterMatrix.A 3).Group :=
    Nat.card_le_card_of_surjective _ hsurj
  calc Nat.card ↥(dCoordinateBlock 4 p 3) = Nat.card ↥φ.range := by rw [hrange]
    _ ≤ Nat.card (CoxeterMatrix.A 3).Group := hcard_range
    _ = 24 := by
        rw [l05nK3a_card_coxeterA 3]
        norm_num

private lemma pow_four_sgnAut_mul_of_signed_sq_one {p : ℕ} [Fact p.Prime]
    {u : MulAut (V4 p)} (hu : SpCoord.IsSignedPerm ⇑u) (hu2 : u ^ 2 = 1) (k : Fin 4) :
    (SpCoord.sgnAut (p := p) k * u) ^ 4 = 1 := by
  obtain ⟨π, ε, hε, huπ⟩ := hu
  have hcomm : u * SpCoord.sgnAut (p := p) k =
      SpCoord.sgnAut (p := p) (π k) * u :=
    SpCoord.IsSignedPerm.mul_sgnAut huπ k
  have hk : (SpCoord.sgnAut (p := p) k : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) k = 1 := by
    simpa [pow_two] using SpCoord.sgnAut_sq (p := p) k
  have hpk : (SpCoord.sgnAut (p := p) (π k) : MulAut (V4 p)) *
      SpCoord.sgnAut (p := p) (π k) = 1 := by
    simpa [pow_two] using SpCoord.sgnAut_sq (p := p) (π k)
  have hu2' : u * u = 1 := by simpa [pow_two] using hu2
  have hsq : (SpCoord.sgnAut (p := p) k * u) ^ 2 =
      SpCoord.sgnAut (p := p) k * SpCoord.sgnAut (p := p) (π k) := by
    calc (SpCoord.sgnAut (p := p) k * u) ^ 2
        = SpCoord.sgnAut (p := p) k * (u * SpCoord.sgnAut (p := p) k) * u := by
            rw [pow_two]; group
      _ = SpCoord.sgnAut (p := p) k *
          (SpCoord.sgnAut (p := p) (π k) * u) * u := by rw [hcomm]
      _ = SpCoord.sgnAut (p := p) k * SpCoord.sgnAut (p := p) (π k) := by
            rw [show SpCoord.sgnAut (p := p) k * (SpCoord.sgnAut (p := p) (π k) * u) * u =
              (SpCoord.sgnAut (p := p) k * SpCoord.sgnAut (p := p) (π k)) * (u * u) from by
                group, hu2', mul_one]
  have hdiag : (SpCoord.sgnAut (p := p) k *
      SpCoord.sgnAut (p := p) (π k)) ^ 2 = 1 := by
    have hc := SpCoord.sgnAut_mul_comm (p := p) k (π k)
    calc (SpCoord.sgnAut (p := p) k * SpCoord.sgnAut (p := p) (π k)) ^ 2
        = SpCoord.sgnAut (p := p) k *
          (SpCoord.sgnAut (p := p) (π k) * SpCoord.sgnAut (p := p) k) *
          SpCoord.sgnAut (p := p) (π k) := by rw [pow_two]; group
      _ = SpCoord.sgnAut (p := p) k *
          (SpCoord.sgnAut (p := p) k * SpCoord.sgnAut (p := p) (π k)) *
          SpCoord.sgnAut (p := p) (π k) := by rw [hc]
      _ = 1 := by rw [← mul_assoc, hk, one_mul, hpk]
  calc (SpCoord.sgnAut (p := p) k * u) ^ 4
      = ((SpCoord.sgnAut (p := p) k * u) ^ 2) ^ 2 := by group
    _ = (SpCoord.sgnAut (p := p) k * SpCoord.sgnAut (p := p) (π k)) ^ 2 := by rw [hsq]
    _ = 1 := hdiag

private lemma permAut_swap_ne_three_of_fix {p : ℕ} [Fact p.Prime] {a b : Fin 4} (hab : a ≠ b)
    (h : (SpCoord.permAut (p := p) (Equiv.swap a b) : MulAut (V4 p))
      (e3 p) = e3 p) :
    a ≠ 3 ∧ b ≠ 3 := by
  constructor
  · intro ha
    subst ha
    have hb3 : b ≠ 3 := fun hb => hab (by rw [hb])
    have hc := congrArg (fun f : V4 p => toAdd (f b)) h
    rw [SpCoord.permAut_apply, Function.comp_apply] at hc
    rw [show (Equiv.swap (3:Fin 4) b)⁻¹ b = 3 from by
      rw [Equiv.swap_inv, Equiv.swap_apply_right]] at hc
    simp [e3, hb3] at hc
  · intro hb
    subst hb
    have ha3 : a ≠ 3 := fun ha => hab (by rw [ha])
    have hc := congrArg (fun f : V4 p => toAdd (f a)) h
    rw [SpCoord.permAut_apply, Function.comp_apply] at hc
    rw [show (Equiv.swap a (3:Fin 4))⁻¹ a = 3 from by
      rw [Equiv.swap_inv, Equiv.swap_apply_left]] at hc
    simp [e3, ha3] at hc

private lemma negT_ne_three_of_fix {p : ℕ} [Fact p.Prime] {a b : Fin 4} (hab : a ≠ b)
    (h : (SpCoord.sgnAut (p := p) a * SpCoord.permAut (p := p) (Equiv.swap a b) *
      (SpCoord.sgnAut (p := p) a)⁻¹ : MulAut (V4 p))
      (e3 p) = e3 p) :
    a ≠ 3 ∧ b ≠ 3 := by
  constructor
  · intro ha
    subst ha
    have hb3 : b ≠ 3 := fun hb => hab (by rw [hb])
    have hc := congrArg (fun f : V4 p => toAdd (f b)) h
    rw [negTrans_apply (p := p) (3:Fin 4) b hab] at hc
    simp [e3, hb3] at hc
  · intro hb
    subst hb
    have ha3 : a ≠ 3 := fun ha => hab (by rw [ha])
    have hc := congrArg (fun f : V4 p => toAdd (f a)) h
    rw [negTrans_apply (p := p) a (3:Fin 4) hab] at hc
    simp [e3, ha3] at hc

private lemma not_sgnAut_of_mul_pow_three {p : ℕ} [Fact p.Prime] {u v : MulAut (V4 p)}
    (hu : u ∈ bCoordinateBlock 4 p 3) (hv2 : v ^ 2 = 1)
    (hvsigned : SpCoord.IsSignedPerm ⇑v) (h3 : (u * v) ^ 3 = 1) (hne : u * v ≠ 1)
    (k : Fin 4) : u ≠ SpCoord.sgnAut (p := p) k := by
  intro hk
  have h4 : (u * v) ^ 4 = 1 := by
    rw [hk]
    exact pow_four_sgnAut_mul_of_signed_sq_one hvsigned hv2 k
  have h1 : u * v = 1 :=
    (pow_eq_one_iff_of_coprime (a := u * v) (by decide : Nat.Coprime 3 4)).mp ⟨h3, h4⟩
  exact hne h1

private lemma d3_axis_fix {p : ℕ} [Fact p.Prime] (hp : p.Prime) (hp2 : p ≠ 2) {r : MulAut (V4 p)}
    (hr : r ∈ bCoordinateBlock 4 p 3) :
    r (e3 p) = e3 p := by
  refine (forall_bCoordinateBlock_fix_iff hp hp2 (3:Fin 4) _).mpr ?_ r hr
  intro k hk
  exact Pi.mulSingle_eq_of_ne hk _

theorem le_dCoordinateBlock_of_coxeterA3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Subgroup (MulAut (Fin 4 → Multiplicative (ZMod p)))} (hR : R ≤ bCoordinateBlock 4 p 3)
    (e : (CoxeterMatrix.A 3).Group ≃* ↥R)
    (he : ∀ i, ((e ((CoxeterMatrix.A 3).simple i) : ↥R) :
        MulAut (Fin 4 → Multiplicative (ZMod p))) ^ 2 = 1 ∧
      Nat.card {f : Fin 4 → Multiplicative (ZMod p) //
        ((e ((CoxeterMatrix.A 3).simple i) : ↥R) : MulAut (Fin 4 → Multiplicative (ZMod p))) f =
          f} * p = Nat.card (Fin 4 → Multiplicative (ZMod p))) :
    R ≤ dCoordinateBlock 4 p 3 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let r : Fin 3 → MulAut (V4 p) := fun i =>
    ((e ((CoxeterMatrix.A 3).simple i) : ↥R) : MulAut (V4 p))
  let nb : Fin 3 → Fin 3 := ![1, 0, 1]
  have hnb : ∀ i, i ≠ nb i := by
    intro i
    fin_cases i <;> decide
  have hM : ∀ i, (CoxeterMatrix.A 3) i (nb i) = 3 := by
    intro i
    fin_cases i <;> decide
  have hr_mem : ∀ i, r i ∈ bCoordinateBlock 4 p 3 := fun i => hR (e _).2
  have hr_signed : ∀ i, SpCoord.IsSignedPerm ⇑(r i) := by
    intro i
    have h := bCoordinateBlock_le_bSignedFull (n := 4) (p := p) (3:Fin 4) (hr_mem i)
    rwa [bSignedFull_eq_signedPermSubgroup] at h
  have hr_fix : ∀ i, r i (e3 p) =
      e3 p := fun i => d3_axis_fix hp hp2 (hr_mem i)
  have hr_not_sgn : ∀ i, ¬ ∃ k, r i = SpCoord.sgnAut (p := p) k := by
    intro i
    rintro ⟨k, hk⟩
    have hri_ne : r i ≠ r (nb i) := by
      intro heq
      have hsimple : (CoxeterMatrix.A 3).toCoxeterSystem.simple i =
          (CoxeterMatrix.A 3).toCoxeterSystem.simple (nb i) := by
        apply e.injective
        exact Subtype.ext heq
      exact hnb i ((CoxeterMatrix.A 3).toCoxeterSystem.simple_injective hsimple)
    have hv2 : (r (nb i)) ^ 2 = 1 := (he (nb i)).1
    have h3 : (r i * r (nb i)) ^ 3 = 1 := by
      have hrel := (CoxeterMatrix.A 3).toCoxeterSystem.simple_mul_simple_pow i (nb i)
      rw [hM i] at hrel
      have h := congrArg (fun x : (CoxeterMatrix.A 3).Group =>
        ((e x : ↥R) : MulAut (V4 p))) hrel
      simpa [r, map_mul, map_pow] using h
    have hne : r i * r (nb i) ≠ 1 := by
      intro hprod
      apply hri_ne
      have hv2' : r (nb i) * r (nb i) = 1 := by
        simpa [pow_two] using hv2
      calc r i = r i * 1 := (mul_one _).symm
        _ = r i * (r (nb i) * r (nb i)) := by rw [hv2']
        _ = (r i * r (nb i)) * r (nb i) := by group
        _ = 1 * r (nb i) := by rw [hprod]
        _ = r (nb i) := one_mul _
    exact not_sgnAut_of_mul_pow_three (hr_mem i) hv2 (hr_signed (nb i)) h3 hne k hk
  have hr_cases : ∀ i, ∃ a b : Fin 4, a ≠ b ∧
      (r i = SpCoord.permAut (p := p) (Equiv.swap a b) ∨
        r i = SpCoord.sgnAut (p := p) a *
          SpCoord.permAut (p := p) (Equiv.swap a b) *
          (SpCoord.sgnAut (p := p) a)⁻¹) := by
    intro i
    rcases eq_sgnAut_or_swap_of_isRefl hp hp2
      (bCoordinateBlock_le_bSignedFull (n := 4) (p := p) (3:Fin 4) (hr_mem i))
      (he i).1 (he i).2 with h | h
    · exact absurd h (hr_not_sgn i)
    · exact h
  have hr_dmem : ∀ i, r i ∈ dCoordinateBlock 4 p 3 := by
    intro i
    obtain ⟨a, b, hab, hcase⟩ := hr_cases i
    have hfix := hr_fix i
    rcases hcase with htrans | hneg
    · rw [htrans] at hfix ⊢
      obtain ⟨ha3, hb3⟩ := permAut_swap_ne_three_of_fix hab hfix
      exact Subgroup.subset_closure (Or.inl ⟨a, b, hab, ha3, hb3, rfl⟩)
    · rw [hneg] at hfix ⊢
      obtain ⟨ha3, hb3⟩ := negT_ne_three_of_fix hab hfix
      exact Subgroup.subset_closure (Or.inr ⟨a, b, hab, ha3, hb3, rfl⟩)
  have hE : ∀ w : (CoxeterMatrix.A 3).Group,
      ((e w : ↥R) : MulAut (V4 p)) ∈ dCoordinateBlock 4 p 3 := by
    intro w
    have hw : w ∈ Subgroup.closure (Set.range (CoxeterMatrix.A 3).toCoxeterSystem.simple) := by
      rw [(CoxeterMatrix.A 3).toCoxeterSystem.subgroup_closure_range_simple]
      exact Subgroup.mem_top w
    induction hw using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact hr_dmem i
    | one => simpa using Subgroup.one_mem (dCoordinateBlock 4 p 3)
    | mul u v hu hv ihu ihv =>
        have h : ((e (u * v) : ↥R) : MulAut (V4 p)) =
            ((e u : ↥R) : MulAut (V4 p)) * ((e v : ↥R) : MulAut (V4 p)) := by
          rw [map_mul]
          rfl
        rw [h]
        exact Subgroup.mul_mem _ ihu ihv
    | inv u hu ihu =>
        have h : ((e u⁻¹ : ↥R) : MulAut (V4 p)) =
            ((e u : ↥R) : MulAut (V4 p))⁻¹ := by
          rw [map_inv]
          rfl
        rw [h]
        exact Subgroup.inv_mem _ ihu
  intro x hx
  obtain ⟨w, hw⟩ := e.surjective ⟨x, hx⟩
  have hxw : ((e w : ↥R) : MulAut (V4 p)) = x := congrArg Subtype.val hw
  rw [← hxw]
  exact hE w

end CFSG.StandardType

end
