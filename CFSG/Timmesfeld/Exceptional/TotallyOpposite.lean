module

public import CFSG.Timmesfeld.Exceptional.ThreeFive
public import CFSG.Timmesfeld.Moufang.A6Check
public import CFSG.Timmesfeld.Moufang.LinePres

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G] {D : Set G}

@[expose] def TotallyOpposite (D : Set G) (z e : G) : Prop :=
  ∀ x ∈ D, Commute z x → ¬ Commute x e ∧ Odd (orderOf (x * e))

namespace TotallyOpposite

variable {z e : G}

theorem opposite_self (h : TotallyOpposite D z e) (hz : z ∈ D) :
    ¬ Commute z e ∧ Odd (orderOf (z * e)) :=
  h z hz (Commute.refl z)

theorem opposite_of_line (h : TotallyOpposite D z e) (hz : z ∈ D) {y : G} (hy : y ∈ D)
    (hzy : Commute z y) (hzyD : z * y ∈ D) :
    (¬ Commute z e ∧ Odd (orderOf (z * e))) ∧ (¬ Commute y e ∧ Odd (orderOf (y * e))) ∧
      (¬ Commute (z * y) e ∧ Odd (orderOf (z * y * e))) :=
  ⟨h.opposite_self hz, h y hy hzy, h _ hzyD ((Commute.refl z).mul_right hzy)⟩

theorem orderOf_eq_five (hD : IsRootInvolutionSet D) (h : TotallyOpposite D z e) (hz : z ∈ D)
    (he : e ∈ D) {y : G} (hy : y ∈ D) (hzy : Commute z y) (hzyD : z * y ∈ D)
    (h3 : orderOf (y * e) = 3) (h5 : orderOf (z * e) = 5) : orderOf (y * z * e) = 5 := by
  obtain ⟨-, -, ⟨-, o3⟩⟩ := h.opposite_of_line hz hy hzy hzyD
  refine orderOf_eq_five_of_three_five (hD.mul_self_eq_one hy) (hD.mul_self_eq_one hz)
    (hD.mul_self_eq_one he) hzy.symm h3 h5 ?_
  rwa [← hzy.eq]

end TotallyOpposite

theorem lineConfig_of_totallyOpposite (hD : IsRootInvolutionSet D) {z e x₀ x₁ : G}
    (h : TotallyOpposite D z e) (hz : z ∈ D) (he : e ∈ D) (hx₀ : x₀ ∈ D) (hx₁ : x₁ ∈ D)
    (hzx₀ : Commute z x₀) (hzx₁ : Commute z x₁) (hzx₀D : z * x₀ ∈ D) (hzx₁D : z * x₁ ∈ D)
    (hsq : (x₀ * x₁) ^ 2 = z) (h5 : orderOf (z * e) = 5) (h3₀ : orderOf (x₀ * e) = 3)
    (h3₁ : orderOf (x₁ * e) = 3) : LineConfig z e ![x₀, x₁] := by
  have hx₀2 := hD.mul_self_eq_one hx₀
  have hx₁2 := hD.mul_self_eq_one hx₁
  have hsq' : (x₁ * x₀) ^ 2 = z := by
    have h4 : (x₀ * x₁) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, pow_two, hD.mul_self_eq_one hz]
    have hinv : x₁ * x₀ = (x₀ * x₁)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx₀2, inv_eq_of_mul_eq_one_right hx₁2]
    rw [hinv, inv_pow, ← hsq, inv_eq_iff_mul_eq_one, ← pow_add]
    exact h4
  have hcd : ∀ (y : G), y ∈ D → Commute z y → z * y ∈ D → orderOf (y * e) = 3 →
      (e * (z * y)) ^ 5 = 1 := by
    intro y hy hzy hzyD h3
    have h5' := h.orderOf_eq_five hD hz he hy hzy hzyD h3 h5
    have hinv : e * (z * y) = (y * z * e)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, hD.inv_eq he, hD.inv_eq hz, hD.inv_eq hy, ← mul_assoc]
    rw [hinv, inv_pow, ← h5', pow_orderOf_eq_one, inv_one]
  refine ⟨hD.mul_self_eq_one hz, hD.mul_self_eq_one he, fun i => ?_, ?_, fun i => ?_,
    fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
  · fin_cases i
    · exact hx₀2
    · exact hx₁2
  · rw [← h5]; exact pow_orderOf_eq_one _
  · fin_cases i
    · exact hzx₀
    · exact hzx₁
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hsq
    · exact hsq'
    · exact absurd rfl hij
  · fin_cases i
    · have := pow_orderOf_eq_one (e * x₀)
      rwa [orderOf_mul_comm_eq, h3₀] at this
    · have := pow_orderOf_eq_one (e * x₁)
      rwa [orderOf_mul_comm_eq, h3₁] at this
  · fin_cases i
    · exact hcd x₀ hx₀ hzx₀ hzx₀D h3₀
    · exact hcd x₁ hx₁ hzx₁ hzx₁D h3₁

namespace Exc

theorem mk_eq_one_a6 (w : List (Fin 4 × Bool))
    (hwalk : Exc.coverWalk (2 * 4) A6Data.fx A6Data.fy A6Data.ffi 0 (w.map letterCode) = 0) :
    PresentedGroup.mk (wordRels (lineRels 2 false)) (FreeGroup.mk w) = 1 :=
  mk_eq_one_of_coverWalk (N := 1080) (F := 4320) (fx := A6Data.fx) (fc := A6Data.fc)
    (fy := A6Data.fy) (kind := A6Data.kind) (wi := A6Data.wi) (fs := A6Data.fs)
    (ft := A6Data.ft) (fo := A6Data.fo) (refs := A6Data.refs) (pl := A6Data.pl)
    (ffi := A6Data.ffi) (live := A6Data.live) (rels := wordRels (lineRels 2 false))
    (lineRels 2 false) A6Data.words (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel)
    A6Data.live_zero (by norm_num) A6Data.facts_all A6Data.cover_all w hwalk

end Exc

open Exc

end CFSG.Timmesfeld.Moufang
