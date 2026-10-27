module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Basic
public import CFSG.Foundations.Basic
import CFSG.RankThree.PartOne.N1322.ExtraspecialAbs
import CFSG.RankThree.PartOne.N1322.CaseConj
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import CFSG.RankThree.PartOne.N1322.CasePair

public section

namespace CFSG.StandardType.ZS.DimThree

open Subgroup CFSG.RankThree.PartOne CFSG.RepresentationTheory

variable {p : ℕ} [Fact p.Prime]

private def conjMulEquiv_ze (t : GL (Fin 3) (ZMod p)) (h2 : t * t = 1)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hn : ∀ x ∈ H, t * x * t⁻¹ ∈ H) : H ≃* H where
  toFun x := ⟨t * (x : GL (Fin 3) (ZMod p)) * t⁻¹, hn x x.2⟩
  invFun x := ⟨t⁻¹ * (x : GL (Fin 3) (ZMod p)) * t, by
    simpa [inv_eq_of_mul_eq_one_right h2] using hn x x.2⟩
  left_inv x := Subtype.ext (by
    show t⁻¹ * (t * (x : GL (Fin 3) (ZMod p)) * t⁻¹) * t = (x : GL (Fin 3) (ZMod p))
    group)
  right_inv x := Subtype.ext (by
    show t * (t⁻¹ * (x : GL (Fin 3) (ZMod p)) * t) * t⁻¹ = (x : GL (Fin 3) (ZMod p))
    group)
  map_mul' x y := Subtype.ext (by
    show t * ((x : GL (Fin 3) (ZMod p)) * (y : GL (Fin 3) (ZMod p))) * t⁻¹ =
      (t * (x : GL (Fin 3) (ZMod p)) * t⁻¹) *
        (t * (y : GL (Fin 3) (ZMod p)) * t⁻¹)
    group)

private theorem commute_of_conj_mul_inv_central_ze {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hE : IsExtraspecialPGroup 3 H) {t : GL (Fin 3) (ZMod p)} {φ : H ≃* H}
    (hφcoe : ∀ y : H, ((φ y : H) : GL (Fin 3) (ZMod p)) = t * y * t⁻¹)
    (hφ2 : ∀ y, φ (φ y) = y) (hφz : ∀ z ∈ Subgroup.center H, φ z = z)
    (hminus : ∀ a : H, φ a * a⁻¹ ∈ Subgroup.center H) :
    ∀ a ∈ H, (a : GL (Fin 3) (ZMod p)) * t = t * a := by
  intro a ha
  set ζ : H := φ ⟨a, ha⟩ * ⟨a, ha⟩⁻¹ with hζdef
  have hζZ : ζ ∈ Subgroup.center H := by rw [hζdef]; exact hminus ⟨a, ha⟩
  have hζa : φ ⟨a, ha⟩ = ζ * ⟨a, ha⟩ := by rw [hζdef]; group
  have h4 : (⟨a, ha⟩ : H) = ζ * (ζ * ⟨a, ha⟩) := by
    calc ⟨a, ha⟩ = φ (φ ⟨a, ha⟩) := (hφ2 ⟨a, ha⟩).symm
      _ = φ (ζ * ⟨a, ha⟩) := by rw [hζa]
      _ = φ ζ * φ ⟨a, ha⟩ := map_mul φ ζ ⟨a, ha⟩
      _ = ζ * φ ⟨a, ha⟩ := by rw [hφz ζ hζZ]
      _ = ζ * (ζ * ⟨a, ha⟩) := by rw [hζa]
  have hζ2 : ζ * ζ = 1 := by
    have h5 : (ζ * ζ) * (⟨a, ha⟩ : H) = ⟨a, ha⟩ := by
      rw [mul_assoc]; exact h4.symm
    calc ζ * ζ = (ζ * ζ) * 1 := (mul_one _).symm
      _ = (ζ * ζ) * ((⟨a, ha⟩ : H) * ⟨a, ha⟩⁻¹) := by rw [mul_inv_cancel]
      _ = ((ζ * ζ) * ⟨a, ha⟩) * ⟨a, ha⟩⁻¹ := (mul_assoc _ _ _).symm
      _ = ⟨a, ha⟩ * ⟨a, ha⟩⁻¹ := by rw [h5]
      _ = 1 := mul_inv_cancel _
  have hζ3 : ζ ^ 3 = 1 := N1322.ext27_center_cube hE ζ hζZ
  have hζ1 : ζ = 1 := by
    calc ζ = ζ * (ζ * ζ) := by rw [hζ2, mul_one]
      _ = ζ ^ 3 := by rw [pow_three]
      _ = 1 := hζ3
  have hφa : φ ⟨a, ha⟩ = ⟨a, ha⟩ := by rw [hζa, hζ1, one_mul]
  have hta : t * (a : GL (Fin 3) (ZMod p)) * t⁻¹ = a := by
    have h := congrArg (fun w : H => (w : GL (Fin 3) (ZMod p))) hφa
    rwa [hφcoe] at h
  calc (a : GL (Fin 3) (ZMod p)) * t = (t * a * t⁻¹) * t := by rw [hta]
    _ = t * a := by group

private theorem false_of_commutes_reflection_ze (hp : p ≠ 2)
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    {t : GL (Fin 3) (ZMod p)} (ht : N1322.IsRefl t)
    (hcomm : ∀ a ∈ H, (a : GL (Fin 3) (ZMod p)) * t = t * a) : False := by
  obtain ⟨c, hc⟩ := hsch (t : Matrix (Fin 3) (Fin 3) (ZMod p)) (fun g hg => by
    have h := hcomm g hg
    simpa using congrArg (fun w : GL (Fin 3) (ZMod p) =>
      (w : Matrix (Fin 3) (Fin 3) (ZMod p))) h)
  have ht2 : (t : Matrix (Fin 3) (Fin 3) (ZMod p)) * t = 1 := by
    have := congrArg (fun w : GL (Fin 3) (ZMod p) =>
      (w : Matrix (Fin 3) (Fin 3) (ZMod p))) ht.sq
    simpa using this
  have hc2 : c * c = 1 := by
    apply (Matrix.scalar_inj (n := Fin 3)).mp
    rw [map_mul, map_one, ← hc]
    exact ht2
  have hc3 : c ^ 3 = -1 := by
    have hdet : (Matrix.scalar (Fin 3) c).det = c ^ 3 := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three]
      ring
    have hdet_t : (t : Matrix (Fin 3) (Fin 3) (ZMod p)).det = -1 := ht.det_eq
    rw [hc] at hdet_t
    exact hdet.symm.trans hdet_t
  have hc1 : c = -1 := by
    calc c = c * (c * c) := by rw [hc2, mul_one]
      _ = c ^ 3 := by ring
      _ = -1 := hc3
  have htneg : (t : Matrix (Fin 3) (Fin 3) (ZMod p)) = -1 := by
    rw [hc, hc1, Matrix.scalar_apply]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal, Matrix.neg_apply]
    · simp [Matrix.diagonal, Matrix.neg_apply, hij]
      exact neg_zero.symm
  exact ht.ne_neg_one (four_ne_zero_of_ne_two hp) htneg

private theorem exists_conjMulEquiv_ze {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    {t : GL (Fin 3) (ZMod p)} (ht : N1322.IsRefl t)
    (hn : ∀ x ∈ H, t * x * t⁻¹ ∈ H) :
    ∃ φ : H ≃* H, (∀ y : H, ((φ y : H) : GL (Fin 3) (ZMod p)) = t * y * t⁻¹) ∧
      (∀ z ∈ Subgroup.center H, φ z = z) ∧ (∀ y, φ (φ y) = y) := by
  refine ⟨conjMulEquiv_ze t ht.sq hn, fun _ => rfl, ?_, ?_⟩
  · intro z hz
    apply Subtype.ext
    show t * (z : GL (Fin 3) (ZMod p)) * t⁻¹ = (z : GL (Fin 3) (ZMod p))
    have hzt : t * (z : GL (Fin 3) (ZMod p)) = (z : GL (Fin 3) (ZMod p)) * t :=
      N1322.central_of_center hsch (fun y hy => by
        simpa using congrArg (fun w : H => (w : GL (Fin 3) (ZMod p)))
          (Subgroup.mem_center_iff.mp hz (⟨y, hy⟩ : H))) t
    rw [hzt]; group
  · intro y
    apply Subtype.ext
    change t * (t * (y : GL (Fin 3) (ZMod p)) * t⁻¹) * t⁻¹ = (y : GL (Fin 3) (ZMod p))
    rw [inv_eq_of_mul_eq_one_right ht.sq]
    calc t * (t * (y : GL (Fin 3) (ZMod p)) * t) * t =
        (t * t) * (y : GL (Fin 3) (ZMod p)) * (t * t) := by group
      _ = (y : GL (Fin 3) (ZMod p)) := by rw [ht.sq]; group

theorem exists_scalar_conj_mul_of_extraspecial (hp : p ≠ 2) {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (h27 : Nat.card H = 27)
    (hE : IsExtraspecialPGroup 3 H) {t : GL (Fin 3) (ZMod p)} (ht : N1322.IsRefl t)
    (hn : ∀ x ∈ H, t * x * t⁻¹ ∈ H) {x : GL (Fin 3) (ZMod p)} (hx : x ∈ H) :
    ∃ c : ZMod p, ((t * x * t⁻¹ * x : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      Matrix.scalar (Fin 3) c := by
  have hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := N1322.ext27_noncomm h27 hE
    exact ⟨a, a.2, b, b.2, fun hc => hab (Subtype.ext hc)⟩
  have hsch := N1322.scalar_commutant_of_noncomm hirr hnc
  obtain ⟨φ, hφcoe, hφz, hφ2⟩ := exists_conjMulEquiv_ze hsch ht hn
  rcases N1322.ext27_pm h27 hE φ hφz hφ2 with hminus | hplus
  · exact absurd
      (commute_of_conj_mul_inv_central_ze hE hφcoe hφ2 hφz hminus)
      (fun hcomm => false_of_commutes_reflection_ze hp hsch ht hcomm)
  · have hzH : (t * (x : GL (Fin 3) (ZMod p)) * t⁻¹ * (x : GL (Fin 3) (ZMod p)) :
        GL (Fin 3) (ZMod p)) ∈ H := H.mul_mem (hn x hx) hx
    have hzEq : (⟨t * (x : GL (Fin 3) (ZMod p)) * t⁻¹ * (x : GL (Fin 3) (ZMod p)),
      hzH⟩ : H) = φ ⟨x, hx⟩ * ⟨x, hx⟩ := by
      apply Subtype.ext
      show t * (x : GL (Fin 3) (ZMod p)) * t⁻¹ * (x : GL (Fin 3) (ZMod p)) =
        ((φ ⟨x, hx⟩ : H) : GL (Fin 3) (ZMod p)) * (x : GL (Fin 3) (ZMod p))
      rw [hφcoe]
    have hcent : (⟨t * (x : GL (Fin 3) (ZMod p)) * t⁻¹ * (x : GL (Fin 3) (ZMod p)),
      hzH⟩ : H) ∈ Subgroup.center H := by
      rw [hzEq]
      exact hplus ⟨x, hx⟩
    obtain ⟨c, hc⟩ := hsch
      ((t * (x : GL (Fin 3) (ZMod p)) * t⁻¹ * (x : GL (Fin 3) (ZMod p)) :
        GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) (fun g hg => by
        have hcg : g * (t * (x : GL (Fin 3) (ZMod p)) * t⁻¹ * (x : GL (Fin 3) (ZMod p))) =
            (t * (x : GL (Fin 3) (ZMod p)) * t⁻¹ * (x : GL (Fin 3) (ZMod p))) * g :=
          N1322.central_of_center hsch (fun y hy => by
            simpa using Subgroup.mem_center_iff.mp hcent (⟨y, hy⟩ : H)) g
        simpa using congrArg (fun w : GL (Fin 3) (ZMod p) =>
          (w : Matrix (Fin 3) (Fin 3) (ZMod p))) hcg)
    exact ⟨c, hc⟩

end CFSG.StandardType.ZS.DimThree
