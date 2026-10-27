module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped commutatorElement

variable {W : Type} [Group W] [Finite W] {Q X : Subgroup W}

theorem le_upperCentralSeries_two_of_commutator_le_center
    (hsup : Q ⊔ X = ⊤)
    (hXcomm : ∀ x ∈ X, ∀ x' ∈ X, x * x' = x' * x)
    (hcomm : ∀ x ∈ X, ∀ q ∈ Q, ⁅x, q⁆ ∈ (Subgroup.center ↥Q).map Q.subtype)
    (hZcentral : ∀ x ∈ X, ∀ z ∈ (Subgroup.center ↥Q).map Q.subtype, x * z = z * x) :
    X ≤ Subgroup.upperCentralSeries W 2 := by
  classical
  set Z : Subgroup W := (Subgroup.center ↥Q).map Q.subtype with hZdef
  have hZle : Z ≤ Subgroup.center W := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hw : w ∈ Subgroup.centralizer (Z : Set W) := by
      have hQ : Q ≤ Subgroup.centralizer (Z : Set W) := by
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        obtain ⟨zq, hzq, rfl⟩ := Subgroup.mem_map.mp hz
        exact (congrArg Q.subtype (Subgroup.mem_center_iff.mp hzq ⟨q, hq⟩)).symm
      have hX : X ≤ Subgroup.centralizer (Z : Set W) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (hZcentral x hx z hz).symm
      have htop : (⊤ : Subgroup W) ≤ Subgroup.centralizer (Z : Set W) := by
        rw [← hsup]
        exact sup_le hQ hX
      exact htop (Subgroup.mem_top w)
    exact ((Subgroup.mem_centralizer_iff.mp hw) z hz).symm
  intro x hx
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
    Subgroup.upperCentralSeries_one]
  intro w
  have hgen : Subgroup.closure ((Q : Set W) ∪ (X : Set W)) = (⊤ : Subgroup W) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, hsup]
  have hw : w ∈ Subgroup.closure ((Q : Set W) ∪ (X : Set W)) := by
    rw [hgen]
    exact Subgroup.mem_top w
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with hsQ | hsX
    · exact hZle (hcomm x hx s hsQ)
    · have h1 : ⁅x, s⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hXcomm x hx s hsX
      rw [h1]
      exact Subgroup.one_mem _
  | one => simp
  | mul a b ha hb haZ hbZ =>
    have h : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by group
    rw [h]
    exact Subgroup.mul_mem _ haZ
      (Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center W).Normal) _ hbZ a)
  | inv a ha haZ =>
    have h : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a⁻¹⁻¹ := by group
    rw [h]
    exact Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center W).Normal) _
      (Subgroup.inv_mem _ haZ) a⁻¹

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
