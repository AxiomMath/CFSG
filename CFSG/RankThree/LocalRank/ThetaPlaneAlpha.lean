module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlane
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneProduct
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneTransport

public section

namespace CFSG.RankThree.LocalRank

open CFSG CFSG.RankThreeEvenClassification.Helpers
open scoped Pointwise

@[expose] noncomputable def thetaT (p : ℕ) {X : Type*} [Group X] (B : Subgroup X) : Subgroup X :=
  ⨅ (b : X) (_ : b ∈ B) (_ : b ≠ 1),
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set X))

@[expose] noncomputable def thetaJ (p : ℕ) {X : Type*} [Group X] (B : Subgroup X) : Subgroup X :=
  ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1),
    ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set X)), B⁆

@[expose] noncomputable def thetaAlpha (p : ℕ) {X : Type*} [Group X] (B : Subgroup X) :
    Subgroup X :=
  thetaJ p B ⊔ thetaT p B

theorem thetaT_eq_thetaPlaneIntersection {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (B : Subgroup X) : thetaT p B = thetaPlaneIntersection p B := by
  simp only [thetaT, thetaPlaneIntersection, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]

theorem thetaJ_eq_thetaPlaneCommutators {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (B : Subgroup X) : thetaJ p B = thetaPlaneCommutators p B := by
  simp only [thetaJ, thetaPlaneCommutators, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]

theorem thetaAlpha_eq_thetaPlaneAlpha {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (B : Subgroup X) : thetaAlpha p B = thetaPlaneAlpha p B := by
  rw [thetaAlpha, thetaPlaneAlpha, thetaT_eq_thetaPlaneIntersection hp,
    thetaJ_eq_thetaPlaneCommutators hp]

theorem theta_plane_alpha_product_equivariance {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (B : Subgroup X) (hBcard : Nat.card B = p ^ 2) :
    Group.IsSolvable (thetaT p B) ∧ ¬p ∣ Nat.card (thetaT p B) ∧
    thetaT p B ≤ Subgroup.centralizer (B : Set X) ∧
    ((thetaT p B).subgroupOf (Subgroup.centralizer (B : Set X))).Normal ∧
    thetaT p B ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer (B : Set X)) ∧
    Subgroup.centralizer (B : Set X) ≤ Subgroup.normalizer (thetaJ p B : Set X) ∧
    Subgroup.centralizer (B : Set X) ≤ Subgroup.normalizer (thetaAlpha p B : Set X) ∧
    thetaAlpha p B = thetaJ p B ⊔ thetaT p B ∧
    (thetaAlpha p B : Set X) = (thetaJ p B : Set X) * (thetaT p B : Set X) := by
  have hne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hBcard
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  rw [thetaAlpha_eq_thetaPlaneAlpha hp, thetaT_eq_thetaPlaneIntersection hp,
    thetaJ_eq_thetaPlaneCommutators hp, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
  have hle := thetaPlaneIntersection_le_centralizer p B
  exact ⟨thetaPlaneIntersection_solvable p hp B b hb hb1',
    thetaPlaneIntersection_prime_complement p hp B b hb hb1', hle,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (centralizer_plane_normalizes_intersection p hp B),
    thetaPlaneIntersection_le_fixed_theta p hp B b hb hb1',
    centralizer_plane_normalizes_commutators p hp B, centralizer_plane_normalizes_alpha p hp B,
    rfl, thetaPlaneAlpha_coe_product p hp B⟩

theorem thetaT_map_equiv {p : ℕ} (hp : p.Prime) {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] (φ : X ≃* Y) (B : Subgroup X) :
    (thetaT p B).map φ.toMonoidHom = thetaT p (B.map φ.toMonoidHom) := by
  rw [thetaT_eq_thetaPlaneIntersection hp, thetaT_eq_thetaPlaneIntersection hp]
  exact thetaPlaneIntersection_map_equiv p hp φ B

theorem thetaJ_map_equiv {p : ℕ} (hp : p.Prime) {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] (φ : X ≃* Y) (B : Subgroup X) :
    (thetaJ p B).map φ.toMonoidHom = thetaJ p (B.map φ.toMonoidHom) := by
  rw [thetaJ_eq_thetaPlaneCommutators hp, thetaJ_eq_thetaPlaneCommutators hp]
  exact thetaPlaneCommutators_map_equiv p hp φ B

theorem thetaAlpha_map_equiv {p : ℕ} (hp : p.Prime) {X Y : Type*} [Group X] [Group Y]
    [Finite X] [Finite Y] (φ : X ≃* Y) (B : Subgroup X) :
    (thetaAlpha p B).map φ.toMonoidHom = thetaAlpha p (B.map φ.toMonoidHom) := by
  rw [thetaAlpha_eq_thetaPlaneAlpha hp, thetaAlpha_eq_thetaPlaneAlpha hp]
  exact thetaPlaneAlpha_map_equiv p hp φ B

theorem thetaAlpha_conjugate {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (B : Subgroup X) (g : X) : conjugate (thetaAlpha p B) g = thetaAlpha p (conjugate B g) := by
  simp only [conjugate]
  exact thetaAlpha_map_equiv hp (MulAut.conj g⁻¹) B

end CFSG.RankThree.LocalRank
