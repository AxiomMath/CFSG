module

import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Res7ONPoint

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_le_sup148 {X R : Subgroup G} {b : G} (hX : X ∈ thetaComponentsAt 3 b)
    (h3 : 3 ∣ Nat.card X) (hRC : R ≤ Subgroup.centralizer ({b} : Set G))
    (hCR : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (R : Set G))
    (hR3 : Nat.Coprime 3 (Nat.card R)) {g : G} (hgC : g ∈ Subgroup.centralizer ({b} : Set G))
    (hgN : g ∈ Subgroup.normalizer ((R ⊔ X : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  set θC := inSubgroup (aschbacherSolvableCore 3) C with hθCdef
  by_contra hgX
  set X' := X.map (MulAut.conj g).toMonoidHom with hX'def
  have hX' : X' ∈ thetaComponentsAt 3 b := Sec6.map_conj_mem_thetaComponentsAt hgC hX
  have hne : X ≠ X' := Sec6.ne_map_conj_of_not_mem_normalizer hgX
  have hcomm : ⁅X, X'⁆ ≤ θC := Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hX hX' hne
  have hXC : X ≤ C := le_centralizer_of_mem_thetaComponentsAt hX
  have hX'C : X' ≤ C := le_centralizer_of_mem_thetaComponentsAt hX'
  have hX'RX : X' ≤ R ⊔ X := by
    have h1 : (R ⊔ X).map (MulAut.conj g).toMonoidHom = R ⊔ X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
    rw [hX'def, ← h1]
    exact Subgroup.map_mono le_sup_right
  have hθn : C ≤ Subgroup.normalizer (θC : Set G) :=
    Subgroup.le_normalizer.trans
      (RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore
        3 C)
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := hXC.trans hCR
  have hcomm' : ⁅X', X'⁆ ≤ θC ⊔ R := by
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    have hy₁' : y₁ ∈ ((R ⊔ X : Subgroup G) : Set G) := hX'RX hy₁
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R X hXR] at hy₁'
    obtain ⟨r, hr, x, hx, rfl⟩ := hy₁'
    have hy₂C : y₂ ∈ C := hX'C hy₂
    have hrC : r ∈ C := hRC hr
    have e1 : ⁅r * x, y₂⁆ = (r * ⁅x, y₂⁆ * r⁻¹) * (r * (y₂ * r⁻¹ * y₂⁻¹)) := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · exact (Subgroup.mem_normalizer_iff.mp (hθn hrC) _).mp
        (hcomm (Subgroup.commutator_mem_commutator hx hy₂))
    · exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hCR hy₂C) _).mp (R.inv_mem hr))
  have hX'p : Group.IsPerfect ↥X' := by
    obtain ⟨L', hL', hL'eq⟩ := hX'
    rw [← hL'eq]
    exact isPerfect_map_subtype hL'.1
  have hX'le : X' ≤ θC ⊔ R := by
    have h1 : ⁅X', X'⁆ = X' := Subgroup.isPerfect_iff.mp hX'p
    rw [← h1]
    exact hcomm'
  have hRθ : R ≤ Subgroup.normalizer (θC : Set G) := hRC.trans hθn
  have hθ3 : ¬ 3 ∣ Nat.card θC := by
    have h := (solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three).2.2.1
    rwa [hθCdef, inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
  have hR3' : ¬ 3 ∣ Nat.card R := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hR3
  have hdvd := Main148.card_sup_dvd_of_le_normalizer148 θC R hRθ
  have h3X' : 3 ∣ Nat.card X' := by
    rwa [hX'def, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h3N : 3 ∣ Nat.card θC * Nat.card R :=
    (h3X'.trans (Subgroup.card_dvd_of_le hX'le)).trans hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3N with h | h
  exacts [hθ3 h, hR3' h]

end Res7ONPoint

end CFSG.RankThree.PartTwo.Sec14
