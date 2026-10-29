module

public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoL1
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoL4
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoL5
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoL6

public section

namespace CFSG.RankThree.PartTwo.Sec19

open Matrix CFSG.RankThree.PartOne.CTP
open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.LieType.SeitzGeneration

theorem exists_fixedSubfield_of_orderOf_three {F : Type} [Field F] [Finite F] {σ : F ≃+* F}
    (hσ : orderOf σ = 3) :
    ∃ k : Subfield F, (∀ x, x ∈ k ↔ σ x = x) ∧ Nat.card F = Nat.card k ^ 3 ∧ 1 < Nat.card k := by
  refine ⟨CFSG.GH74.GLS.IVK.fixedField σ, fun x => CFSG.GH74.GLS.IVK.mem_fixedField_iff σ x, ?_,
    CFSG.GH74.GLS.IVK.one_lt_card_fixedField σ⟩
  have h := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
  rw [hσ] at h
  exact h.symm

theorem planeGen_projectiveSL_field {F : Type} [Field F] [Finite F]
    (h3 : (3 : F) ≠ 0) (h8 : Nat.card F ≠ 8) {E : Subgroup (MulAut (projectiveSL 3 F))}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hc : Nat.card E = 9) (hN : ¬ NarrowScope 3 E) :
    PlaneGen E := by
  have hnL : ¬ E ≤ linearAutGroup 3 F := not_le_linearAutGroup_of_not_narrow h3 hE hN
  obtain ⟨y, hyE, hyL, hy1⟩ := exists_ne_one_inf_linearAutGroup h3 hE hc hnL
  obtain ⟨phi, hphiE, hphiN⟩ : ∃ phi ∈ E, phi ∉ linearAutGroup 3 F := by
    by_contra hcon
    push Not at hcon
    exact hnL (fun x hx => hcon x hx)
  obtain ⟨σ, hσ3, H, hphiH⟩ :=
    KFacts.linear_order_three_field_descent (le_refl 3) phi (hE.2 phi hphiE) hphiN
  subst hphiH
  obtain ⟨σ', H', hσ'3, hψH, -, hfix'⟩ :=
    exists_second_field_element hE hσ3 hphiE hphiN hyE hyL
  obtain ⟨k, hk, hF, hk1⟩ := exists_fixedSubfield_of_orderOf_three hσ3
  have hk' : ∀ x, x ∈ k ↔ σ' x = x := fun x => (hk x).trans (hfix' x).symm
  have hk3 : 3 ≤ Nat.card k := by
    by_contra hlt
    have h2 : Nat.card k = 2 := by omega
    exact h8 (by norm_num [hF, h2])
  have hψE : conjAut 3 F H' * fieldAut 3 F σ' * (conjAut 3 F H')⁻¹ ∈ E := by
    rw [← hψH]
    exact E.mul_mem hphiE hyE
  have hφ1 : conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ ≠ 1 := by
    intro h
    apply hphiN
    rw [h]
    exact (linearAutGroup 3 F).one_mem
  have hψ1 : conjAut 3 F H' * fieldAut 3 F σ' * (conjAut 3 F H')⁻¹ ≠ 1 := by
    intro h
    apply hphiN
    have hφy : conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ = y⁻¹ :=
      eq_inv_of_mul_eq_one_left (hψH.trans h)
    rw [hφy]
    exact (linearAutGroup 3 F).inv_mem hyL
  by_cases hne : (slSub 3 k).map (slConjugation 3 F (H⁻¹ * H')).toMonoidHom ≠ slSub 3 k
  · exact planeGen_of_two_field_lines hk hk' hF hk3 hphiE hψE hφ1 hψ1 hne
  · exfalso
    have hmap : (slSub 3 k).map (slConjugation 3 F (H⁻¹ * H')).toMonoidHom = slSub 3 k :=
      not_not.mp hne
    have hfix : ∀ S ∈ slSub 3 k,
        y (proj 3 F (slConjugation 3 F H S)) = proj 3 F (slConjugation 3 F H S) := by
      intro S hS
      have hS' : S ∈ (slSub 3 k).map (slConjugation 3 F (H⁻¹ * H')).toMonoidHom := by
        rw [hmap]
        exact hS
      obtain ⟨T, hT, hTS⟩ := Subgroup.mem_map.mp hS'
      have hcT : slConjugation 3 F H S = slConjugation 3 F H' T := by
        rw [← hTS]
        show slConjugation 3 F H (slConjugation 3 F (H⁻¹ * H') T) = slConjugation 3 F H' T
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
      have h1 := fixed_conjSub_of_fieldAut (H := H) hk hS
      have h2 : (conjAut 3 F H' * fieldAut 3 F σ' * (conjAut 3 F H')⁻¹)
          (proj 3 F (slConjugation 3 F H S)) = proj 3 F (slConjugation 3 F H S) := by
        rw [hcT]
        exact fixed_conjSub_of_fieldAut hk' hT
      have h4 : (conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹)
          (y (proj 3 F (slConjugation 3 F H S))) = proj 3 F (slConjugation 3 F H S) := by
        have hx : (conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹)
            (y (proj 3 F (slConjugation 3 F H S))) =
            (conjAut 3 F H' * fieldAut 3 F σ' * (conjAut 3 F H')⁻¹)
              (proj 3 F (slConjugation 3 F H S)) :=
          DFunLike.congr_fun hψH (proj 3 F (slConjugation 3 F H S))
        rw [hx, h2]
      apply (conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹).injective
      rw [h4, h1]
    exact hy1 (eq_one_of_fixes_conj_slSub h3 hyL hfix)

end CFSG.RankThree.PartTwo.Sec19

end
