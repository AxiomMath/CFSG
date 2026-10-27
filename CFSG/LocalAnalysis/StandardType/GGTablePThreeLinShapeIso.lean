module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly
open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.CALinearPrimary

section Commutator

open scoped commutatorElement

private theorem nonempty_quotient_center_equiv_of_surjective
    {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (φ : G →* H) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) :
    Nonempty (G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H) := by
  let ψ : G →* H ⧸ Subgroup.center H := (QuotientGroup.mk' _).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hkerψ : ψ.ker = Subgroup.center G := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx1 : ψ x = 1 := MonoidHom.mem_ker.mp hx
      have hxH : φ x ∈ Subgroup.center H := by
        change (QuotientGroup.mk (φ x) : H ⧸ Subgroup.center H) = 1 at hx1
        exact (QuotientGroup.eq_one_iff (φ x)).mp hx1
      have hmem : ∀ y : G, ⁅x, y⁆ ∈ Subgroup.center G := by
        intro y
        apply hker
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          ((Subgroup.mem_center_iff.mp hxH) (φ y)).symm
      have hZ2 : Subgroup.upperCentralSeries G 2 = Subgroup.center G := by
        rw [show (2 : ℕ) = 1 + 1 from rfl,
          ← Subgroup.comap_upperCentralSeries_quotient_center (G := G) 1,
          Subgroup.upperCentralSeries_one, Group.IsPerfect.center_quotient_center_eq_bot,
          MonoidHom.comap_bot, QuotientGroup.ker_mk']
      have hxZ2 : x ∈ Subgroup.upperCentralSeries G 2 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
          Subgroup.upperCentralSeries_one]
        exact hmem
      rwa [hZ2] at hxZ2
    · intro x hx
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk (φ x) : H ⧸ Subgroup.center H) = 1
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.map_center_le_center hφ (Subgroup.mem_map_of_mem φ hx)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

end Commutator

theorem isPerfect_specialLinearGroup
    (m : ℕ) (E : Type) [Field E] (hm : 2 ≤ m) (hmE : m = 2 → 4 ≤ Nat.card E) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) E) := by
  rcases lt_or_eq_of_le hm with h3 | h2
  · exact CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  · subst m
    have hcard : 4 ≤ Nat.card E := hmE rfl
    haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
    letI : Fintype E := Fintype.ofFinite E
    have h4 : ∃ s : Finset E, s.card = 4 := by
      have h : 4 ≤ (Finset.univ : Finset E).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact hcard
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h
      exact ⟨t, ht⟩
    exact CFSG.LinearGroups.special_linear_isPerfect le_rfl (Or.inr h4)

private theorem nonempty_specialLinear_centerQuot_equiv_projectiveSL
    (m : ℕ) (E : Type) [Field E] :
    Nonempty (Matrix.SpecialLinearGroup (Fin m) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) ≃* LinearFlag.projectiveSL m E) :=
  ⟨QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center (n := m) (K := E)).symm⟩

theorem linShape_iso
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {X : Type} [Group X] [Finite X]
    {J : Subgroup X}
    {θ : X ⧸ Subgroup.center X ≃* PSLg N K}
    {J' : Subgroup (PSLg N K)} (hJ' : J' = J.map (proj θ)) (hperfJ : commutator J = ⊤)
    {E : Type} [Field E] {m : ℕ}
    {f : Matrix.SpecialLinearGroup (Fin m) E →* ↥J'}
    (hm : 2 ≤ m) (hmE : m = 2 → 4 ≤ Nat.card E)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center _) :
    Nonempty (J ⧸ Subgroup.center J ≃* PSLg m E) := by
  haveI : Group.IsPerfect ↥J := Group.IsPerfect.mk hperfJ
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) E) :=
    isPerfect_specialLinearGroup m E hm hmE
  have hproj : ∀ x : X, proj θ x = 1 → x ∈ Subgroup.center X := by
    intro x hx
    have h1 : θ (QuotientGroup.mk x : X ⧸ Subgroup.center X) = 1 := hx
    have h2 : (QuotientGroup.mk x : X ⧸ Subgroup.center X) = 1 :=
      θ.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff x).mp h2
  let π : ↥J →* ↥J' := ((proj θ).comp J.subtype).codRestrict J' (fun x => by
    change proj θ (x : X) ∈ J'
    rw [hJ']
    exact Subgroup.mem_map_of_mem (proj θ) x.2)
  have hcoe : ∀ x : ↥J, ((π x : ↥J') : PSLg N K) = proj θ (x : X) := fun x => rfl
  have hπsurj : Function.Surjective π := by
    intro y
    have hy : (y : PSLg N K) ∈ J.map (proj θ) := by
      rw [← hJ']; exact y.2
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hxJ, hxy⟩ := hy
    refine ⟨⟨x, hxJ⟩, ?_⟩
    apply Subtype.ext
    rw [hcoe]
    exact hxy
  have hπker : π.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxproj : proj θ (x : X) = 1 := by
      rw [← hcoe x, hx]; rfl
    have hxX : (x : X) ∈ Subgroup.center X := hproj x.1 hxproj
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using (Subgroup.mem_center_iff.mp hxX) (y : X)
  obtain ⟨eJ⟩ := nonempty_quotient_center_equiv_of_surjective π hπsurj hπker
  obtain ⟨eSL⟩ := nonempty_quotient_center_equiv_of_surjective f hf hker
  have e3 : Matrix.SpecialLinearGroup (Fin m) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) ≃* PSLg m E :=
    (nonempty_specialLinear_centerQuot_equiv_projectiveSL m E).some.trans
      (CFSG.StandardType.TypeA.recipeEquiv m E).symm
  exact ⟨(eJ.trans eSL.symm).trans e3⟩

end CFSG.StandardType.TablePThreeKG

end
