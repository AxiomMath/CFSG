module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerMain

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K]

theorem not_isComponentOf_ggFix_diag_two (hKd : UnitaryFieldData 2 1 K)
    {τ : Fin 6 → Kˣ} (hD : diagHom 6 τ ∈ Subgroup.normalizer
      (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))
    (hb : ∀ (i : Fin 6) (S : Finset (Fin 6)), (∀ j, j ∈ S ↔ τ j = τ i) → S.card ≤ 3)
    (J : Subgroup (LargeEvenProj (unitarySU 2 1 K 6))) :
    ¬ IsComponentOf J (ggFix (TableB.projConj (unitarySU 2 1 K 6) ⟨diagHom 6 τ, hD⟩)) := by
  classical
  haveI : Finite K := hKd.finite
  intro hE
  set ē : GL (Fin 6) K ⧸ LargeEvenScalars (Fin 6) K := QuotientGroup.mk (diagHom 6 τ) with hē
  have hJ := isComponentOf_map_of_injective (reducedToPGL K 1 6) reducedToPGL_injective hE
  rw [map_ggFix_eq hD] at hJ
  have hδ : ∀ e ∈ ({ē} : Set (GL (Fin 6) K ⧸ LargeEvenScalars (Fin 6) K)),
      (e, diagHom (5 + 1) ((fun _ => τ) e)) ∈ SUTorus.suPairs (suToPGL K 1 6) := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    refine ⟨hD, fun u v huv => ?_⟩
    show QuotientGroup.mk (diagHom 6 τ) * QuotientGroup.mk (u : GL (Fin 6) K) *
      (QuotientGroup.mk (diagHom 6 τ))⁻¹ = QuotientGroup.mk (v : GL (Fin 6) K)
    rw [huv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  obtain ⟨i, hi⟩ := SUTorus.exists_le_map_blockSU (m := 5) hKd Nat.prime_three (by norm_num)
    ker_suToPGL_le_center hδ hJ
  have hcls : (LinTorus.diagClass {ē} (fun _ => τ) i).card ≤ 3 :=
    hb i _ fun j => by simp [LinTorus.mem_diagClass]
  have hcls1 : 1 ≤ (LinTorus.diagClass {ē} (fun _ => τ) i).card :=
    Finset.card_pos.mpr ⟨i, LinTorus.self_mem_diagClass _ _ i⟩
  haveI hBs : Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1)
      (LinTorus.diagClass {ē} (fun _ => τ) i)).map (suToPGL K 1 6)) :=
    WitSU.isSolvable_map_blockSU_two_one hKd (suToPGL K 1 6) hcls1 hcls
  exact isQuasisimple_not_isSolvable hJ.2.2
    (solvable_of_solvable_injective (Subgroup.inclusion_injective hi))

section Abstract

variable {R : Type*} [Group R]

theorem not_isComponentOf_ggFix_conj (σ a : MulAut R)
    (h : ∀ J, ¬ IsComponentOf J (ggFix (σ⁻¹ * a * σ))) :
    ∀ J, ¬ IsComponentOf J (ggFix a) := by
  intro J hc
  have hf : Function.Injective (σ⁻¹ : MulAut R).toMonoidHom := (σ⁻¹ : MulAut R).injective
  refine h (J.map (σ⁻¹ : MulAut R).toMonoidHom) ?_
  rw [← map_ggFix_conj σ a]
  exact isComponentOf_map_of_injective _ hf hc

end Abstract

theorem not_isComponentOf_ggFix_of_conj (hKd : UnitaryFieldData 2 1 K) {M P D : GL (Fin 6) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))
    (hP : P ∈ primeFormUnitary hKd (idGram K 6)) (hMP : P⁻¹ * M * P = D)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))
    (h : ∀ J, ¬ IsComponentOf J (ggFix (TableB.projConj (unitarySU 2 1 K 6) ⟨D, hD⟩))) :
    ∀ J, ¬ IsComponentOf J (ggFix (TableB.projConj (unitarySU 2 1 K 6) ⟨M, hM⟩)) := by
  have hPN : P ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) :=
    gu_subset_normalizer hKd (mem_guSet_of_mem_primeFormUnitary hKd hP)
  have e : TableB.projConj (unitarySU 2 1 K 6) ⟨D, hD⟩ =
      (TableB.projConj (unitarySU 2 1 K 6) ⟨P, hPN⟩)⁻¹ *
        TableB.projConj (unitarySU 2 1 K 6) ⟨M, hM⟩ *
        TableB.projConj (unitarySU 2 1 K 6) ⟨P, hPN⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hMP.symm
  refine not_isComponentOf_ggFix_conj (TableB.projConj (unitarySU 2 1 K 6) ⟨P, hPN⟩) _ ?_
  rw [← e]
  exact h

theorem not_isComponentOf_ggFix_of_twoBlocks_two (hKd : UnitaryFieldData 2 1 K)
    {M : GL (Fin 6) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))
    (h : TwoBlocks hKd M) :
    ∀ J, ¬ IsComponentOf J (ggFix (TableB.projConj (unitarySU 2 1 K 6) ⟨M, hM⟩)) := by
  obtain ⟨P, hP, τ, hMP, hb, -⟩ := h
  have hPN : P ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) :=
    gu_subset_normalizer hKd (mem_guSet_of_mem_primeFormUnitary hKd hP)
  have hD : diagHom 6 τ ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) := by
    rw [← hMP]
    exact mul_mem (mul_mem (inv_mem hPN) hM) hPN
  exact not_isComponentOf_ggFix_of_conj hKd hM hP hMP hD
    (not_isComponentOf_ggFix_diag_two hKd hD hb)

theorem not_isComponentOf_ggFix_of_heis_two [Finite K] (hKd : UnitaryFieldData 2 1 K)
    (hpq : 3 ∣ 2 ^ 1 + 1)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 1 K 6)))} (hcard : Nat.card Ab = 27)
    (hheis : ∃ (x y z : GL (Fin 6) K)
      (hxN : x ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))
      (hyN : y ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))
      (hzN : z ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K))) (ζ : Kˣ),
      x ∈ primeFormUnitary hKd (idGram K 6) ∧ y ∈ primeFormUnitary hKd (idGram K 6) ∧
      z ∈ primeFormUnitary hKd (idGram K 6) ∧
      TableB.projConj (unitarySU 2 1 K 6) ⟨x, hxN⟩ ∈ Ab ∧
      TableB.projConj (unitarySU 2 1 K 6) ⟨y, hyN⟩ ∈ Ab ∧
      TableB.projConj (unitarySU 2 1 K 6) ⟨z, hzN⟩ ∈ Ab ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧
      x * y = GeneralLinearGroup.scalar (Fin 6) ζ * (y * x) ∧ x * z = z * x ∧ y * z = z * y ∧
      z ∉ LargeEvenScalars (Fin 6) K) :
    ∀ a ∈ Ab, a ≠ 1 → ∀ J, ¬ IsComponentOf J (ggFix a) := by
  obtain ⟨x, y, z, hxN, hyN, hzN, ζ, hxu, hyu, hzu, hxA, hyA, hzA, hx3, hy3, hz3, hζ3, hζ1, hxy,
    hxz, hyz, hzs⟩ := hheis
  intro a ha ha1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hζ : IsPrimitiveRoot ζ 3 := by
    have := IsPrimitiveRoot.orderOf ζ
    rwa [orderOf_eq_prime hζ3 hζ1] at this
  obtain ⟨i, j, k, hM, hi, hj, hk, rfl⟩ := exists_mono_of_card hKd hpq hcard hxN hyN hzN hζ hxA
    hyA hzA hxy hxz hyz hz3 hzs a ha
  by_cases hij : i ≠ 0 ∨ j ≠ 0
  · exact not_isComponentOf_ggFix_of_twoBlocks_two hKd hM
      (twoBlocks_of_mono hKd hpq hxu hyu hzu hx3 hy3 hz3 hζ hxy hxz hyz hij hi hj k)
  · push Not at hij
    obtain ⟨rfl, rfl⟩ := hij
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply ha1
      have : (⟨x ^ 0 * y ^ 0 * z ^ 0, hM⟩ :
          Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K))) = 1 :=
        Subtype.ext (by simp)
      rw [this, map_one]
    refine not_isComponentOf_ggFix_of_twoBlocks_two hKd hM ?_
    rw [pow_zero, pow_zero, one_mul, one_mul]
    exact twoBlocks_of_central_pow hKd hpq hxu hzu hx3 hz3 hζ hxy hxz hyz hzs hk hk0

end CFSG.StandardType.Line63.H5

end
