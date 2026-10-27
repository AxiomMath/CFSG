module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnTwDSpecial
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnAll

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth

section Transport

variable {M M' : Type} [Group M] [Group M']

theorem innerConcl_of_mapEquiv (ψ : M ≃* M') {A D : Subgroup M}
    (h : InnerConcl (A.map ψ.toMonoidHom) (D.map ψ.toMonoidHom)) : InnerConcl A D := by
  obtain ⟨t, htD, htA, j, hjD, htj⟩ := h
  have hback : ∀ (S : Subgroup M) (x : M'), x ∈ S.map ψ.toMonoidHom → ψ.symm x ∈ S := by
    rintro S x ⟨d, hd, rfl⟩
    simpa using hd
  refine ⟨ψ.symm t, hback D t htD, hback A t htA, ψ.symm j, hback D j hjD, fun h' => htj ?_⟩
  have := congrArg ψ h'
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

end Transport

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

theorem innerConcl_of_four (S : FourData Q p A) (h4 : 4 ≤ Nat.card K)
    {D : Subgroup (V ≃ₗ[K] V)} {a : V ≃ₗ[K] V} (hE : EndData p (orthDerived Q) A D a) :
    InnerConcl A D := by
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd S.prime S.odd
  have haA : a ∈ A := hE.a_mem
  have hap : a ^ p = 1 := S.elem.2 a haA
  have hx : OddOrderIsometry Q p a :=
    ⟨orthDerived_le_orthogonalGroup (S.le_omega haA), hap, hpK, fun v hv =>
      S.regular.1 v fun w => by rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨i, hi, hDi⟩ := exists_block_of_endData hx hRep hE.D_le hE.D_cent hE.D_norm hE.D_qs
  by_cases h1 : i = X - 1
  · subst h1
    exact innerConcl_of_fixed_four S hE (hRep.1 hi) hDi
  · exact innerConcl_of_special_four S h4 hE (hRep.1 hi) h1 hDi

end Main

end SmallOrthUn

namespace SmallOrth

open CFSG.Assembly TableB TableBOrth SmallOrthUn CFSG.GroupTheory.WeirSylow

theorem twDFourEndInput_holds : TwDFourEndInput := by
  intro K _ _ n p b c hK hn hp hpn hirr A D a hE hr
  haveI : CharP K 2 := charP_two_of_card (one_le_of_card hK) hK
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set ψ := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx 3) K with hψ
  have hΩ : (LargeEvenOmega (LargeEvenQMinus 3 b c)).map ψ.toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived (qMinusForm K 3 b c) := by
    rw [← coe_qMinusForm (K := K) 3 b c]
    exact map_largeEvenOmega (qMinusForm K 3 b c)
  have hfin : Module.finrank K (LargeEvenMinusIdx 3 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [LargeEvenMinusIdx]
  have hcard : Nat.card (A.map ψ.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective ψ.injective
  have hEnd := endData_mapEquiv ψ hΩ hE
  have hminus : ¬ IsPlusType (qMinusForm K 3 b c) := fun h =>
    not_isPlusType_quadMinus (n := 3 + 1) (by norm_num) hirr
      ((isPlusType_congr (qMinusIsometry 3 b c)).1 h)
  right
  exact innerConcl_of_mapEquiv ψ (innerConcl_of_four
    ⟨nondegenerate_qMinusForm 3 hirr, hp, hp2, hpq, hfin, hminus, hEnd.A_le, hEnd.A_elem,
      by rw [hcard]; exact hr⟩ h4 hEnd)

theorem twDFourInput_holds : TwDFourInput :=
  twDFourInput_of_endInput twDFourEndInput_holds

end SmallOrth

end CFSG.StandardType

end
