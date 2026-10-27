module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFourSpecial

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth

section FourMain

variable {M M' : Type} [Group M] [Group M']

theorem normConcl_of_mapEquiv (ψ : M ≃* M') {p : ℕ} {A D : Subgroup M}
    (h : NormConcl p (A.map ψ.toMonoidHom) (D.map ψ.toMonoidHom)) : NormConcl p A D := by
  obtain ⟨U, hUD, hU1, hU2, hAU, t, htD, htp, htA, htU, j, hjD, htj⟩ := h
  have hback : ∀ x : M', x ∈ D.map ψ.toMonoidHom → ψ.symm x ∈ D := by
    rintro x ⟨d, hd, rfl⟩
    simpa using hd
  refine NormConcl.intro (U.map ψ.symm.toMonoidHom) ?_ ?_ (hU2.map _) ?_ (ψ.symm t)
    (hback t htD) (by rw [← map_pow, htp, map_one]) ?_ ?_ (ψ.symm j) (hback j hjD) ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact hback u (hUD hu)
  · intro hbot
    apply hU1
    rwa [Subgroup.map_eq_bot_iff_of_injective _ ψ.symm.injective] at hbot
  · rintro s hs _ ⟨u, hu, rfl⟩
    refine ⟨ψ s * u * (ψ s)⁻¹, hAU (ψ s) ⟨s, hs, rfl⟩ u hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.symm_apply_apply]
  · intro s hs
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact htA (ψ s) ⟨s, hs, rfl⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp htU (ψ x)
    have key : ∀ y : M, y ∈ U.map ψ.symm.toMonoidHom ↔ ψ y ∈ U := by
      intro y
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa using hu
      · intro hy
        exact ⟨ψ y, hy, by simp⟩
    rw [key, key, map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]
    exact h1
  · intro h'
    apply htj
    have := congrArg ψ h'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this

end FourMain

section Abstract

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p n : ℕ} {A : Subgroup (V ≃ₗ[K] V)}
  {Y : Submodule K V}

theorem normConcl_of_isotropic_four (hOm : OmegaFourInput) (hSU : UnitaryThreeInput)
    (hK2 : Nat.card K = 2) (hp3 : p = 3) (hn4 : n = 4) (S : OrbitData Q p n A Y)
    {D : Subgroup (V ≃ₗ[K] V)} {a : V ≃ₗ[K] V} (hE : EndData p (orthDerived Q) A D a) :
    NormConcl p A D := by
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
    exact normConcl_of_fixed_four hOm hK2 hp3 hn4 S hE (hRep.1 hi) hDi
  · exact normConcl_of_special_four hSU hK2 hp3 hn4 S hE (hRep.1 hi) h1 hDi

theorem normConcl_of_normalizes_four (hOm : OmegaFourInput) (hSU : UnitaryThreeInput)
    (hK2 : Nat.card K = 2) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hK1 : ∀ c : K, c ^ 3 = 1 → c = 1) (hn : finrank K V = 2 * 4)
    {D : Subgroup (V ≃ₗ[K] V)} {a : V ≃ₗ[K] V}
    (hE : EndData 3 (orthDerived Q) A D a) (hcard : 3 ^ (4 - 1) ≤ Nat.card A)
    (hU : NormalizesTwoGroup (orthDerived Q) A) : NormConcl 3 A D := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  have hpK : ((3 : ℕ) : K) ≠ 0 := natCast_ne_zero_of_odd Nat.prime_three (by norm_num)
  have hIso : IsoGroup (QuadraticMap.polarBilin Q) 3 A :=
    isoGroup_of_le hQ hE.A_le hE.A_elem
  obtain ⟨U, hUΩ, hU1, hU2, hAU⟩ := hU
  obtain ⟨Y, hY0, hYinv, hYQ⟩ := OrthBstarOdd.exists_singular_of_two hQ hK1 (S := U) (N := A)
    hU2 hU1
    (fun s hs v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup (hUΩ hs)) v)
    (fun s hs => (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ (hUΩ hs))).2)
    (fun g hg v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup (hE.A_le hg)) v)
    (fun g hg => hE.A_elem.2 g hg)
    (fun g hg s hs => (Subgroup.mem_normalizer_iff.mp (hAU hg) s).mp hs)
  have hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, QuadraticMap.polarBilin Q y y' = 0 := fun y hy y' hy' => by
    have h1 := hYQ (y + y') (Y.add_mem hy hy')
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h1, hYQ y hy, hYQ y' hy']
    simp
  have hle : Nat.card A ≤ 3 ^ (4 - 1) := by
    have := card_le_of_isotropic Nat.prime_three hpK hK1 (2 * 4) V hn (QuadraticMap.polarBilin Q)
      A hIso Y hY0 hYinv hYiso
    simpa using this
  exact normConcl_of_isotropic_four hOm hSU hK2 rfl rfl ⟨hQ, Nat.prime_three, by norm_num, hK1,
    hn, hE.A_le, hE.A_elem, le_antisymm hle hcard, hY0, hYinv, hYQ⟩ hE

end Abstract

end SmallOrthUn

namespace SmallOrth

open CFSG.Assembly TableB TableBOrth SmallOrthUn

theorem plusTwoFourInput_of (hOm : OmegaFourInput) (hSU : UnitaryThreeInput) :
    PlusTwoFourInput := by
  intro K _ _ hK A D a hE hr hU
  haveI : CharP K 2 := charP_two_of_card (n := 1) le_rfl (by rw [hK, pow_one])
  have hK1 : ∀ c : K, c ^ 3 = 1 → c = 1 :=
    OrthRestOdd.eq_one_of_pow_eq_one_of_dvd (n := 1) (p := 3) (by rw [hK, pow_one])
      Nat.prime_three (by norm_num)
  set ψ := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 4 ⊕ Fin 4) K with hψ
  have hΩ : (LargeEvenOmega (LargeEvenQPlus K 4)).map ψ.toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived (qPlusForm K 4) := by
    rw [← coe_qPlusForm (K := K) 4]
    exact map_largeEvenOmega (qPlusForm K 4)
  have hfin : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hcard : Nat.card (A.map ψ.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective ψ.injective
  right
  exact normConcl_of_mapEquiv ψ (normConcl_of_normalizes_four hOm hSU hK
    (nondegenerate_qPlusForm (K := K) 4) hK1 hfin (endData_mapEquiv ψ hΩ hE)
    (by rw [hcard]; simpa using hr) (normalizesTwoGroup_mapEquiv ψ hΩ hU))

theorem minusUnitThreeInput_of (hOm : OmegaFourInput) (hSU : UnitaryThreeInput) :
    MinusUnitThreeInput := by
  intro K _ _ b c hK hirr A D a hE hr hU
  haveI : CharP K 2 := charP_two_of_card (n := 1) le_rfl (by rw [hK, pow_one])
  have hK1 : ∀ x : K, x ^ 3 = 1 → x = 1 :=
    OrthRestOdd.eq_one_of_pow_eq_one_of_dvd (n := 1) (p := 3) (by rw [hK, pow_one])
      Nat.prime_three (by norm_num)
  set ψ := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (LargeEvenMinusIdx 3) K with hψ
  have hΩ : (LargeEvenOmega (LargeEvenQMinus 3 b c)).map ψ.toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived (qMinusForm K 3 b c) := by
    rw [← coe_qMinusForm (K := K) 3 b c]
    exact map_largeEvenOmega (qMinusForm K 3 b c)
  have hfin : Module.finrank K (LargeEvenMinusIdx 3 → K) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [LargeEvenMinusIdx]
  have hcard : Nat.card (A.map ψ.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective ψ.injective
  right
  exact normConcl_of_mapEquiv ψ (normConcl_of_normalizes_four hOm hSU hK
    (nondegenerate_qMinusForm 3 hirr) hK1 hfin (endData_mapEquiv ψ hΩ hE)
    (by rw [hcard]; simpa using hr) (normalizesTwoGroup_mapEquiv ψ hΩ hU))

end SmallOrth

end CFSG.StandardType

end
