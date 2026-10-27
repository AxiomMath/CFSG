module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel

public section

namespace CFSG.StandardType.B36

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.RankThree.Classical2 (orthDerived)

private theorem ltqOm8_three_dvd (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  have h : 2 ^ n % 3 = 2 ^ (n % 2) % 3 := by
    conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hr | hr
  · left
    rw [hr] at h
    norm_num at h
    have hmod : 1 ≡ 2 ^ n [MOD 3] := by
      show 1 % 3 = 2 ^ n % 3
      rw [h]
    exact (Nat.modEq_iff_dvd' (a := 1) (b := 2 ^ n) (n := 3) Nat.one_le_two_pow).1 hmod
  · right
    rw [hr] at h
    norm_num at h
    have hmod : 2 ^ n ≡ 2 [MOD 3] := by
      show 2 ^ n % 3 = 2 % 3
      rw [h]
    exact Nat.modEq_zero_iff_dvd.mp
      ((hmod.add_right 1).trans (by norm_num : (3 : ℕ) ≡ 0 [MOD 3]))

private theorem ltqOm8_exists_order3_orthDerived (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ g : ↥(orthDerived (TableBOrth.qPlusForm K 4)), g ^ 3 = 1 ∧ g ≠ 1 := by
  obtain ⟨g, hg3, -⟩ :=
    (CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.threeFixedModel_statedOmegaPlus
      (K := K) (n := 4) (by norm_num)) (0 : Fin 4 ⊕ Fin 4 → K)
  have hgpow : g ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one g
  have hgne : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg3
    norm_num at hg3
  let e : LargeEvenOmega (LargeEvenQPlus K 4) ≃*
      ↥(orthDerived (TableBOrth.qPlusForm K 4)) :=
    (MulEquiv.subgroupCongr
      (congrArg LargeEvenOmega (TableBOrth.coe_qPlusForm (K := K) 4).symm)).trans
      (TableBOrth.omegaEquivOrthDerived (TableBOrth.qPlusForm K 4))
  refine ⟨e g, ?_, ?_⟩
  · rw [← map_pow, hgpow, map_one]
  · intro h
    exact hgne (e.injective (by rw [h, map_one]))

private theorem ltqOm8_exists_order3_R (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ g : OrthRest.RPlus K 4, g ^ 3 = 1 ∧ g ≠ 1 := by
  obtain ⟨gO, hgO3, hgO1⟩ := ltqOm8_exists_order3_orthDerived K
  let φ := OrthTorus.rPlusEquiv K (show 1 ≤ 4 by norm_num)
  refine ⟨φ.symm gO, ?_, ?_⟩
  · rw [← map_pow, hgO3, map_one]
  · intro h
    exact hgO1 (φ.symm.injective (by rw [h, map_one]))

private theorem ltqOm8_selfCent_RPlus {n : ℕ} (K : Type) [Field K] [Finite K] [CharP K 2]
    (hKcard : Nat.card K = 2 ^ n) :
    ∀ E : Subgroup (OrthRest.RPlus K 4), IsElemAbelian 3 E →
      (∀ g : OrthRest.RPlus K 4, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) →
      Nat.card E = 3 ^ 4 := by
  intro E hE hEself
  let φ := OrthTorus.rPlusEquiv K (show 1 ≤ 4 by norm_num)
  let f : OrthRest.RPlus K 4 →* (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
    (orthDerived (TableBOrth.qPlusForm K 4)).subtype.comp φ.toMonoidHom
  let A : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := E.map f
  have hfinj : Function.Injective f :=
    (orthDerived (TableBOrth.qPlusForm K 4)).subtype_injective.comp φ.injective
  have hAΩ : A ≤ orthDerived (TableBOrth.qPlusForm K 4) := by
    rintro a ⟨e, he, rfl⟩
    exact (φ e).2
  have hApow : ∀ a ∈ A, a ^ 3 = 1 := by
    rintro a ⟨e, he, rfl⟩
    rw [← map_pow f, hE.2 e he, map_one]
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    haveI : IsMulCommutative E := hE.1
    rintro a ⟨e, he, rfl⟩ b ⟨e', he', rfl⟩
    rw [← map_mul f, ← map_mul f]
    exact congrArg f (Subgroup.mul_comm_of_mem_isMulCommutative E he he')
  have hmax : ∀ g ∈ orthDerived (TableBOrth.qPlusForm K 4), g ^ 3 = 1 →
      (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hg3 hgc
    let g' : OrthRest.RPlus K 4 := φ.symm ⟨g, hg⟩
    have hφg' : φ g' = ⟨g, hg⟩ := MulEquiv.apply_symm_apply φ ⟨g, hg⟩
    have hg'mem : g' ∈ E := by
      refine hEself g' ?_ ?_
      · intro e he
        apply φ.injective
        rw [map_mul, map_mul, hφg']
        exact Subtype.ext (hgc ((orthDerived (TableBOrth.qPlusForm K 4)).subtype (φ e))
          ⟨e, he, rfl⟩)
      · apply φ.injective
        rw [map_pow, hφg', map_one]
        exact Subtype.ext hg3
    refine ⟨g', hg'mem, ?_⟩
    show (orthDerived (TableBOrth.qPlusForm K 4)).subtype (φ g') = g
    rw [hφg']
    rfl
  have hEne : E ≠ ⊥ := by
    intro hbot
    obtain ⟨gR, hgR3, hgR1⟩ := ltqOm8_exists_order3_R K
    have hmem : gR ∈ E := hEself gR (fun e he => by
      rw [hbot, Subgroup.mem_bot] at he
      rw [he, mul_one, one_mul]) hgR3
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hgR1 hmem
  have hne : ∃ b ∈ A, b ≠ 1 := by
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
    refine ⟨f e, ⟨e, he, rfl⟩, ?_⟩
    intro hfe1
    apply he1
    apply Subtype.ext
    have hφ : φ e = φ 1 := by
      apply Subtype.ext
      change f e = f 1
      rw [hfe1, map_one]
    exact φ.injective hφ
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpq : 3 ∣ Nat.card K - 1 ∨ 3 ∣ Nat.card K + 1 := by
    rw [hKcard]
    exact ltqOm8_three_dvd n
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qPlusForm K 4)).Nondegenerate :=
    TableBOrth.nondegenerate_qPlusForm 4
  have hT : ∃ T : Submodule K (Fin 4 ⊕ Fin 4 → K), Module.finrank K T = 3 ∧
      ∀ v ∈ T, TableBOrth.qPlusForm K 4 v = 0 := by
    simpa using OrthTorus.exists_totallySingular_qPlusForm (K := K) (n := 3) le_rfl
  obtain ⟨r, τ, hτinj, hτrange, -, -, -, hbranch⟩ :=
    OrthTorus.exists_torus (p := 3) (K := K) (V := Fin 4 ⊕ Fin 4 → K)
      (Q := TableBOrth.qPlusForm K 4) (A := A) (by norm_num) hpq hQ hT hAΩ hApow hAcomm
      hmax hne
  have hchar : OrdPNsOm.charSum (TableBOrth.qPlusForm K 4) ⊤ ≡ 1 [ZMOD 3] := by
    rw [OrthTorus.charSum_qPlusForm, hKcard]
    push_cast
    rw [← pow_mul, show n * 4 = 4 * n by ring, pow_mul]
    have h4 : (2 : ℤ) ^ 4 ≡ 1 [ZMOD 3] := by norm_num
    simpa using h4.pow n
  have hr : r = 4 := by
    rcases hbranch with ⟨-, hdim⟩ | ⟨hneg, -⟩
    · have hV8 : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
        simp [Module.finrank_fintype_fun_eq_card]
      omega
    · exact absurd (hchar.symm.trans hneg)
        (OrthTorus.one_not_modEq_neg_one (by norm_num) (by norm_num))
  have hcardA : Nat.card A = Nat.card (Fin r → Multiplicative (ZMod 3)) := by
    rw [← hτrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv).symm
  have hcardE : Nat.card E = Nat.card A :=
    (Subgroup.card_map_of_injective (f := f) hfinj).symm
  have hcardFun : Nat.card (Fin 4 → Multiplicative (ZMod 3)) = 3 ^ 4 := by
    rw [Nat.card_fun, Nat.card_fin]
    congr 1
    rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod 3)), Nat.card_zmod]
  calc Nat.card E = Nat.card A := hcardE
    _ = Nat.card (Fin r → Multiplicative (ZMod 3)) := hcardA
    _ = 3 ^ 4 := by rw [hr]; exact hcardFun

theorem d4_selfCent_elemAbelian_three {n : ℕ} (hn : 1 ≤ n) :
    LargeEvenLabelAll ⟨.D, 4, n⟩ fun R _ _ _ =>
      ∀ E : Subgroup R, IsElemAbelian 3 E →
        (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) → Nat.card E = 3 ^ 4 := by
  unfold LargeEvenLabelAll
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  by_cases h3 : (4 : ℕ) = 3
  · exact absurd h3 (by norm_num)
  · simp only [if_neg h3] at hQ ⊢
    dsimp only [LargeEvenRecipeOmegaPlus] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := by
      have hmod : Fintype.card K % 2 = 0 := by
        rw [← Nat.card_eq_fintype_card, hK]
        exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
      exact ringChar.of_eq (FiniteField.even_card_iff_char_two.2 hmod)
    intro E hE hEself
    exact ltqOm8_selfCent_RPlus K hK E hE hEself

end CFSG.StandardType.B36

end
