module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveOrthMinus
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveOrthMinusLayer
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndMain

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.AUTSL

namespace IOneOrthEnd

open Module CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2 CFSG.StandardType.OrthRestOdd

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem ggEndNodeRootEltBig_orthDerived {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hV : 10 ≤ finrank K V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {r : ℕ}
    (hr : finrank K V / 2 - 1 = r) : GGEndNodeRootEltBig p r (orthDerived Q) := by
  intro A hA hcard h3 ⟨V₀, hV₀1, hV₀2, hAV₀⟩
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  set E := A.map (orthDerived Q).subtype with hEdef
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hE : IsoGroup (QuadraticMap.polarBilin Q) p E :=
    { sep := hQ.1
      alt := fun v => by rw [QuadraticMap.polarBilin_apply_apply]; exact polar_self_eq_zero Q v
      comm := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (TableB.IsElemAbelian.comm hA ha hb)
      pow := by
        rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow, hA.2 a ha, map_one]
      pres := by
        rintro _ ⟨a, ha, rfl⟩ u w
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
        exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
          (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup a.2) u w }
  have hcardE : Nat.card E = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  have hEQ : ∀ g ∈ E, ∀ v, Q (g v) = Q v := by
    rintro _ ⟨a, -, rfl⟩ v
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup a.2)) v
  obtain ⟨Y, hY0, hYinv, hYQ⟩ := OrthBstarOdd.exists_singular_of_two hQ hK1
    (S := V₀.map (orthDerived Q).subtype) (N := E) (hV₀2.map _)
    (by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
      exact hV₀1)
    (by
      rintro _ ⟨s, -, rfl⟩ v
      exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup s.2)) v)
    (by
      rintro _ ⟨s, -, rfl⟩
      exact (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp
        (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ s.2)).2)
    hEQ (fun g hg => hE.pow g hg)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨v, hv, rfl⟩
      exact ⟨a * v * a⁻¹, Subgroup.le_normalizer_iff.mp hAV₀ a ha v hv, by simp⟩)
  have hYp : ∀ y ∈ Y, ∀ y' ∈ Y, QuadraticMap.polar Q y y' = 0 := fun y hy y' hy' => by
    have h1 := hYQ (y + y') (Y.add_mem hy hy')
    rw [QuadraticMap.polar, h1, hYQ y hy, hYQ y' hy']
    simp
  obtain ⟨t', ⟨t, htA, rfl⟩, ht1, ht2, Y', hY'0, hY'Y, hY'inv, hY'fix⟩ :=
    exists_commSpace_two_fix hp hpK hK1 (by omega) hE hY0 hYinv
      (fun y hy y' hy' => by rw [QuadraticMap.polarBilin_apply_apply]; exact hYp y hy y' hy')
      (by rw [hcardE, hr]; exact hcard)
  have ht1' : t ≠ 1 := fun h => ht1 (by rw [h]; rfl)
  have htp : t ^ p = 1 := hA.2 t htA
  refine ⟨t, isEndNode_of_commSpace_two hQ (by omega) hp hp2 hK1 hA htA ht1' ht2,
    fun _ => Or.inl (seven_dvd_card_layer hK hQ hV hp hp2 hK1 htp ht2), ?_⟩
  exact exists_twoSubgroup_layer hQ hV hp hp2 hK1 hA htA ht2 hY'0
    (fun y hy => hYQ y (hY'Y hy)) (fun a ha y hy => hY'inv _ ⟨a, ha, rfl⟩ y hy) hY'fix

end IOneOrthEnd

section Certs


theorem ggEndNodeRootEltBig_orthMinus {K : Type} [Field K] [Finite K] {n m p : ℕ} {b c : K}
    (hK : Nat.card K = 2 ^ n) (hm : 4 ≤ m) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGEndNodeRootEltBig p m (OrthRest.RMinus K m b c) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0, pow_zero] at this
      omega
    · exact h0
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hn hK
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
      rw [Nat.dvd_add_right (dvd_pow_self 2 (by omega))]
      norm_num
    exact hodd hpn
  have hn4 : 4 ≤ m + 1 := by omega
  obtain ⟨hnd, -⟩ := regular_coordinateQuadMinus (m + 1) K b c hn4 hbc
  have hΓ : GGEndNodeRootEltBig p m
      (CFSG.RankThree.Classical2.orthDerived (Qm (m + 1) hn4 b c)) :=
    IOneOrthEnd.ggEndNodeRootEltBig_orthDerived hK hnd
      (by rw [Module.finrank_fin_fun]; omega) hp hp2
      (OrthRestOdd.eq_one_of_pow_eq_one_of_dvd hK hp hpn)
      (by rw [Module.finrank_fin_fun]; omega)
  exact ggEndNodeRootEltBig_of_mulEquiv
    ((RecipeFieldOmega.minusEquiv hn4 b c).trans
      (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv (Qm (m + 1) hn4 b c))).symm hΓ

theorem ggIOneOrthMinusOddRootInput_holds : GGIOneOrthMinusOddRootInput :=
  fun _ _ _ _ _ _ _ _ hK hm _ hp hpn hbc => ggEndNodeRootEltBig_orthMinus hK hm hp hpn hbc

theorem ggStdSubIOneProperInputOn_orthMinusOddField_holds (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGIOneMoreOrthMinusOddFieldLabel :=
  ggStdSubIOneProperInputOn_orthMinusOddField ha₀ ggIOneOrthMinusOddRootInput_holds

end Certs

end CFSG.StandardType
