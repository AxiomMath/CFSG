module

public import CFSG.LocalAnalysis.SteinbergBTEvenSymplecticFixedNoSL2
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleExclusions
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleGraph

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBT

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open FourGroupEvenCanonical UnitaryHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification CFSG.ComponentClassification.OutcomeLocal
open CFSG.ClassicalGroups.UnitaryFlag

theorem finite_mulAut {P : Type*} [Group P] [Finite P] : Finite (MulAut P) :=
  Finite.of_injective (fun χ : MulAut P => (χ : P → P)) DFunLike.coe_injective

variable {A : Type} [Group A] {W : Subgroup A} {a : A} {L : Subgroup A}
  {n e : ℕ} {K : Type} [Field K]

theorem linear_fixed_field_orderOf_four [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hn : 3 ≤ n) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* projectiveSL n K) {ρ : A →* MulAut (projectiveSL n K)}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    {Aₘ : GL (Fin n) K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hρa : ρ a = conjAut n K Aₘ * fieldAut n K σ) : ∃ x : L, orderOf x = 4 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have hα2 : (conjAut n K Aₘ * fieldAut n K σ) ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨-, -, H, hH⟩ :=
    LinearFlag.even_linear_field_involution_descent he hK hn Aₘ σ hσ hα2
  have hρa' : ρ a = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := hρa.trans hH
  obtain ⟨-, ⟨e₁, -⟩, hNinn, -, hNC, hNnormal, hCN⟩ :=
    linear_quadratic_field_full_centralizer_rigidity σ (n := n) hn
  set χ := conjAut n K H with hχ
  set β := fieldAut n K σ with hβ
  set N := (subfieldConj n σ).range with hNdef
  have hCAimg : (centralizer {a}).map ρ = ρ.range ⊓ centralizer {ρ a} :=
    SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hW : W.map ρ = OuterAutomorphisms.inner (projectiveSL n K) := map_eq_range_conj φ hρW
  have hWle : OuterAutomorphisms.inner (projectiveSL n K) ≤ ρ.range := hW ▸ map_le_range ρ W
  have hCWimg : (W ⊓ centralizer {a}).map ρ =
      OuterAutomorphisms.inner (projectiveSL n K) ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL n K) ⊓ centralizer {ρ a}) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rwa [hCWimg] at this
  have hY : (OuterAutomorphisms.inner (projectiveSL n K) ⊓ centralizer {ρ a}).map
      (MulAut.conj χ⁻¹).toMonoidHom =
        OuterAutomorphisms.inner (projectiveSL n K) ⊓ centralizer {β} := by
    rw [map_conj_inner_inf_centralizer, hρa']
    congr 3
    group
  set L₀ := (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom with hL₀def
  have hL₀ : CFSG.Assembly.IsComponentOf L₀
      (OuterAutomorphisms.inner (projectiveSL n K) ⊓ centralizer {β}) := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [hY] at this
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut
  have hL₀N : CFSG.Assembly.IsComponentOf L₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hL₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β i j).eq
  have : IsSimpleGroup (projectiveSL n (fixedField K σ)) := isSimpleGroup_projectiveSL hn
  have hNsimple : IsSimpleGroup N := e₁.symm.isSimpleGroup
  have hL₀eq : L₀ = N := eq_of_isComponentOf_simple hNsimple hL₀N
  have hid : (MulAut.conj χ).toMonoidHom.comp (MulAut.conj χ⁻¹).toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
  have hLimg : L.map ρ = N.map (MulAut.conj χ).toMonoidHom := by
    rw [← hL₀eq, hL₀def, Subgroup.map_map, hid, Subgroup.map_id]
  let eL : L ≃* projectiveSL n (fixedField K σ) :=
    ((L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLimg).trans
      ((N.equivMapOfInjective _ (MulAut.conj χ).injective).symm))).trans e₁.symm
  have h2 : (2 : fixedField K σ) = 0 := Subtype.ext (by
    change (2 : K) = 0
    exact CharTwo.two_eq_zero)
  obtain ⟨y, -, hy⟩ := SteinbergCD.exists_orderOf_eq_four_projectiveSL h2 hn
  exact ⟨eL.symm (LinearFlag.proj n (fixedField K σ) y), by rw [MulEquiv.orderOf_eq, hy]⟩

theorem linear_fixed_graph_field_orderOf_four [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hn : 4 ≤ n) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* projectiveSL n K) {ρ : A →* MulAut (projectiveSL n K)}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    {Aₘ : GL (Fin n) K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hρa : ρ a = conjAut n K Aₘ * fieldAut n K σ * dualAut n K) : ∃ x : L, orderOf x = 4 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hα2 : (conjAut n K Aₘ * fieldAut n K σ * dualAut n K) ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨heven, hσx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two he hK (by omega) Aₘ σ hσ
      hα2
  have hg : 1 ≤ e / 2 := by obtain ⟨m, hm⟩ := heven; omega
  have hKe : Nat.card K = 2 ^ (2 * (e / 2)) := by
    rw [hK]
    congr 1
    obtain ⟨m, hm⟩ := heven
    omega
  have hud : UnitaryFieldData 2 (e / 2) K := ⟨Nat.prime_two, hg, hKe⟩
  have hσbar : ∀ x, σ x = hud.bar x := fun x => by rw [hσx, hud.bar_apply]
  obtain ⟨-, ⟨ι, -⟩, hNinn, -, hNC, hNnormal, hCN⟩ :=
    linear_graph_field_full_centralizer_rigidity hud (show 3 ≤ n by omega) σ hσbar
  set χ := conjAut n K H with hχ
  set β := fieldAut n K σ * dualAut n K with hβ
  set N := (unitarySU 2 (e / 2) K n).map (conjAut n K) with hNdef
  have hρa' : ρ a = χ * β * χ⁻¹ := by rw [hρa, hH]
  have hW : W.map ρ = OuterAutomorphisms.inner (projectiveSL n K) := map_eq_range_conj φ hρW
  have hWle : OuterAutomorphisms.inner (projectiveSL n K) ≤ ρ.range := hW ▸ map_le_range ρ W
  have hCAimg := SymmetricLocal.map_centralizer_singleton_of_injective ρ hinj a
  have hCWimg : (W ⊓ centralizer {a}).map ρ =
      OuterAutomorphisms.inner (projectiveSL n K) ⊓ centralizer {ρ a} := by
    rw [map_inf_eq _ _ _ hinj, hW, hCAimg, ← inf_assoc, inf_eq_left.mpr hWle]
  have hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL n K) ⊓ centralizer {ρ a}) := by
    have := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
    rwa [hCWimg] at this
  have hY : (OuterAutomorphisms.inner (projectiveSL n K) ⊓ centralizer {ρ a}).map
      (MulAut.conj χ⁻¹).toMonoidHom =
        OuterAutomorphisms.inner (projectiveSL n K) ⊓ centralizer {β} := by
    rw [map_conj_inner_inf_centralizer, hρa']
    congr 3
    group
  set L₀ := (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom with hL₀def
  have hL₀ : CFSG.Assembly.IsComponentOf L₀
      (OuterAutomorphisms.inner (projectiveSL n K) ⊓ centralizer {β}) := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [hY] at this
  have : Finite (MulAut (projectiveSL n K)) := finite_mulAut
  have hL₀N : CFSG.Assembly.IsComponentOf L₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hL₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β i j).eq
  have hK2 : Nat.card K = (2 ^ (e / 2)) ^ 2 := by rw [hKe, ← pow_mul, mul_comm]
  have eU : unitaryPSU hud n ≃* StatedProj (StatedSU n (2 ^ (e / 2)) K) :=
    unitaryPSUEquiv hud (by omega)
  have hnq : (n, 2 ^ (e / 2)) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have : IsSimpleGroup (StatedProj (StatedSU n (2 ^ (e / 2)) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 (e / 2) hK2 n
      (by omega) hnq
  have : IsSimpleGroup (unitaryPSU hud n) := eU.isSimpleGroup
  have hNs : IsSimpleGroup N := ι.symm.isSimpleGroup
  have hL₀eq : L₀ = N := eq_of_isComponentOf_simple hNs hL₀N
  have hid : (MulAut.conj χ).toMonoidHom.comp (MulAut.conj χ⁻¹).toMonoidHom =
      MonoidHom.id _ :=
    MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
  have hLimg : L.map ρ = N.map (MulAut.conj χ).toMonoidHom := by
    rw [← hL₀eq, hL₀def, Subgroup.map_map, hid, Subgroup.map_id]
  let eL : L ≃* unitaryPSU hud n :=
    ((L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLimg).trans
      ((N.equivMapOfInjective _ (MulAut.conj χ).injective).symm))).trans ι.symm
  obtain ⟨y, -, hy⟩ := SteinbergCD.exists_orderOf_eq_four_unitaryPSU hud (by omega : 3 ≤ n)
  exact ⟨eL.symm (unitaryProj hud n y), by rw [MulEquiv.orderOf_eq, hy]⟩

theorem linear_fixed_pure_graph_orderOf_four [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hn : 4 ≤ n) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* projectiveSL n K) {ρ : A →* MulAut (projectiveSL n K)}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    {Aₘ : GL (Fin n) K} (hρa : ρ a = conjAut n K Aₘ * dualAut n K) : ∃ x : L, orderOf x = 4 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  obtain ⟨H, C, hcase, -, -, -, -, hinjO, hL₀⟩ :=
    linear_socle_pure_graph_setup ha hLCW (by omega) he hK φ hinj hρW hρa
  set χ := conjAut n K H with hχ
  let eY : L ≃* (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom :=
    (L.equivMapOfInjective ρ hinj).trans
      ((L.map ρ).equivMapOfInjective _ (MulAut.conj χ⁻¹).injective)
  have : Finite (GL (Fin n) K) := Finite.of_injective Units.val Units.val_injective
  have hA6 : ∀ X : Subgroup (MulAut (projectiveSL n K)),
      (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom = X → Nonempty (X ≃* alternatingGroup (Fin 6)) →
        ∃ x : L, orderOf x = 4 := by
    rintro X hX ⟨eA⟩
    obtain ⟨y, hy⟩ := exists_orderOf_eq_four_alternating_six
    exact ⟨(eY.trans ((MulEquiv.subgroupCongr hX).trans eA)).symm y,
      by rw [MulEquiv.orderOf_eq, hy]⟩
  have hSp : ∀ {r : ℕ}, 2 ≤ r →
      Nonempty ((L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom ≃* StatedSp r K) →
        ∃ x : L, orderOf x = 4 := by
    rintro r hr ⟨eX⟩
    obtain ⟨y, hy, -⟩ := SteinbergCD.exists_orderOf_eq_four_statedSp (k := K)
      CharTwo.two_eq_zero hr
    exact ⟨(eY.trans eX).symm y, by rw [MulEquiv.orderOf_eq, hy]⟩
  rcases hcase with ⟨hC1, ⟨r, hr⟩⟩ | ⟨r, hr, hCJ⟩
  ·
    have hC1' : C = 1 := Units.ext hC1
    subst hC1'
    have hdim := finrank_dotForm_ker (k := K) hr
    have hBalt := dotForm_restrict_isAlt (k := K) (n := n)
    have hBnd := dotForm_restrict_nondegenerate (k := K) hr
    rcases symplectic_component_dichotomy hinjO hL₀ hK (by omega : 1 ≤ r) (by omega) _ hBalt
        hBnd hdim (oneRestrictEquiv hr) with
      ⟨-, -, -, -, hX⟩ | ⟨-, -, hXc, -, -, hX6⟩
    · exact hSp (by omega) hX
    · exact hA6 _ hXc hX6
  ·
    have hBalt : (Matrix.toBilin' (C : Matrix (Fin n) (Fin n) K)).IsAlt := fun x => by
      rw [Matrix.toBilin'_apply', hCJ]
      exact dotProduct_mulVec_self_eq_zero blockSwapJ_transpose
        (fun i => blockSwapJ_apply_self (by omega) i) x
    have hBnd := CatalogueBLinearHigherB.matrixForm_nondegenerate C
    have hdim : Module.finrank K (Fin n → K) = 2 * r := by
      rw [Module.finrank_fin_fun]
      exact hr
    rcases symplectic_component_dichotomy hinjO hL₀ hK (by omega : 1 ≤ r) (by omega) _ hBalt
        hBnd hdim (matrixIsometryGroupEquiv C) with
      ⟨-, -, -, -, hX⟩ | ⟨-, -, hXc, -, -, hX6⟩
    · exact hSp (by omega) hX
    · exact hA6 _ hXc hX6

theorem linear_fixed_false [Finite A] (ha : orderOf a = 2)
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hn : 4 ≤ n) (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* projectiveSL n K) {ρ : A →* MulAut (projectiveSL n K)}
    (hinj : Function.Injective ρ) (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    (hZ : center (projectiveSL n K) = ⊥) (h4 : ∀ x : L, orderOf x ≠ 4) : False := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, hform⟩ := LinearFlag.automorphism_generation (K := K) (by omega : 3 ≤ n)
  obtain ⟨Aₘ, σ, ε, hε, hρa⟩ := hform (ρ a)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hρa
      exact linear_socle_inner_false ha hLCW (by omega) he hK φ hinj hρW hZ hρa
    · obtain ⟨x, hx⟩ :=
        linear_fixed_field_orderOf_four ha hLCW (by omega) he hK φ hinj hρW hσ hρa
      exact h4 x hx
  · rw [pow_one] at hρa
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hρa
      obtain ⟨x, hx⟩ := linear_fixed_pure_graph_orderOf_four ha hLCW hn he hK φ hinj hρW hρa
      exact h4 x hx
    · obtain ⟨x, hx⟩ :=
        linear_fixed_graph_field_orderOf_four ha hLCW hn he hK φ hinj hρW hσ hρa
      exact h4 x hx

end CFSG.LocalAnalysis.SteinbergBT
