module

public import CFSG.Permutation.FiveTransitive.Degree25FiveCodeLinear
public import Mathlib.RingTheory.PiTensorProduct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG

namespace FiveTransitive.Degree25

open FiveTransitive.Degree24

private def standardFiveCodeLinearEquiv :
    StandardFiveParameters ≃ₗ[ZMod 5] standardFiveCode where
  toFun v := ⟨standardFiveCodeVector v, by
    change ∑ i, standardFiveCodeVector v i = 0
    simp [standardFiveCodeVector, Fin.sum_univ_succ]⟩
  invFun w := ![w.1 0, w.1 1, w.1 2]
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv w := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · have hw := w.2
      change (∑ i, w.1 i) = 0 at hw
      simp [Fin.sum_univ_succ] at hw
      change -(w.1 0 + w.1 1 + w.1 2) = w.1 3
      linear_combination -hw
  map_add' u v := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [standardFiveCodeVector]
    all_goals ring
  map_smul' a v := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [standardFiveCodeVector, mul_add]

private theorem exists_standardFiveCode_linearEquiv_of_card_eq_one_hundred_twenty_five
    (W : Submodule (ZMod 5) FiveVector)
    (hWcard : Nat.card W = 125)
    (hnoWeightOne : ¬∃ w : W, fiveWeight w = 1) :
    ∃ e : StandardFiveParameters ≃ₗ[ZMod 5] W,
      (∀ v : StandardFiveParameters,
          fiveWeight (e v) =
            fiveWeight (standardFiveCodeVector v)) ∧
        ∀ v : StandardFiveParameters, ∀ i,
          (e v).1 i = 0 ↔
            standardFiveCodeVector v i = 0 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hWpow :=
    Module.natCard_eq_pow_finrank
      (K := ZMod 5) (V := W)
  rw [Nat.card_zmod, hWcard] at hWpow
  have hWfinrank :
      Module.finrank (ZMod 5) W = 3 := by
    have hle : Module.finrank (ZMod 5) W ≤ 4 := by
      calc
        Module.finrank (ZMod 5) W ≤
            Module.finrank (ZMod 5) FiveVector :=
          Submodule.finrank_le W
        _ = 4 := by
          rw [Module.finrank_fintype_fun_eq_card,
            Fintype.card_fin]
    interval_cases Module.finrank (ZMod 5) W
    all_goals norm_num at hWpow
    all_goals omega
  obtain ⟨Q, hQ⟩ :=
    Submodule.exists_isCompl W
  have hQfinrank :
      Module.finrank (ZMod 5) Q = 1 := by
    have hsum :=
      Submodule.finrank_add_eq_of_isCompl hQ
    rw [hWfinrank,
      Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hsum
    omega
  let eQ : ZMod 5 ≃ₗ[ZMod 5] Q :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one
      hQfinrank).some
  let proj : FiveVector →ₗ[ZMod 5] Q :=
    Q.projectionOnto W hQ.symm
  let f : FiveVector →ₗ[ZMod 5] ZMod 5 :=
    eQ.symm.toLinearMap.comp proj
  have hfker : LinearMap.ker f = W := by
    ext v
    simp [f, proj]
  let c : FiveVector :=
    fun i => f (Pi.single i 1)
  have hf_eq_dot (v : FiveVector) :
      f v = fiveDot c v := by
    have hv :
        v = ∑ i, (v i) •
          Pi.single i (1 : ZMod 5) := by
      calc
        v = ∑ i, Pi.single i (v i) :=
          (Finset.univ_sum_single v).symm
        _ = ∑ i, (v i) •
            Pi.single i (1 : ZMod 5) := by
          apply Finset.sum_congr rfl
          intro i _
          ext j
          by_cases hij : i = j
          · subst j
            simp
          · simp [hij]
    calc
      f v = f (∑ i, (v i) •
          Pi.single i (1 : ZMod 5)) := by rw [← hv]
      _ = ∑ i, (v i) •
          f (Pi.single i (1 : ZMod 5)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
      _ = fiveDot c v := by
        simp only [fiveDot, c, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
  have hmem (v : FiveVector) :
      fiveDot c v = 0 ↔ v ∈ W := by
    rw [← hf_eq_dot]
    change v ∈ LinearMap.ker f ↔ v ∈ W
    rw [hfker]
  have hc : ∀ i, c i ≠ 0 := by
    rcases
        five_hyperplane_weight_one_or_twenty_four_weight_two c with
      hone | hregular
    · apply False.elim
      apply hnoWeightOne
      obtain ⟨v, hv, hweight⟩ := hone
      exact ⟨⟨v, (hmem v).mp hv⟩, hweight⟩
    · exact hregular.2
  let scale : FiveVector ≃ₗ[ZMod 5] FiveVector := {
    toFun v i := c i * v i
    invFun v i := (c i)⁻¹ * v i
    left_inv v := by
      funext i
      simp [hc i]
    right_inv v := by
      funext i
      simp [hc i]
    map_add' u v := by
      funext i
      simp [mul_add]
    map_smul' a v := by
      funext i
      change c i * (a * v i) = a * (c i * v i)
      ring }
  have hscaleWeight (v : FiveVector) :
      fiveWeight (scale v) = fiveWeight v := by
    unfold fiveWeight
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and]
    change c i * v i ≠ 0 ↔ v i ≠ 0
    constructor
    · intro hmul hv
      rw [hv, mul_zero] at hmul
      exact hmul rfl
    · exact mul_ne_zero (hc i)
  have hscaleSymmWeight (v : FiveVector) :
      fiveWeight (scale.symm v) = fiveWeight v := by
    rw [← hscaleWeight (scale.symm v),
      scale.apply_symm_apply]
  let eWS : W ≃ₗ[ZMod 5] standardFiveCode := {
    toFun w := ⟨scale w.1, by
      change ∑ i, c i * w.1 i = 0
      exact (hmem w.1).mpr w.2⟩
    invFun z := ⟨scale.symm z.1, by
      apply (hmem (scale.symm z.1)).mp
      change ∑ i, c i * ((c i)⁻¹ * z.1 i) = 0
      calc
        (∑ i, c i * ((c i)⁻¹ * z.1 i)) =
            ∑ i, z.1 i := by
          apply Finset.sum_congr rfl
          intro i _
          simp [hc i]
        _ = 0 := z.2⟩
    left_inv w := by
      apply Subtype.ext
      exact scale.symm_apply_apply w.1
    right_inv z := by
      apply Subtype.ext
      exact scale.apply_symm_apply z.1
    map_add' u v := by
      apply Subtype.ext
      exact map_add scale u.1 v.1
    map_smul' a v := by
      apply Subtype.ext
      exact map_smul scale a v.1 }
  let e :
      StandardFiveParameters ≃ₗ[ZMod 5] W :=
    standardFiveCodeLinearEquiv.trans eWS.symm
  refine ⟨e, ?_, ?_⟩
  · intro v
    change
      fiveWeight
          (scale.symm
            (standardFiveCodeVector v)) =
        fiveWeight (standardFiveCodeVector v)
    simpa using
      hscaleSymmWeight (standardFiveCodeVector v)
  · intro v i
    change
      (c i)⁻¹ * standardFiveCodeVector v i = 0 ↔
        standardFiveCodeVector v i = 0
    simp [hc i]

private theorem standardFiveCode_separates_coordinates
    (i j : Fin 4) (hij : i ≠ j) :
    ∃ v : StandardFiveParameters,
      standardFiveCodeVector v i = 0 ∧
        standardFiveCodeVector v j ≠ 0 := by
  decide +revert

private theorem standardFiveCode_exists_weight_four :
    ∃ v : StandardFiveParameters,
      fiveWeight (standardFiveCodeVector v) = 4 := by
  exact ⟨![1, 1, 1], by decide⟩

theorem five_submodule_separates_coordinates
    (W : Submodule (ZMod 5) FiveVector)
    (hWcard : Nat.card W = 125)
    (hnoWeightOne : ¬∃ w : W, fiveWeight w = 1)
    (i j : Fin 4) (hij : i ≠ j) :
    ∃ w : W, w.1 i = 0 ∧ w.1 j ≠ 0 := by
  obtain ⟨e, _, hzero⟩ :=
    exists_standardFiveCode_linearEquiv_of_card_eq_one_hundred_twenty_five
      W hWcard hnoWeightOne
  obtain ⟨v, hvi, hvj⟩ :=
    standardFiveCode_separates_coordinates i j hij
  exact ⟨e v, (hzero v i).mpr hvi,
    fun h => hvj ((hzero v j).mp h)⟩

theorem five_submodule_exists_weight_four
    (W : Submodule (ZMod 5) FiveVector)
    (hWcard : Nat.card W = 125)
    (hnoWeightOne : ¬∃ w : W, fiveWeight w = 1) :
    ∃ w : W, fiveWeight w = 4 := by
  obtain ⟨e, hweight, _⟩ :=
    exists_standardFiveCode_linearEquiv_of_card_eq_one_hundred_twenty_five
      W hWcard hnoWeightOne
  obtain ⟨v, hv⟩ :=
    standardFiveCode_exists_weight_four
  exact ⟨e v, (hweight v).trans hv⟩

theorem five_submodule_weight_preserving_order_ne_five
    (W : Submodule (ZMod 5) FiveVector)
    (hWcard : Nat.card W = 125)
    (hnoWeightOne : ¬∃ w : W, fiveWeight w = 1)
    (a : W ≃ₗ[ZMod 5] W)
    (hweight : ∀ w : W,
      fiveWeight (a w) = fiveWeight w) :
    orderOf a ≠ 5 := by
  classical
  obtain ⟨e, he, _⟩ :=
    exists_standardFiveCode_linearEquiv_of_card_eq_one_hundred_twenty_five
      W hWcard hnoWeightOne
  let g :
      StandardFiveParameters ≃ₗ[ZMod 5]
        StandardFiveParameters :=
    e.trans (a.trans e.symm)
  have hgweight (v : StandardFiveParameters) :
      fiveWeight (standardFiveCodeVector (g v)) =
        fiveWeight (standardFiveCodeVector v) := by
    calc
      fiveWeight (standardFiveCodeVector (g v)) =
          fiveWeight (e (g v)) := (he (g v)).symm
      _ = fiveWeight (a (e v)) := by
        rw [show e (g v) = a (e v) by
          simp only [g, LinearEquiv.trans_apply,
            e.apply_symm_apply]]
      _ = fiveWeight (e v) := hweight (e v)
      _ = fiveWeight (standardFiveCodeVector v) := he v
  intro haOrder
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have haPow : a ^ 5 = 1 := by
    simpa only [haOrder] using pow_orderOf_eq_one a
  have hgPow : g ^ 5 = 1 := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.coe_one]
    simp only [id_eq]
    have happ : (a ^ 5) (e v) = e v := by
      rw [haPow]
      rfl
    simpa only [pow_succ, pow_zero, one_mul,
      LinearEquiv.mul_apply, g,
      LinearEquiv.trans_apply, e.apply_symm_apply,
      e.symm_apply_apply, one_apply] using
      congrArg e.symm happ
  have hgNe : g ≠ 1 := by
    intro hgOne
    have haOne : a = 1 := by
      apply LinearEquiv.ext
      intro w
      rw [LinearEquiv.coe_one]
      simp only [id_eq]
      let v : StandardFiveParameters := e.symm w
      have happ :=
        congrArg
          (fun q :
            StandardFiveParameters ≃ₗ[ZMod 5]
              StandardFiveParameters => q v)
          hgOne
      change e.symm (a (e v)) = v at happ
      have happ' := congrArg e happ
      dsimp only [v] at happ'
      simpa only [e.apply_symm_apply,
        one_apply] using happ'
    rw [haOne, orderOf_one] at haOrder
    norm_num at haOrder
  have hgOrder : orderOf g = 5 :=
    orderOf_eq_prime hgPow hgNe
  exact
    standardFiveCode_weight_preserving_order_ne_five
      g hgweight hgOrder

end FiveTransitive.Degree25

end CFSG
