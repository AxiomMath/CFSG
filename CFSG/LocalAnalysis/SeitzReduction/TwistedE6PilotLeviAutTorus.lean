module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectW
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SeitzReduction.E6Pilot (IsAutConj IsAutConjIn)

section SL2

variable {k : Type*} [Field k]

theorem exists_conj_eq_HSL_of_apply_one_zero [Finite k] [CharP k 2]
    {A : SL2 k} (hA : A ^ (Nat.card k - 1) = 1) (hA2 : A ^ 2 ≠ 1)
    (hc : (A : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) :
    ∃ (P : SL2 k) (l : kˣ), P⁻¹ * A * P = HSL l := by
  classical
  have h2k : (2 : k) = 0 := CharTwo.two_eq_zero
  have hι := (algebraMap k (FiniteField.Extension k 2 2)).injective
  obtain ⟨x, hx⟩ := F4Pilot.exists_sq_sub_mul_add_one_eq_zero
    (Matrix.trace (A : Matrix (Fin 2) (Fin 2) k))
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  set xu : (FiniteField.Extension k 2 2)ˣ := Units.mk0 x hx0 with hxu
  have hxinv : ((xu⁻¹ : (FiniteField.Extension k 2 2)ˣ) : FiniteField.Extension k 2 2) = x⁻¹ := by
    rw [hxu, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hxx : (xu : FiniteField.Extension k 2 2) ≠ ((xu⁻¹ : (FiniteField.Extension k 2 2)ˣ) :
      FiniteField.Extension k 2 2) := by
    intro h
    rw [hxinv, hxu, Units.val_mk0] at h
    have h1 : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hx0
    have hx1 : x = 1 := by
      have h2E : (2 : FiniteField.Extension k 2 2) = 0 := CharTwo.two_eq_zero
      have hsq : (x - 1) * (x - 1) = 0 := by linear_combination h1 - (x - 1) * h2E
      exact sub_eq_zero.1 (mul_self_eq_zero.1 hsq)
    have ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) k) = 0 := by
      apply hι
      have h2E : (2 : FiniteField.Extension k 2 2) = 0 := CharTwo.two_eq_zero
      rw [hx1] at hx
      rw [map_zero]
      linear_combination -hx + h2E
    have hA2' : A ^ 2 = 1 := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [F4Pilot.sq_eq_trace_smul_sub_one, ht, zero_smul, zero_sub, Matrix.neg_apply,
        CharTwo.neg_eq, Matrix.SpecialLinearGroup.coe_one]
    exact hA2 hA2'
  set AE := Matrix.SpecialLinearGroup.map (algebraMap k (FiniteField.Extension k 2 2)) A with hAE
  have hcE : (AE : Matrix (Fin 2) (Fin 2) (FiniteField.Extension k 2 2)) 1 0 ≠ 0 := by
    rw [hAE, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (map_ne_zero_iff _ hι).2 hc
  have htE : Matrix.trace (AE : Matrix (Fin 2) (Fin 2) (FiniteField.Extension k 2 2)) =
      algebraMap k _ (Matrix.trace (A : Matrix (Fin 2) (Fin 2) k)) := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]
    rfl
  have hlE : (xu : FiniteField.Extension k 2 2) ^ 2 -
      Matrix.trace (AE : Matrix (Fin 2) (Fin 2) (FiniteField.Extension k 2 2)) * xu + 1 = 0 := by
    rw [htE, hxu, Units.val_mk0]
    exact hx
  obtain ⟨P, hP⟩ := F4Pilot.exists_inv_mul_mul_eq_HSL AE hcE xu hlE hxx
  have hconj : ∀ n : ℕ, (P⁻¹ * AE * P) ^ n = P⁻¹ * AE ^ n * P := fun n => by
    have h := map_pow (MulAut.conj P⁻¹) AE n
    simpa [MulAut.conj_apply] using h.symm
  have hpow : HSL xu ^ (Nat.card k - 1) = 1 := by
    rw [← hP, hconj, hAE, ← map_pow, hA, map_one, mul_one, inv_mul_cancel]
  rw [F4Pilot.HSL_pow] at hpow
  have hxq : x ^ (Nat.card k - 1) = 1 := by
    have h00 := congrArg (fun g : SL2 (FiniteField.Extension k 2 2) =>
      (g : Matrix (Fin 2) (Fin 2) (FiniteField.Extension k 2 2)) 0 0) hpow
    simp only [coe_HSL, Matrix.SpecialLinearGroup.coe_one] at h00
    simpa [hxu] using h00
  have hfrob : FiniteField.Extension.frob k 2 2 x = x := by
    rw [FiniteField.Extension.frob_apply]
    have hq1 : Nat.card k = Nat.card k - 1 + 1 := by
      have := Finite.one_lt_card (α := k)
      omega
    rw [hq1, pow_succ, hxq, one_mul]
  obtain ⟨l₀, hl₀⟩ := (F4Pilot.frob_eq_self_iff x).1 hfrob
  have hl₀0 : l₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hl₀
    exact hx0 hl₀.symm
  refine F4Pilot.exists_inv_mul_mul_eq_HSL A hc (Units.mk0 l₀ hl₀0) ?_ ?_ |>.imp
    fun P hP => ⟨Units.mk0 l₀ hl₀0, hP⟩
  · apply hι
    rw [map_zero, map_add, map_sub, map_mul, map_pow, Units.val_mk0, hl₀, map_one]
    exact hx
  · intro h
    apply hxx
    rw [hxinv, hxu, Units.val_mk0, ← hl₀]
    have h' : l₀ = l₀⁻¹ := by
      rw [Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0] at h
      exact h
    rw [← map_inv₀, ← h']

@[expose] def swapSL [CharP k 2] : SL2 k :=
  ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two_of]; simp [CharTwo.neg_eq]⟩

theorem swapSL_mul_self [CharP k 2] : (swapSL : SL2 k) * swapSL = 1 := by
  apply Subtype.ext
  change !![(0 : k), 1; 1, 0] * !![(0 : k), 1; 1, 0] = 1
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem swapSL_conj_apply_one_zero [CharP k 2] (A : SL2 k) :
    ((swapSL * A * swapSL : SL2 k) : Matrix (Fin 2) (Fin 2) k) 1 0 =
      (A : Matrix (Fin 2) (Fin 2) k) 0 1 := by
  change (!![(0 : k), 1; 1, 0] * (A : Matrix (Fin 2) (Fin 2) k) * !![(0 : k), 1; 1, 0]) 1 0 = _
  rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) k), Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

theorem exists_conj_eq_HSL [Finite k] [CharP k 2] {A : SL2 k} (hA : A ^ (Nat.card k - 1) = 1)
    (hA2 : A ^ 2 ≠ 1) : ∃ (P : SL2 k) (l : kˣ), P⁻¹ * A * P = HSL l := by
  by_cases hc : (A : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · by_cases hb : (A : Matrix (Fin 2) (Fin 2) k) 0 1 = 0
    · have hdet := det_SL2 A
      rw [hb, hc, mul_zero, sub_zero] at hdet
      have ha0 : (A : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
      refine ⟨1, Units.mk0 _ ha0, ?_⟩
      rw [inv_one, one_mul, mul_one]
      refine SL2_ext ?_ ?_ ?_ ?_
      · simp [coe_HSL]
      · simp [coe_HSL, hb]
      · simp [coe_HSL, hc]
      · simp only [coe_HSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, Units.val_inv_eq_inv_val, Units.val_mk0]
        exact (eq_inv_of_mul_eq_one_right hdet)
    · set A' := (swapSL : SL2 k) * A * swapSL with hA'
      have hw : (swapSL : SL2 k)⁻¹ = swapSL := inv_eq_of_mul_eq_one_right swapSL_mul_self
      have hconj : ∀ n : ℕ, A' ^ n = swapSL * A ^ n * swapSL := fun n => by
        have h := map_pow (MulAut.conj (swapSL : SL2 k)) A n
        simpa [MulAut.conj_apply, hw, hA'] using h.symm
      have hA'1 : A' ^ (Nat.card k - 1) = 1 := by
        rw [hconj, hA, mul_one, swapSL_mul_self]
      have hA'2 : A' ^ 2 ≠ 1 := by
        intro h
        apply hA2
        rw [hconj] at h
        calc A ^ 2 = swapSL * (swapSL * A ^ 2 * swapSL) * swapSL := by
              rw [← mul_assoc, ← mul_assoc, swapSL_mul_self, one_mul, mul_assoc,
                swapSL_mul_self, mul_one]
          _ = 1 := by rw [h, mul_one, swapSL_mul_self]
      have hc' : (A' : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
        rw [hA', swapSL_conj_apply_one_zero]
        exact hb
      obtain ⟨P, l, hP⟩ := exists_conj_eq_HSL_of_apply_one_zero hA'1 hA'2 hc'
      refine ⟨swapSL * P, l, ?_⟩
      rw [← hP, hA', mul_inv_rev, hw]
      group
  · exact exists_conj_eq_HSL_of_apply_one_zero hA hA2 hc

theorem HSL_mul_HSL_eq (s t : kˣ) : (HSL s : SL2 k) * HSL t = HSL (s * t) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm]

variable (k) in
@[expose] def hslHom : kˣ →* SL2 k where
  toFun := HSL
  map_one' := by
    refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_HSL]
  map_mul' s t := (HSL_mul_HSL_eq s t).symm

theorem hslHom_injective : Function.Injective (hslHom k) := fun s t h => by
  have h00 := congrArg (fun g : SL2 k => (g : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp only [hslHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_HSL] at h00
  exact Units.ext (by simpa using h00)

variable (k) in
@[expose] def diagTorus : Subgroup (SL2 k) := (hslHom k).range

theorem card_diagTorus [Finite k] : Nat.card (diagTorus k) = Nat.card k - 1 := by
  classical
  have := Fintype.ofFinite k
  rw [diagTorus, ← Nat.card_congr (MonoidHom.ofInjective (hslHom_injective (k := k))).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_units, Nat.card_eq_fintype_card]

theorem mem_diagTorus_of_commute {l : kˣ} (hl : (l : k) ≠ ((l⁻¹ : kˣ) : k)) {B : SL2 k}
    (hB : B * HSL l = HSL l * B) : B ∈ diagTorus k := by
  have hmat : (B : Matrix (Fin 2) (Fin 2) k) * (HSL l : Matrix (Fin 2) (Fin 2) k) =
      (HSL l : Matrix (Fin 2) (Fin 2) k) * (B : Matrix (Fin 2) (Fin 2) k) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hB]
  rw [Matrix.eta_fin_two (B : Matrix (Fin 2) (Fin 2) k), coe_HSL, Matrix.mul_fin_two,
    Matrix.mul_fin_two] at hmat
  have h01 := congrFun (congrFun hmat 0) 1
  have h10 := congrFun (congrFun hmat 1) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero,
    zero_add] at h01 h10
  have hLM : (l : k) - ((l⁻¹ : kˣ) : k) ≠ 0 := sub_ne_zero.2 hl
  have hb : (B : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := by
    have h : (B : Matrix (Fin 2) (Fin 2) k) 0 1 * ((l : k) - ((l⁻¹ : kˣ) : k)) = 0 := by
      linear_combination -h01
    exact (mul_eq_zero.1 h).resolve_right hLM
  have hc : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    have h : (B : Matrix (Fin 2) (Fin 2) k) 1 0 * ((l : k) - ((l⁻¹ : kˣ) : k)) = 0 := by
      linear_combination h10
    exact (mul_eq_zero.1 h).resolve_right hLM
  have hdet := det_SL2 B
  rw [hb, hc, mul_zero, sub_zero] at hdet
  have ha0 : (B : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ ha0, ?_⟩
  refine SL2_ext ?_ ?_ ?_ ?_
  · simp [hslHom, coe_HSL]
  · simp [hslHom, coe_HSL, hb]
  · simp [hslHom, coe_HSL, hc]
  · simp only [hslHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_HSL, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact (eq_inv_of_mul_eq_one_right hdet).symm

end SL2

section Js

variable {K : Type} [Field K]

theorem eq_one_of_commute_uSL_vSL [CharP K 2] {A : SL2 K} (hu : A * uSL 1 = uSL 1 * A)
    (hv : A * vSL 1 = vSL 1 * A) : A = 1 := by
  have hu' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K)) hu
  have hv' := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K)) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL] at hu' hv'
  rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) K), Matrix.mul_fin_two,
    Matrix.mul_fin_two] at hu' hv'
  have e1 := congrFun (congrFun hu' 0) 0
  have e2 := congrFun (congrFun hu' 0) 1
  have e3 := congrFun (congrFun hv' 0) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, mul_zero, one_mul, zero_mul, add_zero,
    zero_add] at e1 e2 e3
  have hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by linear_combination -e1
  have hb : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by linear_combination e3
  have had : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = (A : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    linear_combination e2
  have hdet := det_SL2 A
  rw [hb, hc, ← had, mul_zero, sub_zero] at hdet
  have ha : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : ((A : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * ((A : Matrix (Fin 2) (Fin 2) K) 0 0 - 1)
        = 0 := by linear_combination hdet + (1 - (A : Matrix (Fin 2) (Fin 2) K) 0 0) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 hsq)
  refine SL2_ext ?_ ?_ ?_ ?_
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simpa [← had] using ha

theorem pairRootSL2_injective [CharP K 2] : Function.Injective (pairRootSL2 K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hinj := (CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps Tag.E6 K
    (mem_rootFinset.1 shortRoots_check.1)).1
  have h1 : rootSL2 Tag.E6 K shortRootU A = rootSL2 Tag.E6 K shortRootU' A⁻¹ := by
    rw [pairRootSL2_apply] at hA
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left hA
  have hc : ∀ B : SL2 K, A * B = B * A := fun B => by
    apply hinj
    rw [map_mul, map_mul, h1]
    exact ((commute_rootSL2_shortRootU B A⁻¹).symm).eq
  exact eq_one_of_commute_uSL_vSL (hc _) (hc _)

@[expose] noncomputable def jsMap {k : Type} [Field k] (ι : k →+* K) :
    SL2 k →* ModGL TwistTag.E6.tag K :=
  (pairRootSL2 K).comp (Matrix.SpecialLinearGroup.map ι)

variable {k : Type} [Field k] (ι : k →+* K)

theorem jsMap_injective [CharP K 2] : Function.Injective (jsMap ι) :=
  pairRootSL2_injective.comp (F4Pilot.SL2_map_injective ι)

theorem range_jsMap [CharP K 2] : (jsMap ι).range = shortRankOneGroup ι := by
  have hgen : closure (Set.range (uSL (K := k)) ∪ Set.range vSL) = ⊤ :=
    CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
  rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, shortRankOneGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨A, (⟨c, rfl⟩ | ⟨c, rfl⟩), rfl⟩
    · refine ⟨c, Or.inl ?_⟩
      rw [jsMap, MonoidHom.comp_apply, E6GraphLevi.map_uSL, (pairRootSL2_uSL_vSL _).1]
    · refine ⟨c, Or.inr ?_⟩
      rw [jsMap, MonoidHom.comp_apply, E6GraphLevi.map_vSL, (pairRootSL2_uSL_vSL _).2]
  · rintro ⟨c, rfl | rfl⟩
    · refine ⟨uSL c, Or.inl ⟨c, rfl⟩, ?_⟩
      rw [jsMap, MonoidHom.comp_apply, E6GraphLevi.map_uSL, (pairRootSL2_uSL_vSL _).1]
    · refine ⟨vSL c, Or.inr ⟨c, rfl⟩, ?_⟩
      rw [jsMap, MonoidHom.comp_apply, E6GraphLevi.map_vSL, (pairRootSL2_uSL_vSL _).2]

theorem map_jsMap_diagTorus [CharP K 2] : (diagTorus k).map (jsMap ι) = shortRootTorus ι := by
  have key : ∀ l : kˣ, jsMap ι (hslHom k l) = rootDiagUnit Tag.E6
      (d4CentralDiag (Units.map ι.toMonoidHom l) (Units.map ι.toMonoidHom l)) := fun l => by
    change pairRootSL2 K (Matrix.SpecialLinearGroup.map ι (HSL l)) = _
    rw [E6GraphLevi.map_HSL, ← rootTorusSL2_mul_rootTorusSL2_eq]
    rfl
  ext g
  constructor
  · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
    exact ⟨l, (key l).symm⟩
  · rintro ⟨l, rfl⟩
    exact ⟨_, ⟨l, rfl⟩, key l⟩

theorem card_shortRootTorus [CharP K 2] [Finite k] :
    Nat.card (shortRootTorus ι) = Nat.card k - 1 := by
  rw [← map_jsMap_diagTorus, card_map_of_injective (jsMap_injective ι), card_diagTorus]

end Js

section Torus

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_conj_eq_shortRootTorus_of_isCyclic (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {X'' : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (hX : X'' ≤ (shortRankOneGroup (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ))
    (hcyc : IsCyclic X'')
    (hcard : Nat.card X'' = Nat.card ((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ))) :
    ∃ c ∈ (shortRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ),
      X'' = ((shortRootTorus (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).map (MulAut.conj c).toMonoidHom := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have hk2 : (2 : k) = 0 := E6GraphHighestRoot.two_eq_zero_of_card hf hk
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c =>
    (sigma_eq_self_iff hk hσ _).2 ⟨c, rfl⟩
  have hJC : shortRankOneGroup (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    shortRankOneGroup_le_C0 (apply_apply_eq hK hσ) hσι
  have hWC : shortRootTorus (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    shortRootTorus_le_C0 hσι
  have hq4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hcardW : Nat.card ((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)) = Nat.card k - 1 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv, card_shortRootTorus]
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hXz : X'' = zpowers (g : graphFixedRootGroup TwistTag.E6 K σ) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hg ⟨y, hy⟩)
      refine mem_zpowers_iff.2 ⟨n, ?_⟩
      have h := congrArg Subtype.val hn
      simpa using h
    · rw [zpowers_le]
      exact g.2
  have hgJ : ((g : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) ∈
      shortRankOneGroup (algebraMap k K) := mem_subgroupOf.1 (hX g.2)
  rw [← range_jsMap (algebraMap k K)] at hgJ
  obtain ⟨A, hA⟩ := hgJ
  have hordg : orderOf g = Nat.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard, hcardW]
  have hordA : orderOf A = Nat.card k - 1 := by
    rw [← orderOf_injective (jsMap (algebraMap k K)) (jsMap_injective _) A, hA,
      Subgroup.orderOf_coe, Subgroup.orderOf_coe, hordg]
  have hA1 : A ^ (Nat.card k - 1) = 1 := by rw [← hordA, pow_orderOf_eq_one]
  have hA2 : A ^ 2 ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num) h
    omega
  obtain ⟨P, l, hP⟩ := exists_conj_eq_HSL hA1 hA2
  have hconjord : orderOf (P⁻¹ * A * P) = orderOf A := by
    have h := MulEquiv.orderOf_eq (MulAut.conj P⁻¹) A
    rwa [MulAut.conj_apply, inv_inv] at h
  have hAz : zpowers A = (diagTorus k).map (MulAut.conj P).toMonoidHom := by
    have hzl : zpowers (HSL l) = diagTorus k := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [zpowers_le]
        exact ⟨l, rfl⟩
      · rw [card_diagTorus, Nat.card_zpowers, ← hP, hconjord, hordA]
    have hA' : A = P * HSL l * P⁻¹ := by rw [← hP]; group
    rw [← hzl, hA', MonoidHom.map_zpowers]
    rfl
  have hcJ : jsMap (algebraMap k K) P ∈ shortRankOneGroup (algebraMap k K) := by
    rw [← range_jsMap (algebraMap k K)]
    exact ⟨P, rfl⟩
  have hc : jsMap (algebraMap k K) P ∈ graphFixedRootGroup TwistTag.E6 K σ := hJC hcJ
  refine ⟨⟨jsMap (algebraMap k K) P, hc⟩, mem_subgroupOf.2 hcJ, ?_⟩
  rw [← E6Pilot.subgroupOf_map_conj_eq_map_conj_subgroupOf hWC]
  have hmap : X''.map (graphFixedRootGroup TwistTag.E6 K σ).subtype =
      (shortRootTorus (algebraMap k K)).map
        (MulAut.conj (jsMap (algebraMap k K) P)).toMonoidHom := by
    rw [hXz, MonoidHom.map_zpowers, Subgroup.coe_subtype, ← hA, ← MonoidHom.map_zpowers, hAz,
      E6Pilot.map_map_conj_eq_map_conj, map_jsMap_diagTorus]
  rw [← hmap]
  exact (Subgroup.comap_map_eq_self_of_injective
    (graphFixedRootGroup TwistTag.E6 K σ).subtype_injective X'').symm

end Torus

end CFSG.SeitzReduction.TwistedE6Pilot
