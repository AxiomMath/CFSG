module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

namespace TableBExc.E6Three

open TableBExc.Three

local instance tableBExcE6ThreeNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

local instance tableBExcE6ThreeFactThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

@[expose] def wordE6G0 : List (Fin Tag.E6.rank) := [0, 2]

@[expose] def wordE6G1 : List (Fin Tag.E6.rank) := [5, 4]

@[expose] def wordE6G2 : List (Fin Tag.E6.rank) :=
  [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3]

@[expose] def wordE6C : List (Fin Tag.E6.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]

@[expose] def wordE6G : Fin 3 → List (Fin Tag.E6.rank) := ![wordE6G0, wordE6G1, wordE6G2]

@[expose] def gE6 (i : Fin 3) : WeylGroup .E6 := (coxeterSystem .E6).wordProd (wordE6G i)

@[expose] def cE6 : WeylGroup .E6 := (coxeterSystem .E6).wordProd wordE6C

theorem gE6_pow_three (i : Fin 3) : gE6 i ^ 3 = 1 := by
  refine ext_single fun j => ?_
  rw [one_smul, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, gE6, wordProd_smul,
    wordProd_smul, wordProd_smul]
  revert i j
  decide +kernel

theorem gE6_comm (i j : Fin 3) : gE6 i * gE6 j = gE6 j * gE6 i := by
  refine ext_single fun k => ?_
  rw [mul_smul, mul_smul, gE6, gE6, wordProd_smul, wordProd_smul, wordProd_smul, wordProd_smul]
  revert i j k
  decide +kernel

theorem cE6_pow_three : cE6 ^ 3 = 1 := by
  refine ext_single fun j => ?_
  rw [one_smul, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, cE6, wordProd_smul,
    wordProd_smul, wordProd_smul]
  revert j
  decide +kernel

theorem cE6_conj (i : Fin 3) : cE6 * gE6 i * cE6⁻¹ = gE6 (piE7 i) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine ext_single fun j => ?_
  rw [mul_smul, mul_smul, gE6, gE6, cE6, wordProd_smul, wordProd_smul, wordProd_smul,
    wordProd_smul]
  revert i j
  decide +kernel

theorem isModel_E6 : IsModel piE7 gE6 cE6 :=
  ⟨gE6_pow_three, gE6_comm, cE6_pow_three, cE6_conj⟩

@[expose] noncomputable def modelHomE6 : Model piE7 piE7_pow_three →* WeylGroup .E6 :=
  modelHom isModel_E6

@[expose] def testE6 : Fin 3 → Fin Tag.E6.rank → ℤ :=
  ![Pi.single 0 1, Pi.single 4 1, Pi.single 1 1]

theorem testE6_fix : ∀ i j : Fin 3, i ≠ j → gE6 j • testE6 i = testE6 i := by
  intro i j
  rw [gE6, wordProd_smul]
  revert i j
  decide +kernel

theorem testE6_move (i : Fin 3) :
    gE6 i • testE6 i ≠ testE6 i ∧ gE6 i ^ 2 • testE6 i ≠ testE6 i := by
  rw [pow_two, mul_smul, gE6, wordProd_smul, wordProd_smul]
  revert i
  decide +kernel

theorem modelHomE6_injective : Function.Injective modelHomE6 := by
  refine modelHom_injective isModel_E6 (modelN_injective isModel_E6 testE6 testE6_fix testE6_move)
    ⟨0, fun h => ?_, fun h => ?_⟩
  · have h1 := testE6_fix 0 1 (by decide)
    rw [show (1 : Fin 3) = piE7 0 from rfl, h] at h1
    exact (testE6_move 0).1 h1
  · have h1 := testE6_fix 0 2 (by decide)
    rw [show (2 : Fin 3) = (piE7 ^ 2) 0 by decide, h] at h1
    exact (testE6_move 0).1 h1

theorem card_range_modelHomE6 : Nat.card modelHomE6.range = 81 :=
  card_range_modelHom isModel_E6 modelHomE6_injective

@[expose] def nfWordE6 (a b c : ℕ) : List (Fin Tag.E6.rank) :=
  (List.replicate a wordE6G0).flatten ++ (List.replicate b wordE6G1).flatten ++
    (List.replicate c wordE6G2).flatten

theorem modelHomE6_inl (v : Multiplicative (Fin 3 → ZMod 3)) :
    modelHomE6 (SemidirectProduct.inl v) = (coxeterSystem .E6).wordProd
      (nfWordE6 (v.toAdd 0).val (v.toAdd 1).val (v.toAdd 2).val) := by
  have hv : v = .ofAdd (Pi.single 0 (v.toAdd 0)) * .ofAdd (Pi.single 1 (v.toAdd 1)) *
      .ofAdd (Pi.single 2 (v.toAdd 2)) := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  rw [modelHomE6, modelHom_inl]
  conv_lhs => rw [hv]
  rw [map_mul, map_mul, modelN_single, modelN_single, modelN_single, nfWordE6,
    CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, wordProd_replicate,
    wordProd_replicate, wordProd_replicate]
  rfl

theorem modelHomE6_c : modelHomE6 ⟨1, .ofAdd 1⟩ = (coxeterSystem .E6).wordProd wordE6C := by
  rw [show (⟨1, .ofAdd 1⟩ : Model piE7 piE7_pow_three) = SemidirectProduct.inr (.ofAdd 1) from rfl,
    modelHomE6, modelHom_inr, ZMod.val_one, pow_one]
  rfl

theorem fixCard_adPerm_eq (F : Model piE7 piE7_pow_three →* WeylGroup .E6)
    (y : Model piE7 piE7_pow_three) (ω : List (Fin Tag.E6.rank))
    (h : F y = (coxeterSystem .E6).wordProd ω) :
    fixCard (adPerm .E6 3) F y = Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 ω x = x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [adPerm_apply, h, adWord_eq_adAct])

theorem card_fix_adWordE6C :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 wordE6C x = x} ≤ 3 ^ (6 - 3) :=
  card_fix_adWord_le (τ := .E6) wordE6C ![0, 1, 2] ![0, 1, 2] (by decide)
    ![![1, 2, 1], ![0, 2, 0], ![0, 2, 2]] (by decide +kernel)

theorem card_fix_adWordE6G0 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 wordE6G0 x = x} ≤ 3 ^ (6 - 2) :=
  card_fix_adWord_le (τ := .E6) wordE6G0 ![0, 3] ![0, 2] (by decide)
    ![![1, 1], ![0, 1]] (by decide +kernel)

theorem card_fix_adWordE6G1 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 wordE6G1 x = x} ≤ 3 ^ (6 - 2) :=
  card_fix_adWord_le (τ := .E6) wordE6G1 ![3, 4] ![4, 5] (by decide)
    ![![1, 0], ![1, 1]] (by decide +kernel)

theorem card_fix_adWordE6G2 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 wordE6G2 x = x} ≤ 3 ^ (6 - 2) :=
  card_fix_adWord_le (τ := .E6) wordE6G2 ![1, 3] ![0, 1] (by decide)
    ![![2, 0], ![0, 1]] (by decide +kernel)

theorem card_fix_nfWordE6_110 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 (nfWordE6 1 1 0) x = x} ≤
      3 ^ (6 - 3) :=
  card_fix_adWord_le (τ := .E6) _ ![0, 3, 4] ![0, 2, 4] (by decide)
    ![![1, 1, 1], ![0, 1, 1], ![0, 0, 2]] (by decide +kernel)

theorem card_fix_nfWordE6_120 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 (nfWordE6 1 2 0) x = x} ≤
      3 ^ (6 - 3) :=
  card_fix_adWord_le (τ := .E6) _ ![0, 3, 4] ![0, 2, 4] (by decide)
    ![![1, 1, 2], ![0, 1, 2], ![0, 0, 1]] (by decide +kernel)

theorem card_fix_nfWordE6_112 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 (nfWordE6 1 1 2) x = x} ≤
      3 ^ (6 - 3) :=
  card_fix_adWord_le (τ := .E6) _ ![0, 1, 3] ![0, 1, 4] (by decide)
    ![![1, 0, 0], ![1, 1, 2], ![1, 2, 0]] (by decide +kernel)

theorem card_fix_nfWordE6_111 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 (nfWordE6 1 1 1) x = x} ≤
      3 ^ (6 - 3) :=
  card_fix_adWord_le (τ := .E6) _ ![0, 1, 3] ![0, 1, 4] (by decide)
    ![![1, 0, 0], ![2, 2, 1], ![1, 1, 0]] (by decide +kernel)

theorem card_fixAll_adWordE6G01 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ t, adWord .E6 3 (![wordE6G0, wordE6G1] t) x = x} ≤ 3 ^ (6 - 4) :=
  card_fixAll_adWord_le (τ := .E6) ![wordE6G0, wordE6G1] ![(0, 0), (0, 3), (1, 3), (1, 4)]
    ![0, 2, 4, 5] (by decide)
    ![![1, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 1]] (by decide +kernel)

theorem fix_caseI_E6 (v : Multiplicative (Fin 3 → ZMod 3))
    (hv : v * shiftAut piE7 v * (shiftAut piE7 ^ 2) v = 1) :
    ∃ w, fixCard (adPerm .E6 3) modelHomE6 ⟨w * v * (shiftAut piE7 w)⁻¹, .ofAdd 1⟩ ≤ 3 ^ 3 := by
  refine ⟨.ofAdd ![0, -(v.toAdd 1), v.toAdd 0], ?_⟩
  rw [eq_ofAdd_vec3 v] at hv
  have hw := conj_vec3_E7 _ _ _ hv
  rw [← eq_ofAdd_vec3 v] at hw
  rw [hw, fixCard_adPerm_eq _ _ _ modelHomE6_c]
  exact card_fix_adWordE6C

theorem fix_supp_E6 (v : Multiplicative (Fin 3 → ZMod 3)) (hv : 2 ≤ (supp v).card) :
    fixCard (adPerm .E6 3) modelHomE6 (SemidirectProduct.inl v) ≤ 3 ^ 3 := by
  rw [eq_ofAdd_vec3 v] at hv ⊢
  obtain ⟨k, e, he⟩ := exists_rep_E7 _ _ _ hv
  refine fixCard_inl_le_of_rot _ _ k ((e : ℕ) + 1) (by omega) ?_
  have hrep : ∀ r ∈ ({.ofAdd ![1, 1, 0], .ofAdd ![1, 2, 0], .ofAdd ![1, 1, 2],
      .ofAdd ![1, 1, 1]} : Finset (Multiplicative (Fin 3 → ZMod 3))),
      fixCard (adPerm .E6 3) modelHomE6 (SemidirectProduct.inl r) ≤ 3 ^ 3 := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [fixCard_adPerm_eq _ _ (nfWordE6 1 1 0) (by rw [modelHomE6_inl]; rfl)]
      exact card_fix_nfWordE6_110
    · rw [fixCard_adPerm_eq _ _ (nfWordE6 1 2 0) (by rw [modelHomE6_inl]; rfl)]
      exact card_fix_nfWordE6_120
    · rw [fixCard_adPerm_eq _ _ (nfWordE6 1 1 2) (by rw [modelHomE6_inl]; rfl)]
      exact card_fix_nfWordE6_112
    · rw [fixCard_adPerm_eq _ _ (nfWordE6 1 1 1) (by rw [modelHomE6_inl]; rfl)]
      exact card_fix_nfWordE6_111
  exact hrep _ he

theorem fix_single_E6 (i : Fin 3) :
    fixCard (adPerm .E6 3) modelHomE6 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ≤
      3 ^ 4 := by
  rw [fixCard_adPerm_eq _ _ (wordE6G i)
    (by rw [modelHomE6, modelHom_inl, modelN_single, ZMod.val_one, pow_one]; rfl)]
  fin_cases i
  · exact card_fix_adWordE6G0
  · exact card_fix_adWordE6G1
  · exact card_fix_adWordE6G2

theorem fix_N_E6 : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
    ∀ v, adPerm .E6 3 (modelHomE6 (SemidirectProduct.inl v)) x = x} ≤ 3 ^ 2 := by
  have hg : ∀ i : Fin 3, modelHomE6 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) =
      (coxeterSystem .E6).wordProd (wordE6G i) := fun i => by
    rw [modelHomE6, modelHom_inl, modelN_single, ZMod.val_one, pow_one]
    rfl
  refine le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨x.1, fun t => ?_⟩ : {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ t, adWord .E6 3 (![wordE6G0, wordE6G1] t) x = x}))
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) card_fixAll_adWordE6G01
  have h0 := x.2 (.ofAdd (Pi.single 0 1))
  have h1 := x.2 (.ofAdd (Pi.single 1 1))
  rw [adPerm_apply, hg, ← adWord_eq_adAct] at h0 h1
  fin_cases t
  · exact h0
  · exact h1

theorem noOffender_E6ad (A : Subgroup (WeylGroup .E6)) (hAS : A ≤ modelHomE6.range)
    (hA : IsElemAbelian 3 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ a ∈ A, adAct .E6 3 a x = x} <
      3 ^ Tag.E6.rank :=
  card_mul_card_fix_lt_of_model (adPerm .E6 3) modelHomE6 modelHomE6_injective
    (fun _ h3 hc h1 => card_mul_fixAllCard_lt (T := 3 ^ Tag.E6.rank) (adPerm .E6 3) modelHomE6
      fix_caseI_E6 card_fixShift_E7 fix_supp_E6 fix_single_E6 fix_N_E6
      (by decide) (by decide) (by decide) (by decide) h3 hc h1) hAS hA hA1

open CFSG.Timmesfeld.ExceptionalOrders (geomSum)

section Index

variable {K : Type} [Field K]

theorem not_three_dvd_index_E6 [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ (weylX .E6 K modelHomE6.range).index := by
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hq3 := mod_eq_one_of_dvd_sub_one (by norm_num) hq h3
  have hq1 : (Nat.card K : ZMod 3) = 1 := cast_eq_one_of_dvd_sub_one hq h3
  have hG3 := geomSum_three_mod hq3
  have hG9 := geomSum_nine_mod hq3
  have hG34 := geomSum_three_four_mod hq3
  have hm3 := cast_div_eq (p := 3) (c := 1) (by norm_num) (by norm_num) hG3
  have hm34 := cast_div_eq (p := 3) (c := 1) (by norm_num) (by norm_num) hG34
  have hm9 := cast_div_nine_eq hG9
  have hGm3 : geomSum 3 1 (Nat.card K) = 3 * (geomSum 3 1 (Nat.card K) / 3) := by omega
  have hGm34 : geomSum 3 4 (Nat.card K) = 3 * (geomSum 3 4 (Nat.card K) / 3) := by omega
  have hGm9 : geomSum 9 1 (Nat.card K) = 9 * (geomSum 9 1 (Nat.card K) / 9) := by omega
  set M := Nat.card K ^ 36 * (geomSum 2 1 (Nat.card K) * (geomSum 3 1 (Nat.card K) / 3) *
      geomSum 4 1 (Nat.card K) * geomSum 5 1 (Nat.card K) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      ((geomSum 9 1 (Nat.card K) / 9) * (geomSum 3 4 (Nat.card K) / 3))) with hM
  have hC : Nat.card (adjointGroup .E6 K) =
      Nat.card modelHomE6.range * Nat.card (torusGroup .E6 K) * M := by
    rw [card_adjointGroup_E6_eq, prodE6, card_range_modelHomE6, hM]
    nth_rewrite 1 [hGm3]
    nth_rewrite 1 [hGm9]
    nth_rewrite 1 [hGm34]
    ring
  rw [index_weylX_eq hC]
  apply not_dvd_of_cast_ne_zero
  rw [hM]
  push_cast
  simp only [hq1, hm3, hm34, hm9, geomSum_cast hq1, one_pow, Nat.cast_one]
  decide

end Index

end TableBExc.E6Three

end CFSG.StandardType
