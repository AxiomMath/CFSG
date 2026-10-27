module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeKey
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover

namespace TableBExc.Three

local instance tableBExcThreeNeZeroRankE7 : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def wordE7G0 : List (Fin Tag.E7.rank) := [0, 2]

@[expose] def wordE7G1 : List (Fin Tag.E7.rank) := [5, 4]

@[expose] def wordE7G2 : List (Fin Tag.E7.rank) :=
  [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3]

@[expose] def wordE7C : List (Fin Tag.E7.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]

@[expose] def wordE7G : Fin 3 → List (Fin Tag.E7.rank) := ![wordE7G0, wordE7G1, wordE7G2]

@[expose] def gE7 (i : Fin 3) : WeylGroup .E7 := (coxeterSystem .E7).wordProd (wordE7G i)

@[expose] def cE7 : WeylGroup .E7 := (coxeterSystem .E7).wordProd wordE7C

@[expose] def piE7 : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

theorem piE7_pow_three : piE7 ^ 3 = 1 := by decide

theorem gE7_pow_three (i : Fin 3) : gE7 i ^ 3 = 1 := by
  refine ext_single fun j => ?_
  rw [one_smul, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, gE7, wordProd_smul,
    wordProd_smul, wordProd_smul]
  revert i j
  decide +kernel

theorem gE7_comm (i j : Fin 3) : gE7 i * gE7 j = gE7 j * gE7 i := by
  refine ext_single fun k => ?_
  rw [mul_smul, mul_smul, gE7, gE7, wordProd_smul, wordProd_smul, wordProd_smul, wordProd_smul]
  revert i j k
  decide +kernel

theorem cE7_pow_three : cE7 ^ 3 = 1 := by
  refine ext_single fun j => ?_
  rw [one_smul, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, cE7, wordProd_smul,
    wordProd_smul, wordProd_smul]
  revert j
  decide +kernel

theorem cE7_conj (i : Fin 3) : cE7 * gE7 i * cE7⁻¹ = gE7 (piE7 i) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine ext_single fun j => ?_
  rw [mul_smul, mul_smul, gE7, gE7, cE7, wordProd_smul, wordProd_smul, wordProd_smul,
    wordProd_smul]
  revert i j
  decide +kernel

theorem isModel_E7 : IsModel piE7 gE7 cE7 :=
  ⟨gE7_pow_three, gE7_comm, cE7_pow_three, cE7_conj⟩

@[expose] noncomputable def modelHomE7 : Model piE7 piE7_pow_three →* WeylGroup .E7 :=
  modelHom isModel_E7

@[expose] def testE7 : Fin 3 → Fin Tag.E7.rank → ℤ := ![Pi.single 0 1, Pi.single 4 1, Pi.single 1 1]

theorem testE7_fix : ∀ i j : Fin 3, i ≠ j → gE7 j • testE7 i = testE7 i := by
  intro i j
  rw [gE7, wordProd_smul]
  revert i j
  decide +kernel

theorem testE7_move (i : Fin 3) : gE7 i • testE7 i ≠ testE7 i ∧ gE7 i ^ 2 • testE7 i ≠ testE7 i := by
  rw [pow_two, mul_smul, gE7, wordProd_smul, wordProd_smul]
  revert i
  decide +kernel

theorem modelHomE7_injective : Function.Injective modelHomE7 := by
  refine modelHom_injective isModel_E7 (modelN_injective isModel_E7 testE7 testE7_fix testE7_move)
    ⟨0, fun h => ?_, fun h => ?_⟩
  · have h1 := testE7_fix 0 1 (by decide)
    rw [show (1 : Fin 3) = piE7 0 from rfl, h] at h1
    exact (testE7_move 0).1 h1
  · have h1 := testE7_fix 0 2 (by decide)
    rw [show (2 : Fin 3) = (piE7 ^ 2) 0 by decide, h] at h1
    exact (testE7_move 0).1 h1

theorem card_range_modelHomE7 : Nat.card modelHomE7.range = 81 :=
  card_range_modelHom isModel_E7 modelHomE7_injective

local instance tableBExcThreeFactE7 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem cartan_symm_E7 : ∀ i j : Fin Tag.E7.rank, Tag.E7.cartan i j = Tag.E7.cartan j i := by
  have h : ∀ i j : Fin 7, decide (Tag.cartanE 7 i j = Tag.cartanE 7 j i) = true := by decide
  exact fun i j => of_decide_eq_true (h i j)

@[expose] def nfWordE7 (a b c : ℕ) : List (Fin Tag.E7.rank) :=
  (List.replicate a wordE7G0).flatten ++ (List.replicate b wordE7G1).flatten ++
    (List.replicate c wordE7G2).flatten

theorem modelHomE7_inl (v : Multiplicative (Fin 3 → ZMod 3)) :
    modelHomE7 (SemidirectProduct.inl v) = (coxeterSystem .E7).wordProd
      (nfWordE7 (v.toAdd 0).val (v.toAdd 1).val (v.toAdd 2).val) := by
  have hv : v = .ofAdd (Pi.single 0 (v.toAdd 0)) * .ofAdd (Pi.single 1 (v.toAdd 1)) *
      .ofAdd (Pi.single 2 (v.toAdd 2)) := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  rw [modelHomE7, modelHom_inl]
  conv_lhs => rw [hv]
  rw [map_mul, map_mul, modelN_single, modelN_single, modelN_single, nfWordE7,
    CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, wordProd_replicate,
    wordProd_replicate, wordProd_replicate]
  rfl

theorem modelHomE7_c : modelHomE7 ⟨1, .ofAdd 1⟩ = (coxeterSystem .E7).wordProd wordE7C := by
  rw [show (⟨1, .ofAdd 1⟩ : Model piE7 piE7_pow_three) = SemidirectProduct.inr (.ofAdd 1) from rfl,
    modelHomE7, modelHom_inr, ZMod.val_one, pow_one]
  rfl

theorem card_fix_wordE7C :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 wordE7C x = x} ≤ 3 ^ (7 - 3) :=
  card_fix_torusWord_le (τ := .E7) wordE7C ![0, 1, 2] ![0, 1, 2] (by decide)
    ![![2, 0, 0], ![0, 2, 0], ![0, 2, 2]] (by decide +kernel)

theorem card_fix_wordE7G0 :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 wordE7G0 x = x} ≤ 3 ^ (7 - 2) :=
  card_fix_torusWord_le (τ := .E7) wordE7G0 ![0, 2] ![0, 3] (by decide)
    ![![1, 2], ![2, 2]] (by decide +kernel)

theorem card_fix_wordE7G1 :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 wordE7G1 x = x} ≤ 3 ^ (7 - 2) :=
  card_fix_torusWord_le (τ := .E7) wordE7G1 ![4, 5] ![3, 4] (by decide)
    ![![2, 2], ![2, 1]] (by decide +kernel)

theorem card_fix_wordE7G2 :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 wordE7G2 x = x} ≤ 3 ^ (7 - 2) :=
  card_fix_torusWord_le (τ := .E7) wordE7G2 ![0, 1] ![1, 3] (by decide)
    ![![1, 2], ![0, 2]] (by decide +kernel)

theorem card_fix_nfWordE7_110 :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 (nfWordE7 1 1 0) x = x} ≤
      3 ^ (7 - 3) :=
  card_fix_torusWord_le (τ := .E7) _ ![0, 2, 4] ![0, 3, 4] (by decide)
    ![![1, 2, 0], ![2, 2, 0], ![1, 1, 1]] (by decide +kernel)

theorem card_fix_nfWordE7_120 :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 (nfWordE7 1 2 0) x = x} ≤
      3 ^ (7 - 3) :=
  card_fix_torusWord_le (τ := .E7) _ ![0, 2, 4] ![0, 3, 4] (by decide)
    ![![1, 2, 0], ![2, 2, 0], ![2, 2, 2]] (by decide +kernel)

theorem card_fix_nfWordE7_112 :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 (nfWordE7 1 1 2) x = x} ≤
      3 ^ (7 - 3) :=
  card_fix_torusWord_le (τ := .E7) _ ![0, 1, 2] ![0, 3, 6] (by decide)
    ![![2, 1, 0], ![2, 0, 2], ![1, 1, 1]] (by decide +kernel)

theorem card_fix_nfWordE7_111 :
    Nat.card {x : Fin Tag.E7.rank → ZMod 3 // torusWord .E7 3 (nfWordE7 1 1 1) x = x} ≤
      3 ^ (7 - 4) :=
  card_fix_torusWord_le (τ := .E7) _ ![0, 1, 2, 4] ![0, 1, 3, 6] (by decide)
    ![![0, 0, 1, 2], ![0, 1, 0, 2], ![2, 0, 2, 0], ![1, 2, 1, 0]] (by decide +kernel)

theorem eq_ofAdd_vec3 (v : Multiplicative (Fin 3 → ZMod 3)) :
    v = .ofAdd ![v.toAdd 0, v.toAdd 1, v.toAdd 2] := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> rfl

theorem conj_vec3_E7 : ∀ a b c : ZMod 3,
    (Multiplicative.ofAdd ![a, b, c] : Multiplicative (Fin 3 → ZMod 3)) *
        shiftAut piE7 (.ofAdd ![a, b, c]) * (shiftAut piE7 ^ 2) (.ofAdd ![a, b, c]) = 1 →
      (Multiplicative.ofAdd ![0, -b, a] : Multiplicative (Fin 3 → ZMod 3)) * .ofAdd ![a, b, c] *
        (shiftAut piE7 (.ofAdd ![0, -b, a]))⁻¹ = 1 := by
  decide +kernel

theorem fix_caseI_E7 (v : Multiplicative (Fin 3 → ZMod 3))
    (hv : v * shiftAut piE7 v * (shiftAut piE7 ^ 2) v = 1) :
    ∃ w, fixCard (torusPerm .E7 3) modelHomE7 ⟨w * v * (shiftAut piE7 w)⁻¹, .ofAdd 1⟩ ≤ 3 ^ 4 := by
  refine ⟨.ofAdd ![0, -(v.toAdd 1), v.toAdd 0], ?_⟩
  rw [eq_ofAdd_vec3 v] at hv
  have hw := conj_vec3_E7 _ _ _ hv
  rw [← eq_ofAdd_vec3 v] at hw
  rw [hw, fixCard_torusPerm_eq cartan_symm_E7 _ _ _ modelHomE7_c]
  exact card_fix_wordE7C

theorem card_fixShift_E7 :
    Nat.card {w : Multiplicative (Fin 3 → ZMod 3) // shiftAut piE7 w = w} ≤ 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem exists_rep_E7 : ∀ a b c : ZMod 3,
    2 ≤ (supp (.ofAdd ![a, b, c] : Multiplicative (Fin 3 → ZMod 3))).card →
      ∃ k : Fin 3, ∃ e : Fin 2,
        (shiftAut piE7 ^ (k : ℕ)) ((.ofAdd ![a, b, c] : Multiplicative (Fin 3 → ZMod 3)) ^
          ((e : ℕ) + 1)) ∈ ({.ofAdd ![1, 1, 0], .ofAdd ![1, 2, 0], .ofAdd ![1, 1, 2],
            .ofAdd ![1, 1, 1]} : Finset (Multiplicative (Fin 3 → ZMod 3))) := by
  decide +kernel

theorem fix_supp_E7 (v : Multiplicative (Fin 3 → ZMod 3)) (hv : 2 ≤ (supp v).card) :
    fixCard (torusPerm .E7 3) modelHomE7 (SemidirectProduct.inl v) ≤ 3 ^ 4 := by
  rw [eq_ofAdd_vec3 v] at hv ⊢
  obtain ⟨k, e, he⟩ := exists_rep_E7 _ _ _ hv
  refine fixCard_inl_le_of_rot _ _ k ((e : ℕ) + 1) (by omega) ?_
  have hrep : ∀ r ∈ ({.ofAdd ![1, 1, 0], .ofAdd ![1, 2, 0], .ofAdd ![1, 1, 2],
      .ofAdd ![1, 1, 1]} : Finset (Multiplicative (Fin 3 → ZMod 3))),
      fixCard (torusPerm .E7 3) modelHomE7 (SemidirectProduct.inl r) ≤ 3 ^ 4 := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [fixCard_torusPerm_eq cartan_symm_E7 _ _ (nfWordE7 1 1 0) (by rw [modelHomE7_inl]; rfl)]
      exact card_fix_nfWordE7_110
    · rw [fixCard_torusPerm_eq cartan_symm_E7 _ _ (nfWordE7 1 2 0) (by rw [modelHomE7_inl]; rfl)]
      exact card_fix_nfWordE7_120
    · rw [fixCard_torusPerm_eq cartan_symm_E7 _ _ (nfWordE7 1 1 2) (by rw [modelHomE7_inl]; rfl)]
      exact card_fix_nfWordE7_112
    · rw [fixCard_torusPerm_eq cartan_symm_E7 _ _ (nfWordE7 1 1 1) (by rw [modelHomE7_inl]; rfl)]
      exact card_fix_nfWordE7_111.trans (by norm_num)
  exact hrep _ he

theorem fix_single_E7 (i : Fin 3) :
    fixCard (torusPerm .E7 3) modelHomE7 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ≤
      3 ^ 5 := by
  rw [fixCard_torusPerm_eq cartan_symm_E7 _ _ (wordE7G i)
    (by rw [modelHomE7, modelHom_inl, modelN_single, ZMod.val_one, pow_one]; rfl)]
  fin_cases i
  · exact card_fix_wordE7G0
  · exact card_fix_wordE7G1
  · exact card_fix_wordE7G2

theorem fix_N_E7 : Nat.card {x : Fin Tag.E7.rank → ZMod 3 //
    ∀ v, torusPerm .E7 3 (modelHomE7 (SemidirectProduct.inl v)) x = x} ≤ 3 ^ 3 := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨x.1, x.2 (.ofAdd ![1, 1, 1])⟩ : {x : Fin Tag.E7.rank → ZMod 3 //
      torusPerm .E7 3 (modelHomE7 (SemidirectProduct.inl (.ofAdd ![1, 1, 1]))) x = x}))
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) ?_
  change fixCard (torusPerm .E7 3) modelHomE7 _ ≤ _
  rw [fixCard_torusPerm_eq cartan_symm_E7 _ _ (nfWordE7 1 1 1) (by rw [modelHomE7_inl]; rfl)]
  exact card_fix_nfWordE7_111

theorem noOffender_E7 (A : Subgroup (WeylGroup .E7)) (hAS : A ≤ modelHomE7.range)
    (hA : IsElemAbelian 3 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {x : Fin Tag.E7.rank → ZMod 3 // ∀ a ∈ A, torusAct .E7 3 a x = x} <
      3 ^ Tag.E7.rank :=
  card_mul_card_fix_lt_of_model (torusPerm .E7 3) modelHomE7 modelHomE7_injective
    (fun _ h3 hc h1 => card_mul_fixAllCard_lt (T := 3 ^ Tag.E7.rank) (torusPerm .E7 3) modelHomE7
      fix_caseI_E7 card_fixShift_E7 fix_supp_E7 fix_single_E7 fix_N_E7
      (by decide) (by decide) (by decide) (by decide) h3 hc h1) hAS hA hA1

open CFSG.Timmesfeld.ExceptionalOrders (geomSum)

theorem geomSum_three_mod {q : ℕ} (h : q % 3 = 1) : geomSum 3 1 q % 9 = 3 := by
  have hr : q % 9 = 1 ∨ q % 9 = 4 ∨ q % 9 = 7 := by omega
  rw [geomSum]
  simp only [one_mul]
  rw [TableBF4.geomSum_mod]
  rcases hr with h | h | h <;> rw [h] <;> decide

theorem geomSum_nine_mod {q : ℕ} (h : q % 3 = 1) : geomSum 9 1 q % 27 = 9 := by
  have hr : q % 27 = 1 ∨ q % 27 = 4 ∨ q % 27 = 7 ∨ q % 27 = 10 ∨ q % 27 = 13 ∨
      q % 27 = 16 ∨ q % 27 = 19 ∨ q % 27 = 22 ∨ q % 27 = 25 := by omega
  rw [geomSum]
  simp only [one_mul]
  rw [TableBF4.geomSum_mod]
  rcases hr with h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem geomSum_three_four_mod {q : ℕ} (h : q % 3 = 1) : geomSum 3 4 q % 9 = 3 := by
  have e : geomSum 3 4 q = geomSum 3 1 (q ^ 4) := by
    simp only [geomSum, one_mul, ← pow_mul]
  rw [e]
  refine geomSum_three_mod ?_
  rw [Nat.pow_mod, h]

theorem cast_div_nine_eq {n : ℕ} (h : n % 27 = 9) : ((n / 9 : ℕ) : ZMod 3) = 1 := by
  have h1 : n / 9 % 3 = 1 := by omega
  rw [← ZMod.natCast_mod, h1, Nat.cast_one]

section T

variable {K : Type} [Field K]

theorem not_three_dvd_index_E7 [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ (weylX .E7 K modelHomE7.range).index := by
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
  set M := Nat.card K ^ 63 * (geomSum 2 1 (Nat.card K) * (geomSum 3 1 (Nat.card K) / 3) *
      geomSum 4 1 (Nat.card K) * geomSum 5 1 (Nat.card K) *
      (geomSum 2 3 (Nat.card K) * geomSum 8 1 (Nat.card K)) *
      ((geomSum 9 1 (Nat.card K) / 9) * (geomSum 3 4 (Nat.card K) / 3)) *
      (geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * geomSum 14 1 (Nat.card K))) with hM
  have hC : Nat.card (adjointGroup .E7 K) =
      Nat.card modelHomE7.range * Nat.card (torusGroup .E7 K) * M := by
    rw [card_adjointGroup_E7_eq, prodE7, card_range_modelHomE7, hM]
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

theorem ggExcToralRankInput_E7_three [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1) :
    GGExcToralRankInput .E7 K 3 :=
  ggExcToralRankInput_of_noOffender Nat.prime_three h3
    (isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E7 (by norm_num))
    (card_torusPow_E7 Nat.prime_three h3) cartan_symm_E7 (not_three_dvd_index_E7 h3)
    noOffender_E7

end T

end TableBExc.Three

theorem ggE7ThreeToralRankInput_holds :
    GGE7ThreeToralRankInput :=
  fun _ _ _ _ h3 => TableBExc.Three.ggExcToralRankInput_E7_three h3

end CFSG.StandardType
