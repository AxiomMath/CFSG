module

public import CFSG.YGroups.Exact.Y321
public import CFSG.YGroups.Exact.Y322
public import CFSG.YGroups.Y322Central.Transitive
public import Certificates.Data.CFSGNative.YGroups.Y322CentralData
public import CFSG.YGroups.Y322CentralInputs
public import Certificates.Certificate10103
public meta import CFSG.YGroups.Defs
public meta import CFSG.YGroups.Exact.Y322
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.YGroups.ExactData
public meta import Certificates.Data.CFSGNative.YGroups.Y322CentralData

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

@[expose] def y322H : Subgroup (YGroup 3 2 2) := Subgroup.closure (yGen 3 2 2 '' {c | c < 7})

@[expose] noncomputable def y322F1 : YGroup 3 2 2 := evalWord (yGen 3 2 2) y322WordF1

@[expose] noncomputable def y322F2 : YGroup 3 2 2 := evalWord (yGen 3 2 2) y322WordF2

theorem evalWord_const_ofAdd (w : List ℕ) :
    evalWord (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) w =
      Multiplicative.ofAdd ((w.length : ℕ) : ZMod 2) := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [evalWord_cons, ih, List.length_cons, Nat.cast_succ, ← ofAdd_add, add_comm]

theorem y322_parity_relators :
    ∀ w ∈ yRels 3 2 2, evalWord (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) w = 1 := by
  have key : ∀ w ∈ yRels 3 2 2, w.length % 2 = 0 := by decide +kernel
  intro w hw
  rw [evalWord_const_ofAdd]
  have h0 : ((w.length : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero (key w hw)
  rw [h0]
  rfl

noncomputable def y322Parity : YGroup 3 2 2 →* Multiplicative (ZMod 2) :=
  yModelHom (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) y322_parity_relators

theorem y322Parity_yGen {c : ℕ} (hc : c < 8) :
    y322Parity (yGen 3 2 2 c) = Multiplicative.ofAdd 1 :=
  yModelHom_yGen hc

theorem y322Parity_evalWord (w : List ℕ) (hw : ∀ c ∈ w, c < 8) :
    y322Parity (evalWord (yGen 3 2 2) w) = Multiplicative.ofAdd ((w.length : ℕ) : ZMod 2) := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [evalWord_cons, map_mul, y322Parity_yGen (hw c (by simp)),
      ih (fun d hd => hw d (by simp [hd])), List.length_cons, Nat.cast_succ, ← ofAdd_add,
      add_comm]

theorem y322Parity_F1 : y322Parity y322F1 = Multiplicative.ofAdd 1 := by
  rw [y322F1, y322Parity_evalWord _ (by decide)]
  have : y322WordF1.length = 63 := by decide
  rw [this]
  rfl

theorem y322F1_ne_one : y322F1 ≠ 1 := by
  intro h
  have := y322Parity_F1
  rw [h, map_one] at this
  exact absurd (Multiplicative.ofAdd.injective this) (by decide)

theorem y322Central_check :
    eqA 728 (ModelNative.evalW 728 y322Arrays y322WordF1)
      (ModelNative.evalW 728 y322Arrays y322WordF2) = true ∧
    (∀ c < 8, eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [c]))
      (ModelNative.evalW 728 y322Arrays (c :: y322WordF1)) = true) ∧
    eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ y322WordF1))
      (ModelNative.evalW 728 y322Arrays []) = true :=
  Certificates.certificate10103.1

theorem y322F1_eq_F2 :
    y322F1 = y322F2 :=
  (evalWord_yGen_322_eq_iff _ _).2 y322Central_check.1

theorem y322F1_mul_self :
    y322F1 * y322F1 = 1 := by
  have h := (evalWord_yGen_322_eq_iff (y322WordF1 ++ y322WordF1) []).2 y322Central_check.2.2
  rwa [evalWord_append, evalWord_nil] at h

theorem y322F1_comm_yGen
    {c : ℕ} (hc : c < 8) : yGen 3 2 2 c * y322F1 = y322F1 * yGen 3 2 2 c := by
  have h := (evalWord_yGen_322_eq_iff (y322WordF1 ++ [c]) (c :: y322WordF1)).2
    (y322Central_check.2.1 c hc)
  rw [evalWord_append, evalWord_cons, evalWord_cons, evalWord_nil, mul_one] at h
  exact h.symm

theorem y322F1_mem_center :
    y322F1 ∈ Subgroup.center (YGroup 3 2 2) := by
  rw [Subgroup.mem_center_iff]
  have hle : Subgroup.closure (yGen 3 2 2 '' Set.Iio (ngen 3 2 2)) ≤
      Subgroup.centralizer {y322F1} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact y322F1_comm_yGen (by simpa [ngen] using hc)
  intro g
  have hg : g ∈ Subgroup.closure (yGen 3 2 2 '' Set.Iio (ngen 3 2 2)) := by
    rw [closure_yGen]
    trivial
  have := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  exact this

theorem y322F1_orderOf :
    orderOf y322F1 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact y322F1_mul_self) y322F1_ne_one

theorem rels_y321_y322 : ∀ w ∈ yRels 3 2 1, w.map (shiftAt 6) ∈ yRels 3 2 2 := by decide

theorem shiftAt_Iio_ngen_y321 : shiftAt 6 '' Set.Iio (ngen 3 2 1) = {c | c < 7} := by
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hd' : d < 7 := hd
    show shiftAt 6 d < 7
    unfold shiftAt
    split_ifs <;> omega
  · intro hc
    have hc' : c < 7 := hc
    refine ⟨c, hc', ?_⟩
    unfold shiftAt
    rw [ite_eq_left (by omega)]

theorem range_yHom_y321_y322 : (yHom (shiftAt 6) rels_y321_y322).range = y322H := by
  rw [range_yHom, shiftAt_Iio_ngen_y321]
  rfl

theorem y322HSub_check :
    ModelNative.chainOK 728 y322HSubArrays #[] #[0, 1, 2, 3, 4, 5] = true ∧
    ModelNative.chainSizes 728 y322HSubArrays #[] #[0, 1, 2, 3, 4, 5] = [56, 27, 16, 10, 6, 2] :=
  Certificates.certificate10103.2.1

theorem y322HSubArrays_size : y322HSubArrays.size = 7 := by
  simp [y322HSubArrays, y322_check.1]

theorem y322HSubArrays_getElem
    {k : ℕ} (hk : k < 7) : y322HSubArrays[k]! = y322Arrays[k]! := by
  have h1 : k < y322HSubArrays.size := by rw [y322HSubArrays_size]; exact hk
  have h2 : k < y322Arrays.size := by rw [y322_check.1]; omega
  rw [getElem!_pos y322HSubArrays k h1, getElem!_pos y322Arrays k h2]
  simp [y322HSubArrays, Array.getElem_extract]

theorem arrClosure_y322HSub :
    arrClosure 728 y322HSubArrays = Subgroup.closure (y322Gen '' {c | c < 7}) := by
  unfold arrClosure
  congr 1
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk7 : k < 7 := by simpa [y322HSubArrays_size] using hk
    refine ⟨k, hk7, ?_⟩
    rw [y322Gen, arrGen, ite_eq_left (by have := y322_check.1; omega),
      y322HSubArrays_getElem hk7]
  · rintro ⟨k, hk, rfl⟩
    have hk7 : k < 7 := hk
    refine ⟨k, by simpa [y322HSubArrays_size] using hk7, ?_⟩
    rw [y322Gen, arrGen, ite_eq_left (by have := y322_check.1; omega),
      y322HSubArrays_getElem hk7]

theorem map_y322Model_y322H :
    Subgroup.map y322Model y322H = Subgroup.closure (y322Gen '' {c | c < 7}) := by
  rw [y322H, MonoidHom.map_closure, Set.image_image]
  congr 1
  apply Set.image_congr
  intro c hc
  have hc7 : c < 7 := hc
  exact y322Model_yGen (by omega)

theorem y322H_card_ge :
    2903040 ≤ Nat.card y322H := by
  have h1 := chainSizes_prod_le_card y322HSub_check.1
  rw [y322HSub_check.2, arrClosure_y322HSub, ← map_y322Model_y322H,
    Subgroup.card_map_of_injective y322Model_injective] at h1
  have : ([56, 27, 16, 10, 6, 2] : List ℕ).prod = 2903040 := by norm_num
  omega

theorem y322H_card :
    Nat.card y322H = 2903040 := by
  have := y321.1
  have hup : Nat.card y322H ≤ 2903040 := by
    rw [← range_yHom_y321_y322]
    calc Nat.card (yHom (shiftAt 6) rels_y321_y322).range ≤ Nat.card (YGroup 3 2 1) :=
          Nat.card_le_card_of_surjective _
            (yHom (shiftAt 6) rels_y321_y322).rangeRestrict_surjective
      _ = 2903040 := card_y321
  exact le_antisymm hup y322H_card_ge

theorem y322_yHom_injective :
    Function.Injective (yHom (shiftAt 6) rels_y321_y322) := by
  have := y321.1
  refine (injective_and_card_of_model (yHom (shiftAt 6) rels_y321_y322) (B := 2903040)
    card_y321.le ?_).1
  rw [range_yHom_y321_y322, y322H_card]

theorem y322H_index :
    y322H.index = 3159 := by
  have h := y322H.card_mul_index
  rw [y322H_card, card_y322] at h
  omega

theorem y322HAct_check :
    y322HActArrays.size = 8 ∧ ModelNative.permsOK 3159 y322HActArrays = true ∧
    ModelNative.relatorsOK 3159 y322HActArrays (yRels 3 2 2) = true ∧
    ModelNative.chainOK 3159 y322HActArrays #[] #[0, 1, 2, 3, 4, 5, 6] = true ∧
    ModelNative.chainSizes 3159 y322HActArrays #[] #[0, 1, 2, 3, 4, 5, 6] =
      [3159, 288, 35, 12, 3, 2, 2] ∧
    (∀ c < 7, (y322HActArrays[c]!)[0]! = 0) :=
  Certificates.certificate10103.2.2

theorem y322HAct_relators :
    ∀ w ∈ yRels 3 2 2, evalWord (arrGen 3159 y322HActArrays) w = 1 :=
  evalWord_arrGen_eq_one y322HAct_check.2.1 y322HAct_check.2.2.1

noncomputable def y322HAct :
    YGroup 3 2 2 →* Equiv.Perm (Fin 3159) :=
  yModelHom (arrGen 3159 y322HActArrays) y322HAct_relators

theorem y322HAct_yGen {c : ℕ} (hc : c < 8) :
    y322HAct (yGen 3 2 2 c) = arrGen 3159 y322HActArrays c :=
  yModelHom_yGen hc

theorem y322HAct_fix {c : ℕ} (hc : c < 7) :
    y322HAct (yGen 3 2 2 c) ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  rw [y322HAct_yGen (by omega)]
  have hrep := rep_letterOf y322HAct_check.2.1 c
  rw [ModelNative.letterOf, ite_eq_left (by have := y322HAct_check.1; omega)] at hrep
  apply Fin.ext
  have := hrep ⟨0, by norm_num⟩
  rw [← this]
  exact y322HAct_check.2.2.2.2.2 c hc

theorem y322HAct_fix_H :
    ∀ h ∈ y322H, y322HAct h ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  intro h hh
  have hle : y322H ≤ (MulAction.stabilizer (Equiv.Perm (Fin 3159))
      (⟨0, by norm_num⟩ : Fin 3159)).comap y322HAct := by
    rw [y322H, Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    exact y322HAct_fix hc
  have := hle hh
  rwa [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at this

theorem range_y322HAct :
    y322HAct.range = arrClosure 3159 y322HActArrays := by
  rw [y322HAct, range_yModelHom, ← show y322HActArrays.size = ngen 3 2 2 from y322HAct_check.1,
    arrGen_image_eq]
  rfl

theorem y322HAct_transitive :
    ∀ y : Fin 3159, ∃ g : YGroup 3 2 2, y322HAct g ⟨0, by norm_num⟩ = y := by
  obtain ⟨b, hb, h⟩ := chain_transitive (n := 3159) y322HAct_check.2.2.2.1
    (by decide : 0 < (#[0, 1, 2, 3, 4, 5, 6] : Array ℕ).size)
    (by rw [y322HAct_check.2.2.2.2.1]; rfl)
  have hb0 : b = ⟨0, by norm_num⟩ := Fin.ext (by rw [hb]; rfl)
  intro y
  obtain ⟨g, hg, hgy⟩ := h y
  rw [← range_y322HAct] at hg
  obtain ⟨g', rfl⟩ := hg
  exact ⟨g', by rw [← hb0]; exact hgy⟩

theorem y322_normalCore_eq_ker :
    y322H.normalCore = y322HAct.ker := by
  have := y322.1
  exact normalCore_eq_ker_of_transitive y322HAct ⟨0, by norm_num⟩ y322H y322HAct_fix_H
    y322HAct_transitive (by rw [y322H_card, card_y322, Nat.card_fin])

theorem y322HAct_range_card_ge :
    4585351680 ≤ Nat.card y322HAct.range := by
  have h := chainSizes_prod_le_card y322HAct_check.2.2.2.1
  rw [y322HAct_check.2.2.2.2.1, ← range_y322HAct] at h
  have : ([3159, 288, 35, 12, 3, 2, 2] : List ℕ).prod = 4585351680 := by norm_num
  omega

theorem y322HAct_ker_card_le :
    Nat.card y322HAct.ker ≤ 2 := by
  have := y322.1
  have h1 := y322HAct.ker.card_mul_index
  rw [Subgroup.index_ker, card_y322] at h1
  have h2 := y322HAct_range_card_ge
  by_contra hcon
  have h3 := Nat.mul_le_mul (Nat.not_le.1 hcon) h2
  omega

theorem y322F1_mem_H : y322F1 ∈ y322H := by
  have key : ∀ w : List ℕ, (∀ c ∈ w, c < 7) → evalWord (yGen 3 2 2) w ∈ y322H := by
    intro w
    induction w with
    | nil => intro _; exact y322H.one_mem
    | cons c w ih =>
      intro hw
      rw [evalWord_cons]
      exact y322H.mul_mem (Subgroup.subset_closure ⟨c, hw c (by simp), rfl⟩)
        (ih fun d hd => hw d (by simp [hd]))
  exact key y322WordF1 (by decide)

theorem y322F1_mem_normalCore :
    y322F1 ∈ y322H.normalCore := by
  intro b
  rw [(Subgroup.mem_center_iff.1 y322F1_mem_center b)]
  simpa using y322F1_mem_H

theorem y322_normalCore :
    y322H.normalCore = Subgroup.zpowers y322F1 := by
  have := y322.1
  have hle : Subgroup.zpowers y322F1 ≤ y322H.normalCore := by
    rw [Subgroup.zpowers_le]
    exact y322F1_mem_normalCore
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, y322F1_orderOf, y322_normalCore_eq_ker]
  exact y322HAct_ker_card_le

theorem y322_ker_toPermHom :
    (MulAction.toPermHom (YGroup 3 2 2) (YGroup 3 2 2 ⧸ y322H)).ker = Subgroup.zpowers y322F1 := by
  rw [← Subgroup.normalCore_eq_ker]
  exact y322_normalCore

theorem y322_central_word_equality :
    Function.Injective (yHom (shiftAt 6) rels_y321_y322) ∧
    y322H.index = 3159 ∧
    Nat.card (YGroup 3 2 2) = 9170703360 ∧
    y322H.normalCore = Subgroup.zpowers y322F1 ∧
    y322F1 ∈ Subgroup.center (YGroup 3 2 2) ∧
    y322F1 = y322F2 ∧
    orderOf y322F1 = 2 ∧
    y322Parity y322F1 = Multiplicative.ofAdd 1 :=
  ⟨y322_yHom_injective, y322H_index, card_y322, y322_normalCore, y322F1_mem_center,
    y322F1_eq_F2, y322F1_orderOf, y322Parity_F1⟩

end CFSG.YGroups
