module

public import CFSG.YGroups.Model233F.RawChain
public import CFSG.YGroups.Exact.Y432
public import Certificates.Data.CFSGNative.YGroups.Model432FData
public import CFSG.YGroups.Model432FInputs
public import Certificates.Certificate10102
public meta import CFSG.YGroups.Defs
public meta import CFSG.YGroups.Exact.Y432
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.YGroups.Model432FData
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem y432F_check :
    y432FArrays.size = 10 ∧ ModelNative.permsOK 31671 y432FArrays = true ∧
    ModelNative.relatorsOK 31671 y432FArrays (yRels 4 3 2) = true ∧
    ModelNative.chainOK 31671 y432FArrays y432FWords y432FBase = true ∧
    ModelNative.chainSizes 31671 y432FArrays y432FWords y432FBase =
      [31671, 28160, 3159, 288, 35, 12, 3, 2, 2] :=
  Certificates.certificate10102.1

theorem y432C_check :
    y432CArrays.size = 9 ∧ Nat.card (arrClosure 31671 y432CArrays) = 47377612800 :=
  Certificates.certificate10102.2.1

theorem F432_check :
    eqA 31671 (ModelNative.evalW 31671 y432FArrays F432Word) (idA 31671) = true ∧
    eqA 31673 (ModelNative.evalW 31673 y432Arrays F432Word)
      (ModelNative.evalW 31673 y432Arrays F432AltWord) = true ∧
    eqA 31673 (ModelNative.evalW 31673 y432Arrays F432Word) (idA 31673) = false :=
  Certificates.certificate10102.2.2

@[expose] noncomputable def y432FGen (c : ℕ) : Equiv.Perm (Fin 31671) :=
  arrGen 31671 y432FArrays c

theorem y432F_relators :
    ∀ w ∈ yRels 4 3 2, evalWord y432FGen w = 1 :=
  evalWord_arrGen_eq_one y432F_check.2.1 y432F_check.2.2.1

theorem y432FGen_eq
    {c : ℕ} (hc : c < 10) : y432FGen c = permOfArr 31671 y432FArrays[c]! := by
  have hc' : c < y432FArrays.size := by rw [y432F_check.1]; exact hc
  rw [y432FGen, arrGen, ite_eq_left hc']

noncomputable def rho432F :
    YGroup 4 3 2 →* Equiv.Perm (Fin 31671) :=
  yModelHom y432FGen y432F_relators

theorem rho432F_yGen
    {c : ℕ} (hc : c < 10) : rho432F (yGen 4 3 2 c) = y432FGen c :=
  yModelHom_yGen hc

theorem rho432F_rep {c : ℕ} (hc : c < 10) :
    Rep 31671 y432FArrays[c]! (rho432F (yGen 4 3 2 c)) := by
  rw [rho432F_yGen hc]
  have h := rep_letterOf y432F_check.2.1 c
  rwa [ModelNative.letterOf, ite_eq_left (by have := y432F_check.1; omega)] at h

theorem range_rho432F :
    rho432F.range = arrClosure 31671 y432FArrays := by
  rw [rho432F, range_yModelHom, show y432FGen = arrGen 31671 y432FArrays from rfl,
    ← show y432FArrays.size = ngen 4 3 2 from y432F_check.1, arrGen_image_eq]
  rfl

theorem rho432F_evalWord (w : List ℕ) :
    rho432F (evalWord (yGen 4 3 2) w) = evalWord y432FGen w := by
  have hgen : ∀ c, rho432F (yGen 4 3 2 c) = y432FGen c := by
    intro c
    by_cases hc : c < 10
    · exact rho432F_yGen hc
    · rw [yGen_of_le (by simp only [ngen]; omega), map_one,
        y432FGen, arrGen_of_le (by rw [y432F_check.1]; omega)]
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, map_mul, ih, hgen, evalWord_cons]

private theorem evalWord_replicate_flatten_eq {G : Type*} [Group G] (g : ℕ → G) (w : List ℕ)
    (n : ℕ) : evalWord g (List.replicate n w).flatten = (evalWord g w) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, pow_succ', ← ih]
    simp [evalWord, List.map_append, List.prod_append]

@[expose] noncomputable def F432 : YGroup 4 3 2 :=
  (yGen 4 3 2 0 * yGen 4 3 2 5 * yGen 4 3 2 6 * yGen 4 3 2 7 * yGen 4 3 2 8 * yGen 4 3 2 9 *
    yGen 4 3 2 1) ^ 9

@[expose] noncomputable def F432Alt : YGroup 4 3 2 :=
  (yGen 4 3 2 0 * yGen 4 3 2 5 * yGen 4 3 2 6 * yGen 4 3 2 7 * yGen 4 3 2 1 * yGen 4 3 2 2 *
    yGen 4 3 2 8) ^ 9

theorem F432_eq_evalWord : F432 = evalWord (yGen 4 3 2) F432Word := by
  rw [F432Word, evalWord_replicate_flatten_eq, F432]
  simp only [evalWord_cons, evalWord_nil, mul_one, mul_assoc]

theorem F432Alt_eq_evalWord : F432Alt = evalWord (yGen 4 3 2) F432AltWord := by
  rw [F432AltWord, evalWord_replicate_flatten_eq, F432Alt]
  simp only [evalWord_cons, evalWord_nil, mul_one, mul_assoc]

theorem F432_mem_ker : F432 ∈ rho432F.ker := by
  rw [MonoidHom.mem_ker, F432_eq_evalWord, rho432F_evalWord]
  exact (evalWord_arrGen_eq_iff (n := 31671) (O := y432FArrays) y432F_check.2.1 F432Word []).2
    F432_check.1

theorem F432_ne_one :
    F432 ≠ 1 := by
  rw [F432_eq_evalWord, Ne, evalWord_yGen_432_eq_one_iff, F432_check.2.2]
  exact Bool.false_ne_true

theorem F432_eq_alt :
    F432 = F432Alt := by
  rw [F432_eq_evalWord, F432Alt_eq_evalWord, evalWord_yGen_432_eq_iff]
  exact F432_check.2.1

theorem finite_y432 :
    Finite (YGroup 4 3 2) :=
  Nat.finite_of_card_ne_zero (by rw [card_y432]; norm_num)

theorem card_range_and_ker_rho432F :
    Nat.card rho432F.range = 4089470473293004800 ∧ Nat.card rho432F.ker = 2 := by
  have hfin := finite_y432
  have hlow : 4089470473293004800 ≤ Nat.card rho432F.range := by
    have h := chainSizes_prod_le_card y432F_check.2.2.2.1
    rw [y432F_check.2.2.2.2, ← range_rho432F] at h
    simpa using h
  have hker : 1 < Nat.card rho432F.ker := by
    rw [Subgroup.one_lt_card_iff_ne_bot, Ne, Subgroup.eq_bot_iff_forall]
    intro h
    exact F432_ne_one (h _ F432_mem_ker)
  have hmul := Subgroup.card_ker_mul_card_range rho432F
  rw [card_y432] at hmul
  have h2 : Nat.card rho432F.ker = 2 := by
    by_contra hne
    have h3 : 3 ≤ Nat.card rho432F.ker := by omega
    have : 3 * 4089470473293004800 ≤ Nat.card rho432F.ker * Nat.card rho432F.range :=
      Nat.mul_le_mul h3 hlow
    omega
  rw [h2] at hmul
  exact ⟨by omega, h2⟩

theorem card_range_rho432F :
    Nat.card rho432F.range = 4089470473293004800 :=
  card_range_and_ker_rho432F.1

theorem card_ker_rho432F :
    Nat.card rho432F.ker = 2 := card_range_and_ker_rho432F.2

theorem ker_rho432F_eq :
    rho432F.ker = Subgroup.zpowers F432 := by
  have hfin := finite_y432
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact F432_mem_ker
  · rw [card_ker_rho432F]
    have h : 1 < Nat.card (Subgroup.zpowers F432) := by
      rw [Subgroup.one_lt_card_iff_ne_bot, Ne, Subgroup.zpowers_eq_bot]
      exact F432_ne_one
    omega

@[expose] def Ctil432 : Subgroup (YGroup 4 3 2) :=
  Subgroup.closure (yGen 4 3 2 '' {c | c < 10 ∧ c ≠ 9})

theorem yGen_mem_ctil432 {c : ℕ} (hc : c < 10) (hc9 : c ≠ 9) : yGen 4 3 2 c ∈ Ctil432 :=
  Subgroup.subset_closure ⟨c, ⟨hc, hc9⟩, rfl⟩

theorem evalWord_mem_ctil432 {w : List ℕ} (hw : ∀ c ∈ w, c < 10 ∧ c ≠ 9) :
    evalWord (yGen 4 3 2) w ∈ Ctil432 := by
  induction w with
  | nil => exact Ctil432.one_mem
  | cons c w ih =>
    rw [evalWord_cons]
    exact Ctil432.mul_mem (yGen_mem_ctil432 (hw c List.mem_cons_self).1
      (hw c List.mem_cons_self).2) (ih fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))

theorem F432_mem_ctil432 :
    F432 ∈ Ctil432 := by
  rw [F432_eq_alt, F432Alt_eq_evalWord]
  refine evalWord_mem_ctil432 fun c hc => ?_
  simp only [F432AltWord, List.mem_flatten, List.mem_replicate] at hc
  obtain ⟨l, ⟨_, rfl⟩, hcl⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  omega

theorem ker_rho432F_le_ctil :
    rho432F.ker ≤ Ctil432 := by
  rw [ker_rho432F_eq, Subgroup.zpowers_le]
  exact F432_mem_ctil432

theorem y432CArrays_getElem {k : ℕ} (hk : k < 9) : y432CArrays[k]! = y432FArrays[k]! := by
  interval_cases k <;> rfl

theorem map_ctil432_rho432F :
    Ctil432.map rho432F = arrClosure 31671 y432CArrays := by
  rw [Ctil432, MonoidHom.map_closure, Set.image_image]
  unfold arrClosure
  congr 1
  ext g
  rw [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, ⟨hc, hc9⟩, rfl⟩
    have hk : c < 9 := by omega
    refine ⟨c, by rw [y432C_check.1]; exact hk, ?_⟩
    show permOfArr 31671 y432CArrays[c]! = rho432F (yGen 4 3 2 c)
    rw [y432CArrays_getElem hk, rho432F_yGen hc, y432FGen_eq hc]
  · rintro ⟨k, hk, rfl⟩
    have hk9 : k < 9 := by rw [y432C_check.1] at hk; exact hk
    refine ⟨k, ⟨by omega, by omega⟩, ?_⟩
    show rho432F (yGen 4 3 2 k) = permOfArr 31671 y432CArrays[k]!
    rw [rho432F_yGen (by omega), y432FGen_eq (by omega), y432CArrays_getElem hk9]

theorem card_map_ctil432_rho432F :
    Nat.card (Ctil432.map rho432F) = 47377612800 := by
  rw [map_ctil432_rho432F]
  exact y432C_check.2

theorem index_ctil432 :
    Ctil432.index = 86316516 := by
  have h1 := (Ctil432.map rho432F).card_mul_index
  have h2 := rho432F.range.card_mul_index
  have h3 := Ctil432.index_map rho432F
  rw [sup_eq_left.2 ker_rho432F_le_ctil] at h3
  rw [card_map_ctil432_rho432F] at h1
  rw [card_range_rho432F] at h2
  have hR : rho432F.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : (47377612800 * Ctil432.index) * rho432F.range.index =
      4089470473293004800 * rho432F.range.index := by
    calc (47377612800 * Ctil432.index) * rho432F.range.index
        = 47377612800 * (Ctil432.index * rho432F.range.index) := by ring
      _ = 47377612800 * (Ctil432.map rho432F).index := by rw [h3]
      _ = Nat.card (Equiv.Perm (Fin 31671)) := h1
      _ = 4089470473293004800 * rho432F.range.index := h2.symm
  have h5 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hR) h4
  omega

end CFSG.YGroups
