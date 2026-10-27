module

public import CFSG.Sporadic.Th.Recog.GlueTwist
public import CFSG.Sporadic.Th.Recog.CentS
public import CFSG.Sporadic.Th.Recog.Collapse
public import CFSG.Sporadic.Th.Recog.Placement
public import CFSG.Sporadic.Th.Recog.Core
public import CFSG.Sporadic.Th.RecognitionHSW
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NIndAux

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Recognition.PresentedWords
open CFSG.GH74.QTGen4.Recog.G23 (Ghat ghat_card)

theorem mem_normalizer_commutator_centralizer_of_inv {A : Type*} [Group A] {s u : A}
    (hu : u * s * u⁻¹ = s⁻¹) :
    u ∈ Subgroup.normalizer ((⁅Subgroup.centralizer ({s} : Set A),
      Subgroup.centralizer ({s} : Set A)⁆ : Subgroup A) : Set A) := by
  have hC : u ∈ Subgroup.normalizer (Subgroup.centralizer ({s} : Set A) : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_centralizer_singleton_iff]
    have key : Commute h s ↔ Commute (u * h * u⁻¹) (u * s * u⁻¹) := (Commute.conj_iff u).symm
    rw [hu, Commute.inv_right_iff] at key
    exact key
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hC ⊢
  rw [Subgroup.map_commutator, hC]

variable {G : Type} [Group G] [Finite G]

section Tuple


theorem lettersM_zero : lettersM 0 = zM :=
  Subtype.ext ((coe_lettersM 0 (by decide)).trans (hswJ_zero.trans Max3.z_eq_a.symm))

theorem lettersM_five : lettersM 5 = sLetter :=
  Subtype.ext (coe_lettersM 5 (by decide))

@[expose] noncomputable def ThCore.glueTuple (C : ThCore G)
    (ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))) (i : Fin 8) : G :=
  if i = 1 then (ψ' (lettersY 1) : G) else (C.ψ (lettersM i) : G)

variable {C : ThCore G}
  {ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
    ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))}

theorem ThCore.glueTuple_one : C.glueTuple ψ' 1 = (ψ' (lettersY 1) : G) :=
  if_pos rfl

theorem ThCore.glueTuple_of_ne {i : Fin 8} (hi : i ≠ 1) :
    C.glueTuple ψ' i = (C.ψ (lettersM i) : G) :=
  if_neg hi

theorem ThCore.glueTuple_zero : C.glueTuple ψ' 0 = C.z := by
  rw [ThCore.glueTuple_of_ne (by decide), lettersM_zero, C.psi_z]

theorem ThCore.glueTuple_bfree {w : List (Fin 8 × Bool)} (hw : w ∈ bfree) :
    wprod (C.glueTuple ψ') w = 1 := by
  rw [wprod_congr_letters (y := fun i => C.psiG (lettersM i))
      (fun l hl => ThCore.glueTuple_of_ne ((mem_bfree hw).2 l hl)),
    ← map_wprod, wprod_lettersM_bfree hw, map_one]

theorem ThCore.glueTuple_subst {k : Twist}
    (hlet : ∀ j : Fin 6,
      (ψ' (lettersY (dLet j)) : G) = wprod (fun i => (C.ψ (lettersM i) : G)) (wY k j))
    {w : List (Fin 8 × Bool)} (hw : ∀ l ∈ w, l.1 ≠ 5) :
    wprod (fun i => wprod (C.glueTuple ψ') ((hsK k).getD i [])) w =
      (ψ' (wprod lettersY w) : G) := by
  have hY : (ψ' (wprod lettersY w) : G) = wprod (fun i => (ψ' (lettersY i) : G)) w :=
    map_wprod ((Subgroup.subtype _).comp
      (ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) →*
        ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G)))) lettersY w
  rw [hY]
  apply wprod_congr_letters
  intro l hl
  by_cases h1 : l.1 = 1
  · rw [h1, hsK_getD_one, wprod_cons, wprod_nil, mul_one, if_pos rfl, ThCore.glueTuple_one]
  · obtain ⟨j, hj⟩ := exists_dLet l.1 h1 (hw l hl)
    rw [← hj, hsK_getD_dLet, hlet j]
    exact wprod_congr_letters fun l' hl' => ThCore.glueTuple_of_ne (wY_letters k j l' hl').1

theorem ThCore.glueTuple_brel {k : Twist}
    (hlet : ∀ j : Fin 6,
      (ψ' (lettersY (dLet j)) : G) = wprod (fun i => (C.ψ (lettersM i) : G)) (wY k j))
    {w : List (Fin 8 × Bool)} (hw : w ∈ brel) :
    wprod (fun i => wprod (C.glueTuple ψ') ((hsK k).getD i [])) w = 1 := by
  rw [ThCore.glueTuple_subst hlet (mem_brel hw).2, wprod_lettersY_brel hw, map_one,
    Subgroup.coe_one]

theorem ThCore.relators_of_good
    (hlet : ∀ j : Fin 6,
      (ψ' (lettersY (dLet j)) : G) = wprod (fun i => (C.ψ (lettersM i) : G)) (wY .id j))
    (hsb : Commute (C.ψ sLetter : G) (ψ' (lettersY 1) : G)) :
    ∀ w ∈ R0', wprod (C.glueTuple ψ') w = 1 := by
  have hinv : ∀ i : Fin 8, i.val < 5 → i ≠ 1 →
      (C.glueTuple ψ' i)⁻¹ = C.glueTuple ψ' i := by
    intro i hi hi1
    rw [ThCore.glueTuple_of_ne hi1]
    apply inv_eq_of_mul_eq_one_right
    have h : lettersM i * lettersM i = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, coe_lettersM i hi1, Subgroup.coe_one]
      exact hswJ_mul_self i hi
    rw [← Subgroup.coe_mul, ← map_mul, h, map_one, Subgroup.coe_one]
  have hid : ∀ i : Fin 8,
      wprod (C.glueTuple ψ') ((hsK .id).getD i []) = C.glueTuple ψ' i := by
    intro i
    fin_cases i <;>
      simp only [hsK, wY, List.getD_cons_succ, List.getD_cons_zero, wprod_cons, wprod_nil,
        mul_one, if_true, Bool.false_eq_true, if_false, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, Fin.isValue] <;>
      first
        | rfl
        | exact hinv _ (by decide) (by decide)
  refine hsw_of_parts _ (fun w hw => ThCore.glueTuple_bfree hw) (fun w hw => ?_) ?_
  · calc wprod (C.glueTuple ψ') w
        = wprod (fun i => wprod (C.glueTuple ψ') ((hsK .id).getD i [])) w :=
          wprod_congr_letters fun l _ => (hid l.1).symm
      _ = 1 := ThCore.glueTuple_brel hlet hw
  · have h5 : wprod (C.glueTuple ψ') [(5, true)] = (C.ψ sLetter : G) := by
      rw [wprod_cons, wprod_nil, mul_one, if_pos rfl, ThCore.glueTuple_of_ne (by decide),
        lettersM_five]
    have h1 : wprod (C.glueTuple ψ') [(1, true)] = (ψ' (lettersY 1) : G) := by
      rw [wprod_cons, wprod_nil, mul_one, if_pos rfl, ThCore.glueTuple_one]
    rw [sbWord, wprod_commWord, h5, h1, ← mul_inv_rev, mul_assoc, hsb.eq, inv_mul_cancel]

end Tuple

section Bad


variable {C : ThCore G}
  {ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
    ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))}

theorem ThCore.false_of_bad {k : Twist}
    (hlet : ∀ j : Fin 6,
      (ψ' (lettersY (dLet j)) : G) = wprod (fun i => (C.ψ (lettersM i) : G)) (wY k j))
    {i : Fin 2} (hc : (k, i) ≠ (.id, 0))
    (hcomm : ∀ j : Fin 2, Commute (C.ψ sLetter : G) (ψ' (wprod lettersY (xw (k, i) j)) : G)) :
    False := by
  have hx := collapseRels_of (k, i) (C.glueTuple ψ') (fun w hw => ThCore.glueTuple_bfree hw)
    (fun w hw => ThCore.glueTuple_brel hlet hw) fun j => by
      rw [wprod_substWord, ThCore.glueTuple_subst hlet (xw_letters (k, i) j),
        ThCore.glueTuple_of_ne (by decide), lettersM_five]
      exact hcomm j
  have hb := mem_closure_of_collapse (k, i) hc (C.glueTuple ψ') hx
  have hle : Subgroup.closure (C.glueTuple ψ' '' {j | j ≠ 1}) ≤
      Subgroup.centralizer ({C.z} : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, ThCore.glueTuple_of_ne hj]
    exact (C.ψ (lettersM j)).2
  have hbz := Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
  rw [ThCore.glueTuple_one] at hbz
  have ha : (ψ' (lettersY 0) : G) = C.z⁻¹ := by
    have h := hlet 0
    rw [(wY_eq k).1] at h
    simp only [wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, if_false, mul_one, lettersM_zero, C.psi_z] at h
    exact h
  apply hswJ_zero_not_comm_one
  have hab : lettersY 0 * lettersY 1 = lettersY 1 * lettersY 0 := by
    apply ψ'.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ha]
    exact (Commute.inv_right hbz).symm.eq
  have h := congrArg Subtype.val hab
  rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_lettersY 0 (by decide),
    coe_lettersY 1 (by decide)] at h

end Bad

section Place


theorem ThCore.exists_placement (C : ThCore G) (hMF : GlueMFacts) {k : Twist}
    {ψ' : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)) ≃*
      ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G))}
    (hlet : ∀ j : Fin 6,
      (ψ' (lettersY (dLet j)) : G) = wprod (fun i => (C.ψ (lettersM i) : G)) (wY k j))
    (hKc : ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
      (y : ↥J) ∈ Subgroup.closure (Set.range lJ) ↔
        (ψ' y : G) ∈ ⁅Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G),
          Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G)⁆) :
    ∃ (i : Fin 2) (X : Subgroup ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))),
      (∀ y ∈ X, Commute (C.ψ sLetter : G) (ψ' y : G)) ∧ lettersY 2 ∈ X ∧
        lettersY 3 * lettersY 2 * lettersY 3 ∈ X ∧
        ∀ (k' : Twist) (j : Fin 2), wprod lettersY (xw (k', i) j) ∈ X := by
  classical
  obtain ⟨K, -, -, -, hKeq, ⟨eK⟩⟩ := C.centralizer_t_split hMF
  have hK : Nat.card ↥⁅Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G),
      Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G)⁆ = 7371 * 576 := by
    rw [← hKeq, Nat.card_congr eK.toEquiv, ghat_card]
  obtain ⟨L, hLs, -, -, hLeq, ⟨eL⟩⟩ := centralizer_s_split C sLetter tLetter orderOf_sLetter
    orderOf_tLetter tLetter_conj_sLetter hMF.seven D8M D8M_le_centralizer_s hMF.card_D8
    D8M_comm_t hK
  have htL := t_centralizes_L C sLetter tLetter orderOf_sLetter orderOf_tLetter
    tLetter_conj_sLetter hMF.seven D8M D8M_le_centralizer_s hMF.card_D8 D8M_comm_t
  have hD8L := psi_D8_le_L C sLetter orderOf_sLetter hMF.seven D8M D8M_le_centralizer_s
    hMF.card_D8
  rw [← hLeq] at htL hD8L
  have hLT : L ≤ Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (htL x hx).eq.symm
  have hLK : L ≤ ⁅Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G),
      Subgroup.centralizer ({(C.ψ tLetter : G)} : Set G)⁆ := by
    rw [← CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN.commutator_self_of_iso eL]
    exact Subgroup.commutator_mono hLT hLT
  have hLY : L ≤ Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G) :=
    hLT.trans (centralizer_le_normalizer_zpowers _)
  let g : ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G)) →* ↥J :=
    (Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)).subtype.comp
      (ψ'.symm : ↥(Subgroup.normalizer (Subgroup.zpowers (C.ψ tLetter : G) : Set G)) →*
        ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)))
  have hg : Function.Injective g := fun a b h => ψ'.symm.injective (Subtype.ext h)
  let XJ : Subgroup ↥J := (L.subgroupOf _).map g
  have hmem : ∀ y : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J)),
      (y : ↥J) ∈ XJ ↔ (ψ' y : G) ∈ L := by
    intro y
    constructor
    · rintro ⟨l, hl, hly⟩
      have h : ψ'.symm l = y := Subtype.ext hly
      rw [← h, MulEquiv.apply_symm_apply]
      exact hl
    · intro h
      exact ⟨ψ' y, h, congrArg Subtype.val (ψ'.symm_apply_apply y)⟩
  have hX0 : XJ ≤ Subgroup.closure (Set.range lJ) := by
    rintro _ ⟨l, hl, rfl⟩
    refine (hKc (ψ'.symm l)).mpr ?_
    rw [MulEquiv.apply_symm_apply]
    exact hLK hl
  have hX : Nonempty (↥XJ ≃* GL (Fin 3) (ZMod 2)) :=
    ⟨((L.subgroupOf _).equivMapOfInjective g hg).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hLY).trans eL)⟩
  have hc' : (ψ' (lettersY 2) : G) = (C.ψ (lettersM 2) : G)⁻¹ := by
    have h := hlet 1
    rw [(wY_eq k).2.1] at h
    simp only [wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, if_false, mul_one] at h
    exact h
  have hd' : (ψ' (lettersY 3) : G) = (C.ψ (lettersM 3) : G)⁻¹ := by
    have h := hlet 2
    rw [(wY_eq k).2.2.1] at h
    simp only [wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, if_false, mul_one] at h
    exact h
  have hcM : lettersM 2 ∈ D8M := by
    rw [D8M]
    apply Subgroup.subset_closure
    left
    exact Subtype.ext (coe_lettersM 2 (by decide))
  have hdcdM : lettersM 3 * lettersM 2 * lettersM 3 ∈ D8M := by
    rw [D8M]
    apply Subgroup.subset_closure
    right
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_lettersM 3 (by decide),
      coe_lettersM 2 (by decide)]
  have hcX : hswJ 2 ∈ XJ := by
    rw [← coe_lettersY 2 (by decide), hmem, hc']
    exact L.inv_mem (hD8L _ hcM)
  have hdcdX : hswJ 3 * hswJ 2 * hswJ 3 ∈ XJ := by
    have e : hswJ 3 * hswJ 2 * hswJ 3 =
        ((lettersY 3 * lettersY 2 * lettersY 3 :
          ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : ↥J) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_lettersY 3 (by decide),
        coe_lettersY 2 (by decide)]
    rw [e, hmem, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hc', hd']
    have h := L.inv_mem (hD8L _ hdcdM)
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul] at h
    have e' : (C.ψ (lettersM 3) : G)⁻¹ * (C.ψ (lettersM 2) : G)⁻¹ * (C.ψ (lettersM 3) : G)⁻¹ =
        ((C.ψ (lettersM 3) : G) * (C.ψ (lettersM 2) : G) * (C.ψ (lettersM 3) : G))⁻¹ := by
      group
    rw [e']
    exact h
  have hdN : (C.ψ (lettersM 3) : G) ∈ Subgroup.normalizer (L : Set G) := by
    rw [hLeq]
    apply mem_normalizer_commutator_centralizer_of_inv
    have h : lettersM 3 * sLetter * (lettersM 3)⁻¹ = sLetter⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
        coe_lettersM 3 (by decide)]
      exact hswJ_three_conj_five
    have h' := congrArg C.psiG h
    rw [map_mul, map_mul, map_inv, map_inv] at h'
    exact h'
  have hdX : ∀ x ∈ XJ, hswJ 3 * x * (hswJ 3)⁻¹ ∈ XJ := by
    rintro _ ⟨l, hl, rfl⟩
    have e : hswJ 3 * g l * (hswJ 3)⁻¹ =
        ((lettersY 3 * ψ'.symm l * (lettersY 3)⁻¹ :
          ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : ↥J) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_lettersY 3 (by decide)]
      rfl
    rw [e, hmem, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hd']
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) _).mp hl
  obtain ⟨i, hi⟩ := placement XJ hX0 hX hcX hdcdX hdX
  refine ⟨i, XJ.subgroupOf _, fun y hy => ?_, ?_, ?_, fun k' j => ?_⟩
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLs ((hmem y).mp hy))).symm
  · show ((lettersY 2 : ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : ↥J) ∈ XJ
    rw [coe_lettersY 2 (by decide)]
    exact hcX
  · show ((lettersY 3 * lettersY 2 * lettersY 3 :
      ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : ↥J) ∈ XJ
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_lettersY 3 (by decide),
      coe_lettersY 2 (by decide)]
    exact hdcdX
  · show ((wprod lettersY (xw (k', i) j) :
      ↥(Subgroup.normalizer (Subgroup.zpowers (hswJ 6) : Set ↥J))) : ↥J) ∈ XJ
    rw [coe_wprod_lettersY (xw_letters (k', i) j)]
    exact hi k' j

end Place

section Assembly


theorem ThCore.exists_hswTuple (C : ThCore G) (hMF : GlueMFacts) :
    ∃ x : Fin 8 → G, x 0 = C.z ∧ ∀ w ∈ R0', wprod x w = 1 := by
  obtain ⟨k, ψ', hlet, hKc⟩ := C.exists_glue hMF
  obtain ⟨i, X, hXs, hc, hdcd, hxw⟩ := C.exists_placement hMF hlet hKc
  by_cases hgood : (k, i) = (.id, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hgood
    have hb : lettersY 1 ∈ X := by
      have e : lettersY 1 = lettersY 3 * lettersY 2 * lettersY 3 * lettersY 2 *
          wprod lettersY (xw (.id, 0) 1) * (lettersY 2)⁻¹ := by
        simp only [xw, wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          Bool.false_eq_true, if_false, if_true, mul_one]
        group
      rw [e]
      exact X.mul_mem (X.mul_mem (X.mul_mem hdcd hc) (hxw .id 1)) (X.inv_mem hc)
    exact ⟨C.glueTuple ψ', ThCore.glueTuple_zero, ThCore.relators_of_good hlet (hXs _ hb)⟩
  · exact (ThCore.false_of_bad hlet hgood fun j => hXs _ (hxw k j)).elim

theorem ThCore.isSporadic_th [IsSimpleGroup G] (C : ThCore G) (hMF : GlueMFacts) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Th := by
  obtain ⟨x, hx0, hx⟩ := C.exists_hswTuple hMF
  set img : ℕ → G := fun i => if h : i < 8 then x ⟨i, h⟩ else 1 with himg_def
  have himg : img 0 = C.z := by
    show (if h : (0 : ℕ) < 8 then x ⟨0, h⟩ else 1) = C.z
    rw [dif_pos (by norm_num)]
    exact hx0
  refine isSporadic_th_of_hswTuple img ((th_relatorLetters_iff x).mpr hx) ?_ ?_
  · rw [himg]
    intro h
    have h2 := C.orderOf_z
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · rw [himg, ← Nat.card_congr C.ψ.toEquiv, Max3.card_M]

end Assembly

section Setting


theorem isSporadic_th_of_setting [IsSimpleGroup G] (S : ThSetting G) (hBB : A9FaithfulDimEight)
    (hMF : GlueMFacts) : CFSG.Blueprint.NativeSporadic.IsSporadic G .Th :=
  (S.core hBB).isSporadic_th hMF

end Setting

end CFSG.Sporadic.Th.Recog
