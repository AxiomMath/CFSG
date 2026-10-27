module

public import CFSG.YGroups.Y433.TwoCentral
public import CFSG.Sporadic.Bridge.Common
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Sporadic.Bridge.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.BabyMonster
import all TauCeti.GroupTheory.Presentation.Coxeter
import all TauCeti.GroupTheory.Presentation.GroupPresentation
import all TauCeti.GroupTheory.Presentation.Relator

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.YGroups CFSG.Certificates.CosetEnumeration TauCeti

abbrev tcPres : GroupPresentation := TauCeti.Sporadic.BabyMonster.presentation

@[expose] def tcIndex (l : ℕ) : ℕ := [4, 3, 2, 1, 0, 5, 6, 7, 8, 9, 10].getD l 0

noncomputable abbrev tB433 (i : ℕ) : tcPres.Group := presGen tcPres i

@[expose] def IsRelRotation (v : List (ℕ × Bool)) : Prop :=
  ∃ r ∈ tcPres.relatorLetters, ∃ k ∈ List.range (r.length + 1), r.rotate k = v

instance (v : List (ℕ × Bool)) : Decidable (IsRelRotation v) := by
  unfold IsRelRotation; infer_instance

theorem wordProd_presGen_of_mem (P : GroupPresentation) {v : List (ℕ × Bool)}
    (hv : v ∈ P.relatorLetters) : wordProd (presGen P) v = 1 := by
  rw [GroupPresentation.relatorLetters_def, List.mem_map] at hv
  obtain ⟨r, hr, rfl⟩ := hv
  have hlift : FreeGroup.lift (fun i : Fin P.generatorCount => presGen P i.val) =
      PresentedGroup.mk P.relatorSet := by
    ext i
    simp only [presGen, Fin.is_lt, ↓reduceDIte, Fin.eta, FreeGroup.lift_apply_of]
    rfl
  rw [← lift_mk, hlift]
  exact PresentedGroup.one_of_mem (relators_mem P r hr)

theorem wordProd_of_isRelRotation {v : List (ℕ × Bool)} (hv : IsRelRotation v) :
    wordProd tB433 v = 1 := by
  obtain ⟨r, hr, k, -, rfl⟩ := hv
  have h := wordProd_presGen_of_mem _ hr
  unfold wordProd at h ⊢
  rw [List.map_rotate]
  exact List.prod_rotate_eq_one_of_prod_eq_one h k

private theorem wordProd_flatten_replicate {G : Type*} [Group G] (x : ℕ → G) (v : List (ℕ × Bool))
    (k : ℕ) : wordProd x (List.replicate k v).flatten = wordProd x v ^ k := by
  induction k with
  | zero => simp [wordProd]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, pow_succ']
    unfold wordProd at ih ⊢
    rw [List.map_append, List.prod_append, ih]

noncomputable abbrev img (l : ℕ) : tcPres.Group := tB433 (tcIndex l)

theorem evalWord_img (w : List ℕ) :
    evalWord img w = wordProd tB433 (w.map fun l => (tcIndex l, true)) := by
  simp [evalWord, wordProd, List.map_map, Function.comp_def]

theorem relator_images :
    ∀ w ∈ yRels 4 3 3, IsRelRotation (w.map fun l => (tcIndex l, true)) := by
  decide +kernel

theorem img_rels : ∀ w ∈ yRels 4 3 3, evalWord img w = 1 := fun w hw => by
  rw [evalWord_img]
  exact wordProd_of_isRelRotation (relator_images w hw)

noncomputable def u433Hom : U433 →* tcPres.Group :=
  PresentedGroup.toGroup (f := fun c : Fin (ngen 4 3 3) => img c) (by
    rintro x ⟨w, hw, rfl⟩
    rw [lift_wordFG, evalWord_congr (g' := img)]
    · exact img_rels w hw
    · intro c hc
      simp [lt_ngen_of_mem_yRels hw c hc])

theorem u433Hom_yGen {c : ℕ} (hc : c < ngen 4 3 3) : u433Hom (yGen 4 3 3 c) = img c := by
  rw [yGen_of_lt hc, u433Hom, PresentedGroup.toGroup.of]

theorem u433Hom_evalWord : ∀ w : List ℕ, (∀ c ∈ w, c < ngen 4 3 3) →
    u433Hom (evalWord (yGen 4 3 3) w) = evalWord img w
  | [], _ => by simp
  | c :: w, hw => by
    rw [evalWord_cons, map_mul, u433Hom_yGen (hw c List.mem_cons_self),
      u433Hom_evalWord w (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')), evalWord_cons]

theorem commute_of_involutions {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : x * y * (x * y) = 1) : Commute x y := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h
    _ = y * x := by rw [mul_inv_rev, hx', hy']

theorem tB433_commute (i j : ℕ) (h : (IsRelRotation [(i, true), (i, true)] ∧
    IsRelRotation [(j, true), (j, true)]) ∧
    IsRelRotation [(i, true), (j, true), (i, true), (j, true)]) :
    Commute (tB433 i) (tB433 j) := by
  obtain ⟨⟨hi, hj⟩, hij⟩ := h
  refine commute_of_involutions ?_ ?_ ?_
  · simpa [wordProd] using wordProd_of_isRelRotation hi
  · simpa [wordProd] using wordProd_of_isRelRotation hj
  · simpa [wordProd, mul_assoc] using wordProd_of_isRelRotation hij

theorem extra_one :
    (tB433 4 * tB433 3 * tB433 2 * tB433 5 * tB433 6 * tB433 7 * tB433 8) ^ 9 = 1 := by
  have h : IsRelRotation ((List.replicate 9 [(4, true), (3, true), (2, true), (5, true),
      (6, true), (7, true), (8, true)]).flatten) := by decide +kernel
  have := wordProd_of_isRelRotation h
  rw [wordProd_flatten_replicate] at this
  simpa [wordProd, mul_assoc] using this

theorem extra_two :
    (tB433 4 * tB433 3 * tB433 2 * tB433 5 * tB433 8 * tB433 9 * tB433 10) ^ 9 = 1 := by
  have h : IsRelRotation ((List.replicate 9 [(4, true), (3, true), (2, true), (5, true),
      (8, true), (9, true), (10, true)]).flatten) := by decide +kernel
  have := wordProd_of_isRelRotation h
  rw [wordProd_flatten_replicate] at this
  simpa [wordProd, mul_assoc] using this

theorem commute_213 : ∀ i ∈ [5, 6, 7], ∀ j ∈ [3, 2], (IsRelRotation [(i, true), (i, true)] ∧
    IsRelRotation [(j, true), (j, true)]) ∧
    IsRelRotation [(i, true), (j, true), (i, true), (j, true)] := by
  decide +kernel

theorem commute_312 : ∀ i ∈ [8, 9, 10], ∀ j ∈ [3, 2, 5], (IsRelRotation [(i, true), (i, true)] ∧
    IsRelRotation [(j, true), (j, true)]) ∧
    IsRelRotation [(i, true), (j, true), (i, true), (j, true)] := by
  decide +kernel

theorem u433Hom_F213 : u433Hom (F433 2 1 3) = 1 := by
  have c : ∀ i ∈ [5, 6, 7], ∀ j ∈ [3, 2], Commute (tB433 i) (tB433 j) :=
    fun i hi j hj => tB433_commute i j (commute_213 i hi j hj)
  have hseg (j : ℕ) (hj : j ∈ [3, 2]) : Commute (tB433 5 * tB433 6 * tB433 7) (tB433 j) :=
    ((c 5 (by simp) j hj).mul_left (c 6 (by simp) j hj)).mul_left (c 7 (by simp) j hj)
  have hs : Commute (tB433 5 * tB433 6 * tB433 7) (tB433 3 * tB433 2) :=
    (hseg 3 (by simp)).mul_right (hseg 2 (by simp))
  have e : evalWord img [0, U433.armStart 2, U433.armStart 2 + 1, U433.armStart 2 + 2,
      U433.armStart 1, U433.armStart 1 + 1, U433.armStart 3] =
      tB433 4 * ((tB433 5 * tB433 6 * tB433 7) * (tB433 3 * tB433 2)) * tB433 8 := by
    simp only [evalWord, U433.armStart, Nat.reduceAdd, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, img, tcIndex, List.getD_cons_succ,
      List.getD_cons_zero, mul_assoc]
  have e' : tB433 4 * ((tB433 3 * tB433 2) * (tB433 5 * tB433 6 * tB433 7)) * tB433 8 =
      tB433 4 * tB433 3 * tB433 2 * tB433 5 * tB433 6 * tB433 7 * tB433 8 := by
    simp only [mul_assoc]
  rw [F433_eq_evalWord, map_pow, u433Hom_evalWord _ (by decide), e, hs.eq, e', extra_one]

theorem u433Hom_F312 : u433Hom (F433 3 1 2) = 1 := by
  have c : ∀ i ∈ [8, 9, 10], ∀ j ∈ [3, 2, 5], Commute (tB433 i) (tB433 j) :=
    fun i hi j hj => tB433_commute i j (commute_312 i hi j hj)
  have hseg (j : ℕ) (hj : j ∈ [3, 2, 5]) : Commute (tB433 8 * tB433 9 * tB433 10) (tB433 j) :=
    ((c 8 (by simp) j hj).mul_left (c 9 (by simp) j hj)).mul_left (c 10 (by simp) j hj)
  have hs : Commute (tB433 8 * tB433 9 * tB433 10) (tB433 3 * tB433 2 * tB433 5) :=
    ((hseg 3 (by simp)).mul_right (hseg 2 (by simp))).mul_right (hseg 5 (by simp))
  have e : evalWord img [0, U433.armStart 3, U433.armStart 3 + 1, U433.armStart 3 + 2,
      U433.armStart 1, U433.armStart 1 + 1, U433.armStart 2] =
      tB433 4 * ((tB433 8 * tB433 9 * tB433 10) * (tB433 3 * tB433 2 * tB433 5)) := by
    simp only [evalWord, U433.armStart, Nat.reduceAdd, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, img, tcIndex, List.getD_cons_succ,
      List.getD_cons_zero, mul_assoc]
  have e' : tB433 4 * ((tB433 3 * tB433 2 * tB433 5) * (tB433 8 * tB433 9 * tB433 10)) =
      tB433 4 * tB433 3 * tB433 2 * tB433 5 * tB433 8 * tB433 9 * tB433 10 := by
    simp only [mul_assoc]
  rw [F433_eq_evalWord, map_pow, u433Hom_evalWord _ (by decide), e, hs.eq, e', extra_two]

theorem normalClosure_le_ker :
    Subgroup.normalClosure {F433 2 1 3, F433 3 1 2} ≤ u433Hom.ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x (rfl | rfl)
  · exact u433Hom_F213
  · exact u433Hom_F312

noncomputable def b433Hom : B433 →* tcPres.Group :=
  QuotientGroup.lift _ u433Hom normalClosure_le_ker

@[expose] def y433Letter (i : ℕ) : ℕ := [4, 3, 2, 1, 0, 5, 6, 7, 8, 9, 10].getD i 0

theorem y433Letter_spec : ∀ i < 11, y433Letter i < ngen 4 3 3 ∧ tcIndex (y433Letter i) = i := by
  decide

theorem b433Hom_surjective : Function.Surjective b433Hom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hi : i.val < 11 := i.isLt
  obtain ⟨hl, hidx⟩ := y433Letter_spec i.val hi
  refine ⟨QuotientGroup.mk (yGen 4 3 3 (y433Letter i.val)), ?_⟩
  rw [b433Hom, QuotientGroup.lift_mk, u433Hom_yGen hl, img, hidx, tB433, presGen,
    dite_eq_left_of_eq_true (eq_true i.isLt)]

private theorem presentation_eq : SporadicName.B.presentation = tcPres := rfl

theorem finite_card_le_of_B433 {N : ℕ} (hfin : Finite B433) (hcard : Nat.card B433 ≤ N) :
    Finite SporadicName.B.Group ∧ Nat.card SporadicName.B.Group ≤ N := by
  show Finite SporadicName.B.presentation.Group ∧ Nat.card SporadicName.B.presentation.Group ≤ N
  rw [presentation_eq]
  exact ⟨Finite.of_surjective _ b433Hom_surjective,
    (Nat.card_le_card_of_surjective _ b433Hom_surjective).trans hcard⟩

end CFSG.Sporadic.Bridge.B
