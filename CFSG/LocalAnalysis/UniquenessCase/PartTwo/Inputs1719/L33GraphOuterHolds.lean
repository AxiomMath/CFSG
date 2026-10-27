module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33GraphOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33GraphOuterW
public import Certificates.Certificate5176
import CFSG.GH74.KGroups.L33
import CFSG.Quasithin.Vol2.Ch1Sec3Basic
import CFSG.GroupTheory.PermutesPullback
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Certificates CFSG.Sporadic.Schreier
open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin
open CFSG.Blueprint (LieModel)
open scoped Pointwise

private def l33g_img (g : Equiv.Perm (Fin 26)) : List ℕ := List.ofFn fun i => (g i : ℕ)

private def l33g_comp (p q : List ℕ) : List ℕ := q.map fun j => p.getD j 0

private theorem l33g_img_injective : Function.Injective l33g_img := by
  intro g h hgh
  have h1 : (fun i => (g i : ℕ)) = fun i => (h i : ℕ) := List.ofFn_injective hgh
  ext i
  exact congrFun h1 i

private theorem l33g_img_mul (g h : Equiv.Perm (Fin 26)) :
    l33g_img (g * h) = l33g_comp (l33g_img g) (l33g_img h) := by
  simp only [l33g_img, l33g_comp, List.map_ofFn]
  congr 1
  funext i
  change (g (h i) : ℕ) = (List.ofFn fun i => (g i : ℕ)).getD (h i) 0
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (h i).isLt, Option.getD_some]

private def l33g_t : Equiv.Perm (Fin 26) := PA * PB * PA * sg0⁻¹ * PA * PB * PA

private def l33g_x : Equiv.Perm (Fin 26) :=
  PB⁻¹ * PA * PB⁻¹ * PA * PB * PA * PB⁻¹ * PA * PB⁻¹

private def l33g_S0List : List (Equiv.Perm (Fin 26)) :=
  parabolicS0List ++ parabolicS0List.map (· * l33g_t)

private def l33g_cT : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
   [0, 2, 1, 5, 4, 3, 7, 6, 8, 11, 10, 9, 12, 13, 21, 17, 16, 15, 20, 19, 18, 14, 22, 25, 24, 23],
   [1, 4, 7, 0, 3, 6, 2, 5, 8, 12, 11, 10, 9, 13, 16, 19, 14, 20, 17, 25, 23, 24, 15, 18, 21, 22],
   [1, 7, 4, 6, 3, 0, 5, 2, 8, 10, 11, 12, 9, 13, 24, 20, 14, 19, 23, 25, 17, 16, 15, 22, 21, 18],
   [2, 4, 6, 0, 5, 7, 1, 3, 8, 12, 9, 10, 11, 13, 16, 19, 21, 18, 15, 23, 25, 24, 17, 20, 14, 22],
   [2, 6, 4, 7, 5, 0, 3, 1, 8, 10, 9, 12, 11, 13, 24, 18, 21, 19, 25, 23, 15, 16, 17, 22, 14, 20],
   [3, 0, 6, 4, 1, 7, 5, 2, 8, 12, 11, 10, 9, 13, 16, 22, 14, 18, 23, 15, 17, 24, 25, 20, 21, 19],
   [3, 6, 0, 7, 1, 4, 2, 5, 8, 10, 11, 12, 9, 13, 24, 18, 14, 22, 17, 15, 23, 16, 25, 19, 21, 20],
   [4, 3, 5, 1, 0, 2, 7, 6, 8, 9, 10, 11, 12, 13, 14, 25, 16, 23, 20, 22, 18, 21, 19, 17, 24, 15],
   [4, 5, 3, 2, 0, 1, 6, 7, 8, 11, 10, 9, 12, 13, 21, 23, 16, 25, 18, 22, 20, 14, 19, 15, 24, 17],
   [5, 0, 7, 4, 2, 6, 3, 1, 8, 12, 9, 10, 11, 13, 16, 22, 21, 20, 25, 17, 15, 24, 23, 18, 14, 19],
   [5, 7, 0, 6, 2, 4, 1, 3, 8, 10, 9, 12, 11, 13, 24, 20, 21, 22, 15, 17, 25, 16, 23, 19, 14, 18],
   [6, 1, 5, 3, 7, 2, 0, 4, 8, 9, 12, 11, 10, 13, 14, 15, 24, 23, 22, 20, 19, 21, 18, 17, 16, 25],
   [6, 5, 1, 2, 7, 3, 4, 0, 8, 11, 12, 9, 10, 13, 21, 23, 24, 15, 19, 20, 22, 14, 18, 25, 16, 17],
   [7, 2, 3, 5, 6, 1, 0, 4, 8, 11, 12, 9, 10, 13, 21, 17, 24, 25, 22, 18, 19, 14, 20, 15, 16, 23],
   [7, 3, 2, 1, 6, 5, 4, 0, 8, 9, 12, 11, 10, 13, 14, 25, 24, 17, 19, 18, 22, 21, 20, 23, 16, 15]]

private def l33g_ct : List ℕ :=
  [19, 17, 15, 23, 22, 25, 18, 20, 13, 14, 16, 21, 24, 8, 9, 2, 10, 1, 6, 0, 7, 11, 4, 3, 12, 5]

private def l33g_cx : List ℕ :=
  [2, 0, 1, 4, 5, 3, 6, 7, 8, 11, 9, 10, 12, 13, 21, 23, 16, 18, 25, 19, 15, 24, 22, 20, 14, 17]

private def l33g_cid : List ℕ := List.range 26

private def l33g_cx2 : List ℕ := l33g_comp l33g_cx l33g_cx

private def l33g_cS : List (List ℕ) := l33g_cT ++ l33g_cT.map fun c => l33g_comp c l33g_ct

private def l33g_cX : List (List ℕ) := [l33g_cid, l33g_cx, l33g_cx2]

private def l33g_cQ : List (List ℕ) :=
  l33g_cS.filter fun g => decide (l33g_comp (l33g_comp l33g_cx g) l33g_cx2 ∈ l33g_cS) &&
    decide (l33g_comp (l33g_comp l33g_cx2 g) l33g_cx ∈ l33g_cS)

private theorem l33g_img_T : parabolicS0List.map l33g_img = l33g_cT := by decide +kernel

private theorem l33g_img_t : l33g_img l33g_t = l33g_ct := by decide +kernel

private theorem l33g_img_x : l33g_img l33g_x = l33g_cx := by decide +kernel

private theorem l33g_img_one : l33g_img 1 = l33g_cid := by decide +kernel

private theorem l33g_cS_closed : ∀ a ∈ l33g_cS, ∀ b ∈ l33g_cS, l33g_comp a b ∈ l33g_cS := by
  decide +kernel

private theorem l33g_cS_inv : ∀ a ∈ l33g_cS, ∃ b ∈ l33g_cS, l33g_comp a b = l33g_cid := by
  decide +kernel

private theorem l33g_cS_nodup : l33g_cS.Nodup ∧ l33g_cS.length = 32 ∧ l33g_cid ∈ l33g_cS := by
  decide +kernel

private theorem l33g_cx_order : l33g_comp l33g_cx l33g_cx2 = l33g_cid ∧ l33g_cx ≠ l33g_cid := by
  decide +kernel

private theorem l33g_perm_left : ∀ s ∈ l33g_cS, ∀ a ∈ l33g_cX, ∃ b ∈ l33g_cX,
    l33g_comp (l33g_comp a s) b ∈ l33g_cS := by
  decide +kernel

private theorem l33g_perm_right : ∀ s ∈ l33g_cS, ∀ a ∈ l33g_cX, ∃ b ∈ l33g_cX,
    l33g_comp (l33g_comp b s) a ∈ l33g_cS := by
  decide +kernel

private theorem l33g_outer : ∀ u ∈ l33g_cQ, l33g_comp u u = l33g_cid → u ∉ l33g_cT →
    (l33g_cQ.filter fun w => decide (l33g_comp w w = l33g_cid) &&
      decide (l33g_comp u w = l33g_comp w u)).length ≤ 4 ∧
    l33g_comp u (l33g_comp (l33g_comp l33g_cx u) l33g_cx2) ≠
      l33g_comp (l33g_comp (l33g_comp l33g_cx u) l33g_cx2) u := by
  decide +kernel

private theorem l33g_map_S0List : l33g_S0List.map l33g_img = l33g_cS := by
  have h : (parabolicS0List.map (· * l33g_t)).map l33g_img =
      (parabolicS0List.map l33g_img).map fun c => l33g_comp c l33g_ct := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun s _ => ?_
    simp only [Function.comp_apply, l33g_img_mul, l33g_img_t]
  rw [l33g_S0List, List.map_append, h, l33g_img_T]
  rfl

private theorem l33g_mem_S0List {g : Equiv.Perm (Fin 26)} :
    g ∈ l33g_S0List ↔ l33g_img g ∈ l33g_cS := by
  rw [← l33g_map_S0List, List.mem_map_of_injective l33g_img_injective]

private theorem l33g_x_cube : l33g_x * (l33g_x * l33g_x) = 1 :=
  l33g_img_injective (by
    rw [l33g_img_mul, l33g_img_mul, l33g_img_x, l33g_img_one]
    exact l33g_cx_order.1)

private theorem l33g_x_inv : l33g_x⁻¹ = l33g_x * l33g_x :=
  inv_eq_of_mul_eq_one_right l33g_x_cube

private theorem l33g_x_ne_one : l33g_x ≠ 1 := by
  intro h
  apply l33g_cx_order.2
  rw [← l33g_img_x, h, l33g_img_one]

private theorem l33g_x_order : orderOf l33g_x = 3 :=
  orderOf_eq_prime (by rw [pow_three]; exact l33g_x_cube) l33g_x_ne_one

private theorem l33g_map_X : [1, l33g_x, l33g_x * l33g_x].map l33g_img = l33g_cX := by
  simp only [List.map_cons, List.map_nil, l33g_img_one, l33g_img_mul, l33g_img_x]
  rfl

private theorem l33g_mem_X' {z : Equiv.Perm (Fin 26)} :
    z ∈ Subgroup.zpowers l33g_x ↔ z ∈ [1, l33g_x, l33g_x * l33g_x] := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, l33g_x_order, Finset.mem_image]
  simp only [Finset.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (pow_zero _)
    · exact Or.inr (Or.inl (pow_one _))
    · exact Or.inr (Or.inr (sq _))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, pow_zero _⟩
    · exact ⟨1, by norm_num, pow_one _⟩
    · exact ⟨2, by norm_num, sq _⟩

private theorem l33g_mem_X {z : Equiv.Perm (Fin 26)} :
    z ∈ Subgroup.zpowers l33g_x ↔ l33g_img z ∈ l33g_cX := by
  rw [l33g_mem_X', ← l33g_map_X, List.mem_map_of_injective l33g_img_injective]

private theorem l33g_cX_mem {b : List ℕ} (hb : b ∈ l33g_cX) :
    ∃ z ∈ Subgroup.zpowers l33g_x, l33g_img z = b := by
  rw [← l33g_map_X] at hb
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hb
  exact ⟨z, l33g_mem_X'.2 hz, rfl⟩

private theorem l33g_S0_nodup : l33g_S0List.Nodup :=
  List.Nodup.of_map l33g_img (l33g_map_S0List ▸ l33g_cS_nodup.1)

private theorem l33g_S0_one : 1 ∈ l33g_S0List :=
  l33g_mem_S0List.2 (l33g_img_one ▸ l33g_cS_nodup.2.2)

private theorem l33g_S0_mul : ∀ x ∈ l33g_S0List, ∀ y ∈ l33g_S0List, x * y ∈ l33g_S0List := by
  intro x hx y hy
  rw [l33g_mem_S0List] at hx hy ⊢
  rw [l33g_img_mul]
  exact l33g_cS_closed _ hx _ hy

private theorem l33g_S0_inv : ∀ x ∈ l33g_S0List, x⁻¹ ∈ l33g_S0List := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := l33g_cS_inv _ (l33g_mem_S0List.1 hx)
  rw [← l33g_map_S0List] at hb
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
  have hxy : x * y = 1 := l33g_img_injective (by rw [l33g_img_mul, l33g_img_one, hxb])
  rw [inv_eq_of_mul_eq_one_right hxy]
  exact hy

private def l33g_S0 : Subgroup (Equiv.Perm (Fin 26)) :=
  l33ParabolicListSubgroup l33g_S0List l33g_S0_nodup l33g_S0_one l33g_S0_mul l33g_S0_inv

private theorem l33g_mem_S0 {g : Equiv.Perm (Fin 26)} : g ∈ l33g_S0 ↔ l33g_img g ∈ l33g_cS := by
  rw [l33g_S0, mem_l33ParabolicListSubgroup, l33g_mem_S0List]

private theorem l33g_card_S0 : Nat.card l33g_S0 = 32 := by
  rw [l33g_S0, card_l33ParabolicListSubgroup, ← List.length_map (f := l33g_img),
    l33g_map_S0List]
  exact l33g_cS_nodup.2.1

private theorem l33g_QA_closure :
    QA.originalSubgroup = Subgroup.closure {PA, PB, sg0} := by
  rw [QA, certificate_originalSubgroup]
  congr 1
  ext g
  simp

private theorem l33g_P_le_A : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, l33g_QA_closure]
  exact Subgroup.closure_mono
    (Set.insert_subset_insert (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))

private theorem l33g_x_mem_P : l33g_x ∈ QP.originalSubgroup := by
  have hA : PA ∈ QP.originalSubgroup := by
    rw [QP_closure]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : PB ∈ QP.originalSubgroup := by
    rw [QP_closure]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hB' := inv_mem hB
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hB' hA) hB') hA)
    hB) hA) hB') hA) hB'

private theorem l33g_t_mem_A : l33g_t ∈ QA.originalSubgroup := by
  have hA : PA ∈ QA.originalSubgroup := by
    rw [l33g_QA_closure]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : PB ∈ QA.originalSubgroup := by
    rw [l33g_QA_closure]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hg : sg0⁻¹ ∈ QA.originalSubgroup := by
    rw [l33g_QA_closure]
    exact inv_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hA hB) hA) hg) hA) hB) hA

private theorem l33g_T0_mem_P :
    ∀ x ∈ parabolicS0List, x ∈ QP.originalSubgroup := by
  have h := Certificates.certificate5176
  unfold parabolicPairCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hmem⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact memGroupListCheck_sound QP QP_ok hmem

private theorem l33g_S0_le_A :
    l33g_S0 ≤ QA.originalSubgroup := by
  intro g hg
  rw [l33g_S0, mem_l33ParabolicListSubgroup, l33g_S0List, List.mem_append] at hg
  rcases hg with hg | hg
  · exact l33g_P_le_A (l33g_T0_mem_P g hg)
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
    exact mul_mem (l33g_P_le_A (l33g_T0_mem_P s hs)) l33g_t_mem_A

private theorem l33g_permutes : Permutes (Subgroup.zpowers l33g_x) l33g_S0 := by
  unfold Permutes
  ext w
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨z, hz, s, hs, rfl⟩
    obtain ⟨b, hb, hbS⟩ := l33g_perm_left _ (l33g_mem_S0.1 hs) _ (l33g_mem_X.1 hz)
    obtain ⟨z', hz', rfl⟩ := l33g_cX_mem hb
    refine ⟨z * s * z', ?_, z'⁻¹, inv_mem hz', by group⟩
    rw [l33g_mem_S0, l33g_img_mul, l33g_img_mul]
    exact hbS
  · rintro ⟨s, hs, z, hz, rfl⟩
    obtain ⟨b, hb, hbS⟩ := l33g_perm_right _ (l33g_mem_S0.1 hs) _ (l33g_mem_X.1 hz)
    obtain ⟨z', hz', rfl⟩ := l33g_cX_mem hb
    refine ⟨z'⁻¹, inv_mem hz', z' * s * z, ?_, by group⟩
    rw [l33g_mem_S0, l33g_img_mul, l33g_img_mul]
    exact hbS

private theorem l33g_card_le {A : Subgroup (Equiv.Perm (Fin 26))} {L : List (List ℕ)}
    (h : ∀ a ∈ A, l33g_img a ∈ L) : Nat.card A ≤ L.length := by
  classical
  let F : A → L.toFinset := fun a => ⟨l33g_img a, List.mem_toFinset.2 (h a a.2)⟩
  have hF : Function.Injective F := fun a b hab =>
    Subtype.ext (l33g_img_injective (congrArg Subtype.val hab))
  calc Nat.card A ≤ Nat.card L.toFinset := Nat.card_le_card_of_injective F hF
    _ = L.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ L.length := List.toFinset_card_le L

private theorem l33g_conj_img (g : Equiv.Perm (Fin 26)) :
    l33g_img (l33g_x * g * l33g_x⁻¹) = l33g_comp (l33g_comp l33g_cx (l33g_img g)) l33g_cx2 := by
  simp only [l33g_x_inv, l33g_img_mul, l33g_img_x, l33g_cx2]

private theorem l33g_conj_inv_img (g : Equiv.Perm (Fin 26)) :
    l33g_img (l33g_x⁻¹ * g * l33g_x) = l33g_comp (l33g_comp l33g_cx2 (l33g_img g)) l33g_cx := by
  simp only [l33g_x_inv, l33g_img_mul, l33g_img_x, l33g_cx2]

private theorem l33g_model :
    ∃ (S₀ : Subgroup (Equiv.Perm (Fin 26))) (x₀ : Equiv.Perm (Fin 26)),
      S₀ ≤ QA.originalSubgroup ∧ Nat.card S₀ = 32 ∧ x₀ ∈ QP.originalSubgroup ∧
      orderOf x₀ = 3 ∧ Permutes (Subgroup.zpowers x₀) S₀ ∧
      ∀ R A : Subgroup (Equiv.Perm (Fin 26)), R ≤ S₀ →
        (∀ r ∈ R, x₀ * r * x₀⁻¹ ∈ R ∧ x₀⁻¹ * r * x₀ ∈ R) → A ≤ R → IsElemAbelian 2 A →
        ¬ A ≤ QP.originalSubgroup →
          Nat.card A ≤ 4 ∧ ∃ a ∈ A, a * (x₀ * a * x₀⁻¹) ≠ x₀ * a * x₀⁻¹ * a := by
  refine ⟨l33g_S0, l33g_x, l33g_S0_le_A, l33g_card_S0, l33g_x_mem_P, l33g_x_order,
    l33g_permutes, ?_⟩
  intro R A hRS hRx hAR hA hAP
  have hRQ : ∀ r ∈ R, l33g_img r ∈ l33g_cQ := by
    intro r hr
    simp only [l33g_cQ, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨l33g_mem_S0.1 (hRS hr), ?_, ?_⟩
    · rw [← l33g_conj_img]
      exact l33g_mem_S0.1 (hRS (hRx r hr).1)
    · rw [← l33g_conj_inv_img]
      exact l33g_mem_S0.1 (hRS (hRx r hr).2)
  obtain ⟨a, ha, haP⟩ := SetLike.not_le_iff_exists.1 hAP
  have hsq : ∀ b ∈ A, l33g_comp (l33g_img b) (l33g_img b) = l33g_cid := by
    intro b hb
    rw [← l33g_img_mul, ← l33g_img_one, ← sq, hA.2 b hb]
  have hcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := by
    intro b hb c hc
    have := hA.1
    exact congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : A) ⟨c, hc⟩)
  have haT : l33g_img a ∉ l33g_cT := by
    intro haT
    rw [← l33g_img_T, List.mem_map_of_injective l33g_img_injective] at haT
    exact haP (l33g_T0_mem_P a haT)
  obtain ⟨hlen, hne⟩ := l33g_outer _ (hRQ a (hAR ha)) (hsq a ha) haT
  refine ⟨(l33g_card_le fun b hb => ?_).trans hlen, a, ha, fun h => hne ?_⟩
  · simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hRQ b (hAR hb), hsq b hb, ?_⟩
    rw [← l33g_img_mul, ← l33g_img_mul, hcomm a ha b hb]
  · rw [← l33g_conj_img, ← l33g_img_mul, ← l33g_img_mul, h]

private theorem l33g_centA {σ : Equiv.Perm (Fin 26)}
    (hσ : σ ∈ QA.originalSubgroup) (hA : σ * PA = PA * σ) (hB : σ * PB = PB * σ) : σ = 1 := by
  by_contra hne
  have h1 := List.all_eq_true.1 cent_ok σ ((mem_elemsT QA QA_ok σ).2 hσ)
  simp [hA, hB, hne] at h1

private theorem l33g_embed {Y : Type} [Group Y] [Finite Y]
    {K S : Subgroup Y} (hKY : KYForm Y K S) (hLie : LieModel ↥K .PSL 3 3 1) (hSK : ¬ S ≤ K)
    {S₀ : Subgroup (Equiv.Perm (Fin 26))} (hS₀A : S₀ ≤ QA.originalSubgroup)
    (hS₀ : Nat.card S₀ = 32) :
    ∃ f : Y →* Equiv.Perm (Fin 26), Function.Injective f ∧
      (∀ y, f y ∈ QP.originalSubgroup ↔ y ∈ K) ∧
      (∀ g ∈ QP.originalSubgroup, ∃ y, f y = g) ∧ S.map f = S₀ := by
  classical
  obtain ⟨hKN, -, -, hCent, -, hSylY⟩ := hKY
  obtain ⟨e⟩ := equiv_of_lieModel hLie
  obtain ⟨M, hMP, hMA⟩ := autModel e
  have hgenA : PA ∈ QP.originalSubgroup := by
    rw [QP_closure]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hgenB : PB ∈ QP.originalSubgroup := by
    rw [QP_closure]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hMe : ∀ k : K, (M.e k : Equiv.Perm (Fin 26)) ∈ QP.originalSubgroup :=
    fun k => hMP ▸ (M.e k).2
  have hMs : ∀ g ∈ QP.originalSubgroup, ∃ k : K, (M.e k : Equiv.Perm (Fin 26)) = g := by
    intro g hg
    rw [← hMP] at hg
    exact ⟨M.e.symm ⟨g, hg⟩, by simp⟩
  have hcent : ∀ σ ∈ QA.originalSubgroup,
      (∀ k : K, σ * M.e k = M.e k * σ) → σ = 1 := by
    intro σ hσ hc
    obtain ⟨ka, hka⟩ := hMs PA hgenA
    obtain ⟨kb, hkb⟩ := hMs PB hgenB
    refine l33g_centA hσ ?_ ?_
    · rw [← hka]; exact hc ka
    · rw [← hkb]; exact hc kb
  have hZK : ∀ z : K, (∀ k : K, z * k = k * z) → z = 1 := by
    intro z hz
    have h1 : (M.e z : Equiv.Perm (Fin 26)) = 1 := by
      refine hcent _ (l33g_P_le_A (hMe z)) fun k => ?_
      have h2 := congrArg (fun q : K => ((M.e q : M.P) : Equiv.Perm (Fin 26))) (hz k)
      simpa only [map_mul, Subgroup.coe_mul] using h2
    exact M.e.injective ((Subtype.ext h1 : M.e z = 1).trans (map_one M.e).symm)
  have := hKN
  have hconj : Function.Injective (MulAut.conjNormal : Y →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro y hy
    have hy1 : MulAut.conjNormal y = (1 : MulAut K) := hy
    have hmem : y ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h2 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : Y)) hy1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc k * y = y * k * y⁻¹ * y := by rw [h2]
        _ = y * k := by group
    rw [hCent] at hmem
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hmem
    rw [hZK z fun k => (Subgroup.mem_center_iff.mp hz k).symm, map_one]
  set ψ : Y →* Equiv.Perm (Fin 26) :=
    M.A.subtype.comp (M.Φ.toMonoidHom.comp MulAut.conjNormal)
  have hψ : ∀ y, ψ y = (M.Φ (MulAut.conjNormal y) : Equiv.Perm (Fin 26)) := fun y => rfl
  have hψinj : Function.Injective ψ := fun y z h => hconj (M.Φ.injective (Subtype.ext h))
  have hψA : ∀ y, ψ y ∈ QA.originalSubgroup := fun y => hMA ▸ (M.Φ (MulAut.conjNormal y)).2
  have hψK : ∀ k : K, ψ k = M.e k := by
    intro k
    have h1 : (M.e k : Equiv.Perm (Fin 26))⁻¹ * ψ k = 1 := by
      refine hcent _ (mul_mem (inv_mem (l33g_P_le_A (hMe k))) (hψA k)) fun x => ?_
      have hspec := M.spec (MulAut.conjNormal (k : Y)) x
      have hck : MulAut.conjNormal (k : Y) x = k * x * k⁻¹ :=
        Subtype.ext (by simp [MulAut.conjNormal_apply])
      rw [hck, map_mul, map_mul, map_inv] at hspec
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hspec
      rw [← hψ] at hspec
      calc (M.e k : Equiv.Perm (Fin 26))⁻¹ * ψ k * M.e x
          = (M.e k : Equiv.Perm (Fin 26))⁻¹ * (ψ k * M.e x * (ψ k)⁻¹) * ψ k := by group
        _ = (M.e k : Equiv.Perm (Fin 26))⁻¹ *
            (M.e k * M.e x * (M.e k : Equiv.Perm (Fin 26))⁻¹) * ψ k := by rw [hspec]
        _ = M.e x * ((M.e k : Equiv.Perm (Fin 26))⁻¹ * ψ k) := by group
    exact (inv_mul_eq_one.mp h1).symm
  have hψP : ∀ y, ψ y ∈ QP.originalSubgroup ↔ y ∈ K := by
    intro y
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := hMs _ hy
      rw [← hψinj ((hψK k).trans hk)]
      exact k.2
    · intro hy
      have h1 := hψK ⟨y, hy⟩
      rw [h1]
      exact hMe _
  have hψsurjP : ∀ g ∈ QP.originalSubgroup, ∃ y, ψ y = g := by
    intro g hg
    obtain ⟨k, hk⟩ := hMs g hg
    exact ⟨k, (hψK k).trans hk⟩
  have hKcard : Nat.card K = 5616 := by
    rw [Nat.card_congr e.toEquiv, card_group QP QP_ok, QP_valid.2]
  have hAcard : Nat.card QA.originalSubgroup = 11232 := by
    rw [card_group QA QA_ok, QA_valid.2]
  let F : Y → QA.originalSubgroup := fun y => ⟨ψ y, hψA y⟩
  have hFinj : Function.Injective F := fun y z h =>
    hψinj (congrArg (fun q : QA.originalSubgroup => (q : Equiv.Perm (Fin 26))) h)
  have hYle : Nat.card Y ≤ 11232 := hAcard ▸ Nat.card_le_card_of_injective F hFinj
  have hindex : K.index = 2 := by
    have h1 := Subgroup.card_mul_index (H := K)
    rw [hKcard] at h1
    have h2 : K.index ≠ 1 := fun h => hSK (by rw [Subgroup.index_eq_one.mp h]; exact le_top)
    have h3 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hYcard : Nat.card Y = 11232 := by
    rw [← Subgroup.card_mul_index (H := K), hKcard, hindex]
  have hFbij : Function.Bijective F :=
    hFinj.bijective_of_nat_card_le (by rw [hAcard, hYcard])
  have hψsurjA : ∀ g ∈ QA.originalSubgroup, ∃ y, ψ y = g := by
    intro g hg
    obtain ⟨y, hy⟩ := hFbij.2 ⟨g, hg⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  set S' : Subgroup Y := S₀.comap ψ with hS'def
  have hS'map : S'.map ψ = S₀ := by
    rw [hS'def, Subgroup.map_comap_eq, inf_eq_right]
    intro g hg
    obtain ⟨y, hy⟩ := hψsurjA g (hS₀A hg)
    exact MonoidHom.mem_range.mpr ⟨y, hy⟩
  have hS'card : Nat.card S' = 32 := by
    rw [← Subgroup.card_map_of_injective hψinj, hS'map, hS₀]
  have hS'syl : IsSylowIn 2 S' ⊤ := by
    refine isSylowIn_of_card_eq le_top ?_
    have hfac : (11232 : ℕ).factorization 2 = 5 := by
      have h1 : (11232 : ℕ) = 2 ^ 5 * 351 := by norm_num
      rw [h1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (351 : ℕ))]
    rw [hS'card, Subgroup.card_top, hYcard, hfac]
    norm_num
  obtain ⟨h, -, hh⟩ := Ch1Sec3.exists_conj_of_isSylowIn hSylY hS'syl
  refine ⟨ψ.comp (MulAut.conj h).toMonoidHom, hψinj.comp (MulAut.conj h).injective, ?_, ?_, ?_⟩
  · intro y
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [hψP]
    constructor
    · intro hy
      have h1 := hKN.conj_mem _ hy h⁻¹
      have h2 : h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y := by group
      rwa [h2] at h1
    · intro hy
      exact hKN.conj_mem y hy h
  · intro g hg
    obtain ⟨y, rfl⟩ := hψsurjP g hg
    refine ⟨h⁻¹ * y * h, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    congr 1
    group
  · ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have h1 : h * s * h⁻¹ ∈ S' := (hh _).2 (by
        have h2 : h⁻¹ * (h * s * h⁻¹) * h = s := by group
        rw [h2]; exact hs)
      exact h1
    · intro hg
      obtain ⟨y, rfl⟩ := hψsurjA g (hS₀A hg)
      have hy : y ∈ S' := hg
      refine ⟨h⁻¹ * y * h, (hh y).1 hy, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      congr 1
      group

theorem k_L33GraphOuter_holds :
    K_L33GraphOuter := by
  intro Y _ _ K S hKY hLie hSK
  obtain ⟨S₀, x₀, hS₀A, hS₀, hx₀P, hx₀, hperm, hmodel⟩ := l33g_model
  obtain ⟨f, hfinj, hfP, hfsurj, hfS⟩ := l33g_embed hKY hLie hSK hS₀A hS₀
  obtain ⟨x, hx⟩ := hfsurj x₀ hx₀P
  set X : Subgroup Y := (Subgroup.zpowers x₀).comap f with hXdef
  have hXmap : X.map f = Subgroup.zpowers x₀ := by
    rw [hXdef, Subgroup.map_comap_eq, inf_eq_right]
    exact Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨x, hx⟩)
  have hxX : x ∈ X := by
    rw [hXdef, Subgroup.mem_comap, hx]
    exact Subgroup.mem_zpowers x₀
  refine ⟨X, fun y hy => (hfP y).1 (Subgroup.zpowers_le.mpr hx₀P hy), ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective hfinj, hXmap, Nat.card_zpowers, hx₀]
  · unfold Permutes
    refine CFSG.GroupTheory.permutes_of_map_permutes f ?_ ?_
    · intro y hy
      rw [MonoidHom.mem_ker, ← map_one f] at hy
      rw [hfinj hy]
      exact one_mem S
    · rw [hXmap, hfS]
      exact hperm
  · intro R A hRS hRN hAR hA hAK
    have hxN : x ∈ Subgroup.normalizer (R : Set Y) := hRN (Subgroup.mem_sup_left hxX)
    have hxN' : x⁻¹ ∈ Subgroup.normalizer (R : Set Y) := inv_mem hxN
    have hRstab : ∀ r ∈ R.map f, x₀ * r * x₀⁻¹ ∈ R.map f ∧ x₀⁻¹ * r * x₀ ∈ R.map f := by
      intro r' hr'
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hr'
      refine ⟨Subgroup.mem_map.mpr ⟨x * r * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN r).mp hr,
        by simp [hx]⟩, Subgroup.mem_map.mpr ⟨x⁻¹ * r * x⁻¹⁻¹,
        (Subgroup.mem_normalizer_iff.mp hxN' r).mp hr, by simp [hx]⟩⟩
    obtain ⟨a, haA, haK⟩ := SetLike.not_le_iff_exists.1 hAK
    have hAP : ¬ A.map f ≤ QP.originalSubgroup := fun hle =>
      haK ((hfP a).1 (hle (Subgroup.mem_map_of_mem f haA)))
    obtain ⟨hcard, b', hb', hne⟩ := hmodel (R.map f) (A.map f)
      (hfS ▸ Subgroup.map_mono hRS) hRstab (Subgroup.map_mono hAR) (hA.map f) hAP
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
    refine ⟨by rwa [Subgroup.card_map_of_injective hfinj] at hcard, x, hxX, b, hb, b, hb, ?_⟩
    intro heq
    apply hne
    have h1 := congrArg f heq
    simpa [hx] using h1


private def l33w_ctau : List ℕ :=
  [19, 15, 17, 25, 22, 23, 20, 18, 13, 21, 16, 14, 24, 8, 11, 1, 10, 2, 7, 0, 6, 9, 4, 5, 12, 3]

private def l33w_cSp : List (List ℕ) :=
  l33g_cS.filter fun g => decide (l33g_comp g l33w_ctau = l33g_comp l33w_ctau g)

private def l33w_z : Equiv.Perm (Fin 26) :=
  PB * PA * (PB * PA) * PB⁻¹ * PA * (PB * PA) * (PB * PA) * (PB * PA) * (PB * PA) * (PB * PA) *
    PB⁻¹ * PA

private def l33w_cz : List ℕ :=
  [9, 5, 2, 1, 11, 3, 4, 0, 10, 7, 12, 6, 8, 16, 20, 23, 24, 17, 19, 21, 22, 18, 14, 25, 13, 15]

private def l33w_cz2 : List ℕ := l33g_comp l33w_cz l33w_cz

private def l33w_cZ : List (List ℕ) := [l33g_cid, l33w_cz, l33w_cz2]

private def l33w_step (L : List (List ℕ)) : List (List ℕ) :=
  L.filter fun s => decide (l33g_comp (l33g_comp l33w_cz s) l33w_cz2 ∈ L) &&
    decide (l33g_comp (l33g_comp l33w_cz2 s) l33w_cz ∈ L) &&
    l33g_cS.all fun r => L.any fun w => decide (l33g_comp r s = l33g_comp w r)

private theorem l33w_img_z : l33g_img l33w_z = l33w_cz := by decide +kernel

private theorem l33w_cz_order : l33g_comp l33w_cz l33w_cz2 = l33g_cid ∧ l33w_cz ≠ l33g_cid := by
  decide +kernel

private theorem l33w_cSp_one : l33g_cid ∈ l33w_cSp := by decide +kernel

private theorem l33w_cSp_closed : ∀ a ∈ l33w_cSp, ∀ b ∈ l33w_cSp, l33g_comp a b ∈ l33w_cSp := by
  decide +kernel

private theorem l33w_cSp_inv : ∀ a ∈ l33w_cSp, ∃ b ∈ l33w_cSp, l33g_comp a b = l33g_cid := by
  decide +kernel

private theorem l33w_cSp_normal : ∀ s ∈ l33g_cS, ∀ u ∈ l33w_cSp, ∃ w ∈ l33w_cSp,
    l33g_comp s u = l33g_comp w s := by
  decide +kernel

private theorem l33w_perm_left : ∀ s ∈ l33w_cSp, ∀ a ∈ l33w_cZ, ∃ b ∈ l33w_cZ,
    l33g_comp (l33g_comp a s) b ∈ l33w_cSp := by
  decide +kernel

private theorem l33w_perm_right : ∀ s ∈ l33w_cSp, ∀ a ∈ l33w_cZ, ∃ b ∈ l33w_cZ,
    l33g_comp (l33g_comp b s) a ∈ l33w_cSp := by
  decide +kernel

private theorem l33w_outer : ∀ u ∈ l33g_cQ, l33g_comp u u = l33g_cid → u ∉ l33g_cT →
    ∃ c ∈ l33g_cX, ∀ w ∈ l33g_cQ, l33g_comp w w = l33g_cid → l33g_comp u w = l33g_comp w u →
      l33g_comp (l33g_comp c w) (l33g_comp c c) ∈ l33w_cSp := by
  decide +kernel

private theorem l33w_core :
    l33w_step (l33w_step (l33w_step (l33w_step l33w_cSp))) = [l33g_cid] := by
  decide +kernel

private theorem l33w_z_cube : l33w_z * (l33w_z * l33w_z) = 1 :=
  l33g_img_injective (by
    rw [l33g_img_mul, l33g_img_mul, l33w_img_z, l33g_img_one]
    exact l33w_cz_order.1)

private theorem l33w_z_inv : l33w_z⁻¹ = l33w_z * l33w_z :=
  inv_eq_of_mul_eq_one_right l33w_z_cube

private theorem l33w_z_ne_one : l33w_z ≠ 1 := by
  intro h
  apply l33w_cz_order.2
  rw [← l33w_img_z, h, l33g_img_one]

private theorem l33w_z_order : orderOf l33w_z = 3 :=
  orderOf_eq_prime (by rw [pow_three]; exact l33w_z_cube) l33w_z_ne_one

private theorem l33w_z_mem_P : l33w_z ∈ QP.originalSubgroup := by
  have hA : PA ∈ QP.originalSubgroup := by
    rw [QP_closure]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : PB ∈ QP.originalSubgroup := by
    rw [QP_closure]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hB' := inv_mem hB
  have hBA := mul_mem hB hA
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem (mul_mem hBA hBA) hB') hA) hBA) hBA) hBA) hBA) hBA) hB') hA

private theorem l33w_map_Z : [1, l33w_z, l33w_z * l33w_z].map l33g_img = l33w_cZ := by
  simp only [List.map_cons, List.map_nil, l33g_img_one, l33g_img_mul, l33w_img_z]
  rfl

private theorem l33w_mem_zpowers_three {w z : Equiv.Perm (Fin 26)} (hw : orderOf w = 3) :
    z ∈ Subgroup.zpowers w ↔ z ∈ [1, w, w * w] := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hw, Finset.mem_image]
  simp only [Finset.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (pow_zero _)
    · exact Or.inr (Or.inl (pow_one _))
    · exact Or.inr (Or.inr (sq _))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, pow_zero _⟩
    · exact ⟨1, by norm_num, pow_one _⟩
    · exact ⟨2, by norm_num, sq _⟩

private theorem l33w_mem_Z {z : Equiv.Perm (Fin 26)} :
    z ∈ Subgroup.zpowers l33w_z ↔ l33g_img z ∈ l33w_cZ := by
  rw [l33w_mem_zpowers_three l33w_z_order, ← l33w_map_Z,
    List.mem_map_of_injective l33g_img_injective]

private theorem l33w_cZ_mem {b : List ℕ} (hb : b ∈ l33w_cZ) :
    ∃ z ∈ Subgroup.zpowers l33w_z, l33g_img z = b := by
  rw [← l33w_map_Z] at hb
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hb
  exact ⟨z, (l33w_mem_zpowers_three l33w_z_order).2 hz, rfl⟩

private theorem l33w_inv_eq_sq {w c : Equiv.Perm (Fin 26)} (hw : orderOf w = 3)
    (hc : c ∈ Subgroup.zpowers w) : c⁻¹ = c * c := by
  refine inv_eq_of_mul_eq_one_right ?_
  have h3 : c ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hw ▸ orderOf_dvd_of_mem_zpowers hc)
  rw [pow_three] at h3
  exact h3

private theorem l33w_cSp_sub : ∀ g ∈ l33w_cSp, g ∈ l33g_cS := fun _ hg => (List.mem_filter.1 hg).1

private theorem l33w_cS_mem {b : List ℕ} (hb : b ∈ l33g_cS) : ∃ s ∈ l33g_S0, l33g_img s = b := by
  rw [← l33g_map_S0List] at hb
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hb
  exact ⟨s, l33g_mem_S0.2 (l33g_mem_S0List.1 hs), rfl⟩

private def l33w_SpList : List (Equiv.Perm (Fin 26)) :=
  l33g_S0List.filter fun g => decide (l33g_img g ∈ l33w_cSp)

private theorem l33w_mem_SpList {g : Equiv.Perm (Fin 26)} :
    g ∈ l33w_SpList ↔ l33g_img g ∈ l33w_cSp := by
  rw [l33w_SpList, List.mem_filter, decide_eq_true_eq, l33g_mem_S0List]
  exact ⟨And.right, fun h => ⟨l33w_cSp_sub _ h, h⟩⟩

private theorem l33w_Sp_nodup : l33w_SpList.Nodup := l33g_S0_nodup.filter _

private theorem l33w_Sp_one : 1 ∈ l33w_SpList :=
  l33w_mem_SpList.2 (l33g_img_one ▸ l33w_cSp_one)

private theorem l33w_Sp_mul : ∀ x ∈ l33w_SpList, ∀ y ∈ l33w_SpList, x * y ∈ l33w_SpList := by
  intro x hx y hy
  rw [l33w_mem_SpList] at hx hy ⊢
  rw [l33g_img_mul]
  exact l33w_cSp_closed _ hx _ hy

private theorem l33w_Sp_inv : ∀ x ∈ l33w_SpList, x⁻¹ ∈ l33w_SpList := by
  intro x hx
  rw [l33w_mem_SpList] at hx
  obtain ⟨b, hb, hxb⟩ := l33w_cSp_inv _ hx
  obtain ⟨y, -, rfl⟩ := l33w_cS_mem (l33w_cSp_sub _ hb)
  have hxy : x * y = 1 := l33g_img_injective (by rw [l33g_img_mul, l33g_img_one, hxb])
  rw [inv_eq_of_mul_eq_one_right hxy, l33w_mem_SpList]
  exact hb

private def l33w_Sp : Subgroup (Equiv.Perm (Fin 26)) :=
  l33ParabolicListSubgroup l33w_SpList l33w_Sp_nodup l33w_Sp_one l33w_Sp_mul l33w_Sp_inv

private theorem l33w_mem_Sp {g : Equiv.Perm (Fin 26)} : g ∈ l33w_Sp ↔ l33g_img g ∈ l33w_cSp := by
  rw [l33w_Sp, mem_l33ParabolicListSubgroup, l33w_mem_SpList]

private theorem l33w_Sp_le : l33w_Sp ≤ l33g_S0 := fun _ hg =>
  l33g_mem_S0.2 (l33w_cSp_sub _ (l33w_mem_Sp.1 hg))

private theorem l33w_conj_mem {s u : Equiv.Perm (Fin 26)} (hs : s ∈ l33g_S0) (hu : u ∈ l33w_Sp) :
    s * u * s⁻¹ ∈ l33w_Sp := by
  obtain ⟨w, hw, hsw⟩ := l33w_cSp_normal _ (l33g_mem_S0.1 hs) _ (l33w_mem_Sp.1 hu)
  obtain ⟨v, -, rfl⟩ := l33w_cS_mem (l33w_cSp_sub _ hw)
  have hsv : s * u = v * s := l33g_img_injective (by rw [l33g_img_mul, l33g_img_mul, hsw])
  rw [hsv, mul_inv_cancel_right]
  exact l33w_mem_Sp.2 hw

private theorem l33w_S0_le_normalizer : l33g_S0 ≤ Subgroup.normalizer (l33w_Sp : Set _) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => l33w_conj_mem hs hu, fun hu => ?_⟩
  have h := l33w_conj_mem (inv_mem hs) hu
  rwa [inv_inv, show s⁻¹ * (s * u * s⁻¹) * s = u by group] at h

private theorem l33w_permutes : Permutes (Subgroup.zpowers l33w_z) l33w_Sp := by
  unfold Permutes
  ext w
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨z, hz, s, hs, rfl⟩
    obtain ⟨b, hb, hbS⟩ := l33w_perm_left _ (l33w_mem_Sp.1 hs) _ (l33w_mem_Z.1 hz)
    obtain ⟨z', hz', rfl⟩ := l33w_cZ_mem hb
    refine ⟨z * s * z', ?_, z'⁻¹, inv_mem hz', by group⟩
    rw [l33w_mem_Sp, l33g_img_mul, l33g_img_mul]
    exact hbS
  · rintro ⟨s, hs, z, hz, rfl⟩
    obtain ⟨b, hb, hbS⟩ := l33w_perm_right _ (l33w_mem_Sp.1 hs) _ (l33w_mem_Z.1 hz)
    obtain ⟨z', hz', rfl⟩ := l33w_cZ_mem hb
    refine ⟨z'⁻¹, inv_mem hz', z' * s * z, ?_, by group⟩
    rw [l33w_mem_Sp, l33g_img_mul, l33g_img_mul]
    exact hbS

private theorem l33w_mem_step {R : Subgroup (Equiv.Perm (Fin 26))} {L : List (List ℕ)}
    (hzR : ∀ r ∈ R, l33w_z * r * l33w_z⁻¹ ∈ R ∧ l33w_z⁻¹ * r * l33w_z ∈ R)
    (hSR : ∀ s ∈ l33g_S0, ∀ r ∈ R, s * r * s⁻¹ ∈ R) (hL : ∀ r ∈ R, l33g_img r ∈ L) :
    ∀ r ∈ R, l33g_img r ∈ l33w_step L := by
  intro r hr
  simp only [l33w_step, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true]
  refine ⟨hL r hr, ⟨?_, ?_⟩, fun b hb => ?_⟩
  · have h := hL _ (hzR r hr).1
    rwa [l33w_z_inv, l33g_img_mul, l33g_img_mul, l33g_img_mul, l33w_img_z] at h
  · have h := hL _ (hzR r hr).2
    rwa [l33w_z_inv, l33g_img_mul, l33g_img_mul, l33g_img_mul, l33w_img_z] at h
  · obtain ⟨s, hs, rfl⟩ := l33w_cS_mem hb
    refine ⟨l33g_img (s * r * s⁻¹), hL _ (hSR s hs r hr), ?_⟩
    rw [← l33g_img_mul, ← l33g_img_mul, inv_mul_cancel_right]

private theorem l33w_core_eq {R : Subgroup (Equiv.Perm (Fin 26))} (hRS : R ≤ l33w_Sp)
    (hzR : ∀ r ∈ R, l33w_z * r * l33w_z⁻¹ ∈ R ∧ l33w_z⁻¹ * r * l33w_z ∈ R)
    (hSR : ∀ s ∈ l33g_S0, ∀ r ∈ R, s * r * s⁻¹ ∈ R) : R = ⊥ := by
  have h0 : ∀ r ∈ R, l33g_img r ∈ l33w_cSp := fun r hr => l33w_mem_Sp.1 (hRS hr)
  have h4 := l33w_mem_step hzR hSR (l33w_mem_step hzR hSR (l33w_mem_step hzR hSR
    (l33w_mem_step hzR hSR h0)))
  rw [l33w_core] at h4
  rw [Subgroup.eq_bot_iff_forall]
  intro r hr
  have h := h4 r hr
  rw [List.mem_singleton, ← l33g_img_one] at h
  exact l33g_img_injective h

private theorem l33w_model
    (R A : Subgroup (Equiv.Perm (Fin 26))) (hRS : R ≤ l33g_S0)
    (hRx : ∀ r ∈ R, l33g_x * r * l33g_x⁻¹ ∈ R ∧ l33g_x⁻¹ * r * l33g_x ∈ R) (hAR : A ≤ R)
    (hA : IsElemAbelian 2 A) (hAP : ¬ A ≤ QP.originalSubgroup) :
    ∃ c ∈ Subgroup.zpowers l33g_x, CFSG.Quasithin.conjSubgroup A c ≤ l33w_Sp := by
  have hRQ : ∀ r ∈ R, l33g_img r ∈ l33g_cQ := by
    intro r hr
    simp only [l33g_cQ, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨l33g_mem_S0.1 (hRS hr), ?_, ?_⟩
    · rw [← l33g_conj_img]
      exact l33g_mem_S0.1 (hRS (hRx r hr).1)
    · rw [← l33g_conj_inv_img]
      exact l33g_mem_S0.1 (hRS (hRx r hr).2)
  obtain ⟨a, ha, haP⟩ := SetLike.not_le_iff_exists.1 hAP
  have hsq : ∀ b ∈ A, l33g_comp (l33g_img b) (l33g_img b) = l33g_cid := by
    intro b hb
    rw [← l33g_img_mul, ← l33g_img_one, ← sq, hA.2 b hb]
  have hcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := by
    intro b hb c hc
    have := hA.1
    exact congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : A) ⟨c, hc⟩)
  have haT : l33g_img a ∉ l33g_cT := by
    intro haT
    rw [← l33g_img_T, List.mem_map_of_injective l33g_img_injective] at haT
    exact haP (l33g_T0_mem_P a haT)
  obtain ⟨cb, hcb, hcW⟩ := l33w_outer _ (hRQ a (hAR ha)) (hsq a ha) haT
  obtain ⟨c, hc, rfl⟩ := l33g_cX_mem hcb
  refine ⟨c⁻¹, inv_mem hc, fun y hy => ?_⟩
  rw [CFSG.Quasithin.mem_conjSubgroup_iff, inv_inv] at hy
  have hcy := hcW _ (hRQ _ (hAR hy)) (hsq _ hy) (by
    rw [← l33g_img_mul, ← l33g_img_mul, hcomm a ha _ hy])
  rw [← l33g_img_mul, ← l33g_img_mul, ← l33w_inv_eq_sq l33g_x_order hc, ← l33g_img_mul,
    show c * (c⁻¹ * y * c) * c⁻¹ = y by group] at hcy
  exact l33w_mem_Sp.2 hcy

theorem k_L33GraphOuterW_holds :
    K_L33GraphOuterW := by
  intro Y _ _ K S hKY hLie hSK
  obtain ⟨f, hfinj, hfP, hfsurj, hfS⟩ := l33g_embed hKY hLie hSK l33g_S0_le_A l33g_card_S0
  obtain ⟨x, hx⟩ := hfsurj l33g_x l33g_x_mem_P
  obtain ⟨z, hz⟩ := hfsurj l33w_z l33w_z_mem_P
  set X : Subgroup Y := (Subgroup.zpowers l33g_x).comap f with hXdef
  set Z : Subgroup Y := (Subgroup.zpowers l33w_z).comap f with hZdef
  set S' : Subgroup Y := l33w_Sp.comap f with hS'def
  have hXmap : X.map f = Subgroup.zpowers l33g_x := by
    rw [hXdef, Subgroup.map_comap_eq, inf_eq_right]
    exact Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨x, hx⟩)
  have hZmap : Z.map f = Subgroup.zpowers l33w_z := by
    rw [hZdef, Subgroup.map_comap_eq, inf_eq_right]
    exact Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨z, hz⟩)
  have hS'map : S'.map f = l33w_Sp := by
    rw [hS'def, Subgroup.map_comap_eq, inf_eq_right]
    refine l33w_Sp_le.trans ?_
    rw [← hfS]
    exact Subgroup.map_le_range f S
  have hmemS : ∀ y, f y ∈ l33g_S0 → y ∈ S := by
    intro y hy
    rw [← hfS] at hy
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy
    rwa [← hfinj hsy]
  have hS'S : S' ≤ S := fun y hy => hmemS y (l33w_Sp_le hy)
  have hSN : S ≤ Subgroup.normalizer (S' : Set Y) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have hs0 : f s ∈ l33g_S0 := hfS ▸ Subgroup.mem_map_of_mem f hs
    have h := (Subgroup.mem_normalizer_iff.mp (l33w_S0_le_normalizer hs0)) (f u)
    simp only [hS'def, Subgroup.mem_comap, map_mul, map_inv]
    exact h
  have hxX : x ∈ X := by
    rw [hXdef, Subgroup.mem_comap, hx]
    exact Subgroup.mem_zpowers l33g_x
  refine ⟨X, fun y hy => (hfP y).1 (Subgroup.zpowers_le.mpr l33g_x_mem_P hy), ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective hfinj, hXmap, Nat.card_zpowers, l33g_x_order]
  · unfold Permutes
    refine CFSG.GroupTheory.permutes_of_map_permutes f ?_ ?_
    · intro y hy
      rw [MonoidHom.mem_ker, ← map_one f] at hy
      rw [hfinj hy]
      exact one_mem S
    · rw [hXmap, hfS]
      exact l33g_permutes
  · intro R A hRS hRN hAR hA hAK
    have hxN : x ∈ Subgroup.normalizer (R : Set Y) := hRN (Subgroup.mem_sup_left hxX)
    have hxN' : x⁻¹ ∈ Subgroup.normalizer (R : Set Y) := inv_mem hxN
    have hRstab : ∀ r ∈ R.map f, l33g_x * r * l33g_x⁻¹ ∈ R.map f ∧
        l33g_x⁻¹ * r * l33g_x ∈ R.map f := by
      intro r' hr'
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hr'
      refine ⟨Subgroup.mem_map.mpr ⟨x * r * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN r).mp hr,
        by simp [hx]⟩, Subgroup.mem_map.mpr ⟨x⁻¹ * r * x⁻¹⁻¹,
        (Subgroup.mem_normalizer_iff.mp hxN' r).mp hr, by simp [hx]⟩⟩
    have hAP : ¬ A.map f ≤ QP.originalSubgroup := by
      obtain ⟨a, haA, haK⟩ := SetLike.not_le_iff_exists.1 hAK
      exact fun hle => haK ((hfP a).1 (hle (Subgroup.mem_map_of_mem f haA)))
    obtain ⟨c, hc, hcS⟩ := l33w_model (R.map f) (A.map f) (hfS ▸ Subgroup.map_mono hRS) hRstab
      (Subgroup.map_mono hAR) (hA.map f) hAP
    have hcX : c ∈ X.map f := hXmap ▸ hc
    obtain ⟨x', hx'X, rfl⟩ := Subgroup.mem_map.mp hcX
    refine ⟨x', hx'X, Z, S', ?_, hS'S, ?_, ?_, ?_⟩
    · rw [← Subgroup.card_map_of_injective hfinj, hZmap, Nat.card_zpowers, l33w_z_order]
    · unfold Permutes
      refine CFSG.GroupTheory.permutes_of_map_permutes f ?_ ?_
      · intro y hy
        rw [MonoidHom.mem_ker, ← map_one f] at hy
        rw [hfinj hy]
        exact one_mem S'
      · rw [hZmap, hS'map]
        exact l33w_permutes
    · intro y hy
      rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hy
      have h := hcS (show f y ∈ CFSG.Quasithin.conjSubgroup (A.map f) (f x') by
        rw [CFSG.Quasithin.mem_conjSubgroup_iff, ← map_inv, ← map_mul, ← map_mul]
        exact Subgroup.mem_map_of_mem f hy)
      exact h
    · intro R' hAR' hR'S' hN
      have hZN : Z ≤ Subgroup.normalizer (R' : Set Y) := le_sup_left.trans hN
      have hSN' : S ≤ Subgroup.normalizer (R' : Set Y) :=
        (le_inf le_rfl hSN).trans (le_sup_right.trans hN)
      have hzZ : z ∈ Z := by
        rw [hZdef, Subgroup.mem_comap, hz]
        exact Subgroup.mem_zpowers l33w_z
      have hzN := hZN hzZ
      have hzN' : z⁻¹ ∈ Subgroup.normalizer (R' : Set Y) := inv_mem hzN
      have hbot : R'.map f = ⊥ := by
        refine l33w_core_eq ?_ ?_ ?_
        · rw [← hS'map]
          exact Subgroup.map_mono hR'S'
        · intro r' hr'
          obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hr'
          refine ⟨Subgroup.mem_map.mpr ⟨z * r * z⁻¹, (Subgroup.mem_normalizer_iff.mp hzN r).mp hr,
            by simp [hz]⟩, Subgroup.mem_map.mpr ⟨z⁻¹ * r * z⁻¹⁻¹,
            (Subgroup.mem_normalizer_iff.mp hzN' r).mp hr, by simp [hz]⟩⟩
        · intro s hs r' hr'
          rw [← hfS] at hs
          obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hs
          obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hr'
          exact Subgroup.mem_map.mpr ⟨s' * r * s'⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hSN' hs') r).mp hr, by simp⟩
      obtain ⟨a, haA, haK⟩ := SetLike.not_le_iff_exists.1 hAK
      have ha' : x'⁻¹ * a * x' ∈ R' := hAR' (by
        rw [CFSG.Quasithin.mem_conjSubgroup_iff]
        simpa [mul_assoc] using haA)
      have h1 : f (x'⁻¹ * a * x') = 1 := by
        have := Subgroup.mem_map_of_mem f ha'
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      have h2 : x'⁻¹ * a * x' = 1 := hfinj (h1.trans (map_one f).symm)
      have h3 : a = 1 := by
        have : a = x' * (x'⁻¹ * a * x') * x'⁻¹ := by group
        rw [this, h2, mul_one, mul_inv_cancel]
      exact haK (h3 ▸ one_mem K)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
