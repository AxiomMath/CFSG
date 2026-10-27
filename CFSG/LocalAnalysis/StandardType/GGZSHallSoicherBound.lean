module

public import CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
import all CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
public import Certificates.Certificate709541
public import Mathlib

public section

namespace CFSG.StandardType.ZS

open CFSG.CosetTable

private theorem rels_of_words {G : Type*} [Group G] {m : ℕ} {ws : List (List (Fin m × Bool))}
    {r : Fin m → G} (h : ∀ w ∈ ws, FreeGroup.lift r (FreeGroup.mk w) = 1) :
    ∀ ρ ∈ ({ρ : FreeGroup (Fin m) | ρ ∈ ws.map FreeGroup.mk} : Set (FreeGroup (Fin m))),
      FreeGroup.lift r ρ = 1 := by
  rintro ρ hρ
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hρ
  exact h w hw

private theorem range_toGroup {G : Type*} [Group G] {m : ℕ} {ws : List (List (Fin m × Bool))}
    {r : Fin m → G} (h : ∀ w ∈ ws, FreeGroup.lift r (FreeGroup.mk w) = 1) :
    (PresentedGroup.toGroup (rels_of_words h)).range = Subgroup.closure (Set.range r) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}, MonoidHom.map_closure]
  congr 1
  ext x
  simp [PresentedGroup.toGroup.of]

private theorem card_closure_le_of_words {G : Type*} [Group G] {m : ℕ}
    {ws : List (List (Fin m × Bool))} {N : ℕ} (hfin : Finite (PG m ws))
    (hN : Nat.card (PG m ws) ≤ N) {r : Fin m → G}
    (h : ∀ w ∈ ws, FreeGroup.lift r (FreeGroup.mk w) = 1) :
    Nat.card (Subgroup.closure (Set.range r)) ≤ N := by
  have : Finite (PG m ws) := hfin
  let φ : PG m ws →* G := PresentedGroup.toGroup (rels_of_words h)
  have hrange : φ.range = Subgroup.closure (Set.range r) := range_toGroup h
  rw [← hrange]
  exact (Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective).trans hN

private theorem lift_pairPowWord {G : Type*} [Group G] {m : ℕ} (r : Fin m → G)
    (i j : Fin m) (k : ℕ) :
    FreeGroup.lift r (FreeGroup.mk (pairPowWord i j k)) = (r i * r j) ^ k := by
  rw [pairPowWord, mk_flatten_replicate, map_pow]
  congr 1
  simp [FreeGroup.lift_mk]

private theorem lift_four_letter_power {G : Type*} [Group G] {α : Type*} (r : α → G)
    (a b c d : α) :
    FreeGroup.lift r
        (FreeGroup.mk ((List.replicate 3 [(a, true), (b, true), (c, true), (d, true)]).flatten)) =
      (r a * r b * r c * r d) ^ 3 := by
  rw [mk_flatten_replicate, map_pow]
  congr 1
  simp [FreeGroup.lift_mk, mul_assoc]

private theorem lift_eq_one_of_hsFiveRel {G : Type*} [Group G] {r : Fin 5 → G}
    (h : HSFiveRel r) : ∀ w ∈ hsFiveRels, FreeGroup.lift r (FreeGroup.mk w) = 1 := by
  change (∀ i j, (r i * r j) ^ kFiveExp i j = 1) ∧
    (r 2 * r 1 * r 2 * r 3) ^ 3 = 1 at h
  obtain ⟨hpair, hextra⟩ := h
  intro w hw
  simp only [hsFiveRels, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, decide_eq_true_eq, true_and, List.mem_singleton] at hw
  rcases hw with ⟨i, -, j, -, rfl⟩ | rfl
  · rw [lift_pairPowWord, hpair]
  · rw [lift_four_letter_power]
    simpa using hextra

private theorem lift_eq_one_of_hsSixRel {G : Type*} [Group G] {r : Fin 6 → G}
    (h : HSSixRel r) : ∀ w ∈ hsSixRels, FreeGroup.lift r (FreeGroup.mk w) = 1 := by
  change (∀ i j, (r i * r j) ^ kSixExp i j = 1) ∧
    (r 2 * r 1 * r 2 * r 3) ^ 3 = 1 at h
  obtain ⟨hpair, hextra⟩ := h
  intro w hw
  simp only [hsSixRels, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, decide_eq_true_eq, true_and, List.mem_singleton] at hw
  rcases hw with ⟨i, -, j, -, rfl⟩ | rfl
  · rw [lift_pairPowWord, hpair]
  · rw [lift_four_letter_power]
    simpa using hextra

private theorem card_le_of_hsFiveRels :
    Finite (PG 5 hsFiveRels) ∧ Nat.card (PG 5 hsFiveRels) ≤ 51840 :=
  Certificates.certificate709541.1

private theorem card_le_of_hsSixRels :
    Finite (PG 6 hsSixRels) ∧ Nat.card (PG 6 hsSixRels) ≤ 39191040 :=
  Certificates.certificate709541.2

private theorem exists_mulEquiv_of_words {G H : Type*} [Group G] [Group H]
    {m N : ℕ} {ws : List (List (Fin m × Bool))} (hfin : Finite (PG m ws))
    (hN : Nat.card (PG m ws) ≤ N) {r : Fin m → G} {s : Fin m → H}
    (hr : ∀ w ∈ ws, FreeGroup.lift r (FreeGroup.mk w) = 1)
    (hs : ∀ w ∈ ws, FreeGroup.lift s (FreeGroup.mk w) = 1)
    (hG : Subgroup.closure (Set.range r) = ⊤) (hH : Subgroup.closure (Set.range s) = ⊤)
    (hcG : N ≤ Nat.card G) (hcH : N ≤ Nat.card H) :
    ∃ f : G ≃* H, ∀ i, f (r i) = s i := by
  have : Finite (PG m ws) := hfin
  let φG : PG m ws →* G := PresentedGroup.toGroup (rels_of_words hr)
  let φH : PG m ws →* H := PresentedGroup.toGroup (rels_of_words hs)
  have hsurjG : Function.Surjective φG := by
    rw [← MonoidHom.range_eq_top]
    exact (range_toGroup hr).trans hG
  have hsurjH : Function.Surjective φH := by
    rw [← MonoidHom.range_eq_top]
    exact (range_toGroup hs).trans hH
  let eG : PG m ws ≃* G :=
    MulEquiv.ofBijective φG (hsurjG.bijective_of_nat_card_le (hN.trans hcG))
  let eH : PG m ws ≃* H :=
    MulEquiv.ofBijective φH (hsurjH.bijective_of_nat_card_le (hN.trans hcH))
  refine ⟨eG.symm.trans eH, fun i => ?_⟩
  have hGof : eG (PresentedGroup.of i) = r i := by simp [eG, φG]
  have hHof : eH (PresentedGroup.of i) = s i := by simp [eH, φH]
  rw [MulEquiv.trans_apply, ← hGof, MulEquiv.symm_apply_apply, hHof]

theorem card_closure_le_of_hsFiveRel {G : Type*} [Group G]
    {r : Fin 5 → G} (h : HSFiveRel r) : Nat.card (Subgroup.closure (Set.range r)) ≤ 51840 := by
  obtain ⟨hfin, hN⟩ := card_le_of_hsFiveRels
  exact card_closure_le_of_words hfin hN (lift_eq_one_of_hsFiveRel h)

theorem card_closure_le_of_hsSixRel {G : Type*} [Group G]
    {r : Fin 6 → G} (h : HSSixRel r) : Nat.card (Subgroup.closure (Set.range r)) ≤ 39191040 := by
  obtain ⟨hfin, hN⟩ := card_le_of_hsSixRels
  exact card_closure_le_of_words hfin hN (lift_eq_one_of_hsSixRel h)

theorem exists_mulEquiv_of_hsFiveRel {G H : Type*} [Group G]
    [Group H] {r : Fin 5 → G} {s : Fin 5 → H} (hr : HSFiveRel r) (hs : HSFiveRel s)
    (hG : Subgroup.closure (Set.range r) = ⊤) (hH : Subgroup.closure (Set.range s) = ⊤)
    (hcG : 51840 ≤ Nat.card G) (hcH : 51840 ≤ Nat.card H) :
    ∃ f : G ≃* H, ∀ i, f (r i) = s i := by
  obtain ⟨hfin, hN⟩ := card_le_of_hsFiveRels
  exact exists_mulEquiv_of_words hfin hN (lift_eq_one_of_hsFiveRel hr)
    (lift_eq_one_of_hsFiveRel hs) hG hH hcG hcH

theorem exists_mulEquiv_of_hsSixRel {G H : Type*} [Group G]
    [Group H] {r : Fin 6 → G} {s : Fin 6 → H} (hr : HSSixRel r) (hs : HSSixRel s)
    (hG : Subgroup.closure (Set.range r) = ⊤) (hH : Subgroup.closure (Set.range s) = ⊤)
    (hcG : 39191040 ≤ Nat.card G) (hcH : 39191040 ≤ Nat.card H) :
    ∃ f : G ≃* H, ∀ i, f (r i) = s i := by
  obtain ⟨hfin, hN⟩ := card_le_of_hsSixRels
  exact exists_mulEquiv_of_words hfin hN (lift_eq_one_of_hsSixRel hr)
    (lift_eq_one_of_hsSixRel hs) hG hH hcG hcH

end CFSG.StandardType.ZS

end
