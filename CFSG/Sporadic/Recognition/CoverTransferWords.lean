module

public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.WordSubgroup
public import CFSG.LieType.Multipliers.TitsCheckInputs

public section

namespace CFSG.Sporadic.Recognition.CoverTransfer

open CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Sporadic.Schreier.Tits CFSG.LieType.Multipliers.Tits
  Subgroup

theorem toLetters_zword {m : ℕ} : ∀ w : List (Fin m × Bool), toLetters m (zword w) = w
  | [] => rfl
  | (i, b) :: w => by
    have hw : toLetters m (zword w) = w := toLetters_zword w
    have hi := i.2
    have hcons : ∀ (l : ℤ) (h : l ≠ 0 ∧ l.natAbs ≤ m) (w' : List ℤ),
        toLetters m (l :: w') = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) :: toLetters m w' :=
      fun l h w' => by simp [toLetters, h]
    cases b
    · have e : zword ((i, false) :: w) = -((i.val : ℤ) + 1) :: zword w := rfl
      rw [e, hcons _ (by omega), hw]
      refine congrArg₂ List.cons (Prod.ext (Fin.ext ?_) ?_) rfl
      · show (-((i.val : ℤ) + 1)).natAbs - 1 = i.val
        omega
      · show decide (0 < -((i.val : ℤ) + 1)) = false
        simp only [decide_eq_false_iff_not, not_lt]
        omega
    · have e : zword ((i, true) :: w) = ((i.val : ℤ) + 1) :: zword w := rfl
      rw [e, hcons _ (by omega), hw]
      refine congrArg₂ List.cons (Prod.ext (Fin.ext ?_) ?_) rfl
      · show ((i.val : ℤ) + 1).natAbs - 1 = i.val
        omega
      · show decide (0 < (i.val : ℤ) + 1) = true
        simp only [decide_eq_true_eq]
        omega

theorem lift_mk_eq_wordIn {G : Type*} [Group G] {m : ℕ} (gs : ℕ → G)
    (w : List (Fin m × Bool)) :
    FreeGroup.lift (fun i : Fin m => gs i) (FreeGroup.mk w) = wordIn m gs (zword w) := by
  rw [wordIn, toLetters_zword]
  rfl

theorem lift_mk_substWord {G : Type*} [Group G] {m k : ℕ} (g : Fin m → G)
    (hs : List (List (Fin m × Bool))) (r : List (Fin k × Bool)) :
    FreeGroup.lift (fun i : Fin k => FreeGroup.lift g (FreeGroup.mk (hs.getD i [])))
      (FreeGroup.mk r) = FreeGroup.lift g (FreeGroup.mk (substWord hs r)) := by
  induction r with
  | nil => simp [substWord]
  | cons l r ih =>
    obtain ⟨i, b⟩ := l
    rw [show FreeGroup.mk ((i, b) :: r) = FreeGroup.mk [(i, b)] * FreeGroup.mk r from
      by rw [FreeGroup.mul_mk]; rfl, map_mul, ih]
    simp only [substWord, List.flatMap_cons]
    rw [← FreeGroup.mul_mk, map_mul]
    congr 1
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← FreeGroup.inv_mk, map_inv, show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl,
        map_inv, FreeGroup.lift_apply_of]
    · simp only [↓reduceIte]
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]

theorem mk_eq_lift_of {α : Type*} (rels : Set (FreeGroup α)) (x : FreeGroup α) :
    PresentedGroup.mk rels x = FreeGroup.lift PresentedGroup.of x := by
  have h : FreeGroup.lift (PresentedGroup.of : α → PresentedGroup rels) = PresentedGroup.mk rels :=
    FreeGroup.ext_hom _ _ fun _ => FreeGroup.lift_apply_of
  rw [h]

theorem index_le_of_subsetCheckShortCC {m : ℕ} (ws : List (List (Fin m × Bool))) (S : List ℕ)
    {k cap n : ℕ} (h : subsetCheckShortCC ws S k cap n = true) (H : Subgroup (PG m ws))
    (hH : ∀ i ∈ subsetOf m S, (PresentedGroup.of i : PG m ws) ∈ H) :
    H.FiniteIndex ∧ H.index ≤ n :=
  index_le_of_checkHLT (goodColParamsShort ws _ k H (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
      exact hH i hi))
    (by simpa [colParamsShort, mkParams] using closure_colLetter ws)
    (subsetCheckShortC_of_subsetCheckShortCC ws S h)

theorem card_PG_le_of_subsetCheckShortCC_nil {m : ℕ} (ws : List (List (Fin m × Bool)))
    {k cap n : ℕ} (h : subsetCheckShortCC ws [] k cap n = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have hS : subsetOf m [] = [] := by simp [subsetOf]
  have : Finite (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) := by
    rw [hS]; exact (inferInstance : Finite (PG 0 _))
  have hc : Nat.card (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) = 1 := by
    rw [hS]; exact card_PG_zero _
  have := card_le_of_subsetCheckShortCC ws [] h
  rwa [hc, mul_one] at this

theorem lift_mk_map {G : Type*} [Group G] {α β : Type*} (g : β → G) (σ : α → β)
    (w : List (α × Bool)) :
    FreeGroup.lift (fun a => g (σ a)) (FreeGroup.mk w) =
      FreeGroup.lift g (FreeGroup.mk (w.map fun l => (σ l.1, l.2))) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨a, b⟩ := l
    rw [List.map_cons, show FreeGroup.mk ((a, b) :: w) = FreeGroup.mk [(a, b)] * FreeGroup.mk w
      from rfl, show FreeGroup.mk ((σ a, b) :: w.map fun l => (σ l.1, l.2)) =
        FreeGroup.mk [(σ a, b)] * FreeGroup.mk (w.map fun l => (σ l.1, l.2)) from rfl,
      map_mul, map_mul, ih]
    congr 1

theorem lift_restrictWords {G : Type*} [Group G] {m : ℕ} (ws : List (List (Fin m × Bool)))
    (S : List (Fin m)) (g : Fin m → G) (hg : ∀ w ∈ ws, FreeGroup.lift g (FreeGroup.mk w) = 1) :
    ∀ r ∈ {r : FreeGroup (Fin S.length) | r ∈ (restrictWords S ws).map FreeGroup.mk},
      FreeGroup.lift (fun j => g (S.get j)) r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, List.mem_map, restrictWords, List.mem_filterMap] at hr
  obtain ⟨w', ⟨w, hw, hren⟩, rfl⟩ := hr
  rw [lift_mk_map, map_renumber S w w' hren]
  exact hg w hw

theorem mk_replicate {α : Type*} (a : α) (n : ℕ) :
    FreeGroup.mk (List.replicate n (a, true)) = FreeGroup.of a ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, pow_succ', ← ih]
    rfl

theorem card_range_le_index_mul {A B : Type*} [Group A] [Group B] (f : A →* B) (H : Subgroup A)
    [H.FiniteIndex] : Nat.card f.range ≤ H.index * Nat.card (H.map f) := by
  have hd : (H.map f.rangeRestrict).index ∣ H.index :=
    H.index_map_dvd f.rangeRestrict_surjective
  have hle : (H.map f.rangeRestrict).index ≤ H.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))) hd
  have hmap : (H.map f.rangeRestrict).map f.range.subtype = H.map f := by
    rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
  have hcard : Nat.card (H.map f.rangeRestrict) = Nat.card (H.map f) := by
    rw [← hmap, Subgroup.card_map_of_injective f.range.subtype_injective]
  rw [← (H.map f.rangeRestrict).index_mul_card, hcard]
  exact Nat.mul_le_mul_right _ hle

theorem eq_of_mem_zpowers_of_ne_one {L : Type*} [Group L] {t x : L} (ht : orderOf t = 2)
    (hx : x ∈ zpowers t) (hx1 : x ≠ 1) : x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, ht] at hx1 ⊢
  have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h2 with h | h
  · rw [h, zpow_zero] at hx1; exact absurd rfl hx1
  · rw [h, zpow_one]

end CFSG.Sporadic.Recognition.CoverTransfer
