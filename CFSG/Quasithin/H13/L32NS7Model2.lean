module

public import CFSG.Quasithin.H13.L32NS7Model
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.Quasithin.H13.S7Cert

open Mat8Cert CFSG.Quasithin.H13.L1442M

theorem bimp {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  cases a <;> cases b <;> simp_all

@[expose] def N7 : Subgroup (GL (Fin 8) (ZMod 2)) := genSub n8G

theorem cvB_spec :
    (elemsOf n8G).length = 8 ∧ subB n8G (elemsOf n8G) = true ∧ (∀ g ∈ n8G, g ∈ s7E) ∧
      (∀ n ∈ cvE, mul8 (invCv n) n = one8) ∧
      ∀ x ∈ cvE, mul8 x x = one8 →
        (∀ n ∈ cvE, mul8 x (mul8 (mul8 n x) (invCv n)) = mul8 (mul8 (mul8 n x) (invCv n)) x) →
        x ∈ elemsOf n8G := by
  have h := s7Check_parts.2.2.1
  simp only [cvB] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun x hx hsq hcomm => ?_⟩
  have := bimp (h5 x hx) (by
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    exact ⟨hsq, hcomm⟩)
  simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using this

theorem mem_N7_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ N7 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ elemsOf n8G :=
  mem_genSub_iff_of cvB_spec.2.1 (unit_of_s7E cvB_spec.2.2.1) u

theorem card_N7 : Nat.card N7 = 8 := by
  rw [N7, card_genSub_of cvB_spec.2.1 (unit_of_s7E cvB_spec.2.2.1), cvB_spec.1]

theorem colsOf_inv_of {n : GL (Fin 8) (ZMod 2)} {c : List ℕ} (hc : Valid8 c)
    (h : mul8 c (colsOf (n : Matrix (Fin 8) (Fin 8) (ZMod 2))) = one8) :
    colsOf ((n⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) = c := by
  rw [colsOf_eq_iff hc]
  have h1 : dec8 c * (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) = 1 := by
    have := congrArg dec8 h
    rwa [dec8_mul8 _ _ (valid8_colsOf _).1, dec8_colsOf, dec8_one8] at this
  calc dec8 c = dec8 c * ((n : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
      ((n⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    _ = ((n⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
        rw [← mul_assoc, h1, one_mul]

theorem mem_N7_of {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ s7)
    (hfix : (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vStar) = vec8 vStar)
    (hsq : x * x = 1)
    (hcomm : ∀ n ∈ s7, (n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vStar) = vec8 vStar →
      x * (n * x * n⁻¹) = (n * x * n⁻¹) * x) : x ∈ N7 := by
  have hvS : vStar < 256 := by decide
  have hcv : ∀ y : GL (Fin 8) (ZMod 2), y ∈ s7 →
      (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vStar) = vec8 vStar →
      colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ cvE := by
    intro y hy hyf
    refine List.mem_filter.mpr ⟨colsOf_mem_s7E hy, ?_⟩
    rw [mulVec_vec8] at hyf
    exact beq_iff_eq.mpr (vec8_inj (mv8_lt (valid8_colsOf _) _) hvS hyf)
  rw [mem_N7_iff]
  refine cvB_spec.2.2.2.2 _ (hcv x hx hfix) ?_ ?_
  · rw [← colsOf_mul, ← Units.val_mul, hsq, Units.val_one, colsOf_one]
  · intro n' hn'
    obtain ⟨hn's7, hn'fix⟩ := List.mem_filter.mp hn'
    obtain ⟨n, hn, hnc⟩ := exists_mem_s7 hn's7
    have hval : Valid8 n' := (subB_spec s7Basic_spec.1).1 _ hn's7
    have hnn : colsOf (n : Matrix (Fin 8) (Fin 8) (ZMod 2)) = n' := by
      rw [hnc, colsOf_dec8 hval]
    have hnfix : (n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vStar) = vec8 vStar := by
      rw [mulVec_vec8, hnn, beq_iff_eq.mp hn'fix]
    have hinv : colsOf ((n⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
        invCv n' := by
      refine colsOf_inv_of ?_ (by rw [hnn]; exact cvB_spec.2.2.2.1 n' hn')
      unfold invCv
      cases hf : cvE.find? (fun m => mul8 m n' == one8) with
      | none => exact ⟨rfl, by decide⟩
      | some m =>
        exact (subB_spec s7Basic_spec.1).1 _ (List.mem_filter.mp (List.mem_of_find?_eq_some hf)).1
    have := congrArg (fun y : GL (Fin 8) (ZMod 2) => colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)))
      (hcomm n hn hnfix)
    simp only [Units.val_mul, colsOf_mul, hnn, hinv] at this
    exact this

theorem eW_spec :
    ∀ p ∈ eW, p.1 ∈ elemsOf n8G ∧ b4N p.2 vStar = false := by
  have h := s7Check_parts.2.2.2.1
  simp only [eWB] at h
  simp only [List.all_eq_true, Bool.and_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.not_eq_true'] at h
  exact h

theorem eSpan_mem (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hW : ∀ p ∈ eW, vec8 (mv8 p.1 p.2 ^^^ p.2) ∈ W) : ∀ c ∈ eSpan, vec8 c ∈ W := by
  refine spanN_mem _ W ?_
  intro v hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact hW p hp

@[expose] def M7 (i : ℕ) : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (pG ++ [mReps.getD i one8])

theorem ovB_spec :
    mReps.length = 3 ∧ (∀ r ∈ mReps, r ∈ s7E) ∧
      (∀ i ∈ [0, 1, 2], (mE i).length = 48 ∧ subB (pG ++ [mReps.getD i one8]) (mE i) = true) ∧
      ∀ y ∈ s7E, y ∈ elemsOf pG ∨
        (49 ≤ (elemsOf (pG ++ [y]) 49).length ∧ nodupB (elemsOf (pG ++ [y]) 49) = true) ∨
        ((elemsOf (pG ++ [y]) 49).length = 48 ∧ nodupB (elemsOf (pG ++ [y]) 49) = true ∧
          ∃ i ∈ [0, 1, 2], ∀ b ∈ elemsOf (pG ++ [y]) 49, b ∈ mE i) := by
  have h := s7Check_parts.2.2.2.2.1
  simp only [ovB] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_map] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  rcases h4 y hy with h | h | ⟨⟨h5, h6⟩, ⟨_, ⟨i, hi, rfl⟩, h7⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨h5, h6, i, hi, fun b hb => ?_⟩)
    have := h7 b hb
    simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using this

theorem mRep_mem {i : ℕ} (hi : i < 3) :
    mReps.getD i one8 ∈ s7E := by
  rw [List.getD_eq_getElem _ _ (by rw [ovB_spec.1]; exact hi)]
  exact ovB_spec.2.1 _ (List.getElem_mem _)

theorem M7_gens_mem {i : ℕ} (hi : i < 3) :
    ∀ g ∈ pG ++ [mReps.getD i one8], g ∈ s7E := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact pB_spec.2.2.1 g hg
  · rw [List.mem_singleton.mp hg]; exact mRep_mem hi

theorem M7_le_s7 {i : ℕ} (hi : i < 3) : M7 i ≤ s7 :=
  genSub_le_s7 (M7_gens_mem hi)

theorem mE_spec {i : ℕ} (hi : i < 3) :
    (mE i).length = 48 ∧ subB (pG ++ [mReps.getD i one8]) (mE i) = true :=
  ovB_spec.2.2.1 i (by interval_cases i <;> simp)

theorem mem_M7_iff {i : ℕ} (hi : i < 3) (u : GL (Fin 8) (ZMod 2)) :
    u ∈ M7 i ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ mE i :=
  mem_genSub_iff_of (mE_spec hi).2 (unit_of_s7E (M7_gens_mem hi)) u

theorem card_M7 {i : ℕ} (hi : i < 3) : Nat.card (M7 i) = 48 := by
  rw [M7, card_genSub_of (mE_spec hi).2 (unit_of_s7E (M7_gens_mem hi))]
  exact (mE_spec hi).1

theorem P7_le_M7 (i : ℕ) : P7 ≤ M7 i :=
  Subgroup.closure_mono fun _ hu => List.mem_append_left _ hu

theorem le_card_of_list {M : Subgroup (GL (Fin 8) (ZMod 2))} {B : List (List ℕ)} (hB : B.Nodup)
    (hBM : ∀ b ∈ B, ∃ u ∈ M, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 b)
    (hval : ∀ b ∈ B, Valid8 b) : B.length ≤ Nat.card M := by
  classical
  let f : {b // b ∈ B} → M := fun b =>
    ⟨Classical.choose (hBM b.1 b.2), (Classical.choose_spec (hBM b.1 b.2)).1⟩
  have hf : Function.Injective f := by
    intro b b' h
    have h1 := congrArg (fun u : M => ((u : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)))
      h
    simp only [f, (Classical.choose_spec (hBM b.1 b.2)).2,
      (Classical.choose_spec (hBM b'.1 b'.2)).2] at h1
    exact Subtype.ext (dec8_injOn (hval _ b.2) (hval _ b'.2) h1)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := B) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hB] at this

theorem eq_M7_of {M : Subgroup (GL (Fin 8) (ZMod 2))}
    (hMs : M ≤ s7) (hPM : P7 ≤ M) (hcard : Nat.card M = 48) : ∃ i < 3, M = M7 i := by
  obtain ⟨y, hyM, hyP⟩ : ∃ y ∈ M, y ∉ P7 := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show M ≤ P7 from h)
    rw [hcard, card_P7] at this
    omega
  set c := colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)) with hc
  have hcs : c ∈ s7E := colsOf_mem_s7E (hMs hyM)
  have hcP : c ∉ elemsOf pG := fun h => hyP ((mem_P7_iff y).mpr h)
  have hgens : ∀ g ∈ pG ++ [c], g ∈ s7E := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact pB_spec.2.2.1 g hg
    · rw [List.mem_singleton.mp hg]; exact hcs
  have hval : ∀ g ∈ pG ++ [c], Valid8 g := fun g hg => (subB_spec s7Basic_spec.1).1 _ (hgens g hg)
  have hle : genSub (pG ++ [c]) ≤ M := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    rcases List.mem_append.mp hu with hu | hu
    · exact hPM (Subgroup.subset_closure hu)
    · have : u = y := eq_of_colsOf_eq (List.mem_singleton.mp hu)
      exact this ▸ hyM
  have hB : ∀ b ∈ elemsOf (pG ++ [c]) 49,
      ∃ u ∈ M, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 b := by
    intro b hb
    obtain ⟨w, rfl⟩ := mem_elemsOf hb
    obtain ⟨u, hu, hu'⟩ := exists_evalW (pG ++ [c]) hval (unit_of_s7E hgens) w
    exact ⟨u, hle hu, hu'⟩
  have hBval : ∀ b ∈ elemsOf (pG ++ [c]) 49, Valid8 b := by
    intro b hb
    obtain ⟨w, rfl⟩ := mem_elemsOf hb
    exact valid8_evalW _ hval w
  rcases ovB_spec.2.2.2 c hcs with h | h | ⟨h48, hnd, i, hi, hsub⟩
  · exact absurd h hcP
  · have := le_card_of_list (nodup_of_nodupB h.2) hB hBval
    rw [hcard] at this
    omega
  · have hi3 : i < 3 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    refine ⟨i, hi3, ?_⟩
    have hBi : ∀ b ∈ elemsOf (pG ++ [c]) 49,
        ∃ u ∈ M ⊓ M7 i, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 b := by
      intro b hb
      obtain ⟨u, hu, hu'⟩ := hB b hb
      refine ⟨u, ⟨hu, (mem_M7_iff hi3 u).mpr ?_⟩, hu'⟩
      rw [hu', colsOf_dec8 (hBval b hb)]
      exact hsub b hb
    have hle48 := le_card_of_list (nodup_of_nodupB hnd) hBi hBval
    rw [h48] at hle48
    have hMi : M ≤ M7 i := by
      have heq : M ⊓ M7 i = M :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard]; exact hle48)
      rw [← heq]
      exact inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hMi (by rw [card_M7 hi3, hcard])

end CFSG.Quasithin.H13.S7Cert
