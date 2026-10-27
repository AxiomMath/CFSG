module

public import CFSG.Sporadic.Recognition.J3MultiplierChecks

public section

namespace CFSG.Sporadic.Recognition.J3Multiplier

open CFSG.CosetTable CFSG.Monster.Schur

@[expose] def lift3 (w : List (Fin 2 × Bool)) : List (Fin 3 × Bool) :=
  w.map fun x => (x.1.castSucc, x.2)

@[expose] def uhatWords : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true), (0, true), (0, true)],
    [(0, true), (0, true), (1, true), (0, false), (0, false), (1, false)],
    [(2, true), (2, true)], [(2, true), (0, true), (2, false), (0, false)],
    [(2, true), (1, true), (2, false), (1, false)]] ++ U.map lift3 ++
    [lift3 (T 1) ++ [(2, false)]]

theorem lift_of_mk {m : ℕ} {S : Set (FreeGroup (Fin m))} (w : FreeGroup (Fin m)) :
    FreeGroup.lift (PresentedGroup.of (rels := S)) w = PresentedGroup.mk S w := by
  have h : FreeGroup.lift (PresentedGroup.of (rels := S)) = PresentedGroup.mk S :=
    FreeGroup.ext_hom _ _ fun i => rfl
  rw [h]

theorem card_le_of_quot {m : ℕ} (ws : List (List (Fin m × Bool))) {Q : Type*} [Group Q]
    (f : Fin m → Q) (hrel : ∀ r ∈ ws, FreeGroup.lift f (FreeGroup.mk r) = 1)
    (hgen : Subgroup.closure (Set.range f) = ⊤) [Finite (PG m ws)] :
    Finite Q ∧ Nat.card Q ≤ Nat.card (PG m ws) := by
  have hrel' : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk},
      FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [Set.mem_setOf_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    exact hrel w hw
  set ρ := PresentedGroup.toGroup hrel'
  have hsurj : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  exact ⟨Finite.of_surjective ρ hsurj, Nat.card_le_card_of_surjective ρ hsurj⟩

theorem lift_mk_lift3 {E : Type*} [Group E] (f : Fin 3 → E) (w : List (Fin 2 × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (lift3 w)) =
      FreeGroup.lift (fun i : Fin 2 => f i.castSucc) (FreeGroup.mk w) := by
  simp [lift3, FreeGroup.lift_mk, List.map_map, Function.comp_def]

theorem lift_mk_append' {α E : Type*} [Group E] (f : α → E) (u v : List (α × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (u ++ v)) =
      FreeGroup.lift f (FreeGroup.mk u) * FreeGroup.lift f (FreeGroup.mk v) := by
  rw [← FreeGroup.mul_mk, map_mul]

theorem uhat_rels {E : Type*} [Group E] (f : Fin 3 → E)
    (hU : ∀ r ∈ U, FreeGroup.lift (fun i : Fin 2 => f i.castSucc) (FreeGroup.mk r) = 1)
    (hT1 : FreeGroup.lift (fun i : Fin 2 => f i.castSucc) (FreeGroup.mk (T 1)) = f 2)
    (h4 : f 0 * f 0 * f 0 * f 0 = 1) (h2c : Commute (f 0 * f 0) (f 1))
    (hv : f 2 * f 2 = 1) (hva : Commute (f 2) (f 0)) (hvc : Commute (f 2) (f 1)) :
    ∀ r ∈ uhatWords, FreeGroup.lift f (FreeGroup.mk r) = 1 := by
  intro w hw
  unfold uhatWords at hw
  rcases List.mem_append.1 hw with hw | hw
  · rcases List.mem_append.1 hw with hw | hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · simpa [FreeGroup.lift_mk, mul_assoc] using h4
      · simp only [FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, Bool.cond_true, Bool.cond_false, mul_one]
        have := h2c.eq
        calc f 0 * (f 0 * (f 1 * ((f 0)⁻¹ * ((f 0)⁻¹ * (f 1)⁻¹))))
            = f 0 * f 0 * f 1 * (f 0 * f 0)⁻¹ * (f 1)⁻¹ := by group
          _ = 1 := by rw [this]; group
      · simpa [FreeGroup.lift_mk] using hv
      · simp only [FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, Bool.cond_true, Bool.cond_false, mul_one]
        rw [← mul_assoc, hva.eq]
        group
      · simp only [FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, Bool.cond_true, Bool.cond_false, mul_one]
        rw [← mul_assoc, hvc.eq]
        group
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw
      rw [lift_mk_lift3]
      exact hU u hu
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    rw [lift_mk_append', lift_mk_lift3, hT1]
    simp [FreeGroup.lift_mk]

theorem card_plain_le_uhat [Finite (PG 3 uhatWords)] :
    Finite (PG 2 plainWords) ∧ Nat.card (PG 2 plainWords) ≤ Nat.card (PG 3 uhatWords) := by
  set S := {r : FreeGroup (Fin 2) | r ∈ plainWords.map FreeGroup.mk}
  have hone : ∀ w ∈ plainWords, FreeGroup.lift (PresentedGroup.of (rels := S))
      (FreeGroup.mk w) = 1 := fun w hw => by
    rw [lift_of_mk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)
  set f : Fin 3 → PresentedGroup S := ![PresentedGroup.of 0, PresentedGroup.of 1, 1]
  have hf : (fun i : Fin 2 => f i.castSucc) = PresentedGroup.of := by
    funext i
    fin_cases i <;> rfl
  have ha2 : f 0 * f 0 = 1 := by
    have := hone (T 0) (List.mem_append_right _ (List.mem_map.2 ⟨0, List.mem_finRange 0, rfl⟩))
    simpa [T, a2, FreeGroup.lift_mk, f] using this
  refine card_le_of_quot uhatWords f (uhat_rels f ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [hf]
    exact fun r hr => hone r (List.mem_append_left _ hr)
  · rw [hf]
    exact hone _ (List.mem_append_right _ (List.mem_map.2 ⟨1, List.mem_finRange 1, rfl⟩))
  · rw [ha2, one_mul, ha2]
  · rw [ha2]
    exact Commute.one_left _
  · simp [f]
  · simp [f]
  · simp [f]
  · rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i.castSucc, by rw [congrFun hf i]⟩

theorem card_eps_le_uhat [Finite (PG 3 uhatWords)] (e : Fin 2 → Bool) (he : ∃ i, e i = true) :
    Finite (PG (2 + 1) (epsRels U T e)) ∧
      Nat.card (PG (2 + 1) (epsRels U T e)) ≤ Nat.card (PG 3 uhatWords) := by
  classical
  set S := {r : FreeGroup (Fin (2 + 1)) | r ∈ (epsRels U T e).map FreeGroup.mk}
  have hone : ∀ w ∈ epsRels U T e, FreeGroup.lift (PresentedGroup.of (rels := S))
      (FreeGroup.mk w) = 1 := fun w hw => by
    rw [lift_of_mk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)
  obtain ⟨z, hz⟩ : ∃ z : PresentedGroup S, z = PresentedGroup.of (Fin.last 2) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin 2 → PresentedGroup S, g = fun i => PresentedGroup.of i.castSucc :=
    ⟨_, rfl⟩
  have hz2 : z * z = 1 := by
    have := hone _ (by unfold epsRels; exact List.mem_cons_self)
    simpa [zLetter, FreeGroup.lift_mk, hz] using this
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzc : ∀ i : Fin 2, Commute z (g i) := by
    intro i
    have := hone [zLetter 2, (i.castSucc, true), zLetter 2, (i.castSucc, false)] (by
      unfold epsRels
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))))
    simp only [zLetter, FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, Bool.cond_true, Bool.cond_false, mul_one] at this
    rw [← hz, show PresentedGroup.of i.castSucc = g i by rw [hg]] at this
    have h1 : z * (g i * z) = g i := by
      have := congrArg (· * g i) this
      simpa [mul_assoc] using this
    calc z * g i = z * g i * z * z := by rw [mul_assoc _ z z, hz2, mul_one]
      _ = g i * z := by rw [mul_assoc z, h1]
  have hU : ∀ r ∈ U, FreeGroup.lift g (FreeGroup.mk r) = 1 := by
    intro r hr
    have := hone (castWord r) (by
      unfold epsRels
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨r, hr, rfl⟩))))
    rwa [lift_mk_castWord, ← hg] at this
  have hT : ∀ i : Fin 2, FreeGroup.lift g (FreeGroup.mk (T i)) = if e i then z else 1 := by
    intro i
    have := hone (castWord (T i) ++ (if e i then [zLetter 2] else [])) (by
      unfold epsRels
      exact List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)))
    rw [lift_mk_append', lift_mk_castWord, ← hg] at this
    split_ifs at this ⊢ with h
    · simp only [zLetter, FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, Bool.cond_true, mul_one] at this
      rw [← hz] at this
      rw [← hzi]
      exact eq_inv_of_mul_eq_one_left this
    · simpa [← FreeGroup.one_eq_mk] using this
  have hzc' : ∀ x : PresentedGroup S, x = z ∨ x = 1 → ∀ i : Fin 2, Commute x (g i) := by
    rintro x (rfl | rfl) i
    · exact hzc i
    · exact Commute.one_left _
  have hzz : ∀ x : PresentedGroup S, x = z ∨ x = 1 → x * x = 1 := by
    rintro x (rfl | rfl)
    · exact hz2
    · exact mul_one 1
  set w0 : PresentedGroup S := if e 0 then z else 1
  set w1 : PresentedGroup S := if e 1 then z else 1
  have hw0 : w0 = z ∨ w0 = 1 := by simp only [w0]; split_ifs <;> simp
  have hw1 : w1 = z ∨ w1 = 1 := by simp only [w1]; split_ifs <;> simp
  have ha2 : g 0 * g 0 = w0 := by
    have := hT 0
    simpa [T, a2, FreeGroup.lift_mk] using this
  set f : Fin 3 → PresentedGroup S := ![g 0, g 1, w1]
  have hf : (fun i : Fin 2 => f i.castSucc) = g := by
    funext i
    fin_cases i <;> rfl
  refine card_le_of_quot uhatWords f (uhat_rels f ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · rw [hf]; exact hU
  · rw [hf, hT 1]; rfl
  · change g 0 * g 0 * g 0 * g 0 = 1
    rw [ha2, mul_assoc, ha2]
    exact hzz _ hw0
  · change Commute (g 0 * g 0) (g 1)
    rw [ha2]
    exact hzc' _ hw0 1
  · exact hzz _ hw1
  · exact hzc' _ hw1 0
  · exact hzc' _ hw1 1
  · have hzm : z ∈ Subgroup.closure (Set.range f) := by
      obtain ⟨i, hi⟩ := he
      fin_cases i
      · have hi' : e 0 = true := hi
        have : g 0 * g 0 = z := by rw [ha2]; simp [w0, hi']
        rw [← this]
        exact mul_mem (Subgroup.subset_closure ⟨0, rfl⟩) (Subgroup.subset_closure ⟨0, rfl⟩)
      · have hi' : e 1 = true := hi
        exact Subgroup.subset_closure ⟨2, by simp [f, w1, hi']⟩
    rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [← hz]
      exact hzm
    · exact Subgroup.subset_closure ⟨j.castSucc, by rw [congrFun hf j, hg]⟩

end CFSG.Sporadic.Recognition.J3Multiplier
