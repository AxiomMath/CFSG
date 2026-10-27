module

public import CFSG.Milestones.ASVolI.F48.Small.AutChartInputs
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutIface
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP0Base

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42Aut
open CFSG.Quasithin.H13.F431.U42 (P45)

section Words

@[expose] def burnsideF48s_autc_ev (G : Fin 5 → Ah) (w : List (Fin 5 × Bool)) : Ah :=
  (w.map fun l => cond l.2 (G l.1) (G l.1)⁻¹).prod

theorem burnsideF48s_autc_ev_nil (G : Fin 5 → Ah) : burnsideF48s_autc_ev G [] = 1 := by
  simp [burnsideF48s_autc_ev]

theorem burnsideF48s_autc_ev_cons (G : Fin 5 → Ah) (l : Fin 5 × Bool) (w : List (Fin 5 × Bool)) :
    burnsideF48s_autc_ev G (l :: w) = cond l.2 (G l.1) (G l.1)⁻¹ * burnsideF48s_autc_ev G w := by
  simp [burnsideF48s_autc_ev]

theorem burnsideF48s_autc_ev_mem {K : Subgroup Ah} (G : Fin 5 → Ah) (w : List (Fin 5 × Bool))
    (hK : ∀ l ∈ w, G l.1 ∈ K) : burnsideF48s_autc_ev G w ∈ K := by
  induction w with
  | nil => rw [burnsideF48s_autc_ev_nil]; exact K.one_mem
  | cons l w ih =>
    rw [burnsideF48s_autc_ev_cons]
    refine K.mul_mem ?_ (ih fun l' hl' => hK l' (List.mem_cons_of_mem _ hl'))
    have hl := hK l (List.mem_cons_self ..)
    obtain ⟨i, b⟩ := l
    cases b
    · exact K.inv_mem hl
    · exact hl

theorem burnsideF48s_autc_repL_ev (G : Fin 5 → Ah) (gl gli : List (List ℕ))
    (hl : ∀ k : Fin 5, RepL (gl.getD k []) ((G k : Ah) : P45))
    (hli : ∀ k : Fin 5, RepL (gli.getD k []) (((G k)⁻¹ : Ah) : P45)) (w : List (Fin 5 × Bool)) :
    RepL (burnsideF48s_autc_evL gl gli w) ((burnsideF48s_autc_ev G w : Ah) : P45) := by
  have hlet : ∀ l : Fin 5 × Bool, RepL (burnsideF48s_autc_letL gl gli l)
      ((cond l.2 (G l.1) (G l.1)⁻¹ : Ah) : P45) := by
    rintro ⟨i, b⟩
    cases b
    · exact hli i
    · exact hl i
  have key : ∀ (w : List (Fin 5 × Bool)) (acc : List ℕ) (σ : P45), RepL acc σ →
      RepL (w.foldl (fun acc l => compL acc (burnsideF48s_autc_letL gl gli l)) acc)
        (σ * ((burnsideF48s_autc_ev G w : Ah) : P45)) := by
    intro w
    induction w with
    | nil =>
      intro acc σ hacc
      simpa [burnsideF48s_autc_ev_nil] using hacc
    | cons l w ih =>
      intro acc σ hacc
      rw [List.foldl_cons, burnsideF48s_autc_ev_cons, Subgroup.coe_mul, ← mul_assoc]
      exact ih _ _ (repL_mul hacc (hlet l))
  have := key w (List.range 45) 1 (repL_one 45)
  rwa [one_mul] at this

theorem burnsideF48s_autc_gl_getD (XY : List (List ℕ)) (k : Fin 5) :
    (burnsideF48s_autc_gl XY).getD k [] = evalAL (XY.getD k []) := by
  unfold burnsideF48s_autc_gl
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]

theorem burnsideF48s_autc_gli_getD (XY : List (List ℕ)) (k : Fin 5) :
    (burnsideF48s_autc_gli XY).getD k [] = evalAL (invAL (XY.getD k [])) := by
  unfold burnsideF48s_autc_gli
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]

theorem burnsideF48s_autc_repL_gl (XY : List (List ℕ)) (k : Fin 5) :
    RepL ((burnsideF48s_autc_gl XY).getD k []) (wordAP (XY.getD k [])) := by
  rw [burnsideF48s_autc_gl_getD]
  exact repL_wordAP _

theorem burnsideF48s_autc_repL_gli (XY : List (List ℕ)) (k : Fin 5) :
    RepL ((burnsideF48s_autc_gli XY).getD k []) (wordAP (XY.getD k []))⁻¹ := by
  rw [burnsideF48s_autc_gli_getD, ← wordAP_invAL]
  exact repL_wordAP _

end Words

section WordLists

variable {G : Fin 5 → Ah} {gl gli : List (List ℕ)}

theorem burnsideF48s_autc_groupB_spec {idx : List (Fin 5)} {W : List (List (Fin 5 × Bool))}
    {n : ℕ} (hW : burnsideF48s_autc_groupB gl gli idx W n = true) :
    W.length = n ∧ [] ∈ W ∧ (W.map (burnsideF48s_autc_evL gl gli)).Nodup ∧
      (∀ w ∈ W, ∀ l ∈ w, l.1 ∈ idx) ∧
      ∀ x ∈ W.map (burnsideF48s_autc_evL gl gli), ∀ k ∈ idx,
        compL x (gl.getD k []) ∈ W.map (burnsideF48s_autc_evL gl gli) := by
  simp only [burnsideF48s_autc_groupB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_eq_mem] at hW
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hW
  exact ⟨h1, h2, h3, h4, h5⟩

theorem burnsideF48s_autc_mem_closure_iff
    (hl : ∀ k : Fin 5, RepL (gl.getD k []) ((G k : Ah) : P45))
    (hli : ∀ k : Fin 5, RepL (gli.getD k []) (((G k)⁻¹ : Ah) : P45)) {idx : List (Fin 5)}
    {W : List (List (Fin 5 × Bool))} {n : ℕ}
    (hW : burnsideF48s_autc_groupB gl gli idx W n = true) (z : Ah) :
    z ∈ Subgroup.closure {x | ∃ k ∈ idx, G k = x} ↔ ∃ w ∈ W, burnsideF48s_autc_ev G w = z := by
  obtain ⟨-, h0, -, hlet, hcl⟩ := burnsideF48s_autc_groupB_spec hW
  constructor
  · intro hz
    refine closure_subset_of_right_closed (S := {x | ∃ k ∈ idx, G k = x})
      (P := {z | ∃ w ∈ W, burnsideF48s_autc_ev G w = z})
      (fun s _ => (isOfFinOrder_of_finite s).exists_pow_eq_one)
      ⟨[], h0, burnsideF48s_autc_ev_nil G⟩ ?_ hz
    rintro _ ⟨w, hw, rfl⟩ s ⟨k, hk, rfl⟩
    obtain ⟨w', hw', he⟩ := List.mem_map.1 (hcl _ (List.mem_map_of_mem hw) k hk)
    refine ⟨w', hw', Subtype.ext (eq_of_repL (burnsideF48s_autc_repL_ev G gl gli hl hli w') ?_)⟩
    rw [he, Subgroup.coe_mul]
    exact repL_mul (burnsideF48s_autc_repL_ev G gl gli hl hli w) (hl k)
  · rintro ⟨w, hw, rfl⟩
    exact burnsideF48s_autc_ev_mem G w fun l hlw =>
      Subgroup.subset_closure ⟨l.1, hlet w hw l hlw, rfl⟩

theorem burnsideF48s_autc_mem_closure_of_mem
    (hl : ∀ k : Fin 5, RepL (gl.getD k []) ((G k : Ah) : P45))
    (hli : ∀ k : Fin 5, RepL (gli.getD k []) (((G k)⁻¹ : Ah) : P45)) {idx : List (Fin 5)}
    {W : List (List (Fin 5 × Bool))} {n : ℕ}
    (hW : burnsideF48s_autc_groupB gl gli idx W n = true) {z : Ah} {x : List ℕ}
    (hz : RepL x (z : P45)) (hx : x ∈ W.map (burnsideF48s_autc_evL gl gli)) :
    z ∈ Subgroup.closure {x | ∃ k ∈ idx, G k = x} := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
  refine (burnsideF48s_autc_mem_closure_iff hl hli hW z).2 ⟨w, hw, ?_⟩
  exact Subtype.ext (eq_of_repL (burnsideF48s_autc_repL_ev G gl gli hl hli w) hz)

theorem burnsideF48s_autc_mem_of_mem_closure
    (hl : ∀ k : Fin 5, RepL (gl.getD k []) ((G k : Ah) : P45))
    (hli : ∀ k : Fin 5, RepL (gli.getD k []) (((G k)⁻¹ : Ah) : P45)) {idx : List (Fin 5)}
    {W : List (List (Fin 5 × Bool))} {n : ℕ}
    (hW : burnsideF48s_autc_groupB gl gli idx W n = true) {z : Ah} {x : List ℕ}
    (hz : RepL x (z : P45)) (hzK : z ∈ Subgroup.closure {x | ∃ k ∈ idx, G k = x}) :
    x ∈ W.map (burnsideF48s_autc_evL gl gli) := by
  obtain ⟨w, hw, rfl⟩ := (burnsideF48s_autc_mem_closure_iff hl hli hW z).1 hzK
  rw [repL_unique hz (burnsideF48s_autc_repL_ev G gl gli hl hli w)]
  exact List.mem_map_of_mem hw

theorem burnsideF48s_autc_card_closure
    (hl : ∀ k : Fin 5, RepL (gl.getD k []) ((G k : Ah) : P45))
    (hli : ∀ k : Fin 5, RepL (gli.getD k []) (((G k)⁻¹ : Ah) : P45)) {idx : List (Fin 5)}
    {W : List (List (Fin 5 × Bool))} {n : ℕ}
    (hW : burnsideF48s_autc_groupB gl gli idx W n = true) :
    Nat.card ↥(Subgroup.closure {x | ∃ k ∈ idx, G k = x}) = n := by
  obtain ⟨hn, -, hnd, hlet, -⟩ := burnsideF48s_autc_groupB_spec hW
  let f : Fin W.length → ↥(Subgroup.closure {x | ∃ k ∈ idx, G k = x}) := fun i =>
    ⟨burnsideF48s_autc_ev G W[i], (burnsideF48s_autc_mem_closure_iff hl hli hW _).2
      ⟨W[i], List.getElem_mem _, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j hij => ?_, fun z => ?_⟩
    · have e1 : burnsideF48s_autc_ev G W[i] = burnsideF48s_autc_ev G W[j] :=
        congrArg Subtype.val hij
      have e2 : burnsideF48s_autc_evL gl gli W[i] = burnsideF48s_autc_evL gl gli W[j] :=
        repL_unique (burnsideF48s_autc_repL_ev G gl gli hl hli _)
          (e1 ▸ burnsideF48s_autc_repL_ev G gl gli hl hli _)
      have e3 : (W.map (burnsideF48s_autc_evL gl gli))[(i : ℕ)]'(by simp) =
          (W.map (burnsideF48s_autc_evL gl gli))[(j : ℕ)]'(by simp) := by
        simpa using e2
      exact Fin.ext ((hnd.getElem_inj_iff).1 e3)
    · obtain ⟨w, hw, hz⟩ := (burnsideF48s_autc_mem_closure_iff hl hli hW z).1 z.2
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
      exact ⟨⟨i, hi⟩, Subtype.ext hz⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin, hn]

end WordLists

theorem burnsideF48s_autc_set3 (G : Fin 5 → Ah) (i j k : Fin 5) :
    ({G i, G j, G k} : Set Ah) = {x | ∃ l ∈ [i, j, k], G l = x} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨i, Or.inl rfl, rfl⟩
    · exact ⟨j, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨k, Or.inr (Or.inr rfl), rfl⟩
  · rintro ⟨l, hl | hl | hl, rfl⟩ <;> subst hl <;> simp

theorem burnsideF48s_autc_set4 (G : Fin 5 → Ah) (i j k m : Fin 5) :
    ({G i, G j, G k, G m} : Set Ah) = {x | ∃ l ∈ [i, j, k, m], G l = x} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨i, Or.inl rfl, rfl⟩
    · exact ⟨j, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨k, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨m, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
  · rintro ⟨l, hl | hl | hl | hl, rfl⟩ <;> subst hl <;> simp

end CFSG.ASVolI
