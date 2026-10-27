module

public import CFSG.Quasithin.Background.G2UClosure
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.G2Three

@[expose] def dec14 (m : List ℕ) : Matrix (Fin 14) (Fin 14) (ZMod 3) :=
  Matrix.of fun i j => ((m.getD (14 * i + j) 0 : ℕ) : ZMod 3)

@[expose] def ent (a : Array ℕ) (i j : ℕ) : ℕ :=
  a.getD (14 * i + j) 0

@[expose] def dot (a b : Array ℕ) (i j : ℕ) : ℕ :=
  ((List.range 14).map fun k => ent a i k * ent b k j).sum

@[expose] def mul14 (m n : List ℕ) : List ℕ :=
  let a := m.toArray
  let b := n.toArray
  (List.range 196).map fun t => dot a b (t / 14) (t % 14) % 3

@[expose] def one14 : List ℕ :=
  (List.range 196).map fun t => if t / 14 = t % 14 then 1 else 0

@[expose] def canon14 (m : List ℕ) : Bool :=
  m.length == 196 && m.all (· < 3)

theorem ent_toArray (m : List ℕ) (i j : ℕ) : ent m.toArray i j = m.getD (14 * i + j) 0 := by
  simp [ent, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
                 simp

theorem dec14_mul14 (m n : List ℕ) : dec14 (mul14 m n) = dec14 m * dec14 n := by
  ext i j
  have hlt : 14 * (i : ℕ) + j < 196 := by omega
  have hdiv : (14 * (i : ℕ) + j) / 14 = i := by omega
  have hmod : (14 * (i : ℕ) + j) % 14 = j := by omega
  rw [Matrix.mul_apply]
  simp only [dec14, Matrix.of_apply, mul14]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range,
    hdiv, hmod, ZMod.natCast_mod, dot, Nat.cast_list_sum, List.map_map, list_sum_range,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, Nat.cast_mul, ent_toArray]

theorem dec14_one14 : dec14 one14 = 1 := by
  ext i j
  have hlt : 14 * (i : ℕ) + j < 196 := by omega
  have hdiv : (14 * (i : ℕ) + j) / 14 = i := by omega
  have hmod : (14 * (i : ℕ) + j) % 14 = j := by omega
  simp only [dec14, Matrix.of_apply, one14]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range,
    hdiv, hmod, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

theorem canon14_mul14 (m n : List ℕ) : canon14 (mul14 m n) = true := by
  simp only [canon14, mul14, List.length_map, List.length_range, beq_self_eq_true,
    Bool.true_and, List.all_eq_true, List.mem_map, List.mem_range, decide_eq_true_eq]
  rintro _ ⟨t, -, rfl⟩
  exact Nat.mod_lt _ (by norm_num)

theorem canon14_one14 : canon14 one14 = true := by
  simp only [canon14, one14, List.length_map, List.length_range, beq_self_eq_true,
    Bool.true_and, List.all_eq_true, List.mem_map, List.mem_range, decide_eq_true_eq]
  rintro _ ⟨t, -, rfl⟩
  split_ifs <;> norm_num

theorem natCast_injective_three :
    ∀ x : ℕ, x < 3 → ∀ y : ℕ, y < 3 → ((x : ℕ) : ZMod 3) = ((y : ℕ) : ZMod 3) → x = y := by
  decide

theorem dec14_injective {m m' : List ℕ} (h : canon14 m = true) (h' : canon14 m' = true)
    (e : dec14 m = dec14 m') : m = m' := by
  simp only [canon14, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h h'
  refine List.ext_getElem (h.1.trans h'.1.symm) fun t ht ht' => ?_
  have ht196 : t < 196 := h.1 ▸ ht
  have := congrFun (congrFun e ⟨t / 14, by omega⟩) ⟨t % 14, by omega⟩
  have hdm : 14 * (t / 14) + t % 14 = t := Nat.div_add_mod t 14
  simp only [dec14, Matrix.of_apply, hdm, List.getD_eq_getElem _ _ ht,
    List.getD_eq_getElem _ _ ht'] at this
  exact natCast_injective_three _ (h.2 _ (List.getElem_mem ht)) _
    (h'.2 _ (List.getElem_mem ht')) this

@[expose] def conjStep (gp x : List ℕ) : List ℕ :=
  mul14 (mul14 (gp.take 196) x) (gp.drop 196)

@[expose] def orbitBuild (t : List ℕ) (gps : List (List ℕ)) (par : List (ℕ × ℕ)) :
    Array (List ℕ) :=
  par.foldl (fun acc ps => acc.push (conjStep (gps.getD ps.2 (one14 ++ one14))
    (acc.getD ps.1 t))) #[t]

@[expose] def orbitParents (t : List ℕ) (gps : List (List ℕ)) (fuel : ℕ) : List (ℕ × ℕ) :=
  CFSG.Quasithin.G2U.bfsParents t (fun x gp => conjStep gp x) gps fuel

theorem take_drop_one14 :
    (one14 ++ one14).take 196 = one14 ∧ (one14 ++ one14).drop 196 = one14 := by
  have h : one14.length = 196 := by simp [one14]
  exact ⟨List.take_left' h, List.drop_left' h⟩

theorem orbitBuild_spec (H : Subgroup (GL (Fin 14) (ZMod 3))) (t : List ℕ) (gps : List (List ℕ))
    (hgps : ∀ gp ∈ gps, ∃ g ∈ H, dec14 (gp.take 196) = (g : Matrix (Fin 14) (Fin 14) (ZMod 3)) ∧
      dec14 (gp.drop 196) = ((g⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)))
    (par : List (ℕ × ℕ)) :
    ∀ x ∈ orbitBuild t gps par, ∃ g ∈ H, dec14 x =
      (g : Matrix (Fin 14) (Fin 14) (ZMod 3)) * dec14 t *
        ((g⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) := by
  set P : List ℕ → Prop := fun x => ∃ g ∈ H, dec14 x =
    (g : Matrix (Fin 14) (Fin 14) (ZMod 3)) * dec14 t *
      ((g⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) with hP
  have ht : P t := ⟨1, H.one_mem, by simp⟩
  have hgp : ∀ s, ∃ g ∈ H, dec14 ((gps.getD s (one14 ++ one14)).take 196) =
      (g : Matrix (Fin 14) (Fin 14) (ZMod 3)) ∧
      dec14 ((gps.getD s (one14 ++ one14)).drop 196) =
        ((g⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) := by
    intro s
    rw [List.getD_eq_getElem?_getD]
    cases hs : gps[s]? with
    | none =>
      refine ⟨1, H.one_mem, ?_, ?_⟩
      · rw [Option.getD_none, take_drop_one14.1, dec14_one14, Units.val_one]
      · rw [Option.getD_none, take_drop_one14.2, dec14_one14, inv_one, Units.val_one]
    | some gp => exact hgps gp (List.mem_of_getElem? hs)
  have hstep : ∀ s x, P x → P (conjStep (gps.getD s (one14 ++ one14)) x) := by
    rintro s x ⟨g, hg, hx⟩
    obtain ⟨g', hg', h1, h2⟩ := hgp s
    refine ⟨g' * g, H.mul_mem hg' hg, ?_⟩
    rw [conjStep, dec14_mul14, dec14_mul14, h1, h2, hx, mul_inv_rev, Units.val_mul,
      Units.val_mul]
    simp only [Matrix.mul_assoc]
  have hget : ∀ (acc : Array (List ℕ)), (∀ x ∈ acc, P x) → ∀ p, P (acc.getD p t) := by
    intro acc h p
    rw [Array.getD]
    split_ifs with hp
    · exact h _ (Array.getElem_mem hp)
    · exact ht
  have key : ∀ (l : List (ℕ × ℕ)) (acc : Array (List ℕ)), (∀ x ∈ acc, P x) →
      ∀ x ∈ l.foldl (fun acc ps => acc.push (conjStep (gps.getD ps.2 (one14 ++ one14))
        (acc.getD ps.1 t))) acc, P x := by
    intro l
    induction l with
    | nil => exact fun acc h => h
    | cons ps l ih =>
      intro acc h
      rw [List.foldl_cons]
      refine ih _ fun x hx => ?_
      rcases Array.mem_push.mp hx with hx | rfl
      · exact h x hx
      · exact hstep _ _ (hget acc h _)
  refine key par #[t] fun x hx => ?_
  rw [Array.mem_singleton.mp hx]
  exact ht

end CFSG.RankThree.PartTwo.Census.Carrier.G2Three
