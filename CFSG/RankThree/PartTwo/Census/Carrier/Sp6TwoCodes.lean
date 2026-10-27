module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeCodes

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

@[expose] def dec6 (m : List ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => ((m.getD (6 * i + j) 0 : ℕ) : ZMod 2)

@[expose] def ent (a : Array ℕ) (i j : ℕ) : ℕ :=
  a.getD (6 * i + j) 0

@[expose] def dot (a b : Array ℕ) (i j : ℕ) : ℕ :=
  ((List.range 6).map fun k => ent a i k * ent b k j).sum

@[expose] def mul6 (m n : List ℕ) : List ℕ :=
  let a := m.toArray
  let b := n.toArray
  (List.range 36).map fun t => dot a b (t / 6) (t % 6) % 2

@[expose] def one6 : List ℕ :=
  (List.range 36).map fun t => if t / 6 = t % 6 then 1 else 0

@[expose] def tr6 (m : List ℕ) : List ℕ :=
  (List.range 36).map fun t => m.getD (6 * (t % 6) + t / 6) 0

@[expose] def canon6 (m : List ℕ) : Bool :=
  m.length == 36 && m.all (· < 2)

theorem ent_toArray (m : List ℕ) (i j : ℕ) : ent m.toArray i j = m.getD (6 * i + j) 0 := by
  simp [ent, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem dec6_mul6 (m n : List ℕ) : dec6 (mul6 m n) = dec6 m * dec6 n := by
  ext i j
  have hlt : 6 * (i : ℕ) + j < 36 := by omega
  have hdiv : (6 * (i : ℕ) + j) / 6 = i := by omega
  have hmod : (6 * (i : ℕ) + j) % 6 = j := by omega
  rw [Matrix.mul_apply]
  simp only [dec6, Matrix.of_apply, mul6]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range,
    hdiv, hmod, ZMod.natCast_mod, dot, Nat.cast_list_sum, List.map_map,
    G2Three.list_sum_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, Nat.cast_mul, ent_toArray]

theorem dec6_one6 : dec6 one6 = 1 := by
  ext i j
  have hlt : 6 * (i : ℕ) + j < 36 := by omega
  have hdiv : (6 * (i : ℕ) + j) / 6 = i := by omega
  have hmod : (6 * (i : ℕ) + j) % 6 = j := by omega
  simp only [dec6, Matrix.of_apply, one6]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range,
    hdiv, hmod, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

theorem dec6_tr6 (m : List ℕ) : dec6 (tr6 m) = (dec6 m).transpose := by
  ext i j
  have hlt : 6 * (i : ℕ) + j < 36 := by omega
  have hdiv : (6 * (i : ℕ) + j) / 6 = i := by omega
  have hmod : (6 * (i : ℕ) + j) % 6 = j := by omega
  simp only [dec6, Matrix.of_apply, tr6, Matrix.transpose_apply]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range,
    hdiv, hmod]

theorem canon6_mul6 (m n : List ℕ) : canon6 (mul6 m n) = true := by
  simp only [canon6, mul6, List.length_map, List.length_range, beq_self_eq_true,
    Bool.true_and, List.all_eq_true, List.mem_map, List.mem_range, decide_eq_true_eq]
  rintro _ ⟨t, -, rfl⟩
  exact Nat.mod_lt _ (by norm_num)

theorem canon6_one6 : canon6 one6 = true := by
  simp only [canon6, one6, List.length_map, List.length_range, beq_self_eq_true,
    Bool.true_and, List.all_eq_true, List.mem_map, List.mem_range, decide_eq_true_eq]
  rintro _ ⟨t, -, rfl⟩
  split_ifs <;> norm_num

theorem natCast_injective_two :
    ∀ x : ℕ, x < 2 → ∀ y : ℕ, y < 2 → ((x : ℕ) : ZMod 2) = ((y : ℕ) : ZMod 2) → x = y := by
  decide

theorem dec6_injective {m m' : List ℕ} (h : canon6 m = true) (h' : canon6 m' = true)
    (e : dec6 m = dec6 m') : m = m' := by
  simp only [canon6, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h h'
  refine List.ext_getElem (h.1.trans h'.1.symm) fun t ht ht' => ?_
  have ht36 : t < 36 := h.1 ▸ ht
  have := congrFun (congrFun e ⟨t / 6, by omega⟩) ⟨t % 6, by omega⟩
  have hdm : 6 * (t / 6) + t % 6 = t := Nat.div_add_mod t 6
  simp only [dec6, Matrix.of_apply, hdm, List.getD_eq_getElem _ _ ht,
    List.getD_eq_getElem _ _ ht'] at this
  exact natCast_injective_two _ (h.2 _ (List.getElem_mem ht)) _
    (h'.2 _ (List.getElem_mem ht')) this

@[expose] def conjStep6 (gp x : List ℕ) : List ℕ :=
  mul6 (mul6 (gp.take 36) x) (gp.drop 36)

@[expose] def orbitBuild6 (t : List ℕ) (gps : List (List ℕ)) (par : List (ℕ × ℕ)) :
    Array (List ℕ) :=
  par.foldl (fun acc ps => acc.push (conjStep6 (gps.getD ps.2 (one6 ++ one6))
    (acc.getD ps.1 t))) #[t]

@[expose] def orbitParents6 (t : List ℕ) (gps : List (List ℕ)) (fuel : ℕ) : List (ℕ × ℕ) :=
  CFSG.Quasithin.G2U.bfsParents t (fun x gp => conjStep6 gp x) gps fuel

theorem take_drop_one6 :
    (one6 ++ one6).take 36 = one6 ∧ (one6 ++ one6).drop 36 = one6 := by
  have h : one6.length = 36 := by simp [one6]
  exact ⟨List.take_left' h, List.drop_left' h⟩

theorem orbitBuild6_spec {G : Type*} [Group G] (f : G →* Matrix (Fin 6) (Fin 6) (ZMod 2))
    {t : List ℕ} {t₀ : G} (ht₀ : dec6 t = f t₀) (gps : List (List ℕ))
    (hgps : ∀ gp ∈ gps, ∃ g : G, dec6 (gp.take 36) = f g ∧ dec6 (gp.drop 36) = f g⁻¹)
    (par : List (ℕ × ℕ)) :
    ∀ x ∈ orbitBuild6 t gps par, ∃ g : G, dec6 x = f (g * t₀ * g⁻¹) := by
  set P : List ℕ → Prop := fun x => ∃ g : G, dec6 x = f (g * t₀ * g⁻¹) with hP
  have ht : P t := ⟨1, by rw [ht₀]; simp⟩
  have hgp : ∀ s, ∃ g : G, dec6 ((gps.getD s (one6 ++ one6)).take 36) = f g ∧
      dec6 ((gps.getD s (one6 ++ one6)).drop 36) = f g⁻¹ := by
    intro s
    rw [List.getD_eq_getElem?_getD]
    cases hs : gps[s]? with
    | none =>
      refine ⟨1, ?_, ?_⟩
      · rw [Option.getD_none, take_drop_one6.1, dec6_one6, map_one]
      · rw [Option.getD_none, take_drop_one6.2, dec6_one6, inv_one, map_one]
    | some gp => exact hgps gp (List.mem_of_getElem? hs)
  have hstep : ∀ s x, P x → P (conjStep6 (gps.getD s (one6 ++ one6)) x) := by
    rintro s x ⟨g, hx⟩
    obtain ⟨g', h1, h2⟩ := hgp s
    refine ⟨g' * g, ?_⟩
    rw [conjStep6, dec6_mul6, dec6_mul6, h1, h2, hx, ← map_mul, ← map_mul, mul_inv_rev]
    simp only [mul_assoc]
  have hget : ∀ (acc : Array (List ℕ)), (∀ x ∈ acc, P x) → ∀ p, P (acc.getD p t) := by
    intro acc h p
    rw [Array.getD]
    split_ifs with hp
    · exact h _ (Array.getElem_mem hp)
    · exact ht
  have key : ∀ (l : List (ℕ × ℕ)) (acc : Array (List ℕ)), (∀ x ∈ acc, P x) →
      ∀ x ∈ l.foldl (fun acc ps => acc.push (conjStep6 (gps.getD ps.2 (one6 ++ one6))
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

theorem found_spec {es : Array (List ℕ)} {m : Std.HashMap (List ℕ) ℕ} {y : List ℕ}
    (h : CFSG.Quasithin.G2U.found es m y = true) : ∃ t < es.size, es.getD t [] = y := by
  simp only [CFSG.Quasithin.G2U.found] at h
  split at h
  · rename_i t _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨t, h.1, h.2⟩
  · exact absurd h Bool.false_ne_true

end CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
