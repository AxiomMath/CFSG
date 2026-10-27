module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleGramDefs

public section

set_option autoImplicit false

namespace CFSG.StandardType.CoxTriple.OrderK

structure Z9 where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  a4 : ℤ
  a5 : ℤ
  a6 : ℤ
  a7 : ℤ
  a8 : ℤ

@[expose] def toM (x : Z9) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![x.a0, x.a1, x.a2; x.a3, x.a4, x.a5; x.a6, x.a7, x.a8]

@[expose] def ofM (m : Matrix (Fin 3) (Fin 3) ℤ) : Z9 :=
  ⟨m 0 0, m 0 1, m 0 2, m 1 0, m 1 1, m 1 2, m 2 0, m 2 1, m 2 2⟩

theorem ofM_toM (x : Z9) : ofM (toM x) = x := rfl

theorem toM_ofM (m : Matrix (Fin 3) (Fin 3) ℤ) : toM (ofM m) = m := by
  rw [Matrix.eta_fin_three m]
  rfl

theorem toM_injective : Function.Injective toM := fun x y h => by
  rw [← ofM_toM x, ← ofM_toM y, h]

@[expose] def mulZ (x y : Z9) : Z9 :=
  ⟨x.a0 * y.a0 + x.a1 * y.a3 + x.a2 * y.a6, x.a0 * y.a1 + x.a1 * y.a4 + x.a2 * y.a7,
   x.a0 * y.a2 + x.a1 * y.a5 + x.a2 * y.a8, x.a3 * y.a0 + x.a4 * y.a3 + x.a5 * y.a6,
   x.a3 * y.a1 + x.a4 * y.a4 + x.a5 * y.a7, x.a3 * y.a2 + x.a4 * y.a5 + x.a5 * y.a8,
   x.a6 * y.a0 + x.a7 * y.a3 + x.a8 * y.a6, x.a6 * y.a1 + x.a7 * y.a4 + x.a8 * y.a7,
   x.a6 * y.a2 + x.a7 * y.a5 + x.a8 * y.a8⟩

theorem toM_mulZ (x y : Z9) : toM (mulZ x y) = toM x * toM y := by
  rw [toM, toM, toM, Matrix.mul_fin_three]
  rfl

@[expose] def eqZ (x y : Z9) : Bool :=
  (x.a0 == y.a0) && (x.a1 == y.a1) && (x.a2 == y.a2) && (x.a3 == y.a3) && (x.a4 == y.a4) &&
    (x.a5 == y.a5) && (x.a6 == y.a6) && (x.a7 == y.a7) && (x.a8 == y.a8)

theorem eqZ_iff (x y : Z9) : eqZ x y = true ↔ x = y := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := x
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := y
  simp [eqZ, and_assoc]

@[expose] def oneZ : Z9 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

theorem toM_oneZ : toM oneZ = 1 := by
  rw [← toM_ofM 1]
  rfl

@[expose] def reflZ (n : Z9) (k : Fin 3) : Z9 :=
  if k.val = 0 then
    ⟨1 - 2 * n.a0 / n.a0, -(2 * n.a1 / n.a0), -(2 * n.a2 / n.a0), 0, 1, 0, 0, 0, 1⟩
  else if k.val = 1 then
    ⟨1, 0, 0, -(2 * n.a3 / n.a4), 1 - 2 * n.a4 / n.a4, -(2 * n.a5 / n.a4), 0, 0, 1⟩
  else
    ⟨1, 0, 0, 0, 1, 0, -(2 * n.a6 / n.a8), -(2 * n.a7 / n.a8), 1 - 2 * n.a8 / n.a8⟩

theorem gramRefl_toM (n : Z9) (k : Fin 3) : gramRefl (toM n) k = toM (reflZ n k) := by
  rw [gramRefl]
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [reflZ, toM, Matrix.one_apply]

@[expose] def gensZ (n : Z9) : List Z9 := [reflZ n 0, reflZ n 1, reflZ n 2]

theorem reflZ_mem_gensZ (n : Z9) (k : Fin 3) : reflZ n k ∈ gensZ n := by
  fin_cases k <;> simp [gensZ]

@[expose] def addAll (acc : List Z9) : List Z9 → List Z9
  | [] => acc
  | c :: cs => addAll (if acc.any (eqZ c) then acc else c :: acc) cs

theorem mem_addAll (acc cs : List Z9) (y : Z9) (hy : y ∈ addAll acc cs) : y ∈ acc ∨ y ∈ cs := by
  induction cs generalizing acc with
  | nil => exact Or.inl hy
  | cons c cs ih =>
    rw [addAll] at hy
    rcases ih _ hy with h | h
    · split_ifs at h with hc
      · exact Or.inl h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

@[expose] def stepZ (gs L : List Z9) : List Z9 :=
  addAll L (L.flatMap fun x => gs.map fun g => mulZ g x)

@[expose] def closeZ (gs : List Z9) : ℕ → List Z9 → List Z9
  | 0, L => L
  | m + 1, L => closeZ gs m (stepZ gs L)

@[expose] def nodupZ : List Z9 → Bool
  | [] => true
  | x :: xs => !(xs.any (eqZ x)) && nodupZ xs

theorem nodup_of_nodupZ (L : List Z9) (h : nodupZ L = true) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [nodupZ, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
    refine List.nodup_cons.2 ⟨fun hx => ?_, ih h.2⟩
    have := h.1 x hx
    rw [(eqZ_iff x x).2 rfl] at this
    exact this rfl

@[expose] def chkL (gs L : List Z9) : Bool :=
  L.any (eqZ oneZ) && nodupZ L && L.all (fun x => gs.all fun g => L.any (eqZ (mulZ g x))) &&
    (48 % L.length == 0)

@[expose] def chkN (n : Z9) : Bool := chkL (gensZ n) (closeZ (gensZ n) 12 [oneZ])

theorem card_closure_eq_length {M : Type*} [Monoid M] [DecidableEq M]
    (gen : Fin 3 → M) (L : List M) (h1 : 1 ∈ L) (hnd : L.Nodup)
    (hstab : ∀ x ∈ L, ∀ k : Fin 3, gen k * x ∈ L)
    (hsub : ∀ x ∈ L, x ∈ Submonoid.closure (Set.range gen)) :
    Nat.card ↥(Submonoid.closure (Set.range gen)) = L.length := by
  have hclos : ∀ x ∈ Submonoid.closure (Set.range gen), x ∈ L := by
    intro x hx
    refine Submonoid.closure_induction_left (s := Set.range gen) (motive := fun m _ => m ∈ L)
      ?_ ?_ hx
    · exact h1
    · intro a ha y _ hyl
      obtain ⟨k, rfl⟩ := ha
      exact hstab y hyl k
  have hmem : ∀ x, x ∈ L.toFinset ↔ x ∈ (Submonoid.closure (Set.range gen) : Set M) :=
    fun x => ⟨fun hx => hsub x (List.mem_toFinset.mp hx), fun hx => List.mem_toFinset.mpr (hclos x hx)⟩
  change Nat.card { x // x ∈ (Submonoid.closure (Set.range gen) : Set M) } = L.length
  rw [Nat.subtype_card L.toFinset hmem]
  exact List.toFinset_card_of_nodup hnd

theorem closeZ_mem (n : Z9) : ∀ (m : ℕ) (L : List Z9), (∀ x ∈ L, toM x ∈ gramReflGroup (toM n)) →
    ∀ x ∈ closeZ (gensZ n) m L, toM x ∈ gramReflGroup (toM n) := by
  intro m
  induction m with
  | zero => exact fun L hL => hL
  | succ m ih =>
    intro L hL
    refine ih _ fun y hy => ?_
    rcases mem_addAll _ _ y hy with h | h
    · exact hL y h
    · obtain ⟨x, hx, hxg⟩ := List.mem_flatMap.1 h
      obtain ⟨g, hgm, rfl⟩ := List.mem_map.1 hxg
      rw [toM_mulZ]
      refine Submonoid.mul_mem _ ?_ (hL x hx)
      rw [gensZ, List.mem_cons, List.mem_cons, List.mem_singleton] at hgm
      rw [gramReflGroup]
      rcases hgm with h | h | h <;> rw [h] <;>
        exact Submonoid.subset_closure ⟨_, gramRefl_toM _ _⟩

theorem card_dvd_of_chkN (n : Z9) (h : chkN n = true) :
    Nat.card ↥(gramReflGroup (toM n)) ∣ 48 := by
  rw [chkN, chkL] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, hnd⟩, hst⟩, hlen⟩ := h
  set L := closeZ (gensZ n) 12 [oneZ]
  have hsub := closeZ_mem n 12 [oneZ] (by
    intro x hx
    rw [List.mem_singleton.1 hx, toM_oneZ]
    exact Submonoid.one_mem _)
  have hc := card_closure_eq_length (gramRefl (toM n)) (L.map toM)
    (by
      obtain ⟨x, hx, hx1⟩ := List.any_eq_true.1 h1
      rw [← toM_oneZ, (eqZ_iff _ _).1 hx1]
      exact List.mem_map_of_mem hx)
    ((nodup_of_nodupZ L hnd).map toM_injective)
    (by
      intro y hy k
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      have := List.all_eq_true.1 (List.all_eq_true.1 hst x hx) (reflZ n k) (reflZ_mem_gensZ n k)
      obtain ⟨z, hz, hzx⟩ := List.any_eq_true.1 this
      rw [gramRefl_toM, ← toM_mulZ, (eqZ_iff _ _).1 hzx]
      exact List.mem_map_of_mem hz)
    (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact hsub x hx)
  rw [gramReflGroup, hc, List.length_map]
  exact Nat.dvd_of_mod_eq_zero hlen

@[expose] def chkAll : Bool := admList.all fun N => chkN (ofM N)

theorem chkAll_ok : chkAll = true := by decide +kernel

theorem card_dvd_of_mem_admList {N : Matrix (Fin 3) (Fin 3) ℤ} (h : N ∈ admList) :
    Nat.card ↥(gramReflGroup N) ∣ 48 := by
  have := card_dvd_of_chkN (ofM N) (List.all_eq_true.1 chkAll_ok N h)
  rwa [toM_ofM] at this

end CFSG.StandardType.CoxTriple.OrderK
