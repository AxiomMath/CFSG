module

public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.Monster.B.Classical.E6Folded

@[expose] def A : Finset (Fin 6 × Fin 6) := {(0, 2), (2, 3), (3, 4), (4, 5), (1, 3)}

@[expose] def form (u v : Fin 6 → ℤ) : ℤ :=
  2 * ∑ i, u i * v i - ∑ p ∈ A, (u p.1 * v p.2 + u p.2 * v p.1)

@[expose] def e (i : Fin 6) : Fin 6 → ℤ := Pi.single i 1

@[expose] def s (i : Fin 6) (v : Fin 6 → ℤ) : Fin 6 → ℤ := v - form v (e i) • e i

@[expose] def r : Fin 4 → (Fin 6 → ℤ) → Fin 6 → ℤ
  | 0 => s 1
  | 1 => s 3
  | 2 => s 2 ∘ s 4
  | 3 => s 0 ∘ s 5

@[expose] def θ : Fin 6 → ℤ := ![1, 2, 2, 3, 2, 1]

inductive InOrbit : (Fin 6 → ℤ) → Prop
  | base : InOrbit θ
  | step (k : Fin 4) {v : Fin 6 → ℤ} : InOrbit v → InOrbit (r k v)

abbrev Λ : Type := {v : Fin 6 → ℤ // InOrbit v}

@[expose] def θΛ : Λ := ⟨θ, .base⟩

theorem sum_A (f : Fin 6 × Fin 6 → ℤ) :
    ∑ p ∈ A, f p = f (0, 2) + f (2, 3) + f (3, 4) + f (4, 5) + f (1, 3) := by
  simp [A, Finset.sum_insert, add_assoc]

theorem form_eq (u v : Fin 6 → ℤ) :
    form u v = 2 * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4 + u 5 * v 5) -
      (u 0 * v 2 + u 2 * v 0 + u 2 * v 3 + u 3 * v 2 + u 3 * v 4 + u 4 * v 3 + u 4 * v 5 +
        u 5 * v 4 + u 1 * v 3 + u 3 * v 1) := by
  simp only [form, sum_A, Fin.sum_univ_six]
  ring

theorem form_e_eq_cartanE (v : Fin 6 → ℤ) (i : Fin 6) :
    form v (e i) = ∑ j : Fin 6, CFSG.Blueprint.Chevalley.Tag.cartanE 6 i j * v j := by
  rw [form_eq]
  fin_cases i <;> simp [e, Fin.sum_univ_six, CFSG.Blueprint.Chevalley.Tag.cartanE] <;> ring

theorem s_eq_reflect (i : Fin 6) (v : Fin 6 → ℤ) :
    s i v = CFSG.Blueprint.Chevalley.reflect .E6 i v := by
  have h : CFSG.Blueprint.Chevalley.reflect .E6 i v =
      v - (∑ j : Fin 6, CFSG.Blueprint.Chevalley.Tag.cartanE 6 i j * v j) •
        (Pi.single i 1 : Fin 6 → ℤ) := rfl
  rw [h, s, form_e_eq_cartanE]
  rfl

theorem form_symm (u v : Fin 6 → ℤ) : form u v = form v u := by
  rw [form_eq, form_eq]
  ring

theorem form_sub_smul_left (v w x : Fin 6 → ℤ) (c : ℤ) :
    form (v - c • w) x = form v x - c * form w x := by
  simp only [form_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem form_e_e (i : Fin 6) : form (e i) (e i) = 2 := by
  revert i
  decide

theorem s_s (i : Fin 6) (v : Fin 6 → ℤ) : s i (s i v) = v := by
  have h : form (s i v) (e i) = -form v (e i) := by
    rw [s, form_sub_smul_left, form_e_e]
    ring
  rw [s, h, s, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem s_comm {i j : Fin 6} (h : form (e i) (e j) = 0) (v : Fin 6 → ℤ) :
    s i (s j v) = s j (s i v) := by
  have hji : form (e j) (e i) = 0 := by rw [form_symm, h]
  have hi : form (s j v) (e i) = form v (e i) := by
    rw [s, form_sub_smul_left, hji, mul_zero, sub_zero]
  have hj : form (s i v) (e j) = form v (e j) := by
    rw [s, form_sub_smul_left, h, mul_zero, sub_zero]
  rw [s, hi, s, s, hj, s]
  abel

theorem r_r (k : Fin 4) (v : Fin 6 → ℤ) : r k (r k v) = v := by
  match k with
  | 0 => exact s_s 1 v
  | 1 => exact s_s 3 v
  | 2 =>
    change s 2 (s 4 (s 2 (s 4 v))) = v
    rw [s_comm (by decide) (s 4 v), s_s, s_s]
  | 3 =>
    change s 0 (s 5 (s 0 (s 5 v))) = v
    rw [s_comm (by decide) (s 5 v), s_s, s_s]

@[expose] def gen (k : Fin 4) : Equiv.Perm Λ where
  toFun v := ⟨r k v.1, .step k v.2⟩
  invFun v := ⟨r k v.1, .step k v.2⟩
  left_inv v := Subtype.ext (r_r k v.1)
  right_inv v := Subtype.ext (r_r k v.1)

theorem gen_apply (k : Fin 4) (v : Λ) : (gen k v).1 = r k v.1 := rfl

theorem gen_mul_self (k : Fin 4) : gen k * gen k = 1 :=
  Equiv.ext fun v => Subtype.ext (r_r k v.1)

theorem gen_inv (k : Fin 4) : (gen k)⁻¹ = gen k :=
  inv_eq_of_mul_eq_one_right (gen_mul_self k)

@[expose] def W : Subgroup (Equiv.Perm Λ) := Subgroup.closure (Set.range gen)

@[expose] def J : Set (Fin 4) := {1, 2, 3}

@[expose] def K : Set (Fin 4) := {0, 1, 2}

@[expose] def WJ : Subgroup (Equiv.Perm Λ) := Subgroup.closure (gen '' J)

@[expose] def WK : Subgroup (Equiv.Perm Λ) := Subgroup.closure (gen '' K)

@[expose] def orbitK : Set Λ := {α | ∃ w ∈ WK, w θΛ = α}

theorem gen_mem_W (k : Fin 4) : gen k ∈ W := Subgroup.subset_closure ⟨k, rfl⟩

theorem WJ_le_W : WJ ≤ W := Subgroup.closure_mono (Set.image_subset_range _ _)

theorem WK_le_W : WK ≤ W := Subgroup.closure_mono (Set.image_subset_range _ _)

@[expose] def wordProd (l : List (Fin 4)) : Equiv.Perm Λ := (l.map gen).prod

@[expose] def letterWeight : Fin 4 → ℕ
  | 0 => 2
  | 1 => 2
  | 2 => 4
  | 3 => 4

@[expose] def wordWeight (l : List (Fin 4)) : ℕ := (l.map letterWeight).prod

@[expose] noncomputable def wordLength (w : Equiv.Perm Λ) : ℕ :=
  sInf {n | ∃ l : List (Fin 4), wordProd l = w ∧ l.length = n}

@[expose] def IsReducedWord (w : Equiv.Perm Λ) (l : List (Fin 4)) : Prop :=
  wordProd l = w ∧ l.length = wordLength w

open _root_.Classical in
@[expose] noncomputable def qWeight (w : Equiv.Perm Λ) : ℕ :=
  if h : ∃ l, IsReducedWord w l then wordWeight h.choose else 0

@[simp] theorem wordProd_nil : wordProd [] = 1 := rfl

@[simp] theorem wordProd_cons (k : Fin 4) (l : List (Fin 4)) :
    wordProd (k :: l) = gen k * wordProd l := by
  simp [wordProd]

@[simp] theorem wordWeight_nil : wordWeight [] = 1 := rfl

@[simp] theorem wordWeight_cons (k : Fin 4) (l : List (Fin 4)) :
    wordWeight (k :: l) = letterWeight k * wordWeight l := by
  simp [wordWeight]

theorem wordProd_mem_closure {S : Set (Fin 4)} {l : List (Fin 4)} (hl : ∀ k ∈ l, k ∈ S) :
    wordProd l ∈ Subgroup.closure (gen '' S) := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons k l ih =>
    rw [wordProd_cons]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨k, hl k (by simp), rfl⟩)
      (ih fun k' hk' => hl k' (by simp [hk']))

theorem wordProd_mem_W (l : List (Fin 4)) : wordProd l ∈ W := by
  have h := wordProd_mem_closure (S := Set.univ) (l := l) (fun _ _ => trivial)
  rwa [Set.image_univ] at h

theorem wordLength_le {w : Equiv.Perm Λ} {l : List (Fin 4)} (h : wordProd l = w) :
    wordLength w ≤ l.length :=
  Nat.sInf_le ⟨l, h, rfl⟩

theorem wordLength_eq_and_weight_eq {cl cq : Equiv.Perm Λ → ℕ} (h1 : cl 1 = 0) (hq1 : cq 1 = 1)
    (hle : ∀ w ∈ W, ∀ k, cl (gen k * w) ≤ cl w + 1)
    (hq : ∀ w ∈ W, ∀ k, cl (gen k * w) = cl w + 1 → cq (gen k * w) = letterWeight k * cq w)
    (hdesc : ∀ w ∈ W, w ≠ 1 → ∃ k, cl (gen k * w) + 1 = cl w) :
    (∀ w ∈ W, wordLength w = cl w) ∧ (∀ w l, IsReducedWord w l → wordWeight l = cq w) := by
  have c1 : ∀ l, cl (wordProd l) ≤ l.length := by
    intro l
    induction l with
    | nil => simp [h1]
    | cons k l ih =>
      rw [wordProd_cons, List.length_cons]
      exact (hle _ (wordProd_mem_W l) k).trans (by omega)
  have c2 : ∀ n, ∀ w ∈ W, cl w = n → ∃ l, wordProd l = w ∧ l.length = n := by
    intro n
    induction n with
    | zero =>
      intro w hw hcl
      by_cases h : w = 1
      · exact ⟨[], h ▸ rfl, rfl⟩
      · obtain ⟨k, hk⟩ := hdesc w hw h
        omega
    | succ n ih =>
      intro w hw hcl
      have hne : w ≠ 1 := by
        rintro rfl
        rw [h1] at hcl
        omega
      obtain ⟨k, hk⟩ := hdesc w hw hne
      obtain ⟨l, hl, hlen⟩ := ih (gen k * w) (Subgroup.mul_mem _ (gen_mem_W k) hw) (by omega)
      refine ⟨k :: l, ?_, by simp [hlen]⟩
      rw [wordProd_cons, hl, ← mul_assoc, gen_mul_self, one_mul]
  have c3 : ∀ w ∈ W, wordLength w = cl w := by
    intro w hw
    obtain ⟨l, hl, hlen⟩ := c2 _ w hw rfl
    refine le_antisymm (hlen ▸ wordLength_le hl) ?_
    have hne : {n | ∃ l : List (Fin 4), wordProd l = w ∧ l.length = n}.Nonempty :=
      ⟨_, l, hl, rfl⟩
    obtain ⟨l', hl', hlen'⟩ := Nat.sInf_mem hne
    have := c1 l'
    rw [hl'] at this
    unfold wordLength
    omega
  have c4 : ∀ l, cl (wordProd l) = l.length → wordWeight l = cq (wordProd l) := by
    intro l
    induction l with
    | nil => intro _; simp [hq1]
    | cons k l ih =>
      intro h
      rw [wordProd_cons, List.length_cons] at h
      have hx := hle _ (wordProd_mem_W l) k
      have hx' := c1 l
      have hcl : cl (wordProd l) = l.length := by omega
      rw [wordWeight_cons, ih hcl, wordProd_cons,
        hq _ (wordProd_mem_W l) k (by omega)]
  refine ⟨c3, fun w l hl => ?_⟩
  obtain ⟨hl, hlen⟩ := hl
  subst hl
  exact c4 l (by rw [← c3 _ (wordProd_mem_W l), hlen])

end CFSG.Monster.B.Classical.E6Folded
