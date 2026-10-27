module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

private lemma c2slomqmfo_spIsSign_ite_one {n : ℕ} (a : Fin n) {e : ℤ}
    (he : e = 1 ∨ e = -1) : SpIsSign (fun x : Fin n => if x = a then e else 1) := by
  intro x
  change (if x = a then e else 1) = 1 ∨ (if x = a then e else 1) = -1
  by_cases hx : x = a
  · rw [if_pos hx]; exact he
  · rw [if_neg hx]; exact Or.inl rfl

private lemma c2slomqmfo_spIsSign_ite_two {n : ℕ} (a b : Fin n) {e e' : ℤ}
    (he : e = 1 ∨ e = -1) (he' : e' = 1 ∨ e' = -1) :
    SpIsSign (fun x : Fin n => if x = a then e else if x = b then e' else 1) := by
  intro x
  change (if x = a then e else if x = b then e' else 1) = 1 ∨
    (if x = a then e else if x = b then e' else 1) = -1
  by_cases hx : x = a
  · rw [if_pos hx]; exact he
  · rw [if_neg hx]
    by_cases hx' : x = b
    · rw [if_pos hx']; exact he'
    · rw [if_neg hx']; exact Or.inl rfl

private lemma c2slomqmfo_spIsSign_mul {n : ℕ} {s u : Fin n → ℤ} (hs : SpIsSign s)
    (hu : SpIsSign u) : SpIsSign (fun c => s c * u c) := by
  simpa using hs.mul hu (Equiv.refl (Fin n))

private lemma c2slomqmfo_injective_vec_four {α : Type*} (f0 f1 f2 f3 : α)
    (h01 : f0 ≠ f1) (h02 : f0 ≠ f2) (h03 : f0 ≠ f3) (h12 : f1 ≠ f2)
    (h13 : f1 ≠ f3) (h23 : f2 ≠ f3) :
    Function.Injective (![f0, f1, f2, f3] : Fin 4 → α) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private lemma c2slomqmfo_injective_vec_two {α : Type*} (f0 f1 : α) (h : f0 ≠ f1) :
    Function.Injective (![f0, f1] : Fin 2 → α) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private lemma c2slomqmfo_ne_of_vals {l : ℕ} {u v : Fin l → ℤ} {c : Fin l} {a b : ℤ}
    (hu : u c = a) (hv : v c = b) (hab : a ≠ b) : u ≠ v := by
  intro h
  have hc := congrFun h c
  rw [hu, hv] at hc
  exact hab hc

private lemma c2slomqmfo_fin_ne {l : ℕ} {a b : Fin l} (h : a.val ≠ b.val) : a ≠ b :=
  fun hab => h (by rw [hab])

private lemma c2slomqmfo_ne_shapeA {l : ℕ} (z p : Fin l) {π : Equiv.Perm (Fin l)}
    {s : Fin l → ℤ} (hs1 : ∀ a, s a = 1) (hπz : π z = p) {u u' : Fin l → ℤ}
    {a : ℤ} (hup : u p = a) (huz : u' z ≠ a) : u ≠ omqSignedActZ π s u' := by
  intro h
  have hval := congrFun h p
  change u p = s (π.symm p) * u' (π.symm p) at hval
  rw [(Equiv.symm_apply_eq π).mpr hπz.symm, hs1 z, one_mul, hup] at hval
  exact huz hval.symm

private lemma c2slomqmfo_ne_shapeA_z {l : ℕ} (z p : Fin l) {π : Equiv.Perm (Fin l)}
    {s : Fin l → ℤ} (hs1 : ∀ a, s a = 1) (hπp : π p = z) {u u' : Fin l → ℤ}
    (huz : u z = 2 ∨ u z = -2) (hup : u' p = 1 ∨ u' p = -1) :
    u ≠ omqSignedActZ π s u' := by
  intro h
  have hval := congrFun h z
  change u z = s (π.symm z) * u' (π.symm z) at hval
  rw [(Equiv.symm_apply_eq π).mpr hπp.symm, hs1 p, one_mul] at hval
  rcases huz with h2 | h2 <;> rcases hup with h1 | h1 <;>
    rw [h2, h1] at hval <;> norm_num at hval

private lemma c2slomqmfo_ne_shapeC {l : ℕ} (z : Fin l) {s : Fin l → ℤ} (hz : s z = -1)
    {u u' : Fin l → ℤ} (huz : u z = 1) (huz' : u' z = 1) :
    u ≠ omqSignedActZ 1 s u' := by
  intro h
  have hval := congrFun h z
  change u z = s z * u' z at hval
  rw [huz, hz, huz', mul_one] at hval
  norm_num at hval

theorem omq_minus_exists_four_flag {l : ℕ} (hl : 3 ≤ l) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j + 2 ≤ l)
    {π : Equiv.Perm (Fin l)} {s : Fin l → ℤ} (hs : SpIsSign s)
    (hsh : OmqMinusShape (by omega : 2 ≤ l) π s) :
    ∃ u : Fin 4 → Fin l → ℤ, Function.Injective u ∧
      (∀ i, OmqFormalInOrbit (omqMinusFlag l j) (u i)) ∧
      ∀ i i', u i ≠ omqSignedActZ π s (u i') := by
  classical
  let z : Fin l := ⟨0, by omega⟩
  let p : Fin l := ⟨1, by omega⟩
  let q : Fin l := ⟨2, by omega⟩
  have hzp : z ≠ p := c2slomqmfo_fin_ne (by simp only [z, p, Fin.val_mk]; omega)
  have hzq : z ≠ q := c2slomqmfo_fin_ne (by simp only [z, q, Fin.val_mk]; omega)
  have hpq : p ≠ q := c2slomqmfo_fin_ne (by simp only [p, q, Fin.val_mk]; omega)
  rcases hsh with ⟨hs1, hπ2, hπz, hπp⟩ | ⟨hπ1, hsz, hodd⟩
  ·
    let v : Fin l → ℤ := omqMinusFlag l j
    let w : Fin l := ⟨j + 1, by omega⟩
    have hwp : w ≠ p := c2slomqmfo_fin_ne (by simp only [w, p, Fin.val_mk]; omega)
    have hwz : w ≠ z := c2slomqmfo_fin_ne (by simp only [w, z, Fin.val_mk]; omega)
    have hπz' : π z = p := by simpa [z, p] using hπz
    let π' : Equiv.Perm (Fin l) := Equiv.swap p w
    have hπ'symm_z : π'.symm z = z := by
      dsimp [π']
      exact Equiv.swap_apply_of_ne_of_ne hzp (Ne.symm hwz)
    have hπ'symm_p : π'.symm p = w := by
      dsimp [π']
      exact Equiv.swap_apply_left p w
    have hπ'symm_w : π'.symm w = p := by
      dsimp [π']
      exact Equiv.swap_apply_right p w
    let t : ℤ → ℤ → Fin l → ℤ :=
      fun e e' b => if b = z then e else if b = p then e' else 1
    let f : ℤ → ℤ → Fin l → ℤ := fun e e' => omqSignedActZ π' (t e e') v
    have hv_z : v z = 1 := by simp [v, omqMinusFlag, z]
    have hv_p : v p = 1 := by simp [v, omqMinusFlag, p, hj1]
    have hv_w : v w = 0 := by
      have h : ¬ (j + 1 ≤ j) := by omega
      simp [v, omqMinusFlag, w, h]
    have hf_z : ∀ e e', f e e' z = e := by
      intro e e'
      change t e e' (π'.symm z) * v (π'.symm z) = e
      rw [hπ'symm_z, hv_z]
      simp [t]
    have hf_p : ∀ e e', f e e' p = 0 := by
      intro e e'
      change t e e' (π'.symm p) * v (π'.symm p) = 0
      rw [hπ'symm_p, hv_w]
      simp
    have hf_w : ∀ e e', f e e' w = e' := by
      intro e e'
      change t e e' (π'.symm w) * v (π'.symm w) = e'
      rw [hπ'symm_w, hv_p]
      simp [t, hzp.symm]
    have hf_orbit : ∀ e e', (e = 1 ∨ e = -1) → (e' = 1 ∨ e' = -1) →
        OmqFormalInOrbit v (f e e') := fun e e' he he' =>
      ⟨π', t e e', c2slomqmfo_spIsSign_ite_two z p he he', rfl⟩
    refine ⟨![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)], ?_, ?_, ?_⟩
    · exact c2slomqmfo_injective_vec_four _ _ _ _
        (c2slomqmfo_ne_of_vals (hf_w 1 1) (hf_w 1 (-1)) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_z 1 1) (hf_z (-1) 1) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_z 1 1) (hf_z (-1) (-1)) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_z 1 (-1)) (hf_z (-1) 1) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_z 1 (-1)) (hf_z (-1) (-1)) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_w (-1) 1) (hf_w (-1) (-1)) (by norm_num))
    · intro i
      fin_cases i
      · exact hf_orbit 1 1 (Or.inl rfl) (Or.inl rfl)
      · exact hf_orbit 1 (-1) (Or.inl rfl) (Or.inr rfl)
      · exact hf_orbit (-1) 1 (Or.inr rfl) (Or.inl rfl)
      · exact hf_orbit (-1) (-1) (Or.inr rfl) (Or.inr rfl)
    · intro i i'
      have hup : ∀ i : Fin 4, (![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)] :
          Fin 4 → Fin l → ℤ) i p = 0 := by
        intro i; fin_cases i <;> simp [hf_p]
      have huz : ∀ i : Fin 4, (![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)] :
          Fin 4 → Fin l → ℤ) i z ≠ 0 := by
        intro i; fin_cases i <;> simp [hf_z]
      exact c2slomqmfo_ne_shapeA z p hs1 hπz' (a := 0) (hup i) (huz i')
  ·
    subst hπ1
    let v : Fin l → ℤ := omqMinusFlag l j
    by_cases hjge : 2 ≤ j
    ·
      have hsz' : s z = -1 := by simpa [z] using hsz
      let t : ℤ → ℤ → Fin l → ℤ :=
        fun e e' b => if b = p then e else if b = q then e' else 1
      let f : ℤ → ℤ → Fin l → ℤ := fun e e' => omqSignedActZ 1 (t e e') v
      have hv_z : v z = 1 := by simp [v, omqMinusFlag, z]
      have hv_p : v p = 1 := by simp [v, omqMinusFlag, p, hj1]
      have hv_q : v q = 1 := by simp [v, omqMinusFlag, q, hjge]
      have hf_z : ∀ e e', f e e' z = 1 := by
        intro e e'; change t e e' z * v z = 1; simp [t, hzp, hzq, hv_z]
      have hf_p : ∀ e e', f e e' p = e := by
        intro e e'; change t e e' p * v p = e; simp [t, hv_p]
      have hf_q : ∀ e e', f e e' q = e' := by
        intro e e'; change t e e' q * v q = e'; simp [t, hpq.symm, hv_q]
      have hf_orbit : ∀ e e', (e = 1 ∨ e = -1) → (e' = 1 ∨ e' = -1) →
          OmqFormalInOrbit v (f e e') := fun e e' he he' =>
        ⟨1, t e e', c2slomqmfo_spIsSign_ite_two p q he he', rfl⟩
      refine ⟨![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)], ?_, ?_, ?_⟩
      · exact c2slomqmfo_injective_vec_four _ _ _ _
          (c2slomqmfo_ne_of_vals (hf_q 1 1) (hf_q 1 (-1)) (by norm_num))
          (c2slomqmfo_ne_of_vals (hf_p 1 1) (hf_p (-1) 1) (by norm_num))
          (c2slomqmfo_ne_of_vals (hf_p 1 1) (hf_p (-1) (-1)) (by norm_num))
          (c2slomqmfo_ne_of_vals (hf_p 1 (-1)) (hf_p (-1) 1) (by norm_num))
          (c2slomqmfo_ne_of_vals (hf_p 1 (-1)) (hf_p (-1) (-1)) (by norm_num))
          (c2slomqmfo_ne_of_vals (hf_q (-1) 1) (hf_q (-1) (-1)) (by norm_num))
      · intro i
        fin_cases i
        · exact hf_orbit 1 1 (Or.inl rfl) (Or.inl rfl)
        · exact hf_orbit 1 (-1) (Or.inl rfl) (Or.inr rfl)
        · exact hf_orbit (-1) 1 (Or.inr rfl) (Or.inl rfl)
        · exact hf_orbit (-1) (-1) (Or.inr rfl) (Or.inr rfl)
      · intro i i'
        have huz : ∀ i : Fin 4, (![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)] :
            Fin 4 → Fin l → ℤ) i z = 1 := by
          intro i; fin_cases i <;> simp [hf_z]
        exact c2slomqmfo_ne_shapeC z hsz' (huz i) (huz i')
    ·
      have hj_eq : j = 1 := by omega
      have hsz' : s z = -1 := by simpa [z] using hsz
      let t : ℤ → Fin l → ℤ := fun e b => if b = p then e else 1
      let fA : ℤ → Fin l → ℤ := fun e => omqSignedActZ 1 (t e) v
      let fB : ℤ → Fin l → ℤ := fun e => omqSignedActZ (Equiv.swap p q) (t e) v
      have hv_z : v z = 1 := by simp [v, omqMinusFlag, z]
      have hv_p : v p = 1 := by simp [v, omqMinusFlag, p, hj1]
      have hv_q : v q = 0 := by
        have h : ¬ (q.val ≤ j) := by simp only [q, Fin.val_mk]; omega
        simp [v, omqMinusFlag, q, h]
      have hfA_z : ∀ e, fA e z = 1 := by
        intro e; change t e z * v z = 1; simp [t, hzp, hv_z]
      have hfA_p : ∀ e, fA e p = e := by
        intro e; change t e p * v p = e; simp [t, hv_p]
      have hfA_q : ∀ e, fA e q = 0 := by
        intro e; change t e q * v q = 0; simp [t, hpq.symm, hv_q]
      have hfB_z : ∀ e, fB e z = 1 := by
        intro e
        change t e ((Equiv.swap p q) z) * v ((Equiv.swap p q) z) = 1
        rw [Equiv.swap_apply_of_ne_of_ne hzp hzq]
        simp [t, hzp, hv_z]
      have hfB_p : ∀ e, fB e p = 0 := by
        intro e
        change t e ((Equiv.swap p q) p) * v ((Equiv.swap p q) p) = 0
        rw [Equiv.swap_apply_left p q]
        simp [hv_q]
      have hfB_q : ∀ e, fB e q = e := by
        intro e
        change t e ((Equiv.swap p q) q) * v ((Equiv.swap p q) q) = e
        rw [Equiv.swap_apply_right p q]
        simp [t, hv_p]
      have hfA_orbit : ∀ e, (e = 1 ∨ e = -1) → OmqFormalInOrbit v (fA e) :=
        fun e he => ⟨1, t e, c2slomqmfo_spIsSign_ite_one p he, rfl⟩
      have hfB_orbit : ∀ e, (e = 1 ∨ e = -1) → OmqFormalInOrbit v (fB e) :=
        fun e he => ⟨Equiv.swap p q, t e, c2slomqmfo_spIsSign_ite_one p he, rfl⟩
      refine ⟨![fA 1, fA (-1), fB 1, fB (-1)], ?_, ?_, ?_⟩
      · exact c2slomqmfo_injective_vec_four _ _ _ _
          (c2slomqmfo_ne_of_vals (hfA_p 1) (hfA_p (-1)) (by norm_num))
          (c2slomqmfo_ne_of_vals (hfA_p 1) (hfB_p 1) (by norm_num))
          (c2slomqmfo_ne_of_vals (hfA_p 1) (hfB_p (-1)) (by norm_num))
          (c2slomqmfo_ne_of_vals (hfA_p (-1)) (hfB_p 1) (by norm_num))
          (c2slomqmfo_ne_of_vals (hfA_p (-1)) (hfB_p (-1)) (by norm_num))
          (c2slomqmfo_ne_of_vals (hfB_q 1) (hfB_q (-1)) (by norm_num))
      · intro i
        fin_cases i
        · exact hfA_orbit 1 (Or.inl rfl)
        · exact hfA_orbit (-1) (Or.inr rfl)
        · exact hfB_orbit 1 (Or.inl rfl)
        · exact hfB_orbit (-1) (Or.inr rfl)
      · intro i i'
        have huz : ∀ i : Fin 4, (![fA 1, fA (-1), fB 1, fB (-1)] :
            Fin 4 → Fin l → ℤ) i z = 1 := by
          intro i; fin_cases i <;> simp [hfA_z, hfB_z]
        exact c2slomqmfo_ne_shapeC z hsz' (huz i) (huz i')

theorem omq_minus_exists_four_cube {l : ℕ} (hl : 3 ≤ l) {π : Equiv.Perm (Fin l)}
    {s : Fin l → ℤ} (hs : SpIsSign s) (hsh : OmqMinusShape (by omega : 2 ≤ l) π s)
    (hc : 4 ≤ l ∨ π = 1) :
    ∃ u : Fin 4 → Fin l → ℤ, Function.Injective u ∧
      (∀ i, OmqFormalInOrbit (omqMinusCube l) (u i)) ∧
      ∀ i i', u i ≠ omqSignedActZ π s (u i') := by
  classical
  let z : Fin l := ⟨0, by omega⟩
  let p : Fin l := ⟨1, by omega⟩
  let q : Fin l := ⟨2, by omega⟩
  have hzp : z ≠ p := c2slomqmfo_fin_ne (by simp only [z, p, Fin.val_mk]; omega)
  have hzq : z ≠ q := c2slomqmfo_fin_ne (by simp only [z, q, Fin.val_mk]; omega)
  have hpq : p ≠ q := c2slomqmfo_fin_ne (by simp only [p, q, Fin.val_mk]; omega)
  rcases hsh with ⟨hs1, hπ2, hπz, hπp⟩ | ⟨hπ1, hsz, hodd⟩
  ·
    have hl4 : 4 ≤ l := by
      rcases hc with h4 | hπ1
      · exact h4
      · exfalso
        have hz_eq : π z = z := by rw [hπ1]; rfl
        rw [hπz] at hz_eq
        exact hzp hz_eq.symm
    let r : Fin l := ⟨3, by omega⟩
    have hzr : z ≠ r := c2slomqmfo_fin_ne (by simp only [z, r, Fin.val_mk]; omega)
    have hpr : p ≠ r := c2slomqmfo_fin_ne (by simp only [p, r, Fin.val_mk]; omega)
    have hqr : q ≠ r := c2slomqmfo_fin_ne (by simp only [q, r, Fin.val_mk]; omega)
    have hπz' : π z = p := by simpa [z, p] using hπz
    let v : Fin l → ℤ := omqMinusCube l
    let t : ℤ → ℤ → Fin l → ℤ := fun e e' b =>
      (if b = p then (-1 : ℤ) else 1) * (if b = q then e else 1) *
        (if b = r then e' else 1)
    let f : ℤ → ℤ → Fin l → ℤ := fun e e' => omqSignedActZ 1 (t e e') v
    have hv : ∀ b, v b = 1 := fun b => by simp [v, omqMinusCube]
    have hf_z : ∀ e e', f e e' z = 1 := by
      intro e e'
      change t e e' z * v z = 1
      simp [t, hzp, hzq, hzr, hv]
    have hf_p : ∀ e e', f e e' p = -1 := by
      intro e e'
      change t e e' p * v p = -1
      simp [t, hpq, hpr, hv]
    have hf_q : ∀ e e', f e e' q = e := by
      intro e e'
      change t e e' q * v q = e
      simp [t, hpq.symm, hqr, hv]
    have hf_r : ∀ e e', f e e' r = e' := by
      intro e e'
      change t e e' r * v r = e'
      simp [t, hpr.symm, hqr.symm, hv]
    have hf_orbit : ∀ e e', (e = 1 ∨ e = -1) → (e' = 1 ∨ e' = -1) →
        OmqFormalInOrbit v (f e e') := fun e e' he he' =>
      ⟨1, t e e', c2slomqmfo_spIsSign_mul
        (c2slomqmfo_spIsSign_mul (c2slomqmfo_spIsSign_ite_one p (Or.inr rfl))
          (c2slomqmfo_spIsSign_ite_one q he))
        (c2slomqmfo_spIsSign_ite_one r he'), rfl⟩
    refine ⟨![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)], ?_, ?_, ?_⟩
    · exact c2slomqmfo_injective_vec_four _ _ _ _
        (c2slomqmfo_ne_of_vals (hf_r 1 1) (hf_r 1 (-1)) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_q 1 1) (hf_q (-1) 1) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_q 1 1) (hf_q (-1) (-1)) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_q 1 (-1)) (hf_q (-1) 1) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_q 1 (-1)) (hf_q (-1) (-1)) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_r (-1) 1) (hf_r (-1) (-1)) (by norm_num))
    · intro i
      fin_cases i
      · exact hf_orbit 1 1 (Or.inl rfl) (Or.inl rfl)
      · exact hf_orbit 1 (-1) (Or.inl rfl) (Or.inr rfl)
      · exact hf_orbit (-1) 1 (Or.inr rfl) (Or.inl rfl)
      · exact hf_orbit (-1) (-1) (Or.inr rfl) (Or.inr rfl)
    · intro i i'
      have hup : ∀ i : Fin 4, (![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)] :
          Fin 4 → Fin l → ℤ) i p = -1 := by
        intro i; fin_cases i <;> simp [hf_p]
      have huz : ∀ i : Fin 4, (![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)] :
          Fin 4 → Fin l → ℤ) i z ≠ -1 := by
        intro i; fin_cases i <;> simp [hf_z]
      exact c2slomqmfo_ne_shapeA z p hs1 hπz' (a := -1) (hup i) (huz i')
  ·
    subst hπ1
    have hsz' : s z = -1 := by simpa [z] using hsz
    let v : Fin l → ℤ := omqMinusCube l
    let t : ℤ → ℤ → Fin l → ℤ :=
      fun e e' b => (if b = p then e else 1) * (if b = q then e' else 1)
    let f : ℤ → ℤ → Fin l → ℤ := fun e e' => omqSignedActZ 1 (t e e') v
    have hv : ∀ b, v b = 1 := fun b => by simp [v, omqMinusCube]
    have hf_z : ∀ e e', f e e' z = 1 := by
      intro e e'; change t e e' z * v z = 1; simp [t, hzp, hzq, hv]
    have hf_p : ∀ e e', f e e' p = e := by
      intro e e'; change t e e' p * v p = e; simp [t, hpq, hv]
    have hf_q : ∀ e e', f e e' q = e' := by
      intro e e'; change t e e' q * v q = e'; simp [t, hpq.symm, hv]
    have hf_orbit : ∀ e e', (e = 1 ∨ e = -1) → (e' = 1 ∨ e' = -1) →
        OmqFormalInOrbit v (f e e') := fun e e' he he' =>
      ⟨1, t e e', c2slomqmfo_spIsSign_mul
        (c2slomqmfo_spIsSign_ite_one p he) (c2slomqmfo_spIsSign_ite_one q he'), rfl⟩
    refine ⟨![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)], ?_, ?_, ?_⟩
    · exact c2slomqmfo_injective_vec_four _ _ _ _
        (c2slomqmfo_ne_of_vals (hf_q 1 1) (hf_q 1 (-1)) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_p 1 1) (hf_p (-1) 1) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_p 1 1) (hf_p (-1) (-1)) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_p 1 (-1)) (hf_p (-1) 1) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_p 1 (-1)) (hf_p (-1) (-1)) (by norm_num))
        (c2slomqmfo_ne_of_vals (hf_q (-1) 1) (hf_q (-1) (-1)) (by norm_num))
    · intro i
      fin_cases i
      · exact hf_orbit 1 1 (Or.inl rfl) (Or.inl rfl)
      · exact hf_orbit 1 (-1) (Or.inl rfl) (Or.inr rfl)
      · exact hf_orbit (-1) 1 (Or.inr rfl) (Or.inl rfl)
      · exact hf_orbit (-1) (-1) (Or.inr rfl) (Or.inr rfl)
    · intro i i'
      have huz : ∀ i : Fin 4, (![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)] :
          Fin 4 → Fin l → ℤ) i z = 1 := by
        intro i; fin_cases i <;> simp [hf_z]
      exact c2slomqmfo_ne_shapeC z hsz' (huz i) (huz i')

theorem omq_minus_exists_two_cube {l : ℕ} (hl : 3 ≤ l) {π : Equiv.Perm (Fin l)}
    {s : Fin l → ℤ} (hs : SpIsSign s) (hsh : OmqMinusShape (by omega : 2 ≤ l) π s) :
    ∃ u : Fin 2 → Fin l → ℤ, Function.Injective u ∧
      (∀ i, OmqFormalInOrbit (omqMinusCube l) (u i)) ∧
      ∀ i i', u i ≠ omqSignedActZ π s (u i') := by
  classical
  let z : Fin l := ⟨0, by omega⟩
  let p : Fin l := ⟨1, by omega⟩
  let q : Fin l := ⟨2, by omega⟩
  have hzp : z ≠ p := c2slomqmfo_fin_ne (by simp only [z, p, Fin.val_mk]; omega)
  have hzq : z ≠ q := c2slomqmfo_fin_ne (by simp only [z, q, Fin.val_mk]; omega)
  have hpq : p ≠ q := c2slomqmfo_fin_ne (by simp only [p, q, Fin.val_mk]; omega)
  rcases hsh with ⟨hs1, hπ2, hπz, hπp⟩ | ⟨hπ1, hsz, hodd⟩
  ·
    let v : Fin l → ℤ := omqMinusCube l
    let t : ℤ → Fin l → ℤ :=
      fun e b => (if b = p then (-1 : ℤ) else 1) * (if b = q then e else 1)
    let f : ℤ → Fin l → ℤ := fun e => omqSignedActZ 1 (t e) v
    have hv : ∀ b, v b = 1 := fun b => by simp [v, omqMinusCube]
    have hf_z : ∀ e, f e z = 1 := by
      intro e; change t e z * v z = 1; simp [t, hzp, hzq, hv]
    have hf_p : ∀ e, f e p = -1 := by
      intro e; change t e p * v p = -1; simp [t, hpq, hv]
    have hf_q : ∀ e, f e q = e := by
      intro e; change t e q * v q = e; simp [t, hpq.symm, hv]
    have hf_orbit : ∀ e, (e = 1 ∨ e = -1) → OmqFormalInOrbit v (f e) := fun e he =>
      ⟨1, t e, c2slomqmfo_spIsSign_mul
        (c2slomqmfo_spIsSign_ite_one p (Or.inr rfl))
        (c2slomqmfo_spIsSign_ite_one q he), rfl⟩
    refine ⟨![f 1, f (-1)], ?_, ?_, ?_⟩
    · exact c2slomqmfo_injective_vec_two _ _
        (c2slomqmfo_ne_of_vals (hf_q 1) (hf_q (-1)) (by norm_num))
    · intro i
      fin_cases i
      · exact hf_orbit 1 (Or.inl rfl)
      · exact hf_orbit (-1) (Or.inr rfl)
    · intro i i'
      have hup : ∀ i : Fin 2, (![f 1, f (-1)] : Fin 2 → Fin l → ℤ) i p = -1 := by
        intro i; fin_cases i <;> simp [hf_p]
      have huz : ∀ i : Fin 2, (![f 1, f (-1)] : Fin 2 → Fin l → ℤ) i z ≠ -1 := by
        intro i; fin_cases i <;> simp [hf_z]
      exact c2slomqmfo_ne_shapeA z p hs1 hπz (a := -1) (hup i) (huz i')
  ·
    subst hπ1
    have hsz' : s z = -1 := by simpa [z] using hsz
    let v : Fin l → ℤ := omqMinusCube l
    let t : ℤ → Fin l → ℤ := fun e b => if b = p then e else 1
    let f : ℤ → Fin l → ℤ := fun e => omqSignedActZ 1 (t e) v
    have hv : ∀ b, v b = 1 := fun b => by simp [v, omqMinusCube]
    have hf_z : ∀ e, f e z = 1 := by
      intro e; change t e z * v z = 1; simp [t, hzp, hv]
    have hf_p : ∀ e, f e p = e := by
      intro e; change t e p * v p = e; simp [t, hv]
    have hf_orbit : ∀ e, (e = 1 ∨ e = -1) → OmqFormalInOrbit v (f e) := fun e he =>
      ⟨1, t e, c2slomqmfo_spIsSign_ite_one p he, rfl⟩
    refine ⟨![f 1, f (-1)], ?_, ?_, ?_⟩
    · exact c2slomqmfo_injective_vec_two _ _
        (c2slomqmfo_ne_of_vals (hf_p 1) (hf_p (-1)) (by norm_num))
    · intro i
      fin_cases i
      · exact hf_orbit 1 (Or.inl rfl)
      · exact hf_orbit (-1) (Or.inr rfl)
    · intro i i'
      have huz : ∀ i : Fin 2, (![f 1, f (-1)] : Fin 2 → Fin l → ℤ) i z = 1 := by
        intro i; fin_cases i <;> simp [hf_z]
      exact c2slomqmfo_ne_shapeC z hsz' (huz i) (huz i')

theorem omq_minus_exists_four_two_one_one {l : ℕ} (hl : 3 ≤ l) {π : Equiv.Perm (Fin l)}
    {s : Fin l → ℤ} (hA : (∀ a, s a = 1) ∧ π * π = 1 ∧ π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
      π ⟨1, by omega⟩ = ⟨0, by omega⟩) :
    ∃ u : Fin 4 → Fin l → ℤ, Function.Injective u ∧
      (∀ i, OmqFormalInOrbit (fun b : Fin l => if b.val = 0 then 2 else 1) (u i)) ∧
      ∀ i i', u i ≠ omqSignedActZ π s (u i') := by
  classical
  let z : Fin l := ⟨0, by omega⟩
  let p : Fin l := ⟨1, by omega⟩
  have hzp : z ≠ p := c2slomqmfo_fin_ne (by simp only [z, p, Fin.val_mk]; omega)
  have hπp : π p = z := by simpa [z, p] using hA.2.2.2
  let v : Fin l → ℤ := fun b => if b.val = 0 then 2 else 1
  let t : ℤ → ℤ → Fin l → ℤ :=
    fun e e' b => (if b = z then e else 1) * (if b = p then e' else 1)
  let f : ℤ → ℤ → Fin l → ℤ := fun e e' => omqSignedActZ 1 (t e e') v
  have hv_z : v z = 2 := by simp [v, z]
  have hv_p : v p = 1 := by simp [v, p]
  have hf_z : ∀ e e', f e e' z = e * 2 := by
    intro e e'; change t e e' z * v z = e * 2; simp [t, hzp, hv_z]
  have hf_p : ∀ e e', f e e' p = e' := by
    intro e e'; change t e e' p * v p = e'; simp [t, hzp.symm, hv_p]
  have hf_orbit : ∀ e e', (e = 1 ∨ e = -1) → (e' = 1 ∨ e' = -1) →
      OmqFormalInOrbit v (f e e') := fun e e' he he' =>
    ⟨1, t e e', c2slomqmfo_spIsSign_mul
      (c2slomqmfo_spIsSign_ite_one z he) (c2slomqmfo_spIsSign_ite_one p he'), rfl⟩
  refine ⟨![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)], ?_, ?_, ?_⟩
  · exact c2slomqmfo_injective_vec_four _ _ _ _
      (c2slomqmfo_ne_of_vals (hf_p 1 1) (hf_p 1 (-1)) (by norm_num))
      (c2slomqmfo_ne_of_vals (hf_z 1 1) (hf_z (-1) 1) (by norm_num))
      (c2slomqmfo_ne_of_vals (hf_z 1 1) (hf_z (-1) (-1)) (by norm_num))
      (c2slomqmfo_ne_of_vals (hf_z 1 (-1)) (hf_z (-1) 1) (by norm_num))
      (c2slomqmfo_ne_of_vals (hf_z 1 (-1)) (hf_z (-1) (-1)) (by norm_num))
      (c2slomqmfo_ne_of_vals (hf_p (-1) 1) (hf_p (-1) (-1)) (by norm_num))
  · intro i
    fin_cases i
    · exact hf_orbit 1 1 (Or.inl rfl) (Or.inl rfl)
    · exact hf_orbit 1 (-1) (Or.inl rfl) (Or.inr rfl)
    · exact hf_orbit (-1) 1 (Or.inr rfl) (Or.inl rfl)
    · exact hf_orbit (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  · intro i i'
    have hz_i : (![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)] :
        Fin 4 → Fin l → ℤ) i z = 2 ∨
        (![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)] : Fin 4 → Fin l → ℤ) i z = -2 := by
      fin_cases i <;> simp [hf_z]
    have hp_i : (![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)] :
        Fin 4 → Fin l → ℤ) i' p = 1 ∨
        (![f 1 1, f 1 (-1), f (-1) 1, f (-1) (-1)] : Fin 4 → Fin l → ℤ) i' p = -1 := by
      fin_cases i' <;> simp [hf_p]
    exact c2slomqmfo_ne_shapeA_z z p hA.1 hπp hz_i hp_i

end CFSG.LocalAnalysis.WeakClosure81
