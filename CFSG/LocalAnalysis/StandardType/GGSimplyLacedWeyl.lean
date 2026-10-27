module

public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedTits
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

variable {ι : Type}

@[expose] def GGSimplyLacedConnected (M : CoxeterMatrix ι) : Prop :=
  GGSimplyLaced M ∧ ∀ i j : ι, Relation.ReflTransGen (fun a b : ι => M.M a b = 3) i j

private theorem reflTransGen_symm {α : Type*} {r : α → α → Prop} (hsymm : Symmetric r)
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact (Relation.ReflTransGen.single (hsymm hstep)).trans ih

private theorem ggSimplyLacedConnected_mk {M : CoxeterMatrix ι}
    (hlab : ∀ i j : ι, i ≠ j → M.M i j = 2 ∨ M.M i j = 3)
    (b : ι) (hb : ∀ i : ι, Relation.ReflTransGen (fun a c : ι => M.M a c = 3) i b) :
    GGSimplyLacedConnected M := by
  refine ⟨hlab, ?_⟩
  intro i j
  have hsymm : Symmetric (fun a c : ι => M.M a c = 3) :=
    fun a c h => (M.symmetric c a).trans h
  exact (hb i).trans (reflTransGen_symm hsymm (hb j))

private theorem ggSimplyLacedConnected_reindex {κ : Type} (N : CoxeterMatrix κ) (e : κ ≃ ι)
    (h : GGSimplyLacedConnected N) :
    GGSimplyLacedConnected (CoxeterMatrix.reindex e N) := by
  obtain ⟨hlab, hconn⟩ := h
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hne : e.symm i ≠ e.symm j := by
      intro hh
      exact hij (by rw [← e.apply_symm_apply i, hh, e.apply_symm_apply j])
    simpa [CoxeterMatrix.reindex_apply] using hlab (e.symm i) (e.symm j) hne
  · intro i j
    have hstep : ∀ a b : κ, N.M a b = 3 →
        (CoxeterMatrix.reindex e N).M (e a) (e b) = 3 := by
      intro a b hab
      simpa [CoxeterMatrix.reindex_apply] using hab
    have hpath := (Relation.ReflTransGen.lift (f := e)
        (p := fun x y : ι => (CoxeterMatrix.reindex e N).M x y = 3) hstep)
        (e.symm i) (e.symm j) (hconn (e.symm i) (e.symm j))
    simpa [Function.onFun] using hpath

private theorem ggSimplyLaced_A (n : ℕ) : GGSimplyLaced (CoxeterMatrix.A n) := by
  intro i j hij
  simp only [CoxeterMatrix.A, Matrix.of_apply, hij, ite_false]
  split_ifs <;> simp

private theorem ggSimplyLaced_connected_A (n : ℕ) (hn : 1 ≤ n) :
    ∀ i : Fin n,
      Relation.ReflTransGen (fun a b : Fin n => (CoxeterMatrix.A n).M a b = 3) i ⟨0, by omega⟩ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  refine Fin.induction ?_ ?_
  · exact Relation.ReflTransGen.refl
  · intro i ih
    refine (Relation.ReflTransGen.single ?_).trans ih
    have hne : i.succ ≠ i.castSucc :=
      Fin.ne_of_val_ne (by simp [Fin.val_succ, Fin.val_castSucc])
    simp [CoxeterMatrix.A, Matrix.of_apply, hne]

private theorem ggSimplyLacedConnected_A (n : ℕ) (hn : 1 ≤ n) :
    GGSimplyLacedConnected (CoxeterMatrix.A n) :=
  ggSimplyLacedConnected_mk (ggSimplyLaced_A n) ⟨0, by omega⟩ (ggSimplyLaced_connected_A n hn)

theorem ggSimplyLaced_D (n : ℕ) : GGSimplyLaced (ggCoxeterMatrixD n) := by
  intro i j hij
  rw [ggCoxeterMatrixD_apply, if_neg hij]
  split_ifs <;> simp

private theorem ggCoxeterMatrixD_edge_succ (n : ℕ) (hn : 4 ≤ n) (j : ℕ)
    (hj : j + 1 ≤ n - 3) :
    (ggCoxeterMatrixD n).M ⟨j + 1, by omega⟩ ⟨j, by omega⟩ = 3 := by
  rw [ggCoxeterMatrixD_apply,
    if_neg (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)]
  have hD : CartanMatrix.D n ⟨j + 1, by omega⟩ ⟨j, by omega⟩ = -1 := by
    rw [CartanMatrix.D, Matrix.of_apply]
    simp only [Fin.val_mk]
    rw [if_neg (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega),
      if_neg (by omega),
      if_neg (by rintro ⟨h1, h2⟩; omega)]
    simp only [true_and]
    rw [if_pos (by omega)]
  rw [hD]
  norm_num

private theorem ggCoxeterMatrixD_edge_fork_left (n : ℕ) (hn : 4 ≤ n) :
    (ggCoxeterMatrixD n).M ⟨n - 2, by omega⟩ ⟨n - 3, by omega⟩ = 3 := by
  rw [ggCoxeterMatrixD_apply,
    if_neg (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)]
  have hD : CartanMatrix.D n ⟨n - 2, by omega⟩ ⟨n - 3, by omega⟩ = -1 := by
    rw [CartanMatrix.D, Matrix.of_apply]
    simp only [Fin.val_mk]
    rw [if_neg (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega),
      if_neg (by omega),
      if_neg (by rintro ⟨h1, h2⟩; omega),
      if_neg (by rintro ⟨h1, h2⟩; omega),
      if_neg (by rintro ⟨h1, h2⟩; omega),
      if_pos (by refine ⟨by omega, Or.inl (by omega)⟩)]
  rw [hD]
  norm_num

private theorem ggCoxeterMatrixD_edge_fork_right (n : ℕ) (hn : 4 ≤ n) :
    (ggCoxeterMatrixD n).M ⟨n - 1, by omega⟩ ⟨n - 3, by omega⟩ = 3 := by
  rw [ggCoxeterMatrixD_apply,
    if_neg (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)]
  have hD : CartanMatrix.D n ⟨n - 1, by omega⟩ ⟨n - 3, by omega⟩ = -1 := by
    rw [CartanMatrix.D, Matrix.of_apply]
    simp only [Fin.val_mk]
    rw [if_neg (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega),
      if_neg (by omega),
      if_neg (by rintro ⟨h1, h2⟩; omega),
      if_neg (by rintro ⟨h1, h2⟩; omega),
      if_neg (by rintro ⟨h1, h2⟩; omega),
      if_pos (by refine ⟨by omega, Or.inr (by omega)⟩)]
  rw [hD]
  norm_num

private theorem ggSimplyLaced_connected_D_chain (n : ℕ) (hn : 4 ≤ n) :
    ∀ j : ℕ, (hj : j ≤ n - 3) →
      Relation.ReflTransGen (fun a b : Fin n => (ggCoxeterMatrixD n).M a b = 3)
        ⟨j, by omega⟩ ⟨0, by omega⟩ := by
  intro j
  induction j with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ j ih =>
      intro hj
      refine (Relation.ReflTransGen.single
        (r := fun a b : Fin n => (ggCoxeterMatrixD n).M a b = 3)
        (ggCoxeterMatrixD_edge_succ n hn j (by omega))).trans ?_
      exact ih (by omega)

private theorem ggSimplyLaced_connected_D (n : ℕ) (hn : 4 ≤ n) :
    ∀ i : Fin n,
      Relation.ReflTransGen (fun a b : Fin n => (ggCoxeterMatrixD n).M a b = 3)
        i ⟨0, by omega⟩ := by
  intro i
  by_cases hi : i.val ≤ n - 3
  · simpa using ggSimplyLaced_connected_D_chain n hn i.val hi
  · have htop : i.val = n - 2 ∨ i.val = n - 1 := by omega
    rcases htop with h | h
    · have hi_eq : i = ⟨n - 2, by omega⟩ := Fin.ext h
      rw [hi_eq]
      exact (Relation.ReflTransGen.single
        (r := fun a b : Fin n => (ggCoxeterMatrixD n).M a b = 3)
        (ggCoxeterMatrixD_edge_fork_left n hn)).trans
        (ggSimplyLaced_connected_D_chain n hn (n - 3) (by omega))
    · have hi_eq : i = ⟨n - 1, by omega⟩ := Fin.ext h
      rw [hi_eq]
      exact (Relation.ReflTransGen.single
        (r := fun a b : Fin n => (ggCoxeterMatrixD n).M a b = 3)
        (ggCoxeterMatrixD_edge_fork_right n hn)).trans
        (ggSimplyLaced_connected_D_chain n hn (n - 3) (by omega))

private theorem ggSimplyLacedConnected_D (n : ℕ) (hn : 4 ≤ n) :
    GGSimplyLacedConnected (ggCoxeterMatrixD n) :=
  ggSimplyLacedConnected_mk (ggSimplyLaced_D n) ⟨0, by omega⟩ (ggSimplyLaced_connected_D n hn)

private theorem ggSimplyLaced_E6 : GGSimplyLaced (CoxeterMatrix.E₆) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [CoxeterMatrix.E₆, Matrix.of_apply, Matrix.cons_val']

private theorem ggSimplyLaced_connected_E6 :
    ∀ i : Fin 6,
      Relation.ReflTransGen (fun a b : Fin 6 => (CoxeterMatrix.E₆).M a b = 3) i 3 := by
  intro i
  fin_cases i
  · exact (Relation.ReflTransGen.single (r := fun a b : Fin 6 => (CoxeterMatrix.E₆).M a b = 3) (show (CoxeterMatrix.E₆).M 0 2 = 3 by
        simp [CoxeterMatrix.E₆, Matrix.of_apply, Matrix.cons_val'])).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 6 => (CoxeterMatrix.E₆).M a b = 3) (show (CoxeterMatrix.E₆).M 2 3 = 3 by
        simp [CoxeterMatrix.E₆, Matrix.of_apply, Matrix.cons_val']))
  · exact Relation.ReflTransGen.single (r := fun a b : Fin 6 => (CoxeterMatrix.E₆).M a b = 3) (show (CoxeterMatrix.E₆).M 1 3 = 3 by
        simp [CoxeterMatrix.E₆, Matrix.of_apply, Matrix.cons_val'])
  · exact Relation.ReflTransGen.single (r := fun a b : Fin 6 => (CoxeterMatrix.E₆).M a b = 3) (show (CoxeterMatrix.E₆).M 2 3 = 3 by
        simp [CoxeterMatrix.E₆, Matrix.of_apply, Matrix.cons_val'])
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (r := fun a b : Fin 6 => (CoxeterMatrix.E₆).M a b = 3) (show (CoxeterMatrix.E₆).M 4 3 = 3 by
        simp [CoxeterMatrix.E₆, Matrix.of_apply, Matrix.cons_val'])
  · exact (Relation.ReflTransGen.single (r := fun a b : Fin 6 => (CoxeterMatrix.E₆).M a b = 3) (show (CoxeterMatrix.E₆).M 5 4 = 3 by
        simp [CoxeterMatrix.E₆, Matrix.of_apply, Matrix.cons_val'])).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 6 => (CoxeterMatrix.E₆).M a b = 3) (show (CoxeterMatrix.E₆).M 4 3 = 3 by
        simp [CoxeterMatrix.E₆, Matrix.of_apply, Matrix.cons_val']))

private theorem ggSimplyLacedConnected_E6 : GGSimplyLacedConnected (CoxeterMatrix.E₆) :=
  ggSimplyLacedConnected_mk ggSimplyLaced_E6 3 ggSimplyLaced_connected_E6

private theorem ggSimplyLaced_E7 : GGSimplyLaced (CoxeterMatrix.E₇) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val']

private theorem ggSimplyLaced_connected_E7 :
    ∀ i : Fin 7,
      Relation.ReflTransGen (fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) i 3 := by
  intro i
  fin_cases i
  · exact (Relation.ReflTransGen.single (r := fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) (show (CoxeterMatrix.E₇).M 0 2 = 3 by
        simp [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val'])).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) (show (CoxeterMatrix.E₇).M 2 3 = 3 by
        simp [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val']))
  · exact Relation.ReflTransGen.single (r := fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) (show (CoxeterMatrix.E₇).M 1 3 = 3 by
        simp [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val'])
  · exact Relation.ReflTransGen.single (r := fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) (show (CoxeterMatrix.E₇).M 2 3 = 3 by
        simp [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val'])
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (r := fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) (show (CoxeterMatrix.E₇).M 4 3 = 3 by
        simp [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val'])
  · exact (Relation.ReflTransGen.single (r := fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) (show (CoxeterMatrix.E₇).M 5 4 = 3 by
        simp [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val'])).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) (show (CoxeterMatrix.E₇).M 4 3 = 3 by
        simp [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val']))
  · exact ((Relation.ReflTransGen.single (r := fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) (show (CoxeterMatrix.E₇).M 6 5 = 3 by
        simp [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val'])).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) (show (CoxeterMatrix.E₇).M 5 4 = 3 by
        simp [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val']))).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 7 => (CoxeterMatrix.E₇).M a b = 3) (show (CoxeterMatrix.E₇).M 4 3 = 3 by
        simp [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val']))

private theorem ggSimplyLacedConnected_E7 : GGSimplyLacedConnected (CoxeterMatrix.E₇) :=
  ggSimplyLacedConnected_mk ggSimplyLaced_E7 3 ggSimplyLaced_connected_E7

private theorem ggSimplyLaced_E8 : GGSimplyLaced (CoxeterMatrix.E₈) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val']

private theorem ggSimplyLaced_connected_E8 :
    ∀ i : Fin 8,
      Relation.ReflTransGen (fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) i 3 := by
  intro i
  fin_cases i
  · exact (Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 0 2 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val'])).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 2 3 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val']))
  · exact Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 1 3 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val'])
  · exact Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 2 3 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val'])
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 4 3 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val'])
  · exact (Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 5 4 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val'])).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 4 3 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val']))
  · exact ((Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 6 5 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val'])).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 5 4 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val']))).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 4 3 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val']))
  · exact (((Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 7 6 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val'])).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 6 5 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val']))).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 5 4 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val']))).trans
      (Relation.ReflTransGen.single (r := fun a b : Fin 8 => (CoxeterMatrix.E₈).M a b = 3) (show (CoxeterMatrix.E₈).M 4 3 = 3 by
        simp [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val']))

private theorem ggSimplyLacedConnected_E8 : GGSimplyLacedConnected (CoxeterMatrix.E₈) :=
  ggSimplyLacedConnected_mk ggSimplyLaced_E8 3 ggSimplyLaced_connected_E8

theorem ggIsWeylMatrix_finite {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M) : Finite ι := by
  rcases hM with ⟨n, e, _, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
  · exact Finite.of_equiv (Fin n) e
  · exact Finite.of_equiv (Fin 6) e
  · exact Finite.of_equiv (Fin 7) e
  · exact Finite.of_equiv (Fin 8) e
  · exact Finite.of_equiv (Fin 4) e
  · exact Finite.of_equiv (Fin 2) e

theorem ggSimplyLacedConnected_of_weyl {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) : GGSimplyLacedConnected M := by
  rcases hM with ⟨n, e, hn, hcase⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ | ⟨e, hG2⟩
  · rcases hcase with hA | hB | hD
    · rw [hA]
      exact ggSimplyLacedConnected_reindex (CoxeterMatrix.A n) e (ggSimplyLacedConnected_A n hn)
    · obtain ⟨hn2, hB⟩ := hB
      exfalso
      have hne : e ⟨n - 1, by omega⟩ ≠ e ⟨n - 2, by omega⟩ := by
        intro hh
        have hv := congrArg Fin.val (e.injective hh)
        simp only [Fin.val_mk] at hv
        omega
      have hle := h3 (e ⟨n - 1, by omega⟩) (e ⟨n - 2, by omega⟩) hne
      rw [hB] at hle
      have hlab : ((CoxeterMatrix.B n).reindex e).M (e ⟨n - 1, by omega⟩)
          (e ⟨n - 2, by omega⟩) = 4 := by
        rw [CoxeterMatrix.reindex_apply]
        simp only [Equiv.symm_apply_apply]
        have hneFin : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := by
          intro hh
          have hv := congrArg Fin.val hh
          simp only [Fin.val_mk] at hv
          omega
        simp [CoxeterMatrix.B, Matrix.of_apply, hneFin]
      rw [hlab] at hle
      omega
    · obtain ⟨hn4, hD⟩ := hD
      rw [hD]
      exact ggSimplyLacedConnected_reindex (ggCoxeterMatrixD n) e (ggSimplyLacedConnected_D n hn4)
  · rw [hE6]
    exact ggSimplyLacedConnected_reindex (CoxeterMatrix.E₆) e ggSimplyLacedConnected_E6
  · rw [hE7]
    exact ggSimplyLacedConnected_reindex (CoxeterMatrix.E₇) e ggSimplyLacedConnected_E7
  · rw [hE8]
    exact ggSimplyLacedConnected_reindex (CoxeterMatrix.E₈) e ggSimplyLacedConnected_E8
  · exfalso
    have hne : e 1 ≠ e 2 := by
      intro hh
      have hv := congrArg Fin.val (e.injective hh)
      norm_num at hv
    have hle := h3 (e 1) (e 2) hne
    rw [hF4] at hle
    have hlab : ((CoxeterMatrix.F₄).reindex e).M (e 1) (e 2) = 4 := by
      rw [CoxeterMatrix.reindex_apply]
      simp only [Equiv.symm_apply_apply]
      simp [CoxeterMatrix.F₄, Matrix.of_apply, Matrix.cons_val']
    rw [hlab] at hle
    omega
  · exfalso
    have hne : e 0 ≠ e 1 := by
      intro hh
      have hv := congrArg Fin.val (e.injective hh)
      norm_num at hv
    have hle := h3 (e 0) (e 1) hne
    rw [hG2] at hle
    have hlab : ((CoxeterMatrix.G₂).reindex e).M (e 0) (e 1) = 6 := by
      rw [CoxeterMatrix.reindex_apply]
      simp only [Equiv.symm_apply_apply]
      simp [CoxeterMatrix.G₂, Matrix.of_apply, Matrix.cons_val']
    rw [hlab] at hle
    omega

private def SimpleConj (M : CoxeterMatrix ι) (a b : ι) : Prop :=
  ∃ w : M.Group, M.simple b = w * M.simple a * w⁻¹

private theorem simple_conj_of_label3 {M : CoxeterMatrix ι} {a b : ι} (h : M.M a b = 3) :
    M.simple b = (M.simple a * M.simple b) * M.simple a * (M.simple a * M.simple b)⁻¹ := by
  have hbraid : M.simple a * M.simple b * M.simple a = M.simple b * M.simple a * M.simple b :=
    ggSimplyLaced_braid h
  have ha : M.simple a * M.simple a = 1 := by
    simpa [CoxeterMatrix.toCoxeterSystem_simple] using
      (CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem a)
  have hb : M.simple b * M.simple b = 1 := by
    simpa [CoxeterMatrix.toCoxeterSystem_simple] using
      (CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem b)
  have hia : (M.simple a)⁻¹ = M.simple a := by
    simpa [CoxeterMatrix.toCoxeterSystem_simple] using
      (CoxeterSystem.inv_simple M.toCoxeterSystem a)
  have hib : (M.simple b)⁻¹ = M.simple b := by
    simpa [CoxeterMatrix.toCoxeterSystem_simple] using
      (CoxeterSystem.inv_simple M.toCoxeterSystem b)
  rw [mul_inv_rev, hia, hib, hbraid]
  rw [mul_assoc (M.simple b * M.simple a) (M.simple b) (M.simple b * M.simple a),
    ← mul_assoc (M.simple b) (M.simple b) (M.simple a), hb, one_mul,
    mul_assoc (M.simple b) (M.simple a) (M.simple a), ha, mul_one]

private theorem simpleConj_refl (M : CoxeterMatrix ι) (a : ι) : SimpleConj M a a :=
  ⟨1, by simp⟩

private theorem simpleConj_trans {M : CoxeterMatrix ι} {a b c : ι}
    (h1 : SimpleConj M a b) (h2 : SimpleConj M b c) : SimpleConj M a c := by
  obtain ⟨w1, hw1⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  refine ⟨w2 * w1, ?_⟩
  rw [hw2, hw1, mul_inv_rev]
  group

private theorem reflTransGen_to_rel {α : Type*} {r : α → α → Prop}
    (hrefl : ∀ a, r a a) (htrans : ∀ a b c, r a b → r b c → r a c) :
    ∀ a b, Relation.ReflTransGen r a b → r a b := by
  intro a b h
  induction h with
  | refl => exact hrefl a
  | tail _ step ih => exact htrans _ _ _ ih step

theorem ggSimplyLaced_simple_conj {M : CoxeterMatrix ι} (hM : GGSimplyLacedConnected M)
    (i j : ι) : ∃ w : M.Group, M.simple j = w * M.simple i * w⁻¹ := by
  obtain ⟨_, hconn⟩ := hM
  have hstep : ∀ a b : ι, M.M a b = 3 → SimpleConj M a b :=
    fun a b h => ⟨M.simple a * M.simple b, simple_conj_of_label3 h⟩
  exact reflTransGen_to_rel (simpleConj_refl M)
    (fun a b c hab hbc => simpleConj_trans hab hbc) i j
    ((Relation.ReflTransGen.lift id hstep) i j (hconn i j))

end CFSG.StandardType

end
