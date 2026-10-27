module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Tau

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_sT)

@[expose] def Vidx : List ℕ :=
  [0, 3, 4, 5, 6, 17, 18, 20, 24, 25, 26, 50, 56, 57, 58, 61]

@[expose] def Vw : List (List ℕ) :=
  [[], [1], [2, 3], [2, 4], [0], [0, 4], [0, 3], [3, 4], [0, 1], [1, 4], [1, 3], [0, 2], [4], [3],
    [1, 2], [2]]

@[expose] def Vl : List PL := Vidx.map fun i => Thl.getD i []

@[expose] def gp (i : ℕ) : Fin 45 := ⟨L0.getD i 0 % 45, Nat.mod_lt _ (by norm_num)⟩

@[expose] def gL (i : ℕ) : PL := tpL (L0.getD i 0)

@[expose] def prodR : List ℕ → PL
  | [] => idL
  | i :: w => comp (gL i) (prodR w)

theorem Vl_length : Vl.length = 16 := by decide +kernel

theorem Vl_nodup : Vl.Nodup := by decide +kernel

theorem Vl_mem_Thl : ∀ l ∈ Vl, l ∈ Thl := by decide +kernel

theorem Vl_mem_Tl : ∀ l ∈ Vl, l ∈ Tl := by decide +kernel

theorem Vl_mul : ∀ l ∈ Vl, ∀ m ∈ Vl, comp l m ∈ Vl := by decide +kernel

theorem Vl_comm : ∀ l ∈ Vl, ∀ m ∈ Vl, comp l m = comp m l := by decide +kernel

theorem Vl_sq : ∀ l ∈ Vl, comp l l = idL := by decide +kernel

theorem Vw_check : ∀ i < 16, prodR (Vw.getD i []) = Vl.getD i [] := by decide +kernel

theorem Vw_lt : ∀ w ∈ Vw, ∀ j ∈ w, j < 5 := by decide +kernel

theorem Vl_special : idL ∈ Vl ∧ Tl.getD 6 [] ∈ Vl ∧ Tl.getD 20 [] ∈ Vl := by decide +kernel

theorem gp_check : ∀ i < 5, L0.getD i 0 % 45 ∈ L0 ∧ L0.getD i 0 < 45 := by decide +kernel

@[expose] def gA (i : ℕ) : Ah := sA (gp i)

theorem repL_gA {i : ℕ} (hi : i < 5) : RepL (gL i) (gA i : P45) := by
  have e : ((gp i : Fin 45) : ℕ) = L0.getD i 0 := Nat.mod_eq_of_lt (gp_check i hi).2
  have h : gL i = tpL ((gp i : Fin 45) : ℕ) := by rw [e]; rfl
  rw [h]
  exact repL_sT (gp i)

theorem gA_mem_VA {i : ℕ} (hi : i < 5) : gA i ∈ VA :=
  Subgroup.subset_closure ⟨gp i, (gp_check i hi).1, rfl⟩

@[expose] def prodA (w : List ℕ) : Ah := (w.map gA).prod

theorem repL_prodA : ∀ w : List ℕ, (∀ j ∈ w, j < 5) → RepL (prodR w) (prodA w : P45)
  | [], _ => by
    show RepL idL ((1 : Ah) : P45)
    exact repL_one 45
  | i :: w, h => by
    have h1 := repL_gA (h i (List.mem_cons_self))
    have h2 := repL_prodA w (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have e : prodA (i :: w) = gA i * prodA w := by simp [prodA]
    rw [e]
    exact repL_mul h1 h2

theorem prodA_mem_VA : ∀ w : List ℕ, (∀ j ∈ w, j < 5) → prodA w ∈ VA := by
  intro w h
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact gA_mem_VA (h j hj)

end CFSG.Quasithin.H13.F431.U42Aut
