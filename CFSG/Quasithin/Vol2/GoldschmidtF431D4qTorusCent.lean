module

public import CFSG.GH74.BNPair.RootCalc

public section

namespace CFSG.Quasithin.H13.F431.D4q.F48

open CFSG.GH74.BNPair

variable {X : Type*} [Group X]

theorem intList_nodup (i j : ℤ) : (intList i j).Nodup :=
  List.Nodup.map (fun a b h => by simpa using h) List.nodup_range

theorem exists_fun_of_mem_chainProd (A : ℤ → Subgroup X) :
    ∀ l : List ℤ, l.Nodup → ∀ x ∈ chainProd A l,
      ∃ f : ℤ → X, (∀ k ∈ l, f k ∈ A k) ∧ (l.map f).prod = x
  | [], _, x, hx => ⟨fun _ => 1, fun k hk => by simp at hk, by
      simpa [chainProd, eq_comm] using hx⟩
  | k :: l, hnd, x, hx => by
    rw [List.nodup_cons] at hnd
    rw [chainProd_cons] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨f, hf, hfb⟩ := exists_fun_of_mem_chainProd A l hnd.2 b hb
    refine ⟨Function.update f k a, ?_, ?_⟩
    · intro k' hk'
      rcases List.mem_cons.1 hk' with rfl | h
      · simpa using ha
      · rw [Function.update_of_ne (fun h' : k' = k => hnd.1 (h' ▸ h))]
        exact hf k' h
    · rw [List.map_cons, List.prod_cons, Function.update_self, ← hfb]
      congr 2
      exact List.map_congr_left fun k' hk' =>
        Function.update_of_ne (fun h : k' = k => hnd.1 (h ▸ hk')) _ _

theorem conj_list_prod_map (h : X) (l : List ℤ) (g : ℤ → X) :
    h * (l.map g).prod * h⁻¹ = (l.map fun k => h * g k * h⁻¹).prod := by
  induction l with
  | nil => simp
  | cons k l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    group

theorem centralizer_U_trivial {n : ℕ} (D : RankTwoSystem X n) {h : X} (hh : h ∈ D.B ⊓ D.N)
    (hf : ∀ k : ℤ, 1 ≤ k → k ≤ n → ∀ x ∈ D.root k, h * x * h⁻¹ = x → x = 1)
    {y : X} (hy : y ∈ D.U) (hc : h * y * h⁻¹ = y) : y = 1 := by
  have hy' : y ∈ chainProd D.root (intList 1 n) := by
    rw [← D.roots.carrier_eq]
    exact hy
  obtain ⟨g, hg, hprod⟩ := exists_fun_of_mem_chainProd D.root _ (intList_nodup 1 n) y hy'
  have hrange : ∀ k ∈ intList 1 n, 1 ≤ k ∧ k ≤ n := fun k hk => mem_intList_iff.1 hk
  have hinv : ∀ k ∈ intList 1 n, h * g k * h⁻¹ ∈ D.root k := fun k hk =>
    D.roots.invariant k ⟨by have := (hrange k hk).1; omega, by have := hrange k hk; omega⟩ h hh
      (g k) (hg k hk)
  have heq := D.roots.unique (fun k => h * g k * h⁻¹) g hinv hg (by
    rw [← conj_list_prod_map, hprod, hc])
  have hone : ∀ k ∈ intList 1 n, g k = 1 := fun k hk =>
    hf k (hrange k hk).1 (hrange k hk).2 (g k) (hg k hk) (heq k hk)
  rw [← hprod]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hone k hk

end CFSG.Quasithin.H13.F431.D4q.F48
