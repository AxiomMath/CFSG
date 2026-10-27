module

public import CFSG.LocalAnalysis.StandardType.GGKacTablePatternList
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma k0patPerm_mem_bound {rho : List ℕ} {N : ℕ} (h : k0patPerm rho N) {i : Fin N} :
    rho.getD i.1 0 < N := by
  have hi : i.1 < rho.length := by rw [h.2.1]; exact i.2
  have hmem : rho.getD i.1 0 ∈ rho := by
    rw [← List.getElem_eq_getD (h := hi) 0]
    exact List.getElem_mem hi
  exact h.2.2 _ hmem

private lemma k0patPerm_toFun_bijective (rho : List ℕ) (N : ℕ) (h : k0patPerm rho N) :
    Function.Bijective (fun i : Fin N => (⟨rho.getD i.1 0, k0patPerm_mem_bound h⟩ : Fin N)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  intro i j hij
  apply Fin.ext
  have hi : i.1 < rho.length := by rw [h.2.1]; exact i.2
  have hj : j.1 < rho.length := by rw [h.2.1]; exact j.2
  exact (h.1.getD_inj hi hj).mp (congrArg Fin.val hij)

noncomputable def k0patPermEquiv (rho : List ℕ) (N : ℕ) (h : k0patPerm rho N) :
    Equiv.Perm (Fin N) :=
  Equiv.ofBijective (fun i : Fin N => (⟨rho.getD i.1 0, k0patPerm_mem_bound h⟩ : Fin N))
    (k0patPerm_toFun_bijective rho N h)

theorem k0patPermEquiv_apply_val (rho : List ℕ) (N : ℕ) (h : k0patPerm rho N) (i : Fin N) :
    ((k0patPermEquiv rho N h) i).1 = rho.getD i.1 0 := by
  rw [k0patPermEquiv, Equiv.ofBijective_apply]

private theorem k0patPermEquiv_iterate_val (rho : List ℕ) (N : ℕ) (h : k0patPerm rho N) :
    ∀ (t : ℕ) (i : Fin N),
      (((k0patPermEquiv rho N h)^[t]) i).1 = (fun x => rho.getD x 0)^[t] i.1 := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih =>
      intro i
      rw [Function.iterate_succ_apply, ih (k0patPermEquiv rho N h i), k0patPermEquiv_apply_val,
        Function.iterate_succ_apply]

private lemma k0patNodeGo_length {rho : List ℕ} {N k : ℕ} (hN : rho.length = N) {i : ℕ}
    (hkpos : 0 < k) (hkl : k ≤ N) (hfix : (fun x => rho.getD x 0)^[k] i = i)
    (hmin : ∀ t, 0 < t → t < k → (fun x => rho.getD x 0)^[t] i ≠ i) :
    (k0NodeOrbit rho i).length = k := by
  have key : ∀ m t, k - t = m → t < k → ∀ acc : List ℕ, acc.length = t + 1 →
      (k0NodeOrbit.go rho i (N - t + 1) ((fun x => rho.getD x 0)^[t + 1] i) acc).length = k := by
    intro m
    induction m with
    | zero =>
        intro t ht hlt acc _
        omega
    | succ m ih =>
        intro t ht hlt acc hacc
        rw [k0NodeOrbit.go.eq_2]
        by_cases hk1 : t + 1 = k
        · rw [if_pos (by rw [hk1]; exact hfix), hacc]
          omega
        · rw [if_neg (hmin (t + 1) (by omega) (by omega))]
          have hfuel : N - t = N - (t + 1) + 1 := by omega
          rw [hfuel]
          have hstep := ih (t + 1) (by omega) (by omega)
            (acc ++ [(fun x => rho.getD x 0)^[t + 1] i]) (by simp [hacc])
          simpa only [Function.iterate_succ_apply'] using hstep
  rw [k0NodeOrbit]
  have h := key k 0 (by omega) hkpos [i] (by simp)
  simpa [hN] using h

private theorem k0patNodeGo_length_ge (rho : List ℕ) (i : ℕ) :
    ∀ (fuel cur : ℕ) (acc : List ℕ),
      acc.length ≤ (k0NodeOrbit.go rho i fuel cur acc).length := by
  intro fuel
  induction fuel with
  | zero => intro cur acc; rw [k0NodeOrbit.go.eq_1]
  | succ fuel ih =>
      intro cur acc
      rw [k0NodeOrbit.go.eq_2]
      split
      · exact le_rfl
      · exact le_trans (by simp) (ih (rho.getD cur 0) (acc ++ [cur]))

theorem k0patNodeOrbit_length_pos (rho : List ℕ) (i : ℕ) : 0 < (k0NodeOrbit rho i).length := by
  rw [k0NodeOrbit]
  exact lt_of_lt_of_le (by simp)
    (k0patNodeGo_length_ge rho i (rho.length + 1) (rho.getD i 0) [i])

theorem k0patNodeOrbit_length_eq_minimalPeriod {rho : List ℕ} {N : ℕ} (h : k0patPerm rho N)
    {i : ℕ} (hi : i < N) :
    (k0NodeOrbit rho i).length = Function.minimalPeriod (k0patPermEquiv rho N h) ⟨i, hi⟩ := by
  let σ := k0patPermEquiv rho N h
  let x0 : Fin N := ⟨i, hi⟩
  have hlen : rho.length = N := h.2.1
  have hiter := k0patPermEquiv_iterate_val rho N h
  have hkpos : 0 < Function.minimalPeriod σ x0 :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      (Function.Injective.mem_periodicPts σ.injective x0)
  have hkle : Function.minimalPeriod σ x0 ≤ N := by
    simpa using Function.minimalPeriod_le_card (f := σ) (x := x0)
  have hfix : (fun x => rho.getD x 0)^[Function.minimalPeriod σ x0] i = i := by
    rw [← hiter (Function.minimalPeriod σ x0) x0, Function.iterate_minimalPeriod]
  have hmin : ∀ t, 0 < t → t < Function.minimalPeriod σ x0 →
      (fun x => rho.getD x 0)^[t] i ≠ i := by
    intro t ht hlt heq
    have hper : Function.IsPeriodicPt σ t x0 := by
      apply Fin.ext
      rw [hiter t x0, heq]
    exact (Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (by omega) hlt) hper
  exact k0patNodeGo_length hlen hkpos hkle hfix hmin

end CFSG.StandardType

end
