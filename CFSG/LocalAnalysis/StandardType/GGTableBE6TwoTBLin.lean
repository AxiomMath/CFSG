module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotAct
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus

public section

namespace CFSG.StandardType

open TableBExc.E6Three E6TwoPilot

namespace E6TwoTB

abbrev V : Type := Fin 4 → ZMod 3

theorem zmod3_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  revert a
  decide

theorem sub_refl_eq_update (i : Fin 4) (v : V) :
    v - reflFunE6Two i v • Pi.single i 1 = Function.update v i (-(v i)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    have key : ∀ a : ZMod 3, a - 2 * a * 1 = -a := by decide
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, Function.update_self,
      reflFunE6Two_apply]
    exact key _
  · simp [Pi.single_eq_of_ne hj, hj]

theorem single_mem_of_ne_zero (G : AddSubgroup V) (i : Fin 4) {a : ZMod 3} (ha : a ≠ 0)
    (h : (Pi.single i a : V) ∈ G) (b : ZMod 3) : (Pi.single i b : V) ∈ G := by
  have h1 : (Pi.single i (1 : ZMod 3) : V) ∈ G := by
    rcases zmod3_cases a with rfl | rfl | rfl
    · exact absurd rfl ha
    · exact h
    · have e : (Pi.single i (1 : ZMod 3) : V) = Pi.single i 2 + Pi.single i 2 := by
        rw [← Pi.single_add]
        rfl
      rw [e]
      exact G.add_mem h h
  rcases zmod3_cases b with rfl | rfl | rfl
  · rw [show ((Pi.single i (0 : ZMod 3)) : V) = 0 from Pi.single_zero i]
    exact G.zero_mem
  · exact h1
  · have e : (Pi.single i (2 : ZMod 3) : V) = Pi.single i 1 + Pi.single i 1 := by
      rw [← Pi.single_add]
      rfl
    rw [e]
    exact G.add_mem h1 h1

theorem eq_bot_or_eq_top_of_invariant (G : AddSubgroup V)
    (hrefl : ∀ (i : Fin 4) (v : V), v ∈ G → Function.update v i (-(v i)) ∈ G)
    (hmt : ∀ v ∈ G, mtFun v ∈ G) (hms : ∀ v ∈ G, msFun v ∈ G) : G = ⊥ ∨ G = ⊤ := by
  by_cases hbot : G = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨v, hvG, hv0⟩ : ∃ v ∈ G, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((AddSubgroup.eq_bot_iff_forall G).mpr hcon)
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (funext hcon)
  have hline : (Pi.single i (2 * v i) : V) ∈ G := by
    have h1 := G.sub_mem hvG (hrefl i v hvG)
    have e : v - Function.update v i (-(v i)) = Pi.single i (2 * v i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        have key : ∀ a : ZMod 3, a - -a = 2 * a := by decide
        simp only [Pi.sub_apply, Function.update_self, Pi.single_eq_same]
        exact key _
      · simp [hj, Pi.single_eq_of_ne hj]
    rw [e] at h1
    exact h1
  have h2 : (2 : ZMod 3) * v i ≠ 0 := by
    have key : ∀ a : ZMod 3, a ≠ 0 → 2 * a ≠ 0 := by decide
    exact key _ hi
  have hδi : (Pi.single i 1 : V) ∈ G := single_mem_of_ne_zero G i h2 hline 1
  have ht : ∀ j, (Pi.single j 1 : V) ∈ G → (Pi.single (tPerm j) 1 : V) ∈ G := by
    intro j hj
    have h := hmt _ hj
    rwa [mtFun_single] at h
  have h03 : (Pi.single 0 1 : V) ∈ G → (Pi.single 3 1 : V) ∈ G := by
    intro h0
    have hm := hms _ h0
    have e1 : msFun (Pi.single 0 1) = (![2, 1, 1, 2] : V) := by decide +kernel
    rw [e1] at hm
    have h1 := G.sub_mem hm (hrefl 3 _ hm)
    have e2 : (![2, 1, 1, 2] : V) - Function.update (![2, 1, 1, 2] : V) 3
        (-((![2, 1, 1, 2] : V) 3)) = Pi.single 3 1 := by decide +kernel
    rwa [e2] at h1
  have h30 : (Pi.single 3 1 : V) ∈ G → (Pi.single 0 1 : V) ∈ G := by
    intro h3
    have hm := hms _ h3
    have e1 : msFun (Pi.single 3 1) = (![1, 1, 1, 1] : V) := by decide +kernel
    rw [e1] at hm
    have h1 := G.sub_mem hm (hrefl 0 _ hm)
    have e2 : (![1, 1, 1, 1] : V) - Function.update (![1, 1, 1, 1] : V) 0
        (-((![1, 1, 1, 1] : V) 0)) = Pi.single 0 2 := by decide +kernel
    rw [e2] at h1
    exact single_mem_of_ne_zero G 0 (by decide) h1 1
  have h0 : (Pi.single 0 1 : V) ∈ G := by
    have hs1 : (Pi.single 1 1 : V) ∈ G → (Pi.single 0 1 : V) ∈ G := fun h => ht 2 (ht 1 h)
    have hs2 : (Pi.single 2 1 : V) ∈ G → (Pi.single 0 1 : V) ∈ G := fun h => ht 2 h
    clear hline h2 hi hvG hv0
    fin_cases i
    · exact hδi
    · exact hs1 hδi
    · exact hs2 hδi
    · exact h30 hδi
  have hall : ∀ j : Fin 4, (Pi.single j 1 : V) ∈ G := by
    intro j
    fin_cases j
    · exact h0
    · exact ht 0 h0
    · exact ht 1 (ht 0 h0)
    · exact h03 h0
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  exact G.sum_mem fun j _ => single_mem_of_ne_zero G j one_ne_zero (hall j) (w j)

theorem exists_smul_of_commute (f : V → V) (hadd : ∀ v w, f (v + w) = f v + f w)
    (hrefl : ∀ (i : Fin 4) (v : V),
      f (Function.update v i (-(v i))) = Function.update (f v) i (-(f v i)))
    (hmt : ∀ v, f (mtFun v) = mtFun (f v)) (hms : ∀ v, f (msFun v) = msFun (f v)) :
    ∃ c : ZMod 3, ∀ v, f v = c • v := by
  have f0 : f 0 = 0 := by
    exact map_zero (AddMonoidHom.mk' f hadd)
  have hdiag : ∀ j : Fin 4, f (Pi.single j 1) = Pi.single j (f (Pi.single j 1) j) := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · have h := hrefl i (Pi.single j 1)
      have e : Function.update (Pi.single j (1 : ZMod 3) : V) i
          (-((Pi.single j 1 : V) i)) = Pi.single j 1 := by
        funext k
        by_cases hk : k = i
        · subst hk
          rw [Function.update_self, Pi.single_eq_of_ne hij]
          decide
        · rw [Function.update_of_ne hk]
      rw [e] at h
      have h' := congrFun h i
      simp only [Function.update_self] at h'
      have key : ∀ a : ZMod 3, a = -a → a = 0 := by decide
      rw [Pi.single_eq_of_ne hij]
      exact key _ h'
  set l : Fin 4 → ZMod 3 := fun j => f (Pi.single j 1) j with hl
  have hfs : ∀ j : Fin 4, f (Pi.single j 1) = Pi.single j (l j) := fun j => hdiag j
  have hlt : ∀ j : Fin 4, l (tPerm j) = l j := by
    intro j
    have h := hmt (Pi.single j 1)
    rw [mtFun_single, hfs (tPerm j), hfs j, mtFun_single] at h
    have h' := congrFun h (tPerm j)
    simpa using h'
  have hl1 : l 1 = l 0 := hlt 0
  have hl2 : l 2 = l 0 := (hlt 1).trans hl1
  have hl3 : l 3 = l 0 := by
    have h := hms (Pi.single 3 1)
    have e1 : msFun (Pi.single 3 1) = (![1, 1, 1, 1] : V) := by decide +kernel
    have e2 : (![1, 1, 1, 1] : V) =
        Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1 := by decide +kernel
    have hsum : f (![1, 1, 1, 1] : V) = ![l 0, l 1, l 2, l 3] := by
      rw [e2, hadd, hadd, hadd, hfs 0, hfs 1, hfs 2, hfs 3]
      funext k
      fin_cases k <;> simp
    rw [e1, hsum, hfs 3, msFun_single] at h
    have h' := congrFun h 0
    simpa [msCol] using h'.symm
  have hlall : ∀ j : Fin 4, l j = l 0 := by
    intro j
    fin_cases j
    · rfl
    · exact hl1
    · exact hl2
    · exact hl3
  have hsingle : ∀ (j : Fin 4) (a : ZMod 3), f (Pi.single j a) = Pi.single j (l 0 * a) := by
    intro j a
    rcases zmod3_cases a with rfl | rfl | rfl
    · rw [Pi.single_zero, f0, mul_zero, Pi.single_zero]
    · rw [mul_one, hfs j, hlall j]
    · have e : (Pi.single j (2 : ZMod 3) : V) = Pi.single j 1 + Pi.single j 1 := by
        rw [← Pi.single_add]
        rfl
      rw [e, hadd, hfs j, ← Pi.single_add, hlall j]
      have key : ∀ c : ZMod 3, c + c = c * 2 := by decide
      rw [key]
  refine ⟨l 0, fun v => ?_⟩
  let F : V →+ V := AddMonoidHom.mk' f hadd
  calc f v = F (∑ j, Pi.single j (v j)) := by rw [Finset.univ_sum_single]; rfl
    _ = ∑ j, F (Pi.single j (v j)) := map_sum F _ _
    _ = ∑ j, Pi.single j (l 0 * v j) := by simp only [F, AddMonoidHom.mk'_apply, hsingle]
    _ = l 0 • v := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]

end E6TwoTB

end CFSG.StandardType
