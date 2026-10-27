module

public import CFSG.LocalAnalysis.StandardType.GGHalfX0Bridge
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_decls CFSG.StandardType.GGHalfX0K "CFSG/LocalAnalysis/StandardType/data/gghalf_x0_orbit.txt" 118944 17937482642164541943

namespace CFSG.StandardType.GGHalfX0K

@[expose] noncomputable def gK (G g : ℕ) : List ℕ :=
  (List.range 27).map fun c => Nat.land (Nat.shiftRight G (27 * (27 * g + c))) 134217727

@[expose] noncomputable def rbK (B k : ℕ) : List ℕ :=
  (List.range 5).map fun j => Nat.land (Nat.shiftRight B (27 * (5 * k + j))) 134217727

@[expose] noncomputable def stepsK (G B : ℕ) (ts : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun t _ ih i => Nat.blt (t / 24) i &&
      (rbK B i == (rbK B (t / 24)).map (ggHalfApplyBits (gK G (t % 24)))) && ih (i + 1)) ts

theorem stepsK_spec (G B : ℕ) : ∀ (ts : List ℕ) (i : ℕ), stepsK G B ts i = true →
    ∀ k (hk : k < ts.length), ts[k] / 24 < i + k ∧
      rbK B (i + k) = (rbK B (ts[k] / 24)).map (ggHalfApplyBits (gK G (ts[k] % 24)))
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | t :: ts, i, h, k, hk => by
    have h' : (Nat.blt (t / 24) i && (rbK B i == (rbK B (t / 24)).map
        (ggHalfApplyBits (gK G (t % 24)))) && stepsK G B ts (i + 1)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    cases k with
    | zero => exact ⟨h1, h2⟩
    | succ k =>
      have e : i + (k + 1) = i + 1 + k := by omega
      rw [e]
      exact stepsK_spec G B ts (i + 1) h3 k (by simpa using hk)

theorem getD_reverse_take (R : List (List ℕ)) {i j : ℕ} (hj : j < i) (hi : i ≤ R.length) :
    (R.take i).reverse.getD (i - 1 - j) [] = R.getD j [] := by
  have e : i - 1 - (i - 1 - j) = j := by omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_reverse (by rw [List.length_take]; omega), List.length_take,
    Nat.min_eq_left hi, e, List.getElem?_take_of_lt hj]

theorem reverse_take_succ (R : List (List ℕ)) {i : ℕ} (hi : i < R.length) :
    (R.take (i + 1)).reverse = R.getD i [] :: (R.take i).reverse := by
  rw [List.take_succ, List.reverse_append, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]
  rfl

theorem aux_eq (gens R : List (List ℕ)) (f : List (List ℕ) → ℕ → List ℕ → List (List ℕ))
    (h0 : ∀ acc i, f acc i [] = acc.reverse)
    (h1 : ∀ acc i t ts, f acc i (t :: ts) =
      f ((acc.getD (i - 1 - t / 24) []).map
        (fun b => ggHalfApplyBits (gens.getD (t % 24) ggHalfIdBits) b) :: acc) (i + 1) ts) :
    ∀ (ts : List ℕ) (i : ℕ), i + ts.length = R.length →
      (∀ k (hk : k < ts.length), ts[k] / 24 < i + k ∧ R.getD (i + k) [] =
        (R.getD (ts[k] / 24) []).map (ggHalfApplyBits (gens.getD (ts[k] % 24) ggHalfIdBits))) →
      f (R.take i).reverse i ts = R
  | [], i, hl, _ => by
    rw [h0, List.reverse_reverse, List.take_of_length_le (by simp at hl; omega)]
  | t :: ts, i, hl, hs => by
    obtain ⟨hp, he⟩ := hs 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hp he
    have hlen : i < R.length := by simp at hl; omega
    rw [h1, getD_reverse_take R hp (by omega), ← he, ← reverse_take_succ R hlen]
    refine aux_eq gens R f h0 h1 ts (i + 1) (by simp at hl; omega) fun k hk => ?_
    have := hs (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    have e : i + 1 + k = i + (k + 1) := by omega
    rw [e]
    exact this

theorem subBases_eq (gens : List (List ℕ)) (G B n : ℕ) (W0 ts : List ℕ)
    (f : List (List ℕ) → ℕ → List ℕ → List (List ℕ))
    (h0 : ∀ acc i, f acc i [] = acc.reverse)
    (h1 : ∀ acc i t ts, f acc i (t :: ts) =
      f ((acc.getD (i - 1 - t / 24) []).map
        (fun b => ggHalfApplyBits (gens.getD (t % 24) ggHalfIdBits) b) :: acc) (i + 1) ts)
    (hG : gens = (List.range 24).map (gK G)) (hn : ts.length + 1 = n) (hW : rbK B 0 = W0)
    (hs : stepsK G B ts 1 = true) : f [W0] 1 ts = (List.range n).map (rbK B) := by
  have hR : ∀ k < n, ((List.range n).map (rbK B)).getD k [] = rbK B k := fun k hk => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    rfl
  have hg : ∀ t, gens.getD (t % 24) ggHalfIdBits = gK G (t % 24) := fun t => by
    rw [hG, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Nat.mod_lt _ (by omega))]
    rfl
  have hW' : [W0] = (((List.range n).map (rbK B)).take 1).reverse := by
    rw [← hn, List.range_succ_eq_map, List.map_cons, List.take_succ_cons, List.take_zero, hW]
    rfl
  rw [hW']
  refine aux_eq gens _ f h0 h1 ts 1 (by simp; omega) fun k hk => ?_
  obtain ⟨hp, he⟩ := stepsK_spec G B ts 1 hs k hk
  refine ⟨hp, ?_⟩
  rw [hR _ (by omega), hR _ (by omega), hg, he]

end CFSG.StandardType.GGHalfX0K
