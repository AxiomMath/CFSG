module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSet

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Orbit

variable {τ : Tag} {S : TcrSys}

theorem tcrMaskOf_eq_of_iff (n : ℕ) (a b : List ℕ) (h : ∀ i < n, (i ∈ a ↔ i ∈ b)) :
    tcrMaskOf n a = tcrMaskOf n b := by
  apply Array.ext
  · rw [tcrMaskOf_size, tcrMaskOf_size]
  · intro i h1 h2
    have hin : i < n := by simpa only [tcrMaskOf_size] using h1
    rw [← getElem!_pos (tcrMaskOf n a) i h1, ← getElem!_pos (tcrMaskOf n b) i h2,
      Bool.eq_iff_iff, tcrMaskOf_getElem!, tcrMaskOf_getElem!]
    exact ⟨fun ⟨_, h3⟩ => ⟨hin, (h i hin).1 h3⟩, fun ⟨_, h3⟩ => ⟨hin, (h i hin).2 h3⟩⟩

theorem tcrPermPows_key (S : TcrSys) (perm : Array ℕ)
    (F : Array (Array ℕ) → ℕ → Array (Array ℕ))
    (hF : ∀ acc m, F acc m =
      acc.push (Array.ofFn (n := S.tcrN) fun i => perm[(acc.back!)[i.val]!]!))
    (init : Array (Array ℕ)) (hinit : init = #[Array.ofFn (n := S.tcrN) fun i => i.val]) :
    ∀ m : ℕ, ((List.range m).foldl F init).size = m + 1 ∧
      ∀ e ≤ m, ((List.range m).foldl F init)[e]!.size = S.tcrN ∧
        ∀ i < S.tcrN, (((List.range m).foldl F init)[e]!)[i]! = (fun j => perm[j]!)^[e] i := by
  intro m
  induction m with
  | zero =>
    subst hinit
    simp only [List.range_zero, List.foldl_nil]
    refine ⟨by simp, fun e he => ?_⟩
    obtain rfl : e = 0 := by omega
    refine ⟨by simp, fun i hi => ?_⟩
    simp [hi]
  | succ m ih =>
    obtain ⟨hs, hr⟩ := ih
    rw [tc_foldl_range_succ, hF]
    set A := (List.range m).foldl F init with hA
    have hback : A.back! = A[m]! := by
      unfold Array.back!
      rw [hs, Nat.add_sub_cancel]
    rw [hback]
    set x : Array ℕ := Array.ofFn (n := S.tcrN) fun i => perm[(A[m]!)[i.val]!]! with hx
    have hxval : ∀ i < S.tcrN, x[i]! = perm[(A[m]!)[i]!]! := by
      intro i hi
      simp [hx, hi]
    refine ⟨by rw [Array.size_push, hs], fun e he => ?_⟩
    rcases Nat.lt_or_ge e (m + 1) with hlt | hge
    · have he' : e ≤ m := by omega
      have hel : e < A.size := by rw [hs]; omega
      have hpush : e < (A.push x).size := by rw [Array.size_push]; omega
      rw [getElem!_pos (A.push x) e hpush, Array.getElem_push_lt hel, ← getElem!_pos A e hel]
      exact hr e he'
    · obtain rfl : e = m + 1 := by omega
      have hpush : m + 1 < (A.push x).size := by rw [Array.size_push, hs]; omega
      have hx1 : (A.push x)[m + 1]! = x := by
        rw [getElem!_pos (A.push x) (m + 1) hpush, Array.getElem_push hpush,
          dif_neg (show ¬ (m + 1 < A.size) by rw [hs]; omega)]
      rw [hx1]
      refine ⟨by rw [hx]; exact Array.size_ofFn, fun i hi => ?_⟩
      rw [hxval i hi, (hr m le_rfl).2 i hi, Function.iterate_succ_apply']

theorem tcrPermPows_spec (S : TcrSys) (perm : Array ℕ) (_hp : ∀ i < S.tcrN, perm[i]! < S.tcrN) :
    ∀ e ≤ 24, ((tcrPermPows S perm)[e]!).size = S.tcrN ∧
      ∀ i < S.tcrN, ((tcrPermPows S perm)[e]!)[i]! = (fun j => perm[j]!)^[e] i := by
  intro e he
  unfold tcrPermPows
  exact (tcrPermPows_key S perm
    (fun (acc : Array (Array ℕ)) (_ : ℕ) =>
      let q := acc.back!
      acc.push (Array.ofFn (n := S.tcrN) fun i => perm[q[i.val]!]!))
    (fun _ _ => rfl) #[Array.ofFn (n := S.tcrN) fun i => i.val] rfl 24).2 e he

theorem tcrSet_imgSet (hG : TcrGood τ S) (φ : AddMonoid.End (Fin τ.rank → ℤ))
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ) (perm : Array ℕ)
    (hperm : ∀ i < S.tcrN, perm[i]! < S.tcrN ∧ tcrRv S τ perm[i]! = φ (tcrRv S τ i))
    (cs : List ℕ) (hcs : ∀ c ∈ cs, c < S.tcrN) :
    tcrSet S τ (tcrImgSet perm cs) = ρ '' tcrSet S τ cs := by
  ext γ
  constructor
  · rintro ⟨j, hj, hjN, rfl⟩
    have hj' : j ∈ List.map (fun i => perm[i]!) cs := hj
    obtain ⟨i, hi, hij⟩ := List.mem_map.1 hj'
    have hij' : perm[i]! = j := hij
    subst hij'
    refine ⟨tcrRv S τ i, ⟨i, hi, hcs i hi, rfl⟩, ?_⟩
    rw [hρ _ (hG.rv_spec (hcs i hi)).1, (hperm i (hcs i hi)).2]
  · rintro ⟨δ, ⟨i, hi, hiN, rfl⟩, rfl⟩
    refine ⟨perm[i]!, List.mem_map.2 ⟨i, hi, rfl⟩, (hperm i hiN).1, ?_⟩
    rw [hρ _ (hG.rv_spec hiN).1, (hperm i hiN).2]

theorem tcrSet_eq_of_mask_eq (_hG : TcrGood τ S) (a b : List ℕ) (_ha : ∀ c ∈ a, c < S.tcrN)
    (_hb : ∀ c ∈ b, c < S.tcrN) (h : tcrMaskOf S.tcrN a = tcrMaskOf S.tcrN b) :
    tcrSet S τ a = tcrSet S τ b := by
  have key : ∀ i < S.tcrN, (i ∈ a ↔ i ∈ b) := by
    intro i hi
    have h1 : (tcrMaskOf S.tcrN a)[i]! = true ↔ (tcrMaskOf S.tcrN b)[i]! = true := by
      rw [h]
    rw [tcrMaskOf_getElem!, tcrMaskOf_getElem!] at h1
    exact ⟨fun h2 => (h1.1 ⟨hi, h2⟩).2, fun h2 => (h1.2 ⟨hi, h2⟩).2⟩
  ext γ
  constructor
  · rintro ⟨i, hi, hiN, rfl⟩
    exact ⟨i, (key i hiN).1 hi, hiN, rfl⟩
  · rintro ⟨i, hi, hiN, rfl⟩
    exact ⟨i, (key i hiN).2 hi, hiN, rfl⟩

theorem tcrMask_eq_of_tcrSet_eq (hG : TcrGood τ S) (a b : List ℕ) (_ha : ∀ c ∈ a, c < S.tcrN)
    (_hb : ∀ c ∈ b, c < S.tcrN) (h : tcrSet S τ a = tcrSet S τ b) :
    tcrMaskOf S.tcrN a = tcrMaskOf S.tcrN b := by
  apply tcrMaskOf_eq_of_iff
  have sub : ∀ c d : List ℕ, tcrSet S τ c = tcrSet S τ d → ∀ i < S.tcrN, i ∈ c → i ∈ d := by
    intro c d hcd i hi hic
    have hmem : tcrRv S τ i ∈ tcrSet S τ c := ⟨i, hic, hi, rfl⟩
    rw [hcd] at hmem
    obtain ⟨j, hjd, hjN, hj⟩ := hmem
    have hji : j = i := hG.rv_inj hjN hi hj
    rw [← hji]
    exact hjd
  intro i hi
  exact ⟨sub a b h i hi, sub b a h.symm i hi⟩

theorem tcrIter_spec (hG : TcrGood τ S) (φ : AddMonoid.End (Fin τ.rank → ℤ))
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ) (perm : Array ℕ)
    (hperm : ∀ i < S.tcrN, perm[i]! < S.tcrN ∧ tcrRv S τ perm[i]! = φ (tcrRv S τ i))
    (cs : List ℕ) (hcs : ∀ c ∈ cs, c < S.tcrN) (s : ℕ) :
    (∀ c ∈ (tcrImgSet perm)^[s] cs, c < S.tcrN) ∧
      tcrSet S τ ((tcrImgSet perm)^[s] cs) = (⇑ρ)^[s] '' tcrSet S τ cs := by
  induction s with
  | zero => exact ⟨hcs, by simp⟩
  | succ s ih =>
    obtain ⟨hb, hs⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ']
    refine ⟨?_, ?_⟩
    · intro c hc
      have hc' : c ∈ List.map (fun i => perm[i]!) ((tcrImgSet perm)^[s] cs) := hc
      obtain ⟨d, hd, hdc⟩ := List.mem_map.1 hc'
      have hdc' : perm[d]! = c := hdc
      rw [← hdc']
      exact (hperm d (hb d hd)).1
    · rw [tcrSet_imgSet hG φ ρ hρ perm hperm _ hb, hs, Set.image_comp]

theorem tcrPer_iff (hG : TcrGood τ S) (φ : AddMonoid.End (Fin τ.rank → ℤ))
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ) (perm : Array ℕ)
    (hperm : ∀ i < S.tcrN, perm[i]! < S.tcrN ∧ tcrRv S τ perm[i]! = φ (tcrRv S τ i))
    (cs : List ℕ) (hcs : ∀ c ∈ cs, c < S.tcrN) (s : ℕ) :
    (⇑ρ)^[s] '' tcrSet S τ cs = tcrSet S τ cs ↔
      tcrMaskOf S.tcrN ((tcrImgSet perm)^[s] cs) = tcrMaskOf S.tcrN cs := by
  obtain ⟨hb, hs⟩ := tcrIter_spec hG φ ρ hρ perm hperm cs hcs s
  constructor
  · intro h
    exact tcrMask_eq_of_tcrSet_eq hG _ _ hb hcs (hs.trans h)
  · intro h
    rw [← hs]
    exact tcrSet_eq_of_mask_eq hG _ _ hb hcs h

theorem tcrGo_spec (N : ℕ) (perm : Array ℕ) (cs : List ℕ) (m : Array Bool) (k : ℕ) :
    ∀ t e, tcrOrbitLen.go N perm m k (t + 1) ((tcrImgSet perm)^[t] cs) = e →
      (e = 0 ∧ ∀ j, t + 1 ≤ j → j ≤ t + k → tcrMaskOf N ((tcrImgSet perm)^[j] cs) ≠ m) ∨
      (t + 1 ≤ e ∧ e ≤ t + k ∧ tcrMaskOf N ((tcrImgSet perm)^[e] cs) = m ∧
        ∀ j, t + 1 ≤ j → j < e → tcrMaskOf N ((tcrImgSet perm)^[j] cs) ≠ m) := by
  induction k with
  | zero =>
    intro t e he
    rw [tcrOrbitLen.go.eq_1] at he
    exact Or.inl ⟨he.symm, fun j h1 h2 => absurd h2 (by omega)⟩
  | succ k ih =>
    intro t e he
    rw [tcrOrbitLen.go.eq_2, ← Function.iterate_succ_apply' (tcrImgSet perm) t cs] at he
    split_ifs at he with hc
    · have hP : tcrMaskOf N ((tcrImgSet perm)^[t + 1] cs) = m := beq_iff_eq.1 hc
      subst he
      exact Or.inr ⟨by omega, by omega, hP, fun j h1 h2 => absurd h2 (by omega)⟩
    · have hP : ¬ tcrMaskOf N ((tcrImgSet perm)^[t + 1] cs) = m :=
        fun h => hc (beq_iff_eq.2 h)
      rcases ih (t + 1) e he with ⟨h0, hrest⟩ | ⟨h1, h2, h3, h4⟩
      · refine Or.inl ⟨h0, fun j hj1 hj2 => ?_⟩
        rcases Nat.lt_or_ge j (t + 2) with hlt | hge
        · obtain rfl : j = t + 1 := by omega
          exact hP
        · exact hrest j (by omega) (by omega)
      · refine Or.inr ⟨by omega, by omega, h3, fun j hj1 hj2 => ?_⟩
        rcases Nat.lt_or_ge j (t + 2) with hlt | hge
        · obtain rfl : j = t + 1 := by omega
          exact hP
        · exact h4 j (by omega) hj2

theorem tcrOrbitLen_spec (hG : TcrGood τ S) (φ : AddMonoid.End (Fin τ.rank → ℤ))
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : ∀ γ, IsRoot τ γ → ρ γ = φ γ) (perm : Array ℕ)
    (hperm : ∀ i < S.tcrN, perm[i]! < S.tcrN ∧ tcrRv S τ perm[i]! = φ (tcrRv S τ i))
    (cs : List ℕ) (hcs : ∀ c ∈ cs, c < S.tcrN) {e : ℕ}
    (he : tcrOrbitLen S.tcrN perm cs S.tcrN = e) (hne : e ≠ 0) :
    componentOrbitLength ρ (tcrSet S τ cs) = e := by
  have hgo : tcrOrbitLen.go S.tcrN perm (tcrMaskOf S.tcrN cs) S.tcrN (0 + 1)
      ((tcrImgSet perm)^[0] cs) = e := he
  rcases tcrGo_spec S.tcrN perm cs (tcrMaskOf S.tcrN cs) S.tcrN 0 e hgo with
    ⟨h0, -⟩ | ⟨h1, h2, h3, h4⟩
  · exact absurd h0 hne
  have hA : e ∈ {s : ℕ | 0 < s ∧ (⇑ρ)^[s] '' tcrSet S τ cs = tcrSet S τ cs} :=
    ⟨by omega, (tcrPer_iff hG φ ρ hρ perm hperm cs hcs e).2 h3⟩
  have hmin : ∀ s ∈ {s : ℕ | 0 < s ∧ (⇑ρ)^[s] '' tcrSet S τ cs = tcrSet S τ cs}, e ≤ s := by
    rintro s ⟨hs0, hs⟩
    by_contra hlt
    exact h4 s (by omega) (by omega) ((tcrPer_iff hG φ ρ hρ perm hperm cs hcs s).1 hs)
  unfold componentOrbitLength
  exact le_antisymm (Nat.sInf_le hA) (hmin _ (Nat.sInf_mem ⟨e, hA⟩))

end Orbit

end CFSG.StandardType.TableCRes

end
