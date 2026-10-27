module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideWit
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExcRefl
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideGrow

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {T : Chk.Tabs}

@[expose] def PairSigned (m : Fin 6) (σ : Root m → Root m) : Prop :=
  ∃ ε : Root m → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ i j, pairing m (σ i) (σ j) = ε i * ε j * pairing m i j

@[expose] def imgW (T : Chk.Tabs) (m : Fin 6) (w : List (Root m)) (c : ℕ) : ℕ :=
  w.foldr (fun u acc => Chk.imgN T (nroots m) u acc) c

@[expose] def FlagE6 (m : Fin 6) (c : Finset (Root m)) : Prop :=
  (m.val = 2 ∨ m.val = 3) ∧
    (c = Finset.univ ∨ ∃ k, c = Finset.univ.filter fun i => pairing m k i = 0 ∧ pairing m i k = 0)

@[expose] def InsideT (m : Fin 6) (c : Finset (Root m)) : Prop :=
  Nonempty (SatWitness m c) ∨ FlagE6 m c

theorem InsideT.census {c : Finset (Root m)} (h : InsideT m c) :
    Nonempty (SatWitness m c) ∨ InsideFlag m c := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

private theorem sign_mul_self {ε : ℤ} (h : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases h with rfl | rfl <;> norm_num

noncomputable def SatWitness.map {c : Finset (Root m)} (σ : Root m ≃ Root m) {ε : Root m → ℤ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hp : ∀ i j, pairing m (σ i) (σ j) = ε i * ε j * pairing m i j) (W : SatWitness m c) :
    SatWitness m (c.map σ.toEmbedding) where
  r := W.r
  b a := σ (W.b a)
  k a := σ (W.k a)
  e := W.e
  n i a := ε (σ.symm i) * ε (W.b a) * W.n (σ.symm i) a
  A a a'' := ε (W.b a) * ε (W.k a'') * W.A a a''
  D := W.D
  b_mem a := Finset.mem_map_of_mem _ (W.b_mem a)
  pairing_eq := by
    intro i hi j
    rw [Finset.mem_map_equiv] at hi
    have hi' : σ (σ.symm i) = i := σ.apply_symm_apply i
    have hj' : σ (σ.symm j) = j := σ.apply_symm_apply j
    set i0 := σ.symm i
    set j0 := σ.symm j
    rw [← hi', ← hj', hp j0 i0]
    have hterm : ∀ a, ε i0 * ε (W.b a) * W.n i0 a * pairing m (σ j0) (σ (W.b a)) =
        ε j0 * ε i0 * (W.n i0 a * pairing m j0 (W.b a)) := by
      intro a
      rw [hp j0 (W.b a)]
      linear_combination (ε i0 * ε j0 * W.n i0 a * pairing m j0 (W.b a)) *
        sign_mul_self (hε (W.b a))
    rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum, ← W.pairing_eq i0 hi j0]
    ring
  mul_eq := by
    intro a a'
    have hterm : ∀ a'', ε (W.b a) * ε (W.k a'') * W.A a a'' * pairing m (σ (W.k a'')) (σ (W.b a')) =
        ε (W.b a) * ε (W.b a') * (W.A a a'' * pairing m (W.k a'') (W.b a')) := by
      intro a''
      rw [hp (W.k a'') (W.b a')]
      linear_combination (ε (W.b a) * ε (W.b a') * W.A a a'' * pairing m (W.k a'') (W.b a')) *
        sign_mul_self (hε (W.k a''))
    rw [Finset.sum_congr rfl fun a'' _ => hterm a'', ← Finset.mul_sum, W.mul_eq a a']
    split_ifs with h
    · subst h
      rw [sign_mul_self (hε (W.b a)), one_mul]
    · rw [mul_zero]
  not_three_dvd_e := W.not_three_dvd_e
  not_three_dvd_D := W.not_three_dvd_D

theorem satWitness_reflCode (hT : Chk.tabsOK m T = true) {u : Root m} (hp : PairSigned m (rtR hT u))
    {c : Finset (Root m)} (h : Nonempty (SatWitness m c)) :
    Nonempty (SatWitness m (reflCode hT u c)) := by
  obtain ⟨ε, hε, hp⟩ := hp
  obtain ⟨W⟩ := h
  exact ⟨W.map (rtE hT u) hε hp⟩

private theorem flagE6_map {c : Finset (Root m)} (σ : Root m ≃ Root m)
    (hz : ∀ a b, pairing m (σ a) (σ b) = 0 ↔ pairing m a b = 0) (h : FlagE6 m c) :
    FlagE6 m (c.map σ.toEmbedding) := by
  obtain ⟨hm, rfl | ⟨k, rfl⟩⟩ := h
  · exact ⟨hm, Or.inl (Finset.map_univ_equiv σ)⟩
  · refine ⟨hm, Or.inr ⟨σ k, ?_⟩⟩
    ext i
    rw [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_filter, ← hz k, ← hz (σ.symm i),
      σ.apply_symm_apply]
    simp only [Finset.mem_univ, true_and]

theorem flagE6_reflCode (hT : Chk.tabsOK m T = true) (u : Root m) {c : Finset (Root m)}
    (h : FlagE6 m c) : FlagE6 m (reflCode hT u c) :=
  flagE6_map (rtE hT u) (pairing_rtR_eq_zero_iff hT u) h

theorem insideT_reflCode (hT : Chk.tabsOK m T = true) {u : Root m} (hp : PairSigned m (rtR hT u))
    {c : Finset (Root m)} (h : InsideT m c) : InsideT m (reflCode hT u c) := by
  rcases h with h | h
  · exact Or.inl (satWitness_reflCode hT hp h)
  · exact Or.inr (flagE6_reflCode hT u h)

theorem ofMask_imgN (hT : Chk.tabsOK m T = true) (u : Root m) (c : ℕ) :
    ofMask m (Chk.imgN T (nroots m) u c) = reflCode hT u (ofMask m c) := by
  ext t
  rw [mem_ofMask_imgN, reflCode_apply, Finset.mem_map_equiv]
  constructor
  · rintro ⟨s, hs, hst⟩
    have h1 : rtE hT u s = t := Fin.ext hst
    rw [← h1, Equiv.symm_apply_apply]
    exact hs
  · intro ht
    exact ⟨(rtE hT u).symm t, ht, congrArg Fin.val ((rtE hT u).apply_symm_apply t)⟩

theorem insideT_imgN (hT : Chk.tabsOK m T = true) {u : Root m} (hp : PairSigned m (rtR hT u))
    {n : ℕ} (h : InsideT m (ofMask m n)) : InsideT m (ofMask m (Chk.imgN T (nroots m) u n)) := by
  rw [ofMask_imgN hT]
  exact insideT_reflCode hT hp h

end CFSG.StandardType.GGQ2Frame.ExcRaw
