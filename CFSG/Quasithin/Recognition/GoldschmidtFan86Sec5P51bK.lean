module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PTrans
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Line

theorem valence_add_two_nat (F : FanTree Γ G) (ℓ : Line Γ) (i : ℤ) (k : ℕ) :
    valence Γ (ℓ.vert (i + 2 * k)) = valence Γ (ℓ.vert i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := ℓ.valence_add_two F (i + 2 * k)
    rw [show i + 2 * k + 2 = i + 2 * ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
    rw [this, ih]

end Line

theorem fan51b_loc (F : FanTree Γ G) (h40 : Fan40 F) (h36 : Fan36 F) (ℓ : Line Γ) (a : ℤ) (n : ℕ)
    (hn : 3 ≤ n) (hs : ¬ LineSingLe Γ G ℓ (n - 1))
    (hexc : ¬ (n = 4 ∧ LineSingLe Γ G ℓ 4 ∧ valence Γ (ℓ.vert a) = 3 ∧
      valence Γ (ℓ.vert (a + n)) = 3)) :
    ∀ v, LocTr Γ (Subgroup.closure ((nbrStab Γ G (ℓ.vert a) : Set G) ∪
      nbrStab Γ G (ℓ.vert (a + n)))) v := by
  set L : Subgroup G :=
    Subgroup.closure ((nbrStab Γ G (ℓ.vert a) : Set G) ∪ nbrStab Γ G (ℓ.vert (a + n))) with hL
  have hKa : ∀ g ∈ nbrStab Γ G (ℓ.vert a), g ∈ L := fun g hg =>
    Subgroup.subset_closure (Or.inl hg)
  have hKn : ∀ g ∈ nbrStab Γ G (ℓ.vert (a + n)), g ∈ L := fun g hg =>
    Subgroup.subset_closure (Or.inr hg)
  have nsr : ∀ k : ℕ, 1 ≤ k → (k ≤ 3 ∨ k + 1 ≤ n) → LineNSR Γ G ℓ k := by
    intro k hk1 hk
    rcases hk with hk | hk
    · exact lineNSR_of_fan40 h40 ℓ hk1 hk
    · exact lineNSR_of_not hs hk1 (by omega)
  have nsl : ∀ k : ℕ, 1 ≤ k → (k ≤ 3 ∨ k + 1 ≤ n) → LineNSL Γ G ℓ k := by
    intro k hk1 hk
    rcases hk with hk | hk
    · exact lineNSL_of_fan40 h40 ℓ hk1 hk
    · exact lineNSL_of_not hs hk1 (by omega)
  have fixL : ∀ w : ℤ, a + 1 ≤ w → ((w - a + 1).toNat ≤ 3 ∨ (w - a + 1).toNat + 1 ≤ n) →
      ∃ g ∈ L, g • ℓ.vert (w - 1) = ℓ.vert (w - 1) ∧ g • ℓ.vert w = ℓ.vert w ∧
        g • ℓ.vert (w + 1) ≠ ℓ.vert (w + 1) := by
    intro w hw hk
    exact ℓ.exists_fixer_right_mem F hKa hw (i := a - 1) (K := (w - a + 1).toNat) (j := 0)
      (k := (w - a + 1).toNat) (by simp) (by omega) (nsr _ (by omega) hk (a - 1))
  have fixR : ∀ w : ℤ, w + 1 ≤ a + n → ((a + n + 1 - w).toNat ≤ 3 ∨
      (a + n + 1 - w).toNat + 1 ≤ n) →
      ∃ g ∈ L, g • ℓ.vert w = ℓ.vert w ∧ g • ℓ.vert (w + 1) = ℓ.vert (w + 1) ∧
        g • ℓ.vert (w - 1) ≠ ℓ.vert (w - 1) := by
    intro w hw hk
    exact ℓ.exists_fixer_left_mem F hKn hw (i := w) (K := (a + n + 1 - w).toNat) (j := 0)
      (k := (a + n + 1 - w).toNat) (by simp) (by omega) (nsl _ (by omega) hk w)
  by_cases h5 : 5 ≤ n
  · have e2 : LocTr Γ L (ℓ.vert (a + 2)) := F.locTr_of_fixers ℓ (w := a + 2)
      (fixL (a + 2) (by omega) (by omega)) (fixR (a + 2) (by omega) (by omega))
    have e3 : LocTr Γ L (ℓ.vert (a + 2 + 1)) := F.locTr_of_fixers ℓ (w := a + 2 + 1)
      (fixL _ (by omega) (by omega)) (fixR _ (by omega) (by omega))
    exact F.locTr_all (ℓ.adj (a + 2)) e2 e3
  by_cases h3 : n = 3
  · have e1 : LocTr Γ L (ℓ.vert (a + 1)) := F.locTr_of_fixers ℓ (w := a + 1)
      (fixL (a + 1) (by omega) (by omega)) (fixR (a + 1) (by omega) (by omega))
    have e2 : LocTr Γ L (ℓ.vert (a + 1 + 1)) := F.locTr_of_fixers ℓ (w := a + 1 + 1)
      (fixL _ (by omega) (by omega)) (fixR _ (by omega) (by omega))
    exact F.locTr_all (ℓ.adj (a + 1)) e1 e2
  have h4 : n = 4 := by omega
  have hv4 : valence Γ (ℓ.vert (a + n)) = valence Γ (ℓ.vert a) := by
    have := ℓ.valence_add_two_nat F a 2
    rw [show a + 2 * ((2 : ℕ) : ℤ) = a + n by omega] at this
    exact this
  have hfix : (∀ w : ℤ, w = a + 3 → ∃ g ∈ L, g • ℓ.vert (w - 1) = ℓ.vert (w - 1) ∧
        g • ℓ.vert w = ℓ.vert w ∧ g • ℓ.vert (w + 1) ≠ ℓ.vert (w + 1)) ∨
      (∀ w : ℤ, w = a + 1 → ∃ g ∈ L, g • ℓ.vert w = ℓ.vert w ∧
        g • ℓ.vert (w + 1) = ℓ.vert (w + 1) ∧ g • ℓ.vert (w - 1) ≠ ℓ.vert (w - 1)) := by
    by_cases hL4 : LineSingLe Γ G ℓ 4
    · have hp5 : valence Γ (ℓ.vert a) ≠ 3 := fun h3' =>
        hexc ⟨h4, hL4, h3', hv4.trans h3'⟩
      have hP : valence Γ ((ℓ.arc (a - 1) 6).vert 1) ≠ 3 := by
        have : (ℓ.arc (a - 1) 6).vert 1 = ℓ.vert a := by
          simp only [Line.arc]
          congr 1
          push_cast
          omega
        rw [this]
        exact hp5
      have h36' := (h36 h40 (ℓ.arc (a - 1) 6) hP).2.2
      by_cases hR : RightSingular Γ G (ℓ.arc (a - 1) 6).vert 0 4
      · refine Or.inr fun w hw => ?_
        subst hw
        exact ℓ.exists_fixer_left_mem F hKn (by omega) (i := a - 1) (K := 6) (j := 2)
          (k := 6) (by omega) (by omega) fun hL => h36' ⟨hL, hR⟩
      · refine Or.inl fun w hw => ?_
        subst hw
        exact ℓ.exists_fixer_right_mem F hKa (by omega) (i := a - 1) (K := 6) (j := 0)
          (k := 4) (by omega) (by omega) hR
    · refine Or.inl fun w hw => ?_
      subst hw
      exact ℓ.exists_fixer_right_mem F hKa (by omega) (i := a - 1) (K := 4) (j := 0)
        (k := 4) (by omega) (by omega) (lineNSR_of_not hL4 (by norm_num) le_rfl (a - 1))
  rcases hfix with hf | hf
  · have e2 : LocTr Γ L (ℓ.vert (a + 2)) := F.locTr_of_fixers ℓ (w := a + 2)
      (fixL (a + 2) (by omega) (by omega)) (fixR (a + 2) (by omega) (by omega))
    have e3 : LocTr Γ L (ℓ.vert (a + 2 + 1)) := F.locTr_of_fixers ℓ (w := a + 2 + 1)
      (hf _ (by omega)) (fixR _ (by omega) (by omega))
    exact F.locTr_all (ℓ.adj (a + 2)) e2 e3
  · have e1 : LocTr Γ L (ℓ.vert (a + 1)) := F.locTr_of_fixers ℓ (w := a + 1)
      (fixL (a + 1) (by omega) (by omega)) (hf _ rfl)
    have e2 : LocTr Γ L (ℓ.vert (a + 1 + 1)) := F.locTr_of_fixers ℓ (w := a + 1 + 1)
      (fixL _ (by omega) (by omega)) (fixR _ (by omega) (by omega))
    exact F.locTr_all (ℓ.adj (a + 1)) e1 e2

end CFSG.Quasithin.Fan86
