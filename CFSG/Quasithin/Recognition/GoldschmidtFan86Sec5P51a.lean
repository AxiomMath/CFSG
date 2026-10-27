module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PTrans
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Line

theorem exists_five_end (F : FanTree Γ G) (ℓ : Line Γ) (i : ℤ) :
    ∃ j : ℤ, (j = i ∨ j = i + 1) ∧ valence Γ (ℓ.vert j) = 5 := by
  have hval : ∀ v, valence Γ v = 3 ∨ valence Γ v = 5 := fun v => F.valence v
  have h3 : valence Γ (ℓ.vert i) ≠ valence Γ (ℓ.vert (i + 1)) := F.alternating _ _ (ℓ.adj i)
  have h1 := hval (ℓ.vert i)
  have h2 := hval (ℓ.vert (i + 1))
  by_cases h : valence Γ (ℓ.vert i) = 5
  · exact ⟨i, Or.inl rfl, h⟩
  · exact ⟨i + 1, Or.inr rfl, by omega⟩

end Line

theorem fan51a (F : FanTree Γ G) (h36 : Fan36 F) : Fan51a F := by
  intro h40 ℓ a n hn hs d hd1 hd2
  have hval : ∀ v, valence Γ v = 3 ∨ valence Γ v = 5 := fun v => F.valence v
  have hb : a + ((n - 1 : ℕ) : ℤ) = a + n - 1 := by omega
  rw [hb]
  set H : Subgroup G :=
    Subgroup.closure (ℓ.edgeCirc (G := G) a ∪ ℓ.edgeCirc (G := G) (a + n - 1)) with hH
  suffices key : LocTr Γ H (ℓ.vert (a + d)) from F.exists_orderOf_of_locTr key
  obtain ⟨u, hu, hu5⟩ := ℓ.exists_five_end F a
  have hKu : ∀ g ∈ nbrStab Γ G (ℓ.vert u), g ∈ H := fun g hg =>
    Subgroup.subset_closure (Or.inl (ℓ.nbrStab_subset_edgeCirc F hu hu5 hg))
  obtain ⟨v, hv, hv5⟩ := ℓ.exists_five_end F (a + n - 1)
  have hKv : ∀ g ∈ nbrStab Γ G (ℓ.vert v), g ∈ H := fun g hg =>
    Subgroup.subset_closure (Or.inr (ℓ.nbrStab_subset_edgeCirc F hv hv5 hg))
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
  have fixL : ∀ w : ℤ, u + 1 ≤ w → ((w - u + 1).toNat ≤ 3 ∨ (w - u + 1).toNat + 1 ≤ n) →
      ∃ g ∈ H, g • ℓ.vert (w - 1) = ℓ.vert (w - 1) ∧ g • ℓ.vert w = ℓ.vert w ∧
        g • ℓ.vert (w + 1) ≠ ℓ.vert (w + 1) := by
    intro w hw hk
    exact ℓ.exists_fixer_right_mem F hKu hw (i := u - 1) (K := (w - u + 1).toNat) (j := 0)
      (k := (w - u + 1).toNat) (by simp) (by omega) (nsr _ (by omega) hk (u - 1))
  have fixR : ∀ w : ℤ, w + 1 ≤ v → ((v + 1 - w).toNat ≤ 3 ∨ (v + 1 - w).toNat + 1 ≤ n) →
      ∃ g ∈ H, g • ℓ.vert w = ℓ.vert w ∧ g • ℓ.vert (w + 1) = ℓ.vert (w + 1) ∧
        g • ℓ.vert (w - 1) ≠ ℓ.vert (w - 1) := by
    intro w hw hk
    exact ℓ.exists_fixer_left_mem F hKv hw (i := w) (K := (v + 1 - w).toNat) (j := 0)
      (k := (v + 1 - w).toNat) (by simp) (by omega) (nsl _ (by omega) hk w)
  have hL0 : ∀ w : ℤ, w = a + 1 → ∃ g ∈ H, g • ℓ.vert (w - 1) = ℓ.vert (w - 1) ∧
      g • ℓ.vert w = ℓ.vert w ∧ g • ℓ.vert (w + 1) ≠ ℓ.vert (w + 1) := by
    intro w hw
    obtain ⟨g, hg, hgK⟩ := (Line.exists_edgeCirc_not_mem F h40 ℓ a).2
    obtain ⟨h1, h2⟩ := ℓ.edgeCirc_fix hg
    subst hw
    refine ⟨g, Subgroup.subset_closure (Or.inl hg), by rwa [add_sub_cancel_right], h2,
      fun h3 => hgK ?_⟩
    exact ℓ.mem_nbrStab_of_fix F (by rwa [add_sub_cancel_right]) h2 h3
  have hR0 : ∀ w : ℤ, w = a + n - 1 → ∃ g ∈ H, g • ℓ.vert w = ℓ.vert w ∧
      g • ℓ.vert (w + 1) = ℓ.vert (w + 1) ∧ g • ℓ.vert (w - 1) ≠ ℓ.vert (w - 1) := by
    intro w hw
    obtain ⟨g, hg, hgK⟩ := (Line.exists_edgeCirc_not_mem F h40 ℓ (a + n - 1)).1
    obtain ⟨h1, h2⟩ := ℓ.edgeCirc_fix hg
    subst hw
    refine ⟨g, Subgroup.subset_closure (Or.inr hg), h1, h2, fun h3 => hgK ?_⟩
    exact ℓ.mem_nbrStab_of_fix F h3 h1 h2
  by_cases h2 : n = 2
  ·
    have hd : d = 1 := by omega
    subst hd
    have := F.locTr_of_fixers ℓ (w := a + 1) (hL0 _ rfl) (hR0 _ (by omega))
    simpa using this
  by_cases h5 : 5 ≤ n
  ·
    have e2 : LocTr Γ H (ℓ.vert (a + 2)) := F.locTr_of_fixers ℓ (w := a + 2)
      (fixL (a + 2) (by omega) (by omega)) (fixR (a + 2) (by omega) (by omega))
    have e3 : LocTr Γ H (ℓ.vert (a + 2 + 1)) := F.locTr_of_fixers ℓ (w := a + 2 + 1)
      (fixL _ (by omega) (by omega)) (fixR _ (by omega) (by omega))
    exact F.locTr_all (ℓ.adj (a + 2)) e2 e3 _
  by_cases h3 : n = 3
  ·
    have e1 : LocTr Γ H (ℓ.vert (a + 1)) := F.locTr_of_fixers ℓ (w := a + 1)
      (hL0 _ rfl) (fixR (a + 1) (by omega) (by omega))
    have e2 : LocTr Γ H (ℓ.vert (a + 1 + 1)) := F.locTr_of_fixers ℓ (w := a + 1 + 1)
      (fixL _ (by omega) (by omega)) (hR0 _ (by omega))
    exact F.locTr_all (ℓ.adj (a + 1)) e1 e2 _
  have h4 : n = 4 := by omega
  have halt : ∀ i : ℤ, valence Γ (ℓ.vert i) ≠ valence Γ (ℓ.vert (i + 1)) := fun i =>
    F.alternating _ _ (ℓ.adj i)
  have v2 := ℓ.valence_add_two F a
  have v3 := ℓ.valence_add_two F (a + 1)
  have v4 := ℓ.valence_add_two F (a + 2)
  rw [show a + 1 + 2 = a + 3 by omega] at v3
  rw [show a + 2 + 2 = a + 4 by omega] at v4
  have h0 := halt a
  have h1 := hval (ℓ.vert a)
  have h1' := hval (ℓ.vert (a + 1))
  by_cases hp0 : valence Γ (ℓ.vert a) = 5
  ·
    have hua : u = a := by
      rcases hu with hu | hu
      · exact hu
      · rw [hu] at hu5
        omega
    have hva : v = a + 4 := by
      rcases hv with hv | hv
      · rw [hv, show a + ↑n - 1 = a + 3 by omega] at hv5
        omega
      · omega
    have hP : valence Γ ((ℓ.arc (a - 1) 6).vert 1) ≠ 3 := by
      have : (ℓ.arc (a - 1) 6).vert 1 = ℓ.vert a := by
        simp only [Line.arc]
        congr 1
        push_cast
        omega
      rw [this]
      omega
    have h36' := (h36 h40 (ℓ.arc (a - 1) 6) hP).2.2
    by_cases hR : RightSingular Γ G (ℓ.arc (a - 1) 6).vert 0 4
    ·
      have hL : ¬ LeftSingular Γ G (ℓ.arc (a - 1) 6).vert 2 6 := fun hL => h36' ⟨hL, hR⟩
      have e1 : LocTr Γ H (ℓ.vert (a + 1)) := F.locTr_of_fixers ℓ (w := a + 1) (hL0 _ rfl)
        (ℓ.exists_fixer_left_mem F hKv (by omega) (i := a - 1) (K := 6) (j := 2) (k := 6)
          (by omega) (by omega) hL)
      have e2 : LocTr Γ H (ℓ.vert (a + 1 + 1)) := F.locTr_of_fixers ℓ (w := a + 1 + 1)
        (fixL _ (by omega) (by omega)) (fixR _ (by omega) (by omega))
      exact F.locTr_all (ℓ.adj (a + 1)) e1 e2 _
    ·
      have e2 : LocTr Γ H (ℓ.vert (a + 2)) := F.locTr_of_fixers ℓ (w := a + 2)
        (fixL (a + 2) (by omega) (by omega)) (fixR (a + 2) (by omega) (by omega))
      have e3 : LocTr Γ H (ℓ.vert (a + 2 + 1)) := F.locTr_of_fixers ℓ (w := a + 2 + 1)
        (ℓ.exists_fixer_right_mem F hKu (by omega) (i := a - 1) (K := 6) (j := 0) (k := 4)
          (by omega) (by omega) hR) (hR0 _ (by omega))
      exact F.locTr_all (ℓ.adj (a + 2)) e2 e3 _
  ·
    have hva : v = a + 3 := by
      rcases hv with hv | hv
      · omega
      · rw [hv, show a + ↑n - 1 + 1 = a + 4 by omega] at hv5
        omega
    have e1 : LocTr Γ H (ℓ.vert (a + 1)) := F.locTr_of_fixers ℓ (w := a + 1)
      (hL0 _ rfl) (fixR (a + 1) (by omega) (by omega))
    have e2 : LocTr Γ H (ℓ.vert (a + 1 + 1)) := F.locTr_of_fixers ℓ (w := a + 1 + 1)
      (fixL _ (by omega) (by omega)) (fixR _ (by omega) (by omega))
    exact F.locTr_all (ℓ.adj (a + 1)) e1 e2 _

end CFSG.Quasithin.Fan86
