module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem hasRightSingular_of_left {k : ℕ} (hk : 1 ≤ k) (P : Arc Γ k)
    (h : LeftSingular Γ G P.vert 0 k) : HasRightSingular Γ G k := by
  obtain ⟨w, hw, hne, hfix⟩ := h
  refine ⟨P.rev, w, ?_, ?_, ?_⟩
  · rwa [Arc.rev_vert_last]
  · rw [Arc.rev_vert, show k - (k - 1) = 0 + 1 by omega]
    exact hne
  · intro g hg
    refine hfix g ?_
    rw [mem_stabRange] at hg ⊢
    intro m h0 hm
    have := hg (k - m) (Nat.zero_le _) (Nat.sub_le _ _)
    rwa [Arc.rev_vert, Nat.sub_sub_self hm] at this

@[expose] def LineNSR (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] (ℓ : Line Γ)
    (k : ℕ) : Prop :=
  ∀ i : ℤ, ¬ RightSingular Γ G (ℓ.arc i k).vert 0 k

@[expose] def LineNSL (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] (ℓ : Line Γ)
    (k : ℕ) : Prop :=
  ∀ i : ℤ, ¬ LeftSingular Γ G (ℓ.arc i k).vert 0 k

theorem lineNSR_of_fan40 {F : FanTree Γ G} (h40 : Fan40 F) (ℓ : Line Γ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ 3) : LineNSR Γ G ℓ k := fun i h => h40 k hk1 (by omega) ⟨ℓ.arc i k, h⟩

theorem lineNSL_of_fan40 {F : FanTree Γ G} (h40 : Fan40 F) (ℓ : Line Γ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ 3) : LineNSL Γ G ℓ k :=
  fun i h => h40 k hk1 (by omega) (hasRightSingular_of_left hk1 _ h)

theorem lineNSR_of_not {ℓ : Line Γ} {N k : ℕ} (hs : ¬ LineSingLe Γ G ℓ N) (hk1 : 1 ≤ k)
    (hk : k ≤ N) : LineNSR Γ G ℓ k := fun i h => hs ⟨k, i, hk1, hk, Or.inl h⟩

theorem lineNSL_of_not {ℓ : Line Γ} {N k : ℕ} (hs : ¬ LineSingLe Γ G ℓ N) (hk1 : 1 ≤ k)
    (hk : k ≤ N) : LineNSL Γ G ℓ k := fun i h => hs ⟨k, i, hk1, hk, Or.inr h⟩

namespace Line

variable (ℓ : Line Γ)

theorem adj_pred (i : ℤ) : Γ.Adj (ℓ.vert i) (ℓ.vert (i - 1)) := by
  have := (ℓ.adj (i - 1)).symm
  rwa [sub_add_cancel] at this

theorem vert_pred_ne_succ (i : ℤ) : ℓ.vert (i - 1) ≠ ℓ.vert (i + 1) := by
  have := ℓ.nb (i - 1)
  rwa [show i - 1 + 2 = i + 1 by omega] at this

theorem exists_fixer_right' (i : ℤ) (K j k : ℕ) (hk1 : 1 ≤ k)
    (hns : ¬ RightSingular Γ G (ℓ.arc i K).vert j k) :
    ∃ g : G, (∀ m : ℤ, i + j ≤ m → m ≤ i + k → g • ℓ.vert m = ℓ.vert m) ∧
      g • ℓ.vert (i + k + 1) ≠ ℓ.vert (i + k + 1) := by
  by_contra hcon
  push Not at hcon
  refine hns ⟨ℓ.vert (i + k + 1), ?_, ?_, ?_⟩
  · simpa [Line.arc] using ℓ.adj (i + k)
  · have h1 := ℓ.vert_pred_ne_succ (i + k)
    have e : (ℓ.arc i K).vert (k - 1) = ℓ.vert (i + k - 1) := by
      simp only [Line.arc]
      congr 1
      omega
    rw [e]
    exact h1.symm
  · intro g hg
    refine hcon g fun m h1 h2 => ?_
    have h := mem_stabRange.1 hg (m - i).toNat (by omega) (by omega)
    have e : (ℓ.arc i K).vert (m - i).toNat = ℓ.vert m := by
      simp only [Line.arc]
      congr 1
      omega
    rwa [e] at h

theorem exists_fixer_left' (i : ℤ) (K j k : ℕ) (hns : ¬ LeftSingular Γ G (ℓ.arc i K).vert j k) :
    ∃ g : G, (∀ m : ℤ, i + j ≤ m → m ≤ i + k → g • ℓ.vert m = ℓ.vert m) ∧
      g • ℓ.vert (i + j - 1) ≠ ℓ.vert (i + j - 1) := by
  by_contra hcon
  push Not at hcon
  refine hns ⟨ℓ.vert (i + j - 1), ?_, ?_, ?_⟩
  · simpa [Line.arc] using ℓ.adj_pred (i + j)
  · have h1 := ℓ.vert_pred_ne_succ (i + j)
    have e : (ℓ.arc i K).vert (j + 1) = ℓ.vert (i + j + 1) := by
      simp only [Line.arc]
      congr 1
      push_cast
      omega
    rw [e]
    simpa [Line.arc] using h1
  · intro g hg
    refine hcon g fun m h1 h2 => ?_
    have h := mem_stabRange.1 hg (m - i).toNat (by omega) (by omega)
    have e : (ℓ.arc i K).vert (m - i).toNat = ℓ.vert m := by
      simp only [Line.arc]
      congr 1
      omega
    rwa [e] at h

theorem mem_nbrStab_of_fix (F : FanTree Γ G) {g : G} {u : ℤ}
    (h0 : g • ℓ.vert (u - 1) = ℓ.vert (u - 1)) (h1 : g • ℓ.vert u = ℓ.vert u)
    (h2 : g • ℓ.vert (u + 1) = ℓ.vert (u + 1)) : g ∈ nbrStab Γ G (ℓ.vert u) := by
  refine mem_nbrStab.2 fun w hw => ?_
  exact F.frobenius_two (ℓ.vert u) (ℓ.vert (u - 1)) (ℓ.vert (u + 1)) (ℓ.adj_pred u) (ℓ.adj u)
    (ℓ.vert_pred_ne_succ u) g (MulAction.mem_stabilizer_iff.2 h1) h0 h2 w hw

theorem exists_fixer_right_mem (F : FanTree Γ G) {M : Subgroup G} {u w i : ℤ} {K j k : ℕ}
    (hKM : ∀ g ∈ nbrStab Γ G (ℓ.vert u), g ∈ M) (huw : u + 1 ≤ w) (hi : i + j = u - 1)
    (hk : i + k = w) (hns : ¬ RightSingular Γ G (ℓ.arc i K).vert j k) :
    ∃ g ∈ M, g • ℓ.vert (w - 1) = ℓ.vert (w - 1) ∧ g • ℓ.vert w = ℓ.vert w ∧
      g • ℓ.vert (w + 1) ≠ ℓ.vert (w + 1) := by
  obtain ⟨g, hfix, hmove⟩ := ℓ.exists_fixer_right' i K j k (by omega) hns
  have hgK : g ∈ nbrStab Γ G (ℓ.vert u) :=
    ℓ.mem_nbrStab_of_fix F (hfix _ (by omega) (by omega)) (hfix _ (by omega) (by omega))
      (hfix _ (by omega) (by omega))
  refine ⟨g, hKM g hgK, hfix _ (by omega) (by omega), hfix _ (by omega) (by omega), ?_⟩
  rwa [show i + k + 1 = w + 1 by omega] at hmove

theorem exists_fixer_left_mem (F : FanTree Γ G) {M : Subgroup G} {v w i : ℤ} {K j k : ℕ}
    (hKM : ∀ g ∈ nbrStab Γ G (ℓ.vert v), g ∈ M) (hwv : w + 1 ≤ v) (hi : i + j = w)
    (hk : i + k = v + 1) (hns : ¬ LeftSingular Γ G (ℓ.arc i K).vert j k) :
    ∃ g ∈ M, g • ℓ.vert w = ℓ.vert w ∧ g • ℓ.vert (w + 1) = ℓ.vert (w + 1) ∧
      g • ℓ.vert (w - 1) ≠ ℓ.vert (w - 1) := by
  obtain ⟨g, hfix, hmove⟩ := ℓ.exists_fixer_left' i K j k hns
  have hgK : g ∈ nbrStab Γ G (ℓ.vert v) :=
    ℓ.mem_nbrStab_of_fix F (hfix _ (by omega) (by omega)) (hfix _ (by omega) (by omega))
      (hfix _ (by omega) (by omega))
  refine ⟨g, hKM g hgK, hfix _ (by omega) (by omega), hfix _ (by omega) (by omega), ?_⟩
  rwa [hi] at hmove

end Line

end CFSG.Quasithin.Fan86
