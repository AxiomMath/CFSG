module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Ind

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def snoc {s : ℕ} (p : Arc Γ s) (w : V) (hw : Γ.Adj (p.vert s) w)
    (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) : Arc Γ (s + 1) where
  vert i := if i ≤ s then p.vert i else w
  adj i hi := by
    by_cases h : i + 1 ≤ s
    · simp only [show i ≤ s by omega, h, ↓reduceIte]
      exact p.adj i (by omega)
    · have h' : i = s := by omega
      subst h'
      simp only [le_refl, h, ↓reduceIte]
      exact hw
  nb i hi := by
    by_cases h : i + 2 ≤ s
    · simp only [show i ≤ s by omega, h, ↓reduceIte]
      exact p.nb i h
    · have h' : i = s - 1 := by omega
      have hs : 1 ≤ s := by omega
      simp only [show i ≤ s by omega, h, ↓reduceIte]
      rw [h']
      exact (hw' hs).symm

theorem snoc_vert_le {s : ℕ} (p : Arc Γ s) (w : V) (hw : Γ.Adj (p.vert s) w)
    (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) {i : ℕ} (hi : i ≤ s) :
    (snoc p w hw hw').vert i = p.vert i := by
  simp [snoc, hi]

theorem snoc_vert_last {s : ℕ} (p : Arc Γ s) (w : V) (hw : Γ.Adj (p.vert s) w)
    (hw' : 1 ≤ s → w ≠ p.vert (s - 1)) : (snoc p w hw hw').vert (s + 1) = w := by
  simp [snoc]

theorem exists_extend (F : FanTree Γ G) {k : ℕ} (P : Arc Γ k) :
    ∀ s, k ≤ s → ∃ Q : Arc Γ s, ∀ m, m ≤ k → Q.vert m = P.vert m := by
  intro s hs
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hs
  subst hn
  induction n with
  | zero => exact ⟨P, fun m _ => rfl⟩
  | succ n ih =>
    obtain ⟨Q, hQ⟩ := ih (by omega)
    obtain ⟨w, hw, hwne⟩ := F.exists_adj_ne (Q.vert (k + n)) (Q.vert (k + n - 1))
    refine ⟨snoc Q w hw (fun _ => hwne), fun m hm => ?_⟩
    rw [snoc_vert_le Q w hw _ (by omega), hQ m hm]

theorem exists_prepend (F : FanTree Γ G) {s : ℕ} (Q : Arc Γ s) :
    ∃ Q' : Arc Γ (s + 1), Γ.Adj (Q'.vert 0) (Q.vert 0) ∧
      ∀ m, m ≤ s → Q'.vert (m + 1) = Q.vert m := by
  obtain ⟨u, hu, hune⟩ := F.exists_adj_ne (Q.rev.vert s) (Q.rev.vert (s - 1))
  refine ⟨(snoc Q.rev u hu (fun _ => hune)).rev, ?_, fun m hm => ?_⟩
  · rw [Arc.rev_vert, Nat.sub_zero, snoc_vert_last]
    have : Q.rev.vert s = Q.vert 0 := by rw [Arc.rev_vert, Nat.sub_self]
    rw [this] at hu
    exact hu.symm
  · rw [Arc.rev_vert, show s + 1 - (m + 1) = s - m by omega, snoc_vert_le _ _ _ _ (by omega),
      Arc.rev_vert, show s - (s - m) = m by omega]

theorem exists_arc_ext (F : FanTree Γ G) {k : ℕ} (P : Arc Γ k) (hk6 : k ≤ 6) {w : V}
    (hw : Γ.Adj (P.vert k) w) (hwu : 1 ≤ k → w ≠ P.vert (k - 1)) :
    ∃ A : Arc Γ 8, ∃ e, e ≤ 1 ∧ (e = 0 ↔ Fan86.valence Γ (P.vert 0) = 5) ∧
      (∀ m, m ≤ k → A.vert (e + m) = P.vert m) ∧ A.vert (e + k + 1) = w ∧
      Fan86.valence Γ (A.vert 0) = 5 := by
  have hP₁v : ∀ m, m ≤ k → (snoc P w hw hwu).vert m = P.vert m := fun m hm =>
    snoc_vert_le P w hw hwu hm
  have hP₁w : (snoc P w hw hwu).vert (k + 1) = w := snoc_vert_last P w hw hwu
  by_cases h5 : Fan86.valence Γ (P.vert 0) = 5
  · obtain ⟨A, hA⟩ := exists_extend F (snoc P w hw hwu) 8 (by omega)
    refine ⟨A, 0, Nat.zero_le 1, ⟨fun _ => h5, fun _ => rfl⟩, fun m hm => ?_, ?_, ?_⟩
    · rw [zero_add, hA m (by omega), hP₁v m hm]
    · rw [zero_add, hA (k + 1) le_rfl, hP₁w]
    · rw [hA 0 (by omega), hP₁v 0 (by omega)]
      exact h5
  · obtain ⟨P₂, hP₂0, hP₂⟩ := exists_prepend F (snoc P w hw hwu)
    obtain ⟨A, hA⟩ := exists_extend F P₂ 8 (by omega)
    have h3 : Fan86.valence Γ (P.vert 0) = 3 := by
      have := F.valence (P.vert 0)
      have e : Fan86.valence Γ (P.vert 0) = Nat.card (Γ.neighborSet (P.vert 0)) := rfl
      omega
    refine ⟨A, 1, le_rfl, ⟨fun h => absurd h (by omega), fun h => absurd h h5⟩, fun m hm => ?_,
      ?_, ?_⟩
    · rw [hA (1 + m) (by omega), show 1 + m = m + 1 by omega, hP₂ m (by omega), hP₁v m hm]
    · rw [hA (1 + k + 1) (by omega), show 1 + k + 1 = (k + 1) + 1 by omega, hP₂ (k + 1) le_rfl,
        hP₁w]
    · rw [hA 0 (by omega)]
      rw [hP₁v 0 (by omega)] at hP₂0
      exact valence_three_five F hP₂0.symm h3

theorem rightTransitive_of_arcTrans (F : FanTree Γ G) (hA : ArcTrans Γ G) {k : ℕ} (P : Arc Γ k)
    (hk6 : k ≤ 6) : RightTransitive Γ G P.vert 0 k := by
  intro a b ha hau hb hbu
  obtain ⟨A, e, he, hevi, hAP, hAw, hA5⟩ := exists_arc_ext F P hk6 ha (fun _ => hau)
  obtain ⟨B, e', he', hevi', hBP, hBw, hB5⟩ := exists_arc_ext F P hk6 hb (fun _ => hbu)
  have hee : e = e' := by
    by_cases h : Fan86.valence Γ (P.vert 0) = 5
    · rw [hevi.2 h, hevi'.2 h]
    · have h1 : e ≠ 0 := fun h0 => h (hevi.1 h0)
      have h2 : e' ≠ 0 := fun h0 => h (hevi'.1 h0)
      omega
  subst hee
  obtain ⟨g, hg⟩ := hA A B hA5 hB5 
  refine ⟨g, mem_stabRange.2 fun m _ hm => ?_, ?_⟩
  · have := hg (e + m) (by omega)
    rwa [hAP m hm, hBP m hm] at this
  · have := hg (e + k + 1) (by omega)
    rwa [hAw, hBw] at this

theorem leftTransitive_of_rev {k : ℕ} (P : Arc Γ k) (hk : 1 ≤ k)
    (h : RightTransitive Γ G P.rev.vert 0 k) : LeftTransitive Γ G P.vert 0 k := by
  intro a b ha hau hb hbu
  have e1 : P.rev.vert k = P.vert 0 := by rw [Arc.rev_vert, Nat.sub_self]
  have e2 : P.rev.vert (k - 1) = P.vert 1 := by
    rw [Arc.rev_vert, show k - (k - 1) = 1 by omega]
  obtain ⟨g, hg, hga⟩ := h a b (by rwa [e1]) (by rwa [e2]) (by rwa [e1]) (by rwa [e2])
  refine ⟨g, ?_, hga⟩
  rw [mem_stabRange] at hg ⊢
  intro m hm1 hm2
  have := hg (k - m) (Nat.zero_le _) (Nat.sub_le _ _)
  rwa [Arc.rev_vert, Nat.sub_sub_self hm2] at this

theorem transGe_of_arcTrans (F : FanTree Γ G) (hA : ArcTrans Γ G) : TransGe Γ G 7 := by
  intro k hk1 hk7 P
  exact ⟨rightTransitive_of_arcTrans F hA P (by omega),
    leftTransitive_of_rev P hk1 (rightTransitive_of_arcTrans F hA P.rev (by omega))⟩

end P71

end CFSG.Quasithin.Fan86
