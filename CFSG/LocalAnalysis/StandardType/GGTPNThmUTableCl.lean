module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClC
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClD
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTUClAsm_ne_of_iso {o lab L : LargeEvenLabel} (hX : ¬ GGLabelIso o lab)
    (h : GGLabelIso L lab) : o ≠ L := by
  rintro rfl
  exact hX h

private theorem ggTUClAsm_halfSplit_twA {p k n : ℕ} {c : Prop}
    (h : LargeEvenHalfSplit p ⟨.twA, k, n⟩ c) (h1 : p ∣ 2 ^ n - 1)
    (h2 : ¬ p ∣ 2 ^ n + 1) : k = 5 := by
  rcases h with h | h | h | h | h | h
  · unfold LargeEvenSplit LargeEvenUntwisted at h
    rcases h with h | h | h | h
    · exact absurd h.1 (by simp)
    · exact absurd h.2.2 h2
    · exact absurd h.1 (by simp)
    · obtain ⟨rfl, rfl⟩ := h
      norm_num at h1
  · exact absurd h.1 (by simp)
  · simpa using h.1
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)

private theorem ggTUClAsm_some_eq {T T' : GGKacTypeCl} {tw tw' : Bool} {m m' : ℕ}
    (h : some (T', tw', m') = some (T, tw, m)) : T' = T ∧ tw' = tw ∧ m' = m := by
  simpa using h

private theorem ggTUClAsm_pack {p : ℕ} {lab L : LargeEvenLabel} {o : GGKacOrbit}
    (hiso : GGLabelIso lab L) (hL : LargeEvenInLambda2 L)
    (h : LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab L) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      GGLabelIso lab labX ∧ LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
        GGTablePRow p labJ labX :=
  ⟨h.1, o.lab, L, Or.inl rfl, hiso, h.1, hL, h.2⟩

private theorem ggTUClAsm_A {T : GGKacTypeCl} {tw : Bool} {m p n k : ℕ} {D : GGKacDatum}
    {o : GGKacOrbit} (hTlab : ggKacTypeClOfLabel ⟨.A, k, n⟩ = some (T, tw, m)) (hn : 1 ≤ n)
    (hlab' : 1 ≤ k ∧ (k = 1 → 2 ≤ n)) (hDm : D ∈ ggMultTableCl T tw p m)
    (hrZ : D.rZ ≤ 1) (hDo : D.orbits = [o]) (hqs : o.qs = true)
    (hX : ¬ GGLabelIso o.lab ⟨.A, k, n⟩) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      GGLabelIso ⟨.A, k, n⟩ labX ∧ LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
        GGTablePRow p labJ labX := by
  simp only [ggKacTypeClOfLabel] at hTlab
  obtain ⟨hT, htw, hm⟩ := ggTUClAsm_some_eq hTlab
  rw [← hT, ← htw, ← hm] at hDm
  have hX' : o.lab ≠ ⟨.A, k, n⟩ := ggTUClAsm_ne_of_iso hX (Or.inl rfl)
  obtain ⟨ho, hrow⟩ := ggTablePRow_of_mem_ggMultTableCl_A hn (by simp) hDm hrZ hDo hqs hX' hrk
  exact ggTUClAsm_pack (L := ⟨.A, k, n⟩) (Or.inl rfl) ⟨hn, hlab'⟩ ⟨ho, hrow⟩

private theorem ggTUClAsm_twA {T : GGKacTypeCl} {tw : Bool} {m p n k : ℕ} {c : Prop}
    {D : GGKacDatum} {o : GGKacOrbit}
    (hTlab : ggKacTypeClOfLabel ⟨.twA, k, n⟩ = some (T, tw, m)) (hn : 1 ≤ n)
    (hlab' : 2 ≤ k ∧ (k = 2 → 2 ≤ n)) (hT5 : LargeEvenHalfSplit p ⟨.twA, k, n⟩ c)
    (hDm : D ∈ ggMultTableCl T tw p m) (hrZ : D.rZ ≤ 1) (hDo : D.orbits = [o])
    (hqs : o.qs = true) (hX : ¬ GGLabelIso o.lab ⟨.twA, k, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      GGLabelIso ⟨.twA, k, n⟩ labX ∧ LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
        GGTablePRow p labJ labX := by
  simp only [ggKacTypeClOfLabel] at hTlab
  obtain ⟨hT, htw, hm⟩ := ggTUClAsm_some_eq hTlab
  rw [← hT, ← htw, ← hm] at hDm
  have hX' : o.lab ≠ ⟨.twA, k, n⟩ := ggTUClAsm_ne_of_iso hX (Or.inl rfl)
  obtain ⟨ho, hrow⟩ := ggTablePRow_of_mem_ggMultTableCl_A hn
    (fun _ h1 h2 => Or.inr (ggTUClAsm_halfSplit_twA hT5 h1 h2)) hDm hrZ hDo hqs hX' hrk
  exact ggTUClAsm_pack (L := ⟨.twA, k, n⟩) (Or.inl rfl) ⟨hn, hlab'⟩ ⟨ho, hrow⟩

private theorem ggTUClAsm_B {T : GGKacTypeCl} {tw : Bool} {m p n k : ℕ} {D : GGKacDatum}
    {o : GGKacOrbit} (hTlab : ggKacTypeClOfLabel ⟨.B, k, n⟩ = some (T, tw, m)) (hn : 1 ≤ n)
    (hlab' : 2 ≤ k ∧ (k = 2 → 2 ≤ n)) (hDm : D ∈ ggMultTableCl T tw p m)
    (hrZ : D.rZ ≤ 1) (hDo : D.orbits = [o]) (hqs : o.qs = true)
    (hX : ¬ GGLabelIso o.lab ⟨.B, k, n⟩) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      GGLabelIso ⟨.B, k, n⟩ labX ∧ LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
        GGTablePRow p labJ labX := by
  simp only [ggKacTypeClOfLabel] at hTlab
  rw [if_pos hlab'.1] at hTlab
  obtain ⟨hT, htw, hm⟩ := ggTUClAsm_some_eq hTlab
  rw [← hT, ← htw, ← hm] at hDm
  have hX' : o.lab ≠ ⟨.C, k, n⟩ := ggTUClAsm_ne_of_iso hX (by simp [GGLabelIso])
  obtain ⟨ho, hrow⟩ := ggTablePRow_of_mem_ggMultTableCl_C hn hlab'.2 hDm hrZ hDo hqs hX' hrk
  exact ggTUClAsm_pack (L := ⟨.C, k, n⟩) (by simp [GGLabelIso]) ⟨hn, hlab'⟩ ⟨ho, hrow⟩

private theorem ggTUClAsm_C {T : GGKacTypeCl} {tw : Bool} {m p n k : ℕ} {D : GGKacDatum}
    {o : GGKacOrbit} (hTlab : ggKacTypeClOfLabel ⟨.C, k, n⟩ = some (T, tw, m)) (hn : 1 ≤ n)
    (hlab' : 2 ≤ k ∧ (k = 2 → 2 ≤ n)) (hDm : D ∈ ggMultTableCl T tw p m)
    (hrZ : D.rZ ≤ 1) (hDo : D.orbits = [o]) (hqs : o.qs = true)
    (hX : ¬ GGLabelIso o.lab ⟨.C, k, n⟩) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      GGLabelIso ⟨.C, k, n⟩ labX ∧ LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
        GGTablePRow p labJ labX := by
  simp only [ggKacTypeClOfLabel] at hTlab
  rw [if_pos hlab'.1] at hTlab
  obtain ⟨hT, htw, hm⟩ := ggTUClAsm_some_eq hTlab
  rw [← hT, ← htw, ← hm] at hDm
  have hX' : o.lab ≠ ⟨.C, k, n⟩ := ggTUClAsm_ne_of_iso hX (Or.inl rfl)
  obtain ⟨ho, hrow⟩ := ggTablePRow_of_mem_ggMultTableCl_C hn hlab'.2 hDm hrZ hDo hqs hX' hrk
  exact ggTUClAsm_pack (L := ⟨.C, k, n⟩) (Or.inl rfl) ⟨hn, hlab'⟩ ⟨ho, hrow⟩

private theorem ggTUClAsm_D {T : GGKacTypeCl} {tw : Bool} {m p n k : ℕ} {D : GGKacDatum}
    {o : GGKacOrbit} (hTlab : ggKacTypeClOfLabel ⟨.D, k, n⟩ = some (T, tw, m)) (hn : 1 ≤ n)
    (hlab' : 3 ≤ k) (hDm : D ∈ ggMultTableCl T tw p m) (hrZ : D.rZ ≤ 1)
    (hDo : D.orbits = [o]) (hqs : o.qs = true) (hX : ¬ GGLabelIso o.lab ⟨.D, k, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      GGLabelIso ⟨.D, k, n⟩ labX ∧ LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
        GGTablePRow p labJ labX := by
  simp only [ggKacTypeClOfLabel] at hTlab
  by_cases hk4 : 4 ≤ k
  · rw [if_pos hk4] at hTlab
    obtain ⟨hT, htw, hm⟩ := ggTUClAsm_some_eq hTlab
    rw [← hT, ← htw, ← hm] at hDm
    have hX' : o.lab ≠ ⟨.D, k, n⟩ := ggTUClAsm_ne_of_iso hX (Or.inl rfl)
    obtain ⟨ho, labJ, hisoJ, hlabJ, hrow⟩ :=
      ggTablePRow_of_mem_ggMultTableCl_D hn hk4 hDm hrZ hDo hqs hX'
    exact ⟨ho, labJ, ⟨.D, k, n⟩, hisoJ, Or.inl rfl, hlabJ, ⟨hn, hlab'⟩, hrow⟩
  · rw [if_neg hk4] at hTlab
    by_cases hk3eq : k = 3
    · rw [if_pos hk3eq] at hTlab
      obtain ⟨hT, htw, hm⟩ := ggTUClAsm_some_eq hTlab
      rw [← hT, ← htw, ← hm] at hDm
      subst hk3eq
      have hX' : o.lab ≠ ⟨.A, 3, n⟩ := ggTUClAsm_ne_of_iso hX (by simp [GGLabelIso])
      obtain ⟨ho, hrow⟩ := ggTablePRow_of_mem_ggMultTableCl_A hn (by simp) hDm hrZ hDo hqs hX' hrk
      have hL : LargeEvenInLambda2 (⟨.A, 3, n⟩ : LargeEvenLabel) := by
        show 1 ≤ n ∧ 1 ≤ 3 ∧ (3 = 1 → 2 ≤ n)
        exact ⟨hn, by norm_num, by omega⟩
      exact ggTUClAsm_pack (L := ⟨.A, 3, n⟩) (by simp [GGLabelIso]) hL ⟨ho, hrow⟩
    · rw [if_neg hk3eq] at hTlab
      simp at hTlab

private theorem ggTUClAsm_twD {T : GGKacTypeCl} {tw : Bool} {m p n k : ℕ} {D : GGKacDatum}
    {o : GGKacOrbit} (hTlab : ggKacTypeClOfLabel ⟨.twD, k, n⟩ = some (T, tw, m))
    (hn : 1 ≤ n) (hlab' : 2 ≤ k) (hDm : D ∈ ggMultTableCl T tw p m) (hrZ : D.rZ ≤ 1)
    (hDo : D.orbits = [o]) (hqs : o.qs = true) (hX : ¬ GGLabelIso o.lab ⟨.twD, k, n⟩)
    (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      GGLabelIso ⟨.twD, k, n⟩ labX ∧ LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
        GGTablePRow p labJ labX := by
  simp only [ggKacTypeClOfLabel] at hTlab
  by_cases hk4 : 4 ≤ k
  · rw [if_pos hk4] at hTlab
    obtain ⟨hT, htw, hm⟩ := ggTUClAsm_some_eq hTlab
    rw [← hT, ← htw, ← hm] at hDm
    have hX' : o.lab ≠ ⟨.twD, k, n⟩ := ggTUClAsm_ne_of_iso hX (Or.inl rfl)
    obtain ⟨ho, labJ, hisoJ, hlabJ, hrow⟩ :=
      ggTablePRow_of_mem_ggMultTableCl_D hn hk4 hDm hrZ hDo hqs hX'
    exact ⟨ho, labJ, ⟨.twD, k, n⟩, hisoJ, Or.inl rfl, hlabJ, ⟨hn, hlab'⟩, hrow⟩
  · rw [if_neg hk4] at hTlab
    by_cases hk3eq : k = 3
    · rw [if_pos hk3eq] at hTlab
      obtain ⟨hT, htw, hm⟩ := ggTUClAsm_some_eq hTlab
      rw [← hT, ← htw, ← hm] at hDm
      subst hk3eq
      have hX' : o.lab ≠ ⟨.twA, 3, n⟩ := ggTUClAsm_ne_of_iso hX (by simp [GGLabelIso])
      obtain ⟨ho, hrow⟩ := ggTablePRow_of_mem_ggMultTableCl_A hn (fun _ _ _ => Or.inl rfl) hDm hrZ
        hDo hqs hX' hrk
      have hL : LargeEvenInLambda2 (⟨.twA, 3, n⟩ : LargeEvenLabel) := by
        show 1 ≤ n ∧ 2 ≤ 3 ∧ (3 = 2 → 2 ≤ n)
        exact ⟨hn, by norm_num, by omega⟩
      exact ggTUClAsm_pack (L := ⟨.twA, 3, n⟩) (by simp [GGLabelIso]) hL ⟨ho, hrow⟩
    · rw [if_neg hk3eq] at hTlab
      by_cases hk2eq : k = 2
      · rw [if_pos hk2eq] at hTlab
        obtain ⟨hT, htw, hm⟩ := ggTUClAsm_some_eq hTlab
        rw [← hT, ← htw, ← hm] at hDm
        subst hk2eq
        have hX' : o.lab ≠ ⟨.A, 1, 2 * n⟩ :=
          ggTUClAsm_ne_of_iso hX (by simp [GGLabelIso])
        obtain ⟨ho, hrow⟩ := ggTablePRow_of_mem_ggMultTableCl_A (by omega) (by simp) hDm hrZ hDo
          hqs hX' hrk
        have hL : LargeEvenInLambda2 (⟨.A, 1, 2 * n⟩ : LargeEvenLabel) := by
          show 1 ≤ 2 * n ∧ 1 ≤ 1 ∧ (1 = 1 → 2 ≤ 2 * n)
          exact ⟨by omega, by norm_num, by omega⟩
        exact ggTUClAsm_pack (L := ⟨.A, 1, 2 * n⟩) (by simp [GGLabelIso]) hL ⟨ho, hrow⟩
      · rw [if_neg hk2eq] at hTlab
        simp at hTlab

theorem ggTablePRow_of_ggMultValidCl {lab : LargeEvenLabel} {p : ℕ} {c : Prop}
    (hlab : LargeEvenInLambda2 lab) (hT5 : LargeEvenHalfSplit p lab c) {D : GGKacDatum}
    (hD : GGMultValidCl lab p D) (hrZ : D.rZ ≤ 1) {o : GGKacOrbit} (hDo : D.orbits = [o])
    (hqs : o.qs = true) (hX : ¬ GGLabelIso o.lab lab) (hrk : ¬ GGTPNPRankOne p o.lab) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ labX : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      GGLabelIso lab labX ∧ LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
        GGTablePRow p labJ labX := by
  obtain ⟨T, tw, m, hTlab, hDm⟩ := hD
  rcases lab with ⟨tag, k, n⟩
  obtain ⟨hn, hlab'⟩ := hlab
  have hn : 1 ≤ n := hn
  cases tag
  · exact ggTUClAsm_A hTlab hn hlab' hDm hrZ hDo hqs hX hrk
  · exact ggTUClAsm_twA hTlab hn hlab' hT5 hDm hrZ hDo hqs hX hrk
  · exact ggTUClAsm_B hTlab hn hlab' hDm hrZ hDo hqs hX hrk
  · exact ggTUClAsm_C hTlab hn hlab' hDm hrZ hDo hqs hX hrk
  · exact ggTUClAsm_D hTlab hn hlab' hDm hrZ hDo hqs hX hrk
  · exact ggTUClAsm_twD hTlab hn hlab' hDm hrZ hDo hqs hX hrk
  all_goals
    simp only [ggKacTypeClOfLabel] at hTlab
    cases hTlab

end CFSG.StandardType

end
