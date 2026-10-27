module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourDom
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem not_ggLabelIso_of_open_notQTwo {p : ℕ} {lab lab' : LargeEvenLabel}
    (hn : lab.n < 2) (hopen : GGRootGenOpenLabel p lab) (hiso : GGLabelIso lab lab')
    (hn' : 2 ≤ lab'.n) : False := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  dsimp only at hn hn'
  unfold GGRootGenOpenLabel at hopen
  obtain ⟨hphi, hA⟩ := hopen
  unfold GGLabPhiOneTwo at hphi
  dsimp only at hphi
  unfold GGLabelIso at hiso
  rcases hiso with h | ⟨-, -, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h1, h2⟩ | ⟨-, h⟩
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, -, hn2⟩ := h
    omega
  · dsimp only at h
    omega
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, -, hn2⟩ := h
    omega
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, -, hn2⟩ := h
    omega
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, -, hn2⟩ := h
    omega
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, -, hn2⟩ := h
    omega
  · simp only [LargeEvenLabel.mk.injEq] at h1 h2
    obtain ⟨ht, hr, -⟩ := h1
    obtain ⟨-, -, hn2⟩ := h2
    have hn1 : n = 1 := by omega
    rw [hn1] at hphi
    refine hA ?_
    rw [ht, hr, hn1]
    refine Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)
    dsimp only
    norm_num at hphi ⊢
    exact hphi
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, -, hn2⟩ := h
    omega

private theorem not_ggLabelIso_of_rowNine {p : ℕ} {lab lab' : LargeEvenLabel}
    (hr9 : ¬ GGRootGenRowNineLabel p lab) (hiso : GGLabelIso lab lab')
    (ht : lab'.tag = .A) (hn : lab'.n = 1) (hp : p = 3) (hr : 5 ≤ lab'.rank) : False := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  dsimp only at ht hn hr
  subst ht
  subst hn
  unfold GGLabelIso at hiso
  rcases hiso with h | ⟨-, h, -, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · rw [h] at hr9
    exact hr9 ⟨rfl, rfl, hp, hr⟩
  · rcases h with h | h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, hr2, -⟩ := h
    omega
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, hr2, -⟩ := h
    omega
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, hr2, -⟩ := h
    omega
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, hr2, -⟩ := h
    omega
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, hr2, -⟩ := h
    omega
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨-, hr2, -⟩ := h
    omega

theorem ggRootGenLInputOnQFour_of_notQTwo (hRig : GGLabelRigidInput)
    {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ lab.n < 2)) :
    GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab =>
      (GGRootGenOpenLabel p lab ∧ ¬ X p lab ∧ lab.n < 2) ∨
        (GGRootGenOpenLabel p lab ∧ ¬ (X p lab ∨ lab.n < 2)))
      (fun lab hlab => (em (lab.n < 2)).elim
        (fun hn => Or.inl ⟨hlab.1, hlab.2, hn⟩)
        (fun hn => Or.inr ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩)) hL).elim_or with h₁ | h₂
  · obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel h₁
    have hopen : GGRootGenOpenLabel p lab := hP.1.1
    have hn : lab.n < 2 := hP.1.2.2
    obtain ⟨labq, hlq, hhasq, Rq, _, Iq, Fq, θq, hQ⟩ := largeEvenMarking_exists_hasLabel hq
    unfold GGLabQFour at hQ
    exact (not_ggLabelIso_of_open_notQTwo hn hopen
      (hRig lab labq _ hlab hlq hhas hhasq) hQ.1).elim
  · exact h G p B Bs x L D J hHyp hq hN h₂

theorem ggRootGenNbrInputOnQFour_of_notQTwo (hRig : GGLabelRigidInput)
    {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ (lab.n < 2 ∧ ¬ GGRootGenRowNineLabel p lab))) :
    GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hK
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab =>
      (GGRootGenOpenLabel p lab ∧ ¬ X p lab ∧ lab.n < 2 ∧ ¬ GGRootGenRowNineLabel p lab) ∨
        (GGRootGenOpenLabel p lab ∧
          ¬ (X p lab ∨ (lab.n < 2 ∧ ¬ GGRootGenRowNineLabel p lab))))
      (fun lab hlab => (em (lab.n < 2 ∧ ¬ GGRootGenRowNineLabel p lab)).elim
        (fun hn => Or.inl ⟨hlab.1, hlab.2, hn.1, hn.2⟩)
        (fun hn => Or.inr ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩)) hK).elim_or with h₁ | h₂
  · obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel h₁
    have hopen : GGRootGenOpenLabel p lab := hP.1.1
    have hn : lab.n < 2 := hP.1.2.2.1
    have hr9 : ¬ GGRootGenRowNineLabel p lab := hP.1.2.2.2
    obtain ⟨labok, hlok, hhasok, Rok, _, Iok, Fok, θok, hQ⟩ :=
      largeEvenMarking_exists_hasLabel (hN y K hnb)
    have hok : GGLabNbrOk p labok := hQ.1
    have hiso : GGLabelIso lab labok := hRig lab labok _ hlab hlok hhas hhasok
    rcases hok with h2 | ⟨ht, hn', hp, hr⟩
    · exact (not_ggLabelIso_of_open_notQTwo hn hopen hiso h2).elim
    · exact (not_ggLabelIso_of_rowNine hr9 hiso ht hn' hp hr).elim
  · exact h G p B Bs x L D J hHyp hq hN y K hnb h₂

end CFSG.StandardType

end
