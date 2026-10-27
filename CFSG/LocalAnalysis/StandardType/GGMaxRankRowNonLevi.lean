module

public import CFSG.LocalAnalysis.StandardType.GGResRows
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pjr_labelIso_eq_of_maxRank {lab lab' : LargeEvenLabel}
    (ht : lab.tag = .A ∨ lab.tag = .twA) (hr : lab.rank = 8) (hiso : GGLabelIso lab lab') :
    lab' = lab := by
  simp only [GGLabelIso] at hiso
  rcases hiso with h | ⟨h, -, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact h.symm
  · rcases h with hB | hB <;> rcases ht with hA | hA <;> rw [hA] at hB <;>
      exact absurd hB (by decide)
  · exact absurd (show lab.tag = .D from congrArg LargeEvenLabel.tag h)
      (by rcases ht with hA | hA <;> rw [hA] <;> decide)
  · have h3 : lab.rank = 3 := congrArg LargeEvenLabel.rank h
    omega
  · exact absurd (show lab.tag = .twD from congrArg LargeEvenLabel.tag h)
      (by rcases ht with hA | hA <;> rw [hA] <;> decide)
  · have h3 : lab.rank = 3 := congrArg LargeEvenLabel.rank h
    omega
  · exact absurd (show lab.tag = .twD from congrArg LargeEvenLabel.tag h)
      (by rcases ht with hA | hA <;> rw [hA] <;> decide)
  · have h1 : lab.rank = 1 := congrArg LargeEvenLabel.rank h
    omega

private lemma pjr_maxRank_of_nonLevi {p : ℕ} {lab labY : LargeEvenLabel}
    (ht : lab.tag = .A ∨ lab.tag = .twA) (hr : lab.rank = 8) (hp : p = 3)
    (h : ggRowNonLevi p lab labY) : ggRowMaxRank p lab labY := by
  simp only [ggRowNonLevi] at h
  rcases h with h2 | hmax | htri | htriD4 | h7 | htwA2
  · simp only [ggRowTwoNode] at h2
    rcases h2 with ⟨-, -, hdvd, -⟩ | ⟨-, -, hdvd, -⟩ | ⟨hD, -, -, -⟩ | ⟨hD, -, -, -⟩
    · obtain ⟨k, hk⟩ := hdvd
      rw [hp, hr] at hk
      omega
    · obtain ⟨k, hk⟩ := hdvd
      rw [hp, hr] at hk
      omega
    · exact absurd (show lab.tag = .D from congrArg LargeEvenLabel.tag hD)
        (by rcases ht with hA | hA <;> rw [hA] <;> decide)
    · exact absurd (show lab.tag = .D from congrArg LargeEvenLabel.tag hD)
        (by rcases ht with hA | hA <;> rw [hA] <;> decide)
  · exact hmax
  · simp only [ggRowTriality] at htri
    rcases htri with ⟨htag, -, -⟩ | ⟨htag, -, -⟩
    · exact absurd htag (by rcases ht with hA | hA <;> rw [hA] <;> decide)
    · exact absurd htag (by rcases ht with hA | hA <;> rw [hA] <;> decide)
  · simp only [ggRowTriD4TwE6] at htriD4
    obtain ⟨htag, -, -, -⟩ := htriD4
    exact absurd htag (by rcases ht with hA | hA <;> rw [hA] <;> decide)
  · simp only [ggRowSeven] at h7
    obtain ⟨hp7, -⟩ := h7
    omega
  · simp only [ggRowTwA2] at htwA2
    obtain ⟨-, hr2, -, -, -⟩ := htwA2
    omega

theorem ggMaxRank_row_of_nonLevi {G : Type} [Group G] {p : ℕ} {J X Y : Subgroup G}
    (hLab : GGLabelRigidInput) (hrowX : GGResRowAt ggRowMaxRank p J X)
    (hY : GGResRowAt ggRowNonLevi p J Y) : GGResRowAt ggRowMaxRank p J Y := by
  obtain ⟨labJ, labX, hLJ, hLX, hJlab, hXlab, hrowX⟩ := hrowX
  obtain ⟨labJ', labY', hLJ', hLY', hJlab', hYlab', hrowY⟩ := hY
  simp only [ggRowMaxRank] at hrowX
  obtain ⟨ht, hr, hp⟩ : (labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8 ∧ p = 3 := by
    rcases hrowX with ⟨h, hp, -, -⟩ | ⟨h, hp, -, -⟩
    · exact ⟨Or.inl (congrArg LargeEvenLabel.tag h), congrArg LargeEvenLabel.rank h, hp⟩
    · exact ⟨Or.inr (congrArg LargeEvenLabel.tag h), congrArg LargeEvenLabel.rank h, hp⟩
  have hiso : GGLabelIso labJ labJ' :=
    hLab labJ labJ' (↥J ⧸ Subgroup.center ↥J) hLJ hLJ' hJlab hJlab'
  have hEq : labJ' = labJ := pjr_labelIso_eq_of_maxRank ht hr hiso
  subst labJ'
  exact ⟨labJ, labY', hLJ, hLY', hJlab, hYlab',
    pjr_maxRank_of_nonLevi ht hr hp hrowY⟩

end CFSG.StandardType

end
