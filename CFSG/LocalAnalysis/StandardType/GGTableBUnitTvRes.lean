module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvMain
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLCover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGUnitaryTvResLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  Yardstones.M3f9567aba59d.GGRemainderTableBLResTv p lab ∧ lab.tag = .twA ∧
    ¬ (lab.rank = 5 ∧ p = 3)

theorem GGUnitaryTvResLabel.unitary {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGUnitaryTvResLabel p lab) : GGUnitaryTvLabel p lab := by
  obtain ⟨hres, htag, hno⟩ := h
  have hrank : 3 ≤ lab.rank := by
    have h2 : 2 ≤ lab.rank := by
      have := hlab.2
      rw [htag] at this
      exact this.1
    have h3 : lab.rank ≠ 2 := fun hr => hres.1.1.2 (Or.inl (Or.inr (Or.inr ⟨htag, hr⟩)))
    omega
  have hsplit : LargeEvenSplit p lab := hres.1.1.1.1.2.2
  refine ⟨htag, hrank, ?_, hno⟩
  rcases hsplit with ⟨hu, -⟩ | ⟨-, -, hp⟩ | ⟨h1, -⟩ | ⟨hn1, hp3⟩
  · rw [htag] at hu
    exact absurd hu (by simp [LargeEvenUntwisted])
  · exact hp
  · rcases h1 with h1 | h1 <;> rw [htag] at h1 <;> exact absurd h1 (by decide)
  · subst hp3
    rw [hn1]
    norm_num

section Res


theorem ggLTransvectionCenterInputOn_resTv_unitary :
    GGLTransvectionCenterInputOn GGUnitaryTvResLabel :=
  ggLTransvectionCenterInputOn_unitary_of fun _ _ _ hlab h => h.unitary hlab

theorem ggLTransvectionCenterInputOn_resTv_of_rest
    (h : GGLTransvectionCenterInputOn fun p lab =>
      Yardstones.M3f9567aba59d.GGRemainderTableBLResTv p lab ∧ ¬ GGUnitaryTvResLabel p lab) :
    GGLTransvectionCenterInputOn Yardstones.M3f9567aba59d.GGRemainderTableBLResTv :=
  CorFourTwoVacMore.lTransvectionCenterInputOn_mono (fun p lab hlab => by
      by_cases hc : lab.tag = .twA ∧ ¬ (lab.rank = 5 ∧ p = 3)
      · exact Or.inl ⟨hlab, hc⟩
      · exact Or.inr ⟨hlab, fun hu => hc hu.2⟩)
    (ggLTransvectionCenterInputOn_resTv_unitary.or h)

end Res

end CFSG.StandardType

end
