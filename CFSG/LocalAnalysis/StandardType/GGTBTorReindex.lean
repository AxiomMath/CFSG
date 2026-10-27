module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs

@[expose] public section

namespace CFSG.StandardType

variable {m N N' : ℕ} {L : Type} [Group L] {A : Subgroup (MulAut L)}

def GGTorusTorWit.reindex (w : GGTorusTorWit m N L A) (e : Fin N ≃ Fin N') :
    GGTorusTorWit m N' L A where
  T := w.T
  α := fun k => w.α (e.symm k)
  cor := fun k => w.cor (e.symm k)
  n := fun k => w.n (e.symm k)
  hn := fun k => w.hn (e.symm k)
  Tsc := w.Tsc

theorem GGTorusTorWit.holds_reindex (w : GGTorusTorWit m N L A)
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (e : Fin N ≃ Fin N') (hw : w.Holds C M) :
    (w.reindex e).Holds (C.reindex e e) (M.reindex e) := by
  obtain ⟨hTcomm, hAT, hconjT, hαadd, hcorinj, hcorcomm, hfixcor, hpair,
    hnconj, hnel, hsep, hαA, hinnA, hoddTsc, ⟨hCscA, hCscB, hCscC⟩,
    haut, ⟨eM, hsimple⟩⟩ := hw
  have hcor : (⨆ k, ((w.reindex e).cor k).range) = ⨆ k, (w.cor k).range := by
    apply le_antisymm
    · exact iSup_le fun k => le_iSup (fun j => (w.cor j).range) (e.symm k)
    · refine iSup_le fun k => le_iSup_of_le (e k) ?_
      simp only [reindex, Equiv.symm_apply_apply, le_refl]
  have hmarked : Set.range (fun k => ggConjAut A ((w.reindex e).hn k)) =
      Set.range (fun k => ggConjAut A (w.hn k)) := by
    ext a
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨e.symm k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, by simp only [reindex, Equiv.symm_apply_apply]⟩
  refine ⟨hTcomm, hAT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hoddTsc,
    ⟨hCscA, hCscB, ?_⟩, ?_, ?_⟩
  · exact fun k ζ => hconjT (e.symm k) ζ
  · exact fun j => hαadd (e.symm j)
  · exact fun k => hcorinj (e.symm k)
  · exact fun j k ζ ξ => hcorcomm (e.symm j) (e.symm k) ζ ξ
  · exact fun τ hτ k ζ => hfixcor τ hτ (e.symm k) ζ
  · exact fun i j ζ => hpair (e.symm i) (e.symm j) ζ
  · exact fun k => hnconj (e.symm k)
  · exact fun k => hnel (e.symm k)
  · intro τ hτ hzero
    apply hsep τ hτ
    intro k
    simpa only [reindex, Equiv.symm_apply_apply] using hzero (e k)
  · exact fun k => hαA (e.symm k)
  · intro a ha hai
    rw [hcor]
    exact hinnA a ha hai
  · intro t ht htm
    rw [hcor]
    exact hCscC t ht htm
  · rw [hmarked]
    exact haut
  · refine ⟨(M.reindexGroupEquiv e).trans eM, ?_⟩
    intro k
    simpa only [MulEquiv.trans_apply, CoxeterMatrix.reindexGroupEquiv_apply_simple, reindex]
      using hsimple (e.symm k)

theorem GGTorusTorData.reindex
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (h : GGTorusTorData m N C M L A) (e : Fin N ≃ Fin N') :
    GGTorusTorData m N' (C.reindex e e) (M.reindex e) L A := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.reindex e, w.holds_reindex e hw⟩

theorem GGTorusTorW.reindex {p r : ℕ}
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusTorW p r m N C M R I) (e : Fin N ≃ Fin N') :
    GGTorusTorW p r m N' (C.reindex e e) (M.reindex e) R I := by
  intro L' _ _ ψ A hTB
  exact (h L' ψ A hTB).reindex e

end CFSG.StandardType
