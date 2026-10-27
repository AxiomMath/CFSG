module

public import CFSG.LocalAnalysis.StandardType.FS81.Pieces
public import CFSG.LocalAnalysis.StandardType.FS81.RowSplit

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

private theorem fus42_of_span_eq {G : Type} [Group G] {k : ℕ} {B B' : Basis3 G k} {b₀ : G}
    (h : Fus42 B b₀) (hs : B'.span = B.span) : Fus42 B' b₀ := by
  unfold Fus42 at h ⊢
  rw [hs]
  exact h

theorem fs81ThmACRankInput_of_pieces
    (h0 : L0CanonPosition) (h1a : L1Local) (h1b : L1Fus42) (h1c : L1OddCore)
    (h1d : L1NotMonomial) (h1e : L1N6) (h1f : L1N7) (h1g : L1E7)
    (h2 : L2ConstructY) (h3a : L3RootFusion) (h3b : L3HoltEnd) :
    FS81ThmACRankInput := by
  intro G _ _ hsimp hchar b₀ K E m hA hmax hb₀ hcard hm hbig
  obtain ⟨r, hmr, hcp⟩ := h0 G b₀ K E m ⟨hA, hmax, hb₀, hcard, hm, hbig⟩
  subst hmr
  have hstd : StdAssumptions b₀ K E r := ⟨hsimp, ⟨hA, hmax, hb₀, hcard, hm, hbig⟩, hcp⟩
  obtain ⟨B, hB, hloc⟩ := h1a G b₀ K E r hstd
  have hfus : Fus42 B b₀ := h1b G b₀ K E r hstd B hB hloc
  have hodd : OddCoreTrivial E := h1c G b₀ K E r hstd B hB hloc hfus
  have hrec : ∃ B' : Basis3 G (r.n + 1), Adapted B' b₀ K E ∧ RecOut r B' b₀ := by
    cases r with
    | D6 =>
      have hII : LocalOrthII B b₀ := by
        rcases (show LocalOrthI B b₀ ∨ LocalOrthII B b₀ from hloc) with hI | hII
        · exact (h1d G b₀ K E Row.D6 (by decide) hstd B hB hfus hodd hI).elim
        · exact hII
      exact h1e G b₀ K E hstd B hB hII hfus hodd
    | twD7 =>
      have hII : LocalOrthII B b₀ := by
        rcases (show LocalOrthI B b₀ ∨ LocalOrthII B b₀ from hloc) with hI | hII
        · exact (h1d G b₀ K E Row.twD7 (by decide) hstd B hB hfus hodd hI).elim
        · exact hII
      exact h1f G b₀ K E hstd B hB hII hfus hodd
    | E7 => exact h1g G b₀ K E hstd B hB (show LocalE7 B b₀ from hloc) hfus hodd
  obtain ⟨B', hB', hrec'⟩ := hrec
  have hfus' : Fus42 B' b₀ := fus42_of_span_eq hfus (hB'.1.trans hB.1.symm)
  obtain ⟨Y, hYm, hCY, hRY⟩ := h2 G b₀ K E r hstd B' hB' hrec'
  obtain ⟨S, t, hS, htS, ht2, htc, htY⟩ :=
    h3a G b₀ K E r hstd hchar B' hB' hrec' hfus' Y hYm hCY hRY
  have hYtop : Y = ⊤ := by
    by_contra hne
    exact h3b G hsimp hchar r Y S t hYm hne hS htS ht2 htc htY
  rw [hYtop] at hYm
  exact hYm

@[expose] def FS81ThmACRankRest : Prop :=
  L2ConstructYAt Row.twD7 ∧ L3RootFusion

end CFSG.StandardType.FrameRoute.FS81
