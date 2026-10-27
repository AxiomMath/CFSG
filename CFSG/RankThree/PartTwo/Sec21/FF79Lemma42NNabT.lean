module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NNabS
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NInd

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG.RankThree.PartTwo.KFacts (KPSz)

theorem nBase_nab_general (hSz : KPSz) : NBaseNab := by
  intro G _ _ Q L b h hnab hmin
  have hQΓ : Q ≤ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer
  have hLΓ : L ≤ Subgroup.normalizer (Q : Set G) := h.normalizes
  set Γ : Subgroup G := Subgroup.normalizer (Q : Set G) with hΓ
  have h1 := nhyp_subgroupOf h Γ hQΓ hLΓ
  haveI : (Q.subgroupOf Γ).Normal := Subgroup.normal_in_normalizer
  have hnab' : ∃ x ∈ Q.subgroupOf Γ, ∃ y ∈ Q.subgroupOf Γ, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    exact ⟨⟨x, hQΓ hx⟩, hx, ⟨y, hQΓ hy⟩, hy, fun e => hxy (congrArg Subtype.val e)⟩
  have hmin' : NLeast (Q.subgroupOf Γ) (L.subgroupOf Γ) := by
    intro R' hR'Q hR'Q' hR'L
    set R : Subgroup G := R'.map Γ.subtype with hR
    have hRQ : R ≤ Q := by
      rintro _ ⟨r, hr, rfl⟩
      exact hR'Q hr
    have hmem : ∀ r ∈ R, ∃ r' ∈ R', (r' : G) = r := by
      rintro _ ⟨r, hr, rfl⟩
      exact ⟨r, hr, rfl⟩
    rcases hmin R hRQ
      (fun q hq r hr => by
        obtain ⟨r', hr', rfl⟩ := hmem r hr
        have := hR'Q' ⟨q, hQΓ hq⟩ hq r' hr'
        exact ⟨_, this, by simp⟩)
      (fun l hl r hr => by
        obtain ⟨r', hr', rfl⟩ := hmem r hr
        have := hR'L ⟨l, hLΓ hl⟩ hl r' hr'
        exact ⟨_, this, by simp⟩) with h0 | h0
    · left
      rw [eq_bot_iff]
      intro r' hr'
      have : (r' : G) ∈ R := ⟨r', hr', rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Subtype.ext this
    · right
      apply le_antisymm hR'Q
      intro q' hq'
      have : (q' : G) ∈ R := by rw [h0]; exact hq'
      obtain ⟨r', hr', hrq⟩ := hmem _ this
      have : r' = q' := Subtype.ext hrq
      exact this ▸ hr'
  have h2 := nBase_nab_normal hSz h1 inferInstance hnab' hmin'
  intro x hx l hl
  have := Subgroup.mem_centralizer_iff.mp (h2 (show (⟨x, hQΓ hx⟩ : Γ) ∈ Q.subgroupOf Γ from hx))
    ⟨l, hLΓ hl⟩ (show (⟨l, hLΓ hl⟩ : Γ) ∈ L.subgroupOf Γ from hl)
  simpa using congrArg Subtype.val this

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
