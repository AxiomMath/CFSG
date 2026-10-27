module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGB36JNonExc
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestVac
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
public import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRankExc
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem tne_labelIso_tag_eq {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (ht : lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) : lab'.tag = lab.tag := by
  rcases h with h | h | h | h | h | h | h | h
  · rw [h]
  · exfalso
    rcases h.1 with hb | hc
    · rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [hb] at h1 <;>
        exact absurd h1 (by decide)
    · rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [hc] at h1 <;>
        exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.1] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.1] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.1] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.1] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.1] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.2] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)

private theorem tne_split_of_half {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (ht : lab.tag = .triD4 ∨ lab.tag = .twF4) (hh : LargeEvenHalfSplit p lab c) :
    LargeEvenSplit p lab := by
  rcases ht with ht | ht <;> simpa [LargeEvenHalfSplit, ht] using hh

theorem tne_halfSplit_dvd {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (ht : lab.tag = .triD4 ∨ lab.tag = .twF4) (hh : LargeEvenHalfSplit p lab c) :
    p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  have hsp := tne_split_of_half ht hh
  rcases ht with ht | ht
  · simp only [LargeEvenSplit] at hsp
    rcases hsp with ⟨-, h⟩ | ⟨-, hne, h⟩ | ⟨-, h⟩ | ⟨hn, hp3⟩
    · exact Or.inl h
    · exact absurd ht hne
    · exact Or.inl h
    · right
      subst hp3
      rw [hn]
      norm_num
  · simp only [LargeEvenSplit] at hsp
    rcases hsp with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨hbad, -⟩ | ⟨hn, hp3⟩
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases hbad with h | h <;> rw [ht] at h <;> exact absurd h (by decide)
    · right
      subst hp3
      rw [hn]
      norm_num

theorem tne_big_three {X : Type} [Group X] [Finite X] {p n : ℕ}
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNDatumB p n (fun _ _ => True) A Ab σ J) : p ^ 3 ≤ Nat.card A := by
  obtain ⟨-, hflat, hAb3, -, -, -, -, -⟩ := hd.1
  exact hAb3.trans (Nat.card_le_card_of_injective (Subgroup.inclusion hflat.1)
    (Subgroup.inclusion_injective hflat.1))

theorem tne_false_of_bound
    {X : Type} [Group X] [Finite X] {p n k : ℕ} {A Ab : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} {S : LargeEvenLabel → Prop} {labX : LargeEvenLabel}
    (hbound : ¬ LargeEvenMarking X fun lab R _ I _ _ => S lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ k ≤ Nat.card E)
    (hd : GGTPNDatumB p n (fun _ _ => True) A Ab σ J) (hBig : p ^ k ≤ Nat.card A)
    (hΛX : LargeEvenInLambda2 labX) (hhX : GGHasLabel labX (X ⧸ Subgroup.center X))
    (hS_of_iso : ∀ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' →
      GGLabelIso labX lab' → LargeEvenHalfSplit p lab' (Subgroup.center X = ⊥) → S lab') :
    False := by
  obtain ⟨hlocCore, -, -, -, -, -, -, hmarked⟩ := hd.1
  obtain ⟨hcomm, lab', hlab', hraw⟩ := hmarked
  have hHasLabel_lab' : GGHasLabel lab' (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw
  have hiso : GGLabelIso labX lab' :=
    ggLabelRigidInput_holds labX lab' (X ⧸ Subgroup.center X) hΛX hlab' hhX hHasLabel_lab'
  obtain ⟨R₀, hR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, -, hhalf, -⟩ := hQ₀
  have hS : S lab' := hS_of_iso lab' hlab' hiso hhalf
  have hrawE : LargeEvenRawDatum lab' fun R _ I F => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ : X ⧸ Subgroup.center X ≃* R,
        (True ∧ LargeEvenHalfSplit p lab' (Subgroup.center X = ⊥) ∧ GGInducedInn A θ I) ∧
        ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
          p ^ k ≤ Nat.card E := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    refine ⟨hs, hna, θ, hP, ?_⟩
    refine ⟨A.map (ggInducedAut θ), ?_, ?_, ?_⟩
    · rintro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact hP.2.2 a ha
    · exact CFSG.Open.IsElemAbelian.map hlocCore.1 (ggInducedAut θ)
    · rw [Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hcomm θ)]
      exact hBig
  have key : LargeEvenMarking X fun lab R _ I _ _ => S lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ k ≤ Nat.card E :=
    ⟨hcomm, lab', hlab', largeEvenRawDatum_mono (fun R _ I F ⟨hs, hna, θ, hP, hE⟩ =>
      ⟨hs, hna, θ, hS, hE⟩) hrawE⟩
  exact hbound key

theorem ggNonExc_core
    {X : Type} [Group X] [Finite X] {p n : ℕ} {A Ab : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : GGTPNDatumB p n (fun _ _ => True) A Ab σ J) {labJ labX : LargeEvenLabel}
    (hΛJ : LargeEvenInLambda2 labJ) (hΛX : LargeEvenInLambda2 labX)
    (hnotcl : ¬ GGTPNClTag labX.tag) (hnotex : ¬ GGTPNExcTag labX.tag)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) : False := by
  obtain ⟨t, r, nn⟩ := labX
  have htag : t = .triD4 ∨ t = .G2 ∨ t = .twB2 ∨ t = .twF4 ∨ t = .B2der ∨ t = .G2der ∨
      t = .twF4der := by
    revert hnotcl hnotex
    cases t <;> simp [GGTPNClTag, GGTPNExcTag]
  have hBig : p ^ 3 ≤ Nat.card A := tne_big_three hd
  rcases htag with h | h | h | h | h | h | h
  · have hx : (⟨t, r, nn⟩ : LargeEvenLabel).tag = .triD4 := h
    refine tne_false_of_bound (p := p) (k := 3)
      (S := fun lab => lab.tag = .triD4 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1))
      (ggInndiag_pRank_le_two_triD4 (X := X) hp) hd hBig hΛX hhX ?_
    intro lab' _ hiso hhalf
    refine ⟨(tne_labelIso_tag_eq hiso (Or.inl hx)).trans hx, ?_⟩
    exact tne_halfSplit_dvd (Or.inl ((tne_labelIso_tag_eq hiso (Or.inl hx)).trans hx)) hhalf
  · have hx : (⟨t, r, nn⟩ : LargeEvenLabel).tag = .G2 := h
    refine tne_false_of_bound (p := p) (k := 3) (S := fun lab => lab.tag = .G2)
      (ggInndiag_pRank_le_two_G2 (X := X) hp hp2) hd hBig hΛX hhX ?_
    intro lab' _ hiso _
    exact (tne_labelIso_tag_eq hiso (Or.inr (Or.inl hx))).trans hx
  · have hx : (⟨t, r, nn⟩ : LargeEvenLabel).tag = .twB2 := h
    refine tne_false_of_bound (p := p) (k := 3) (S := fun lab => lab.tag = .twB2)
      (ggInndiag_pRank_le_two_twB2 (X := X) hp hp2) hd hBig hΛX hhX ?_
    intro lab' _ hiso _
    exact (tne_labelIso_tag_eq hiso (Or.inr (Or.inr (Or.inl hx)))).trans hx
  · have hx : (⟨t, r, nn⟩ : LargeEvenLabel).tag = .twF4 := h
    refine tne_false_of_bound (p := p) (k := 3)
      (S := fun lab => lab.tag = .twF4 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1))
      (ggInndiag_pRank_le_two_twF4 (X := X) hp hp2) hd hBig hΛX hhX ?_
    intro lab' _ hiso hhalf
    refine ⟨(tne_labelIso_tag_eq hiso (Or.inr (Or.inr (Or.inr (Or.inl hx))))).trans hx, ?_⟩
    exact tne_halfSplit_dvd
      (Or.inr ((tne_labelIso_tag_eq hiso
        (Or.inr (Or.inr (Or.inr (Or.inl hx))))).trans hx)) hhalf
  · have hx : (⟨t, r, nn⟩ : LargeEvenLabel).tag = .B2der := h
    refine tne_false_of_bound (p := p) (k := 3) (S := fun lab => lab.tag = .B2der)
      (ggInndiag_pRank_le_two_B2der (X := X) hp hp2) hd hBig hΛX hhX ?_
    intro lab' _ hiso _
    exact (tne_labelIso_tag_eq hiso (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))).trans hx
  · have hx : (⟨t, r, nn⟩ : LargeEvenLabel).tag = .G2der := h
    refine tne_false_of_bound (p := p) (k := 3) (S := fun lab => lab.tag = .G2der)
      (ggInndiag_pRank_le_two_G2der (X := X) hp hp2) hd hBig hΛX hhX ?_
    intro lab' _ hiso _
    exact (tne_labelIso_tag_eq hiso
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))))).trans hx
  · have hx : (⟨t, r, nn⟩ : LargeEvenLabel).tag = .twF4der := h
    refine tne_false_of_bound (p := p) (k := 3) (S := fun lab => lab.tag = .twF4der)
      (ggInndiag_pRank_le_two_twF4der (X := X) hp hp2) hd hBig hΛX hhX ?_
    intro lab' _ hiso _
    exact (tne_labelIso_tag_eq hiso
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))))).trans hx


theorem ggNonExcRK_holds
    (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : GGNonExcRK R := by
  intro p hp hp2 X _ _ A Ab σ J n hd _hk labJ labX hΛJ hΛX hQ hhJ hhX
  exact (ggNonExc_core hp hp2 hd hΛJ hΛX hQ.2.1 hQ.2.2 hhJ hhX).elim

end CFSG.StandardType

end
