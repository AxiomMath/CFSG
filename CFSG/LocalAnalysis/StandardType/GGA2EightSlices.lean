module

public import CFSG.LocalAnalysis.StandardType.GGA2EightDefs
public import CFSG.LocalAnalysis.StandardType.GGA2EightCentJ
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUKacCentJ
public import CFSG.LocalAnalysis.StandardType.GGMultValidClQs
public import CFSG.LocalAnalysis.StandardType.GGTPNClGen
public import CFSG.LocalAnalysis.StandardType.GGExcCentred
public import CFSG.LocalAnalysis.StandardType.GGTPNNonExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem a2s_regime_not_rankOne (p n : ℕ) (labJ labX : LargeEvenLabel)
    (h : GGRegimeA2Eight p n labJ labX) (lab : LargeEvenLabel) (hiso : GGLabelIso lab labJ) :
    ¬ GGTPNPRankOne p lab := by
  obtain ⟨rfl, rfl⟩ := h
  intro hrk
  simp only [GGLabelIso] at hiso
  simp only [GGTPNPRankOne] at hrk
  rcases hiso with rfl | ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · rcases hrk with ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨h1, -⟩
    · exact absurd h2 (by decide)
    · exact absurd h1 (by decide)
    · norm_num at h3
    · exact absurd h1 (by decide)
  all_goals simp at h

private theorem a2s_centJ {X : Type} [Group X] [Finite X] {p n : ℕ}
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    {labJ labX : LargeEvenLabel}
    (hd : GGTPNDatumB p n (fun _ _ => True) A Ab σ J)
    (hR : GGRegimeA2Eight p n labJ labX)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) : GGCentJRank p X J := by
  have hp7 : p = 7 := hR.1
  have hl : labJ = ⟨.A, 2, 3⟩ := hR.2
  have hd7 : GGTPNBasicB 7 n (fun _ _ => True) A Ab σ J := by simpa [hp7] using hd.1
  have hhJ' : GGHasLabel ⟨.A, 2, 3⟩ (↥J ⧸ Subgroup.center ↥J) := by simpa [hl] using hhJ
  simpa [hp7] using ggCentJRank_a2Eight hd7 hhJ'

theorem ggA2EightClGen_holds :
    GGTablePKnownR fun p n labJ labX => GGRegimeA2Eight p n labJ labX ∧ GGKacGenericCl labX p := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hR hhJ hhX
  obtain ⟨hRreg, hgen⟩ := hR
  obtain ⟨hloc, hflat, hcard, hrank, hnum, hself, honly, hm⟩ := hd.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hK0 : GGK0MainB GGKacGenericCl GGMultValidCl := ggK0MainBS_cl.toB
  have hS : GGK0Schur GGKacGenericCl := ggK0Schur_cl
  have hcent : GGCentJRank p X J := a2s_centJ hd hRreg hhJ
  have hp7 : p = 7 := hRreg.1
  have hqsAll : ∀ (lab : LargeEvenLabel) (D : GGKacDatum), LargeEvenInLambda2 lab →
      GGKacGenericCl lab p → GGMultValidCl lab p D → ∀ o ∈ D.orbits, o.qs = true :=
    fun _ _ _ _ hD => ggMultValidCl_qs_true hp (by omega) hD
  have hperf : commutator X = ⊤ := by
    have hm0 := hm
    unfold GGTPNMarked at hm0
    exact hm0.1
  have hm' : GGTPNMarked p (fun q lab => ∃ c : Prop, LargeEvenHalfSplit q lab c) A := by
    obtain ⟨hX, lab, hlab, hraw⟩ := hm
    exact ⟨hX, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, h1, h2, h3⟩ => ⟨hs, hna, θ, ⟨_, h2⟩, h2, h3⟩) hraw⟩
  obtain ⟨-, labm, hΛm, hrawm⟩ := hm
  have hmHas : GGHasLabel labm (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hrawm
  obtain ⟨Rm, xm, Im, Fm, hQm⟩ := largeEvenRawDatum_exists hrawm
  obtain ⟨-, -, θm, -, hhalfm, -⟩ := hQm
  have hisom : GGLabelIso labm labX :=
    hrig labm labX (X ⧸ Subgroup.center X) hΛm hΛX hmHas hhX
  have hgen' : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (X ⧸ Subgroup.center X) →
      GGKacGenericCl lab p := by
    intro lab hlab hhas
    have hiso : GGLabelIso lab labX :=
      hrig lab labX (X ⧸ Subgroup.center X) hlab hΛX hhas hhX
    have hfix : lab = ⟨.twD, 2, lab.n⟩ → labX = ⟨.A, 1, 2 * lab.n⟩ →
        p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
      intro _ h2
      exact cgen_dvd_sub_or_add_of_dvd_sq_sub_one hp
        (cgen_dvd_two_pow_of_halfSplit_iso_A1 hΛm hhalfm (h2 ▸ hisom))
    exact cgen_genericCl_of_ggLabelIso hlab hiso hgen hfix
  obtain ⟨lab, hΛlab, hSlab, -, hXlab, D, hD, hrZ, -, o, hDo, hqso, -, hoΛ, hJo⟩ :=
    exists_ggKacDatum_of_ggK0MainB_centJ hK0 hS hqsAll hloc hcent honly hm' hgen'
  obtain ⟨c, hc⟩ := hSlab
  have hEq : GGLabelIso o.lab labJ :=
    hrig o.lab labJ (↥J ⧸ Subgroup.center ↥J) hoΛ hΛJ hJo hhJ
  have hrk : ¬ GGTPNPRankOne p o.lab := a2s_regime_not_rankOne p n labJ labX hRreg o.lab hEq
  have hXnot : ¬ GGLabelIso o.lab lab := by
    intro hiso
    exact not_ggHasLabel_of_le_ggAutFixedSubgroup hperf hloc.2.2.1 hloc.2.2.2.1.1 hXlab
      (largeEvenRawDatum_of_ggLabelIso hiso hJo)
  obtain ⟨-, labJ', labX', hiso1, hiso2, hΛJ', hΛX', hrow⟩ :=
    ggTablePRow_of_ggMultValidCl hΛlab hc hD hrZ hDo hqso hXnot hrk
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    largeEvenRawDatum_of_ggLabelIso hiso1 hJo,
    largeEvenRawDatum_of_ggLabelIso hiso2 hXlab⟩

theorem ggA2EightExcPair_holds
    (hB3 : GGK0ExcB3) : GGA2EightExcPair := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hR hhJ hhX
  obtain ⟨hRreg, hpair⟩ := hR
  obtain ⟨hloc, hflat, hcard, hrank, hnum, hself, honly, hm⟩ := hd.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hK0 : GGK0MainB GGKacExcQuasi GGKacValid := (ggK0MainBS_quasi_of_B3 hB3).toB
  have hS : GGK0Schur GGKacExcQuasi := ggK0Schur_excPair.mono fun _ _ h => h.1
  have hcent : GGCentJRank p X J := a2s_centJ hd hRreg hhJ
  have hp7 : p = 7 := hRreg.1
  have hquasi : GGKacExcQuasi labX p := by
    refine ⟨⟨hpair, ?_⟩, ?_⟩
    · rintro ⟨-, hp3⟩; omega
    · rintro ⟨-, hp3⟩; omega
  have htagX : labX.tag = .E6 ∨ labX.tag = .twE6 ∨ labX.tag = .E7 ∨ labX.tag = .E8 ∨
      labX.tag = .F4 := hpair.2.2.2
  have hperf : commutator X = ⊤ := by
    have hm0 := hm
    unfold GGTPNMarked at hm0
    exact hm0.1
  have hqsAll : ∀ (lab : LargeEvenLabel) (D : GGKacDatum), LargeEvenInLambda2 lab →
      GGKacExcQuasi lab p → GGKacValid lab p D → ∀ o ∈ D.orbits, o.qs = true := by
    intro lab D hlab hquasiD hD o ho
    by_contra hqs
    have hfalse : o.qs = false := by cases hq : o.qs <;> simp_all
    obtain ⟨hn1, hp3⟩ :=
      ggKacValid_qs_false_p3 hlab.1 hquasiD.1.1.1 hquasiD.1.1.2.2.1 hD ho hfalse
    exact hquasiD.2 ⟨hn1, hp3⟩
  have hgen' : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (X ⧸ Subgroup.center X) →
      GGKacExcQuasi lab p := by
    intro lab hlab hhas
    have hiso : GGLabelIso lab labX :=
      hrig lab labX (X ⧸ Subgroup.center X) hlab hΛX hhas hhX
    rw [excg_labelIso_eq_of_exc hiso htagX]
    exact hquasi
  obtain ⟨lab, hΛlab, -, hgenlab, hXlab, D, hD, hrZ, -, o, hDo, hqso, -, hoΛ, hJo⟩ :=
    exists_ggKacDatum_of_ggK0MainB_centJ hK0 hS hqsAll hloc hcent honly hm hgen'
  have hXnot : ¬ GGLabelIso o.lab lab := by
    intro hiso
    exact not_ggHasLabel_of_le_ggAutFixedSubgroup hperf hloc.2.2.1 hloc.2.2.2.1.1 hXlab
      (largeEvenRawDatum_of_ggLabelIso hiso hJo)
  have hne : o.lab ≠ lab := fun h => hXnot (Or.inl h)
  have hrow : GGTablePRow p o.lab lab :=
    (ggTablePRow_of_ggKacValid_centred hΛlab hgenlab.1 hD hrZ hDo hne).2
  exact ⟨o.lab, lab, hoΛ, hΛlab, hrow, hJo, hXlab⟩

theorem ggA2EightNonExc_holds :
    GGA2EightNonExc := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hQ hhJ hhX
  exfalso
  obtain ⟨-, hnotcl, hnotex⟩ := hQ
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

end CFSG.StandardType

end
