module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4Regimes
public import CFSG.LocalAnalysis.StandardType.GGInnerD4NoD4Table
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltrd4e_datum
    (hB : GGK0ExcB)
    {L : Type} [Group L] [Finite L] {J : Subgroup L} {y : MulAut L}
    {E : Subgroup (MulAut L)} {labL : LargeEvenLabel}
    (hΛL : LargeEvenInLambda2 labL)
    (hpairKac : GGKacExcPair labL 3) (hperfL : commutator L = ⊤)
    (hraw : LargeEvenRawDatum labL (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : L ⧸ Subgroup.center L ≃* R, GGInducedInn E θ I))
    (hyE : y ∈ E) (hy3 : y ^ 3 = 1)
    (hcomp : IsComponentOf J (ggAutFixedSubgroup y)) :
    ∃ D : GGKacDatum, GGKacValid labL 3 D ∧ ∃ o ∈ D.orbits,
      LargeEvenInLambda2 o.lab ∧ GGHasLabel o.lab (J ⧸ Subgroup.center J) := by
  have hmain := hB 3 labL hΛL hpairKac _ hraw
  obtain ⟨R, hRgrp, I, F, hQR⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨hsimple, hna, θ, hInd⟩ := hQR.1
  let ψ : L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
    refine ⟨l, ?_⟩
    show θ (QuotientGroup.mk' (Subgroup.center L) l) = r
    rw [hl]
    exact hq
  have hker_le : ψ.ker ≤ Subgroup.center L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have hl' : θ (QuotientGroup.mk' (Subgroup.center L) l) = 1 := by simpa [ψ] using hl
    have hl'' : QuotientGroup.mk' (Subgroup.center L) l = 1 :=
      θ.injective (by simpa using hl')
    exact (QuotientGroup.eq_one_iff l).mp hl''
  have hfixsub : ggFixSub y = ggAutFixedSubgroup y := by ext l; rfl
  have hcomp' : IsComponentOf J (ggFixSub y) := by rw [hfixsub]; exact hcomp
  have hφ_apply : ∀ l : L, ggInducedAut θ y (ψ l) = ψ (y l) := by
    intro l
    change ggInducedAut θ y (θ (l : L ⧸ Subgroup.center L)) =
      θ ((y l : L) : L ⧸ Subgroup.center L)
    exact ggInducedAut_apply θ y l
  have hφ_mem : ggInducedAut θ y ∈ I := hInd y hyE
  obtain ⟨D, hDval, ha, -⟩ :=
    hQR.2 L ψ hψ hker_le hperfL y hy3 ⟨ggInducedAut θ y, hφ_mem, hφ_apply⟩
  obtain ⟨o, ho, hqs, hdvd, hΛo, hHasO⟩ := ha J hcomp'
  exact ⟨D, hDval, o, ho, hΛo, hHasO⟩

private theorem ltrd4e_iso_eq {o_lab labJ : LargeEvenLabel}
    (htag : labJ.tag = .D) (hrk : labJ.rank = 4) (hiso : GGLabelIso o_lab labJ) :
    o_lab = labJ := by
  obtain ⟨t, r, n⟩ := labJ
  have ht : t = .D := by simpa using htag
  have hr : r = 4 := by simpa using hrk
  subst ht
  subst hr
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h <;> simp_all

private theorem ltrd4e_typeOfLabel {lab : LargeEvenLabel} {T : GGKacType} {tw : Bool}
    (h : ggKacTypeOfLabel lab = some (T, tw))
    (hS : lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    (T = .F4 ∧ tw = false) ∨ (T = .E7 ∧ tw = false) ∨ (T = .E8 ∧ tw = false) := by
  obtain ⟨tag, rank, n⟩ := lab
  have htag : tag = .F4 ∨ tag = .E7 ∨ tag = .E8 := by simpa using hS
  rcases htag with rfl | rfl | rfl
  · left; simpa [ggKacTypeOfLabel] using h.symm
  · right; left; simpa [ggKacTypeOfLabel] using h.symm
  · right; right; simpa [ggKacTypeOfLabel] using h.symm

private theorem ltrd4e_exc
    (hB : GGK0ExcB) :
    GGInnerOnD4On fun lab => lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8 := by
  intro X _ _ A σ J hA hσ hJ hN hmark labJ hΛJ htag hrk hlab a ha
  exfalso
  obtain ⟨hX, lab', hΛlab', hrawS⟩ := hmark
  have hraw : LargeEvenRawDatum lab' (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, GGInducedInn A θ I) :=
    largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, -, hInd⟩ := h
      exact ⟨hs, hna, θ, hInd⟩) hrawS
  have hS : lab'.tag = .F4 ∨ lab'.tag = .E7 ∨ lab'.tag = .E8 := by
    obtain ⟨R₀, _, I₀, F₀, hQR₀⟩ := largeEvenRawDatum_exists hrawS
    obtain ⟨-, -, -, hS, -⟩ := hQR₀
    exact hS
  have hpairKac : GGKacExcPair lab' 3 :=
    ⟨by norm_num, by norm_num, s2_1586_three_dvd lab'.n, by
      rcases hS with h | h | h <;> rw [h]
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  have hσ3 : σ ^ 3 = 1 := hA.2 σ hσ
  obtain ⟨D, hDval, o, ho, hΛo, hHasO⟩ :=
    ltrd4e_datum hB hΛlab' hpairKac hX hraw hσ hσ3 hJ
  have hiso : GGLabelIso o.lab labJ :=
    ggLabelRigidInput_holds o.lab labJ (J ⧸ Subgroup.center J) hΛo hΛJ hHasO hlab
  have hoeq : o.lab = labJ := ltrd4e_iso_eq htag hrk hiso
  obtain ⟨T, tw, hTtw, hDmem⟩ := hDval
  have hn : 1 ≤ lab'.n := hΛlab'.1
  obtain ⟨hTeq, htw⟩ | ⟨hTeq, htw⟩ | ⟨hTeq, htw⟩ := ltrd4e_typeOfLabel hTtw hS
  · subst hTeq; subst htw
    exact s2_1586_no_D4 .F4 (Or.inl rfl) lab'.n hn D hDmem o ho
      ⟨by rw [hoeq]; exact htag, by rw [hoeq]; exact hrk⟩
  · subst hTeq; subst htw
    exact s2_1586_no_D4 .E7 (Or.inr (Or.inl rfl)) lab'.n hn D hDmem o ho
      ⟨by rw [hoeq]; exact htag, by rw [hoeq]; exact hrk⟩
  · subst hTeq; subst htw
    exact s2_1586_no_D4 .E8 (Or.inr (Or.inr rfl)) lab'.n hn D hDmem o ho
      ⟨by rw [hoeq]; exact htag, by rw [hoeq]; exact hrk⟩

theorem ggInnerOnD4_tagF4
    (hB : GGK0ExcB) : GGInnerOnD4On fun lab => lab.tag = .F4 :=
  GGInnerOnD4On.mono (fun lab h => Or.inl h) (ltrd4e_exc hB)

theorem ggInnerOnD4_tagE7
    (hB : GGK0ExcB) : GGInnerOnD4On fun lab => lab.tag = .E7 :=
  GGInnerOnD4On.mono (fun lab h => Or.inr (Or.inl h)) (ltrd4e_exc hB)

theorem ggInnerOnD4_tagE8
    (hB : GGK0ExcB) : GGInnerOnD4On fun lab => lab.tag = .E8 :=
  GGInnerOnD4On.mono (fun lab h => Or.inr (Or.inr h)) (ltrd4e_exc hB)

end CFSG.StandardType

end
