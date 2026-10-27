module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_two_trans_til (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hconc : Conc4_136 D V₀ V hV L) (hs : s15 D.M V₀ V hV L = 1)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hperf : ⁅lBar V₀ V hV L, lBar V₀ V hV L⁆ = lBar V₀ V hV L)
    (hnot : (⊤ : Subgroup (Vtil V₀ V hV)) ∉ irrSet (lBar V₀ V hV L)) :
    ∀ I₁ ∈ irrSet (lBar V₀ V hV L), ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV, I₂ = I₁.map g.toMonoidHom := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hW : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hconc hs
  obtain ⟨t, -, -, -, -, hsup, hcomm, hcases⟩ := hconc
  rcases hcases with h1 | h2 | h3 | h4
  ·
    obtain ⟨p, hp, hle, -⟩ := h1
    have hpG : IsPGroup p ↥(pCoreOf p (Mbar D.M V₀ V hV)) :=
      (CFSG.pCore_isPGroup (p := p) (G := ↥(Mbar D.M V₀ V hV))).map
        (Mbar D.M V₀ V hV).subtype
    have hpL : IsPGroup p ↥(lBar V₀ V hV L) := hpG.to_le hle
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Group.IsPerfect ↥(lBar V₀ V hV L) :=
      (Subgroup.isPerfect_iff (H := lBar V₀ V hV L)).2 hperf
    haveI : Nontrivial ↥(lBar V₀ V hV L) := hsimple.toNontrivial
    exact False.elim ((Group.IsPerfect.not_isNilpotent ↥(lBar V₀ V hV L)) hpL.isNilpotent)
  ·
    obtain ⟨K, hK, g, hg, hne, hL, -⟩ := h2
    have hKgM : K.map (MulAut.conj g).toMonoidHom ≤ Mbar D.M V₀ V hV := by
      have hMbconj : (Mbar D.M V₀ V hV).map (MulAut.conj g).toMonoidHom =
          Mbar D.M V₀ V hV :=
        (Subgroup.mem_normalizer_iff_map_conj_eq (H := Mbar D.M V₀ V hV)).1
          (Subgroup.le_normalizer hg)
      rw [← hMbconj]
      exact Subgroup.map_mono hK.1
    have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := by
      rw [hL]
      exact sup_le hK.1 hKgM
    have hKLb : K ≤ lBar V₀ V hV L := by
      rw [hL]
      exact le_sup_left
    have hKgLb : K.map (MulAut.conj g).toMonoidHom ≤ lBar V₀ V hV L := by
      rw [hL]
      exact le_sup_right
    have hsub : CFSG.Open.IsSubnormal K (lBar V₀ V hV L) := by
      have h := CFSG.Open.IsSubnormal.inf_of_le hK.2.1 hLM
      rwa [inf_eq_left.2 hKLb] at h
    have hKne : K ≠ ⊥ := by
      haveI : Nontrivial (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2.toNontrivial
      exact (Subgroup.nontrivial_iff_ne_bot K).mp
        (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub hsimple with
      hbot | htop
    · exact absurd hbot hKne
    · have hKconj : K.map (MulAut.conj g).toMonoidHom = K := by
        refine Subgroup.eq_of_le_of_card_ge (htop.symm ▸ hKgLb) ?_
        rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective]
      exact False.elim (hne hKconj.symm)
  ·
    obtain ⟨-, -, hT⟩ := h3
    intro I₁ hI₁ I₂ hI₂
    obtain ⟨g, hg, hgI⟩ := hT I₁ hI₁ I₂ hI₂
    exact ⟨g, (Subgroup.mem_inf.1 hg).1, hgI⟩
  ·
    obtain ⟨h4mem, -⟩ := h4
    have h4' : wTil V₀ V hV L ∈ irrSet (lBar V₀ V hV L) := by
      simpa only [wTil, lBar] using h4mem
    rw [hW] at h4'
    exact False.elim (hnot h4')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
