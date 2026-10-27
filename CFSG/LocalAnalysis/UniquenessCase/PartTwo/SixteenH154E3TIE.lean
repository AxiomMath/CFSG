module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3TIEA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3TIEB
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_sup_pRank_two (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hsimple : IsSimpleGroup ↥(lBar ⊥ V h.hyp151.isElemAbelian L))
    (hqL : q ∣ Nat.card ↥(lBar ⊥ V h.hyp151.isElemAbelian L)) :
    2 ≤ CFSG.Open.pRank q (L ⊔ conjSubgroup L x) := by
  by_cases hq2' : q = 2
  · exact absurd hq2' hq2
  · have hV := h.hyp151.isElemAbelian
    have h125 := h.hyp151.hyp125
    have hMs : D.M ≤ stabTil ⊥ V :=
      le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
    have hLst : L ≤ stabTil ⊥ V := h.hyp151.le.trans hMs
    have hLxM : conjSubgroup L x ≤ D.M := by
      intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ D.M :=
        D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) (h.hyp151.le hy)) hxM
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y from by group] at hy'
    have hLxst : conjSubgroup L x ≤ stabTil ⊥ V := hLxM.trans hMs
    set A : Subgroup (MulAut (Vtil ⊥ V hV)) := lBar ⊥ V hV L with hA
    set B : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV (conjSubgroup L x) with hB
    have hAsimp : IsSimpleGroup ↥A := by
      rw [hA]
      exact hsimple
    have hqA : q ∣ Nat.card ↥A := by
      rw [hA]
      exact hqL
    have hBmap : B = A.map (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹).toMonoidHom := by
      rw [hB, hA, lBar]
      exact s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L
    have hcardAB : Nat.card ↥A = Nat.card ↥B := by
      rw [hBmap, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    have hBA : B ≠ A := by
      intro hEq
      exact hxn ((s15_Infra_mem_nBar_iff h125 hV hxM).2 (by simpa [hA, hB, lBar] using hEq))
    have hcommAB : ⁅A, B⁆ = ⊥ := by
      have hc := (h.hyp151.commute x hxM hxn).1
      simpa [hA, hB, lBar] using hc
    obtain ⟨E, hEAB, hEab, hEcard⟩ :=
      s16h_join_elemAbelian_of_prime hq hAsimp hcardAB hBA hcommAB hqA
    set H : Subgroup G := L ⊔ conjSubgroup L x with hH
    have hHst : H ≤ stabTil ⊥ V := sup_le hLst hLxst
    let φ : ↥H →* MulAut (Vtil ⊥ V hV) :=
      (actTil ⊥ V hV).comp (Subgroup.inclusion hHst)
    have hrange : φ.range = barSub ⊥ V hV H := by
      ext e
      constructor
      · rintro ⟨g, rfl⟩
        exact actTil_mem_barSub ⊥ V hV g.2 (hHst g.2)
      · intro he
        obtain ⟨g, hgH, hge⟩ := (mem_barSub ⊥ V hV H e).1 he
        refine ⟨⟨(g : G), hgH⟩, ?_⟩
        show actTil ⊥ V hV ⟨(g : G), hHst hgH⟩ = e
        rw [show (⟨(g : G), hHst hgH⟩ : ↥(stabTil ⊥ V)) = g from Subtype.ext rfl]
        exact hge
    have hbar : barSub ⊥ V hV H = A ⊔ B := by
      rw [hH, hA, hB, lBar]
      exact s16h_ra1b_barSub_sup ⊥ V hV hLst hLxst
    have hE_range : E ≤ φ.range := by
      rw [hrange, hbar]
      exact hEAB
    have hEnc : ¬ IsCyclic ↥E :=
      s16h_not_isCyclic_of_isElemAbelian_sq hq hEab (by rw [hEcard])
    obtain ⟨S, hSq, hSnc⟩ :=
      s16h_exists_noncyclic_of_le_range φ hq hE_range hEab.isPGroup hEnc
    have hSncmap : ¬ IsCyclic ↥(S.map H.subtype) := fun hc =>
      hSnc (s16h_isCyclic_of_map_subtype hc)
    have h2 := uc22p22u_two_le_pRank hq hq2 (hSq.map H.subtype) hSncmap
    have hle := CFSG.SectionRank.pRank_mono (p := q) hq.one_lt (Subgroup.map_subtype_le S)
    exact le_trans h2 (by simpa [hH] using hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
