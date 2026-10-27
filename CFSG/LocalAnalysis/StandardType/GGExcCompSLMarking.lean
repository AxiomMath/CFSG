module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLCat
public import CFSG.LocalAnalysis.StandardType.GGTorsionDatum
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestE6
public import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.LangRat

private theorem slh_markChar_eq_two {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    markChar lab = 2 := by
  rcases h with h | h | h | h <;> simp [markChar, h]

private theorem slh_markDeg_eq {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    markDeg lab = lab.n := by
  rcases h with h | h | h | h <;> simp [markDeg, h]

private theorem slh_markTag_eq {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    markTag lab = .E6 ∨ markTag lab = .twistedE6 ∨ markTag lab = .E7 ∨ markTag lab = .E8 := by
  rcases h with h | h | h | h <;> simp [markTag, h]

private theorem slh_markTag_mem_chevalleyExceptional {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    markTag lab ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
  rcases h with h | h | h | h <;>
    simp [markTag, CFSG.Blueprint.chevalleyExceptionalTags, h]

private theorem slh_inndiagComm_labelAll
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  rcases ht with h | h | h | h
  · exact largeEvenLabelAll_inndiagComm_E6 h
  · exact largeEvenLabelAll_inndiagComm_twE6 hlab h
  · exact largeEvenLabelAll_inndiagComm_proved hlab (by
      simp [GGInndiagCommProvedLabel, GGRecipeExcOutLabel, h])
  · exact largeEvenLabelAll_inndiagComm_proved hlab (by
      simp [GGInndiagCommProvedLabel, GGRecipeExcOutLabel, h])

private theorem slh_index_exc
    {G : Type} [Group G] {t : CFSG.Open.StatedLieTag} {p f : ℕ}
    (ht : t = .E6 ∨ t = .twistedE6 ∨ t = .E7 ∨ t = .E8)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel G t p f) :
    ∃ d : TauCeti.ValidLieTypeIndex,
      d.1.characteristic = p ∧
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = p ^ f ∧
      ((∃ q : TauCeti.PrimePower, d.1 = .E6 q) ∨
        (∃ q : TauCeti.PrimePower, d.1 = .E7 q) ∨
        (∃ q : TauCeti.PrimePower, d.1 = .E8 q) ∨
        (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q)) ∧
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  rcases ht with rfl | rfl | rfl | rfl
  · obtain ⟨hadm, hm⟩ := h
    have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.E6 q).Valid := by simp
    obtain ⟨b⟩ := hB.e6 q hv K (by rw [hK, hq])
    exact ⟨⟨TauCeti.LieTypeIndex.E6 q, hv⟩, by simp [q],
      by show q.card = p ^ f; rw [hq], Or.inl ⟨q, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨hadm, hm⟩ := h
    have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
    obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by simp
    obtain ⟨b⟩ := hB.twistedE6 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩, by simp [q],
      by show q.card = p ^ f; rw [hq], Or.inr (Or.inr (Or.inr ⟨q, rfl⟩)), ⟨e.trans b⟩⟩
  · obtain ⟨hadm, hm⟩ := h
    have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.E7 q).Valid := by simp
    obtain ⟨b⟩ := hB.e7 q hv K (by rw [hK, hq])
    exact ⟨⟨TauCeti.LieTypeIndex.E7 q, hv⟩, by simp [q],
      by show q.card = p ^ f; rw [hq], Or.inr (Or.inl ⟨q, rfl⟩), ⟨e.trans b⟩⟩
  · obtain ⟨hadm, hm⟩ := h
    have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (TauCeti.LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨b⟩ := hB.e8 q hv K (by rw [hK, hq])
    exact ⟨⟨TauCeti.LieTypeIndex.E8 q, hv⟩, by simp [q],
      by show q.card = p ^ f; rw [hq], Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)), ⟨e.trans b⟩⟩

theorem ggTorsion_exc_simplyLaced
    (hF : LangRatCompFieldLenSL)
    {P : LargeEvenLabel → Prop}
    (hP : ∀ lab, P lab → lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    {p : ℕ} {X : Type} [Group X] [Finite X] {δ : MulAut X} {J : Subgroup X}
    (hdat : GGTorsionDatum P p δ J) :
    LargeEvenMarking X fun lab _ _ _ _ _ => P lab ∧ GGCompFieldDataSL (2 ^ lab.n) J := by
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 := by
    obtain ⟨_, _, _, _, _, _, _, hP0, -⟩ := largeEvenRawDatum_exists hraw
    exact hP lab hP0
  have hrawMM : LargeEvenRawDatumLegacy lab
      (fun R _ I _ => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, P lab ∧ ggInducedAut θ δ ∈ I) ∧ MarkedModel lab R) :=
    largeEvenRawDatum_markedModel hlab
      (fun _ _ _ _ ⟨_, hna, _, _, _⟩ => hna) hraw
  have hraw' := (slh_inndiagComm_labelAll hlab htag) _ hrawMM
  obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, _, hδI⟩, hm⟩, hGuard⟩ :=
    largeEvenRawDatum_exists hraw'
  have hEq : GGInndiagCommEq R I F := hGuard hs hna
  let δbar : MulAut R := ggInducedAut θ δ
  have hδbar1 : δbar ≠ 1 := by
    intro h
    apply hδ1
    exact ggInducedAut_injective_of_perfect hXc θ (h.trans (map_one _).symm)
  have hδbarp : δbar ^ p = 1 := by
    dsimp [δbar]
    rw [← map_pow, hδp, map_one]
  have hβ : δbar ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived R := by
    have hmem : δbar ∈ ggInndiag R I := Subgroup.mem_sup_right (Subgroup.subset_closure hδI)
    have hmem2 : δbar ∈ ggInndiagComm R := by rw [← hEq]; exact hmem
    rwa [ggInndiagComm_eq_innAutDerived] at hmem2
  let Jbar : Subgroup R :=
    J.map ((θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X)))
  have hJbar : IsComponentOf Jbar (ggAutFixedSubgroup δbar) := by
    dsimp [Jbar, δbar]
    exact ggTorsion_isComponentOf_image θ hcomp
  have hC : CFSG.Open.IsComponentOf Jbar
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar) := by
    have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar =
        ggAutFixedSubgroup δbar := Subgroup.ext fun _ => Iff.rfl
    rw [hfix]
    exact isComponentOf_iff_open.mp hJbar
  have ht : markTag lab ∈ CFSG.Blueprint.chevalleyExceptionalTags :=
    slh_markTag_mem_chevalleyExceptional htag
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 lab.n := by
    have hm0 : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) (markChar lab)
        (markDeg lab) := hm
    have h := hm0.chevalleyExceptionalModel ht
    rw [slh_markChar_eq_two htag, slh_markDeg_eq htag] at h
    exact h
  obtain ⟨d, hdchar, hk, hd, he⟩ := slh_index_exc (slh_markTag_eq htag) hchev
  obtain ⟨e⟩ := he
  have hIcomp : CompLabSLAt p d.1 (TauCeti.CFSGIndex.lie d).Group :=
    compLabSL_cat_of_lang hF d hp hp2 hdchar hd
  have hIcomp' : CompLabSLAt p d.1 R := compLabSLAt_of_mulEquiv e.symm hIcomp
  obtain ⟨m, hm1, hfdJbar⟩ := hIcomp' δbar hβ hδbarp hδbar1 Jbar hC
  obtain ⟨eJ⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
  have hfdAt : GGCompFieldAtSL ((2 ^ lab.n) ^ m) J := by
    rw [← hk]
    exact GGCompFieldAtSL.of_centerQuotEquiv eJ.symm hfdJbar
  have hfd : GGCompFieldDataSL (2 ^ lab.n) J := ⟨m, hm1, hfdAt⟩
  refine ⟨hXc, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R' _ I' F' ⟨hs', hna', θ', hPlab', _⟩
  exact ⟨hs', hna', θ', hPlab', hfd⟩

end CFSG.StandardType
