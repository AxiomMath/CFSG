module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA1BAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA1BAB
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16h_sl28_ra1ba_barSub_sup (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {X₁ X₂ : Subgroup G} (h₁ : X₁ ≤ stabTil V₀ V) (h₂ : X₂ ≤ stabTil V₀ V) :
    barSub V₀ V hV (X₁ ⊔ X₂) = barSub V₀ V hV X₁ ⊔ barSub V₀ V hV X₂ := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

private theorem s16h_sl28_not_isCyclic_of_isElemAbelian_seven {X : Type} [Group X]
    {E : Subgroup X} (hE : IsElemAbelian 7 E) (hcard : 7 ^ 2 ≤ Nat.card E) :
    ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ 7 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
  rw [hg] at h1
  have h2 := Nat.le_of_dvd (by norm_num : 0 < 7) h1
  nlinarith

private theorem s16h_sl28_isCyclic_of_map_subtype {S : Type*} [Group S] {H : Subgroup S}
    {P : Subgroup H} (hc : IsCyclic ↥(P.map H.subtype)) : IsCyclic ↥P :=
  isCyclic_of_surjective
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).symm.toMonoidHom
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).symm.surjective

theorem s16h_sl28_seven_sup_pRank_two
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    2 ≤ CFSG.Open.pRank 7 (L ⊔ conjSubgroup L x) := by
  have hV := h.hyp151.isElemAbelian
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
    exact s16h_sl28_eight_simple_of_isSLn_two_three hrow.1
  have h7A : 7 ∣ Nat.card ↥A := by
    rw [hA]
    exact s16h_sl28_eight_seven_dvd_card_of_isSLn_two_three hrow.1
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
    s16h_sl28_join_elemAbelian_seven hAsimp hcardAB hBA hcommAB h7A
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
    exact s16h_sl28_ra1ba_barSub_sup ⊥ V hV hLst hLxst
  have hE_range : E ≤ φ.range := by
    rw [hrange, hbar]
    exact hEAB
  have hEnc : ¬ IsCyclic ↥E :=
    s16h_sl28_not_isCyclic_of_isElemAbelian_seven hEab (by rw [hEcard])
  obtain ⟨S, hS7, hSnc⟩ :=
    s16h_exists_noncyclic_of_le_range φ Nat.prime_seven hE_range hEab.isPGroup hEnc
  have hSncmap : ¬ IsCyclic ↥(S.map H.subtype) := fun hc =>
    hSnc (s16h_sl28_isCyclic_of_map_subtype hc)
  have h2 := uc22p22u_two_le_pRank Nat.prime_seven (by norm_num) (hS7.map H.subtype) hSncmap
  have hle := CFSG.SectionRank.pRank_mono (p := 7) (by norm_num) (Subgroup.map_subtype_le S)
  exact le_trans h2 (by simpa [hH] using hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
