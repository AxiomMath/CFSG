module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RLiftAbs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_of_Lstar {M V₀ V Lst : Subgroup G} {hV : IsElemAbelian 2 V}
    (hMs : M ≤ stabTil V₀ V) {q : ℕ} (hq : q.Prime) (hLM : Lst ≤ M)
    (hLn : M ≤ normalizer (Lst : Set G)) (hLC : ¬ q ∣ Nat.card ↥(Lst ⊓ F11.CTilde M V₀ V))
    {a : MulAut (Vtil V₀ V hV)} {E : Subgroup (MulAut (Vtil V₀ V hV))} (haE : a ∈ E)
    (haM : a ∈ Mbar M V₀ V hV) (hEle : E ≤ barSub V₀ V hV Lst ⊔ Subgroup.zpowers a)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ q = 1)
    (hcard : Nat.card E = q ^ 3) : 3 ≤ CFSG.Open.pRank q M := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let π : ↥M →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hMs)
  have hLn' : (Lst.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hLn
  have hker : ∀ x : ↥M, x ∈ π.ker ↔ (x : G) ∈ F11.CTilde M V₀ V := by
    intro x
    rw [mem_cTilde_iff hV (hMs.trans (stabTil_le_normalizer V₀ V))]
    exact ⟨fun h => ⟨x.2, hMs x.2, h⟩, fun h => h.2.2⟩
  have hLCπ : ¬ q ∣ Nat.card ↥(Lst.subgroupOf M ⊓ π.ker) := by
    have heq : (Lst.subgroupOf M ⊓ π.ker).map M.subtype = Lst ⊓ F11.CTilde M V₀ V := by
      ext x
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        exact ⟨hy1, (hker y).1 hy2⟩
      · rintro ⟨hx1, hx2⟩
        have hxM : x ∈ M := hLM hx1
        exact ⟨⟨x, hxM⟩, ⟨hx1, (hker ⟨x, hxM⟩).2 hx2⟩, rfl⟩
    have hcardeq : Nat.card ↥(Lst.subgroupOf M ⊓ π.ker) = Nat.card ↥(Lst ⊓ F11.CTilde M V₀ V) := by
      rw [← heq]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).toEquiv)
    rw [hcardeq]
    exact hLC
  have hmapπ : (Lst.subgroupOf M).map π = barSub V₀ V hV Lst := by
    ext φ
    rw [mem_barSub]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hMs x.2⟩, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.1, hLM hg⟩, hg, rfl⟩
  obtain ⟨g, hgM, hga⟩ := (mem_barSub V₀ V hV M a).1 haM
  have hπa : π ⟨g.1, hgM⟩ = a := hga
  have hE' : IsElemAbelian q E := ⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, hexp⟩
  obtain ⟨F, hF, hFcard⟩ := exists_isElemAbelian_card_eq_of_lift π hLn' hq hLCπ ⟨g.1, hgM⟩ hE'
    (by rw [hπa]; exact haE) (by rw [hmapπ, hπa]; exact hEle)
  rw [hcard] at hFcard
  obtain ⟨hFc, hFp⟩ := hF
  have hι : Function.Injective (M.subtype.comp F.subtype) :=
    M.subtype_injective.comp F.subtype_injective
  refine CFSG.SectionRank.le_pRank_of_injective (p := q) hq.one_lt (fun x y => ?_)
    (fun x => Subtype.ext (hFp x.1 x.2)) hFcard (M.subtype.comp F.subtype) hι ?_
  · exact hFc.is_comm.comm x y
  · rintro _ ⟨x, rfl⟩
    exact x.1.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
