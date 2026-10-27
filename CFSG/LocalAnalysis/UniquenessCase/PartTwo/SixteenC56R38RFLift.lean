module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RLiftAbs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_isElemAbelian_map_eq_of_Lstar {M V₀ V Lst : Subgroup G} {hV : IsElemAbelian 2 V}
    (hMs : M ≤ stabTil V₀ V) {q : ℕ} (hq : q.Prime) (hLM : Lst ≤ M)
    (hLn : M ≤ normalizer (Lst : Set G)) (hLC : ¬ q ∣ Nat.card ↥(Lst ⊓ F11.CTilde M V₀ V))
    {a : ↥M} (haq : a ^ q = 1) (hnot : barHom V₀ V hV hMs a ∉ barSub V₀ V hV Lst)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hE : IsElemAbelian q E)
    (haE : barHom V₀ V hV hMs a ∈ E)
    (hEle : E ≤ barSub V₀ V hV Lst ⊔ Subgroup.zpowers (barHom V₀ V hV hMs a)) :
    ∃ F : Subgroup ↥M, IsElemAbelian q F ∧ a ∈ F ∧ F ⊓ (barHom V₀ V hV hMs).ker = ⊥ ∧
      F.map (barHom V₀ V hV hMs) = E := by
  classical
  have hMn : M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hLn' : (Lst.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hLn
  have hker : ∀ x : ↥M, x ∈ (barHom V₀ V hV hMs).ker ↔ (x : G) ∈ F11.CTilde M V₀ V := by
    intro x
    rw [ker_barHom V₀ V hV hMn hMs, Subgroup.mem_subgroupOf]
  have hLCπ : ¬ q ∣ Nat.card ↥(Lst.subgroupOf M ⊓ (barHom V₀ V hV hMs).ker) := by
    have heq : (Lst.subgroupOf M ⊓ (barHom V₀ V hV hMs).ker).map M.subtype =
        Lst ⊓ F11.CTilde M V₀ V := by
      ext x
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        exact ⟨hy1, (hker y).1 hy2⟩
      · rintro ⟨hx1, hx2⟩
        have hxM : x ∈ M := hLM hx1
        exact ⟨⟨x, hxM⟩, ⟨hx1, (hker ⟨x, hxM⟩).2 hx2⟩, rfl⟩
    have hcardeq : Nat.card ↥(Lst.subgroupOf M ⊓ (barHom V₀ V hV hMs).ker) =
        Nat.card ↥(Lst ⊓ F11.CTilde M V₀ V) := by
      rw [← heq]
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).toEquiv)
    rw [hcardeq]
    exact hLC
  have hmapπ : (Lst.subgroupOf M).map (barHom V₀ V hV hMs) = barSub V₀ V hV Lst := by
    ext φ
    rw [mem_barSub]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hMs x.2⟩, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.1, hLM hg⟩, hg, rfl⟩
  exact exists_isElemAbelian_map_eq_of_lift (barHom V₀ V hV hMs) hLn' hq hLCπ haq
    (by rw [hmapπ]; exact hnot) hE haE (by rw [hmapπ]; exact hEle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
