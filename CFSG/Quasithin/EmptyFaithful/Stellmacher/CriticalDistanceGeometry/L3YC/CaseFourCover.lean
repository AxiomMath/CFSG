module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.NaturalCover
public import CFSG.Quasithin.MS93.ASC134
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.QChar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

theorem comm_self_of_case4Corr {G₀ R L : Subgroup G} (h : MS93.IsC134Case4Corr G₀ R L) :
    ⁅c134Q G₀ L, L⁆ = c134Q G₀ L := by
  obtain ⟨⟨n, F, iF, iFin, α, hF, hα, hE, hZc, hCU, hU, hΦ, hK, hQ⟩, -⟩ := h
  set Q := c134Q G₀ L with hQdef
  set P := frattiniIn Q with hPdef
  have h1 := commutator_sup_eq hα.1 hQ
  have h2 := commutator_sup_eq hα.1 hK
  have hQL : ⁅Q, L⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.mp hQ.1
  have hPQ : P ≤ Q := Subgroup.map_subtype_le _
  have hsup : ⁅Q, L⁆ ⊔ P = Q := by
    refine le_antisymm (sup_le hQL hPQ) ?_
    calc Q = ⁅Q, L⁆ ⊔ (Q ⊓ Subgroup.centralizer (P : Set G)) := h1.symm
      _ ≤ ⁅Q, L⁆ ⊔ P := by
        refine sup_le le_sup_left ?_
        calc Q ⊓ Subgroup.centralizer (P : Set G)
            = ⁅Q ⊓ Subgroup.centralizer (P : Set G), L⁆ ⊔ P := h2.symm
          _ ≤ ⁅Q, L⁆ ⊔ P :=
            sup_le ((Subgroup.commutator_mono inf_le_left le_rfl).trans le_sup_left) le_sup_right
  have htop : (⁅Q, L⁆).subgroupOf Q ⊔ frattini ↥Q = ⊤ := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQL, Subgroup.map_top,
      Subgroup.range_subtype]
    exact hsup
  have hall := frattini_nongenerating htop
  exact le_antisymm hQL (Subgroup.subgroupOf_eq_top.mp hall)

theorem normalizer_le_normalizer_c134CQ_of_case4 {L S : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (h : MS93.IsC134Case4Corr (L ⊔ S) S L) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (c134CQ (L ⊔ S) L : Set G) :=
  normalizer_le_normalizer_c134CQ (c134Q_eq_of_comm_self hSL (comm_self_of_case4Corr h))

omit [Finite G] in
theorem conj_not_mem_normalizer {L Vc Vn : Subgroup G} {t' y' : G}
    (hN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Vc : Set G))
    (hconj : Vc.map (MulAut.conj t').toMonoidHom = Vn)
    (hy : y' ∉ Subgroup.normalizer (Vn : Set G)) :
    t'⁻¹ * y' * t' ∉ Subgroup.normalizer (L : Set G) := by
  intro hmem
  apply hy
  have hVc := Subgroup.mem_normalizer_iff.mp (hN hmem)
  have hmemVn : ∀ x : G, x ∈ Vn ↔ t'⁻¹ * x * t' ∈ Vc := by
    intro x
    rw [← hconj]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have e : t'⁻¹ * (t' * v * t'⁻¹) * t' = v := by group
      show t'⁻¹ * (t' * v * t'⁻¹) * t' ∈ Vc
      rw [e]
      exact hv
    · intro hx
      exact ⟨t'⁻¹ * x * t', hx, by simp [MulAut.conj_apply]; group⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hmemVn x, hmemVn (y' * x * y'⁻¹)]
  have e : t'⁻¹ * (y' * x * y'⁻¹) * t' =
      (t'⁻¹ * y' * t') * (t'⁻¹ * x * t') * (t'⁻¹ * y' * t')⁻¹ := by group
  rw [e]
  exact hVc (t'⁻¹ * x * t')

end Stellmacher.CD.L3YC

end CFSG.Quasithin
