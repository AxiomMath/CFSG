module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Poly
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Lay

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431 CFSG.Quasithin.H13.F45Ru

theorem encard_neighborSet_smul' {V : Type*} {H : Type*} [Group H] [MulAction H V]
    {Γ : SimpleGraph V} [GraphAction H Γ] (g : H) (v : V) :
    (Γ.neighborSet (g • v)).encard = (Γ.neighborSet v).encard := by
  have : Γ.neighborSet (g • v) = (fun w : V => g • w) '' Γ.neighborSet v := by
    ext w
    constructor
    · intro h
      refine ⟨g⁻¹ • w, ?_, smul_inv_smul g w⟩
      have := (GraphAction.adj_smul g⁻¹ (g • v) w).mpr h
      simpa using this
    · rintro ⟨w', hw', rfl⟩
      exact (GraphAction.adj_smul g v w').mpr hw'
  rw [this]
  exact Function.Injective.encard_image (f := fun w : V => g • w) (MulAction.injective g) _

theorem two_le_encard_of_adj {V : Type*} {Γ : SimpleGraph V} {a w₀ w₁ : V} (h0 : Γ.Adj a w₀)
    (h1 : Γ.Adj a w₁) (hne : w₀ ≠ w₁) : 2 ≤ (Γ.neighborSet a).encard := by
  have : ({w₀, w₁} : Set V) ⊆ Γ.neighborSet a := by
    intro x hx
    rcases hx with rfl | rfl
    · exact h0
    · exact h1
  have h2 := Set.encard_le_encard this
  rwa [Set.encard_pair hne] at h2

theorem zero_mem_lnF_one : (0 : Fin 45) ∈ lnF 1 := by
  have h := p_spec.2.2.1
  have h1 : (1 : ℕ) ∈ (List.range 27).filter (fun k => (lnTab.getD k []).contains 0) := by
    rw [h]
    decide
  have := (List.mem_filter.1 h1).2
  exact List.contains_iff_mem.1 this

theorem valence (v : Vtx) :
    2 ≤ (incGraph.neighborSet v).encard := by
  obtain ⟨g, hg | hg⟩ := cover v
  · rw [← hg, encard_neighborSet_smul']
    refine two_le_encard_of_adj (w₀ := Sum.inr 0) (w₁ := Sum.inr 1) ?_ ?_ (by simp)
    · rw [adj_inl_inr]
      show (0 : Fin 45) ∈ lnS 0
      rw [lnS_zero]
      exact zero_mem_L0S
    · rw [adj_inl_inr]
      exact zero_mem_lnF_one
  · rw [← hg, encard_neighborSet_smul']
    refine two_le_encard_of_adj (w₀ := Sum.inl 0) (w₁ := Sum.inl 15) ?_ ?_ (by simp)
    · rw [adj_inr_inl]
      show (0 : Fin 45) ∈ lnS 0
      rw [lnS_zero]
      exact zero_mem_L0S
    · rw [adj_inr_inl]
      show (15 : Fin 45) ∈ lnS 0
      rw [lnS_zero, L0S_eq]
      simp

theorem isGenPolygon_incGraph :
    IsGenPolygon incGraph 4 :=
  isGenPolygon_of_layers (by norm_num) (fun x => x.isRight)
    (fun a b hab => by
      rcases a with p | k <;> rcases b with q | l
      · exact absurd hab (not_adj_inl_inl p q)
      · simp
      · simp
      · exact absurd hab (not_adj_inr_inr k l))
    (layers_of_cover layers_pt layers_ln cover)
    ⟨Sum.inl 0, layFun layPt0 layLn0, Sum.inl ⟨b01, by decide⟩, layers_pt, by decide⟩
    cycV cycV_adj cycV_ne cycV_per valence

end CFSG.Quasithin.H13.F431.U42
