module

public import CFSG.Quasithin.EmptyFaithful.S1414Group
public import CFSG.Quasithin.EmptyFaithful.S1417Rank
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1414

variable {G : Type} [Group G] [Finite G]

theorem pRank_top_le_two (hqtke : quasithinIsQTKECat G) {M : Subgroup G}
    (hM : quasithinIsMaxTwoLocal M) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup ↥M) ≤ 2 := by
  intro p hp hp2
  have h1 := CFSG.SectionRank.pRank_le_map hp.one_lt M.subtype M.subtype_injective
    (⊤ : Subgroup ↥M)
  have h0 : (⊤ : Subgroup ↥M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h0] at h1
  have h2 := A1b.pRank_le_evenRank hp hp2 hM.1
  have h3 : CFSG.Open.evenRank G ≤ 2 := hqtke.2.2
  omega

theorem blocks_of_solvable {T M₁ V : Subgroup G} (hqtke : quasithinIsQTKECat G)
    (hsylow : quasithinIsSylowTwo T) (hM₁ : InM T M₁) (hV : IsTwoReducedIn M₁ V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (hperf : perfectCore M₁ ≤ Subgroup.centralizer (V : Set G)) :
    ∃ (hVe : IsElemAbelian 2 V) (I : Finset (Subgroup (MulAut (IntMod V hVe)))),
      S1417.BlockSystem (autI hVe M₁) (autI hVe (thompsonJ M₁)) I ∧ I.card ≤ 2 := by
  have hVe : IsElemAbelian 2 V := hV.2.2.1
  have hMN : M₁ ≤ Subgroup.normalizer (V : Set G) := hV.2.1
  have hT' : IsSylowTwoOf T M₁ := by
    refine ⟨hM₁.2, hsylow.1, fun hd => hsylow.2 (dvd_trans hd ?_)⟩
    have := Subgroup.relIndex_dvd_index_of_le hM₁.2
    simpa [Subgroup.relIndex] using this
  obtain ⟨I, hJsyl, hYeq, hcomm, hindep, hnat, hsup, hinf, hindepV, hperm⟩ :=
    B2F.structure_of_not_le_of_quot hVe hV (S1417.isSolvable_autI hVe hMN hperf) hT' hJ
  have hS : S1417.BlockSystem (autI hVe M₁) (autI hVe (thompsonJ M₁)) I :=
    ⟨hYeq, hcomm, hindep, hnat, hsup, hinf, hindepV, hperm⟩
  exact ⟨hVe, I, hS, hS.card_le_two hVe hMN (pRank_top_le_two hqtke hM₁.1)⟩

omit [Finite G] in
theorem le_normalizer_inf_centralizer {M₁ V : Subgroup G}
    (hMN : M₁ ≤ Subgroup.normalizer (V : Set G)) :
    M₁ ≤ Subgroup.normalizer
      ((M₁ ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ y ∈ M₁, ∀ c ∈ M₁ ⊓ Subgroup.centralizer (V : Set G),
      y * c * y⁻¹ ∈ M₁ ⊓ Subgroup.centralizer (V : Set G) := by
    intro y hy c hc
    refine Subgroup.mem_inf.mpr ⟨M₁.mul_mem (M₁.mul_mem hy hc.1) (M₁.inv_mem hy), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : y⁻¹ * v * y ∈ V := (Subgroup.mem_normalizer_iff''.mp (hMN hy) v).mp hv
    have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hv'
    calc v * (y * c * y⁻¹) = y * ((y⁻¹ * v * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * v * y)) * y⁻¹ := by rw [h1]
      _ = y * c * y⁻¹ * v := by group
  intro c
  constructor
  · exact key x hx c
  · intro hc
    have := key x⁻¹ (M₁.inv_mem hx) _ hc
    simpa [mul_assoc] using this

omit [Finite G] in
theorem ordLE_of_decomp {T M M₁ : Subgroup G}
    (hMN : M₁ ≤ Subgroup.normalizer (VZ T M₁ : Set G))
    (h : ∀ x ∈ M₁, ∃ c ∈ M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G), ∃ b ∈ M₁ ⊓ M,
      x = c * b) : OrdLE T M₁ M := by
  intro x hx
  obtain ⟨c, hc, b, hb, rfl⟩ := h x hx
  refine ⟨b, hb, b⁻¹ * c * b, ?_, by group⟩
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_inf_centralizer hMN (M₁.inv_mem hb.1)) c).mp hc
  simpa using this

theorem ordLE_of_le_centralizer {T M M₁ : Subgroup G} (hT₁ : IsSylowTwoOf T M₁)
    (hMN : M₁ ≤ Subgroup.normalizer (VZ T M₁ : Set G))
    (hNJ : Subgroup.normalizer (thompsonJ T : Set G) ≤ M)
    (hJV : thompsonJ T ≤ Subgroup.centralizer (VZ T M₁ : Set G)) : OrdLE T M₁ M := by
  refine ordLE_of_decomp hMN fun x hx => ?_
  have hJN : thompsonJ T ≤ M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) :=
    le_inf ((C1GN.thompsonJ_le T).trans hT₁.1) hJV
  obtain ⟨n, hn, y, hy, rfl⟩ := frattini_decomp hT₁ inf_le_left
    (le_normalizer_inf_centralizer hMN) hJN x hx
  exact ⟨n, hn, y, ⟨hy.1, hNJ hy.2⟩, rfl⟩

end S1414

end CFSG.Quasithin
