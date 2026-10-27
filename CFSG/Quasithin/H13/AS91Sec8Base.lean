module

public import CFSG.Quasithin.H13.AS91Sec8Pt
public import CFSG.Quasithin.Recognition.UniquenessSystemOrbit
public import CFSG.Quasithin.Recognition.UniquenessSystemMono
public import CFSG.Quasithin.Recognition.UniquenessSystemTriangulation

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94 MulAction

variable {G : Type*} [Group G]

private theorem smul_basePt_of_cInc {G₁ G₃ : Subgroup G} {a : G ⧸ G₁}
    (ha : CInc G₁ G₃ a (basePt G₃)) : ∃ h ∈ G₃, h • basePt G₁ = a := by
  obtain ⟨g, rfl, hgb⟩ := ha
  have hg : g ∈ G₃ := by
    have h1 := QuotientGroup.eq.mp hgb
    simpa using G₃.inv_mem h1
  refine ⟨g, hg, ?_⟩
  show g • ((1 : G) : G ⧸ G₁) = ((g : G) : G ⧸ G₁)
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

private theorem orbitSubgraph_adj_of_adj {G₁ G₂ G₃ : Subgroup G} {y : G ⧸ G₁}
    (hxy : (colGraph G₁ G₂).Adj (basePt G₁) y) (hy : ∃ t ∈ G₃, t • basePt G₁ = y)
    (hrank : ∀ b : G ⧸ G₁, CInc G₁ G₃ b (basePt G₃) → (colGraph G₁ G₂).Adj (basePt G₁) b →
      ∃ j ∈ G₁ ⊓ G₃, j • y = b)
    {a b : G ⧸ G₁} (ha : CInc G₁ G₃ a (basePt G₃)) (hb : CInc G₁ G₃ b (basePt G₃))
    (hab : (colGraph G₁ G₂).Adj a b) :
    (orbitSubgraph (colGraph G₁ G₂) G₃ (basePt G₁) y hxy hy).Adj a b := by
  obtain ⟨h, hh, rfl⟩ := smul_basePt_of_cInc ha
  have e : h⁻¹ • basePt G₃ = basePt G₃ := by
    show h⁻¹ • ((1 : G) : G ⧸ G₃) = ((1 : G) : G ⧸ G₃)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact QuotientGroup.eq.mpr (by simpa using hh)
  have hb' : CInc G₁ G₃ (h⁻¹ • b) (basePt G₃) := by
    have := (cInc_smul G₁ G₃ h⁻¹ b (basePt G₃)).mpr hb
    rwa [e] at this
  have hadj : (colGraph G₁ G₂).Adj (basePt G₁) (h⁻¹ • b) := by
    have := (CFSG.Quasithin.GraphAction.adj_smul h⁻¹ (h • basePt G₁) b).mpr hab
    rwa [inv_smul_smul] at this
  obtain ⟨j, hj1, hj⟩ := hrank _ hb' hadj
  obtain ⟨hjG₁, hjG₃⟩ := Subgroup.mem_inf.mp hj1
  have hjx : j • basePt G₁ = basePt G₁ := by
    show j • ((1 : G) : G ⧸ G₁) = ((1 : G) : G ⧸ G₁)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact QuotientGroup.eq.mpr (by simpa using hjG₁)
  refine ⟨h * j, G₃.mul_mem hh hjG₃, Or.inl ⟨?_, ?_⟩⟩
  · rw [mul_smul, hjx]
  · rw [mul_smul, hj, smul_inv_smul]

theorem isBase_orbitSubgraph_colGraph (G₁ G₂ G₃ : Subgroup G) {y : G ⧸ G₁}
    (hxy : (colGraph G₁ G₂).Adj (basePt G₁) y) (hy : ∃ t ∈ G₃, t • basePt G₁ = y)
    (htri : Triangulable (colGraph G₁ G₂))
    (hplane : ∀ a b c : G ⧸ G₁, (colGraph G₁ G₂).Adj a b → (colGraph G₁ G₂).Adj b c →
      (colGraph G₁ G₂).Adj a c →
      ∃ p : G ⧸ G₃, CInc G₁ G₃ a p ∧ CInc G₁ G₃ b p ∧ CInc G₁ G₃ c p)
    (hrank : ∀ b : G ⧸ G₁, CInc G₁ G₃ b (basePt G₃) → (colGraph G₁ G₂).Adj (basePt G₁) b →
      ∃ j ∈ G₁ ⊓ G₃, j • y = b) :
    IsBase G (colGraph G₁ G₂)
      (orbitSubgraph (colGraph G₁ G₂) G₃ (basePt G₁) y hxy hy) := by
  refine isBase_of_triangulable htri ?_
  intro p hp
  obtain ⟨u, v, w, rfl, huv, hvw, hwu⟩ := hp.three
  obtain ⟨q, hu, hv, hw⟩ := hplane u v w huv hvw hwu.symm
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have e : g⁻¹ • ((g : G) : G ⧸ G₃) = basePt G₃ := by
    show g⁻¹ • ((g : G) : G ⧸ G₃) = ((1 : G) : G ⧸ G₃)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
  have tr : ∀ a : G ⧸ G₁, CInc G₁ G₃ a ((g : G) : G ⧸ G₃) →
      CInc G₁ G₃ (g⁻¹ • a) (basePt G₃) := by
    intro a ha
    have := (cInc_smul G₁ G₃ g⁻¹ a ((g : G) : G ⧸ G₃)).mpr ha
    rwa [e] at this
  have h1 := orbitSubgraph_adj_of_adj hxy hy hrank (tr u hu) (tr v hv)
    ((CFSG.Quasithin.GraphAction.adj_smul g⁻¹ u v).mpr huv)
  have h2 := orbitSubgraph_adj_of_adj hxy hy hrank (tr v hv) (tr w hw)
    ((CFSG.Quasithin.GraphAction.adj_smul g⁻¹ v w).mpr hvw)
  have h3 := orbitSubgraph_adj_of_adj hxy hy hrank (tr w hw) (tr u hu)
    ((CFSG.Quasithin.GraphAction.adj_smul g⁻¹ w u).mpr hwu)
  refine ⟨[g⁻¹ • u, g⁻¹ • v, g⁻¹ • w, g⁻¹ • u], g,
    ⟨⟨⟨List.cons_ne_nil _ _, ?_⟩, rfl⟩, ?_⟩, ?_⟩
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true,
      SimpleGraph.Subgraph.spanningCoe_adj]
    exact ⟨h1, h2, h3⟩
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact SimpleGraph.Subgraph.edge_vert _ h1
    · exact SimpleGraph.Subgraph.edge_vert _ h2
    · exact SimpleGraph.Subgraph.edge_vert _ h3
    · exact SimpleGraph.Subgraph.edge_vert _ h1
  · simp only [List.map_cons, List.map_nil, smul_inv_smul]

end CFSG.Quasithin.H13.AS91
