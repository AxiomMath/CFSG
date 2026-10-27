module

public import CFSG.Quasithin.Vol2.Ch3Sec1Cases

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

theorem theorem316 (hC58 : TheoremC58) (hD15 : D15Used) (hB : B513) (hE213 : E213Three)
    (hE215 : E215) (h316 : AS316Sylow) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T) (hM : InM T M)
    (h : Hyp315 T M M₀ H V) :
    (∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
        M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)) ∨
      (¬ V ≤ pCoreOf 2 H ∧ qhatInt M₀ V h.reduced.2.2.1 ≤ 2 ∧
        (IsTISetIn V M → qhatInt M₀ V h.reduced.2.2.1 < 2)) ∨
      qInt M₀ V h.reduced.2.2.1 ≤ 2 := by
  by_cases h1 : ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
      M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)
  · exact Or.inl h1
  right
  by_cases hq : qInt M₀ V h.reduced.2.2.1 ≤ 2
  · exact Or.inr hq
  have hV0 : V ≠ ⊥ := by
    intro hV0
    apply h1
    have hRT : pCoreOf 2 M₀ = T := by
      rw [h.centralizer, hV0]
      ext x
      simp [Subgroup.mem_centralizer_iff]
    have hsyl : IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀) := by
      rw [hRT]
      exact B6.isSylowTwoOf_mono (isSylowTwoOf_of_isSylowTwo hT h.hStar.1.1) le_sup_right
        (sup_le (oTwoUpper_le H) h.hStar.1.1)
    exact h.toHyp315Base.exists_normal_of_sylow hC58 hs hnab hK hT hM hsyl
  have hD : D11Hyp M₀ H T V (H ⊓ M) :=
    h.toHyp315Base.d11Hyp hT hV0 (noNormal_of_not_exists h1)
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    hq (((isFFInt_iff_qInt_le_one _ _ _).mp hff).trans (by norm_num))
  by_cases hVH : V ≤ pCoreOf 2 H
  ·
    exfalso
    have hdual : ¬ IsDualFFInt M₀ V h.reduced.2.2.1 := fun hd =>
      hq (qInt_le_two_of_dualFF hB hs hnab hK h.reduced hV0 hd)
    rcases hD15 G M₀ H T V (H ⊓ M) hD with h1' | ⟨h2, -⟩ | h3 | ⟨h4, -, -⟩ | ⟨h5a, h5b⟩
    · exact h1' hVH
    · exact hq (h2.trans (by norm_num))
    · exact hdual h3
    · exact hq h4
    ·
      have hsyl := h316 G T M M₀ H V hs hnab hK hT hM h hV0 h1
        (fun h1' => hq (h1'.trans (by norm_num))) hdual hVH h5a h5b
      exact h1 (h.toHyp315Base.exists_normal_of_sylow hC58 hs hnab hK hT hM hsyl)
  ·
    obtain ⟨h1', h2'⟩ := case_i hE213 hE215 hs hnab hK hT hM h.toHyp315Base hD hnff hVH
    exact Or.inl ⟨hVH, h1', h2'⟩

end CFSG.Quasithin
