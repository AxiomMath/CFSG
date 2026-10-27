module

public import CFSG.Quasithin.Vol2.Ch3xLem317
public import CFSG.Quasithin.EmptyFaithfulMultiple.Input311Solvable

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Theorem317StatementFE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    (∀ H : Subgroup G, InH T H → ∀ U : Subgroup G, IsTwoReducedIn H U →
      perfectCore H ≤ Subgroup.centralizer (U : Set G)) →
    ∀ M M₀ H V : Subgroup G, InM T M → Hyp315 T M M₀ H V → thompsonJ T ≤ pCoreOf 2 M₀ →
      (quasithinOmegaOneCenter T ≤ centerOf H ∧ centerOf M₀ = ⊥) ∨
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
        M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)

section

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

theorem Hyp315Base.exists_normal_of_sylow_of_solvable (hS : EmptyFaithfulMultiple.Input311Solvable)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hM : InM T M) (h : Hyp315Base T M M₀ H V)
    (hsolv : Group.IsSolvable H)
    (hRS : IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀)) :
    ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
      M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.hyp311 hT hM
  exact hS G T hs hnab hK hT M₀ H (pCoreOf 2 M₀) h1 h2 hsolv h3 h4 h5 hRS h6

theorem lemma317_of_perfectCore (hS : EmptyFaithfulMultiple.Input311Solvable)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hM : InM T M) (h : Hyp315 T M M₀ H V)
    (hJ : thompsonJ T ≤ pCoreOf 2 M₀)
    (h1413 : ∀ H : Subgroup G, InH T H → ∀ U : Subgroup G, IsTwoReducedIn H U →
      perfectCore H ≤ Subgroup.centralizer (U : Set G)) :
    (quasithinOmegaOneCenter T ≤ centerOf H ∧ centerOf M₀ = ⊥) ∨
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
        M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) := by
  have hinH : InH T M₀ := h.inH_M₀ hT hM
  have hRT : pCoreOf 2 M₀ ≤ T := h.pCoreOf_le_T
  have hT0 : T ≠ ⊥ := fun hb => hinH.2 (le_bot_iff.mp (hb ▸ hRT))
  have hJne : thompsonJ T ≠ ⊥ := thompsonJ_ne_bot_of_isPGroup hT.1 hT0
  have hJR : thompsonJ (pCoreOf 2 M₀) = thompsonJ T := B6.thompsonJ_eq_of_le hJ hRT
  have hM₀J : M₀ ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [← hJR]
    exact (le_normalizer_pCoreOf 2 M₀).trans (normalizer_le_normalizer_thompsonJ _)
  by_cases hJn : H ≤ Subgroup.normalizer (thompsonJ T : Set G)
  · exact Or.inr ⟨thompsonJ T, hJne, hJ, sup_le hM₀J hJn⟩
  by_cases hZ : quasithinOmegaOneCenter T ≤ centerOf H
  · by_cases hZ0 : centerOf M₀ = ⊥
    · exact Or.inl ⟨hZ, hZ0⟩
    · right
      have hCT : CharTwo M₀ := charTwo_of_inH' hK hT hinH
      have hZM : centerOf M₀ ≤ pCoreOf 2 M₀ := fun x hx =>
        hCT ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun g hg =>
          Subgroup.mem_centralizer_iff.mp hx.2 g ((pCoreOf_le 2 M₀) hg)⟩
      obtain ⟨y, hyZ, hy⟩ := exists_mem_orderOf_two_of_isPGroup
        ((pCoreOf_isPGroup 2 M₀).to_le hZM) hZ0
      have hyR₀ : y ∈ omegaOneCenterOf M₀ :=
        Subgroup.subset_closure ⟨hyZ, by rw [← hy]; exact pow_orderOf_eq_one y⟩
      have hR₀ne : omegaOneCenterOf M₀ ≠ ⊥ := by
        intro hb
        rw [hb, Subgroup.mem_bot] at hyR₀
        rw [hyR₀, orderOf_one] at hy
        omega
      have hR₀R : omegaOneCenterOf M₀ ≤ pCoreOf 2 M₀ := by
        refine (Subgroup.closure_le _).mpr fun x hx => hZM hx.1
      have hR₀Z : omegaOneCenterOf M₀ ≤ quasithinOmegaOneCenter T := by
        refine (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure ?_
        have hxT : x ∈ T := hRT (hZM hx.1)
        exact ⟨⟨hxT, Subgroup.mem_centralizer_iff.mpr fun t ht =>
          Subgroup.mem_centralizer_iff.mp hx.1.2 t (h.T_le ht)⟩, hx.2⟩
      have hR₀C : omegaOneCenterOf M₀ ≤ Subgroup.centralizer (M₀ : Set G) :=
        (Subgroup.closure_le _).mpr fun x hx => hx.1.2
      refine ⟨omegaOneCenterOf M₀, hR₀ne, hR₀R, sup_le ?_ ?_⟩
      · exact le_normalizer_of_le_centralizer hR₀C
      · exact le_normalizer_of_le_centralizer fun x hx => (hZ (hR₀Z hx)).2
  ·
    have hHinH : InH T H := h.inH_H
    have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_isSylowTwo hT hHinH.1
    have hnormT : ¬ H ≤ Subgroup.normalizer (T : Set G) := fun hHT =>
      hJn (hHT.trans (normalizer_le_normalizer_thompsonJ T))
    have hmin : MinParabolic H T (H ⊓ M) :=
      ⟨hsyl, hnormT, h.toHyp315Base.isUniqueMaxOver hT⟩
    have hsolv : Group.IsSolvable H :=
      isSolvable_of_not_le_centerOf hT hHinH (charTwo_of_inH' hK hT hHinH) hmin hZ (h1413 H hHinH)
    exact Or.inr (h.toHyp315Base.exists_normal_of_sylow_of_solvable hS hs hnab hK hT hM hsolv
      (as317Sylow_of_isSolvable hK hT h hJ hJn hZ hsolv))

theorem theorem317StatementFE_of_solvable (hS : EmptyFaithfulMultiple.Input311Solvable) :
    Theorem317StatementFE := by
  intro G _ _ T hs hnab hK hT h1413 M M₀ H V hM h hJ
  exact lemma317_of_perfectCore hS hs hnab hK hT hM h hJ h1413

end

end CFSG.Quasithin
