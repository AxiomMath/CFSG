module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Act

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem GoldHyp.amalgamHypV (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) : AmalgamHypV (G₁ ⊔ G₂) G₁ G₂ (G₁ ⊓ G₂) V :=
  { toAmalgamHyp := h.amalgamHyp, reduced := hn.reduced, cT := hn.cT }

theorem exists_natural_vertex (h : GoldHyp G₁ G₂) (hT : G₁ ⊓ G₂ ≠ ⊥) :
    (∃ z V, IsNaturalAt G₁ (G₁ ⊓ G₂) z V) ∨ (∃ z V, IsNaturalAt G₂ (G₁ ⊓ G₂) z V) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply h.not_normalizes_both hT
  have key : ∀ H : Subgroup D, Vertex H (G₁ ⊓ G₂) → (∀ z V, ¬ IsNaturalAt H (G₁ ⊓ G₂) z V) →
      H ≤ Subgroup.normalizer (quasithinOmegaOneCenter (G₁ ⊓ G₂) : Set D) := by
    intro H hv hno
    have hcentral : ∀ ω ∈ centerOf (G₁ ⊓ G₂), ω ^ 2 = 1 → ∀ g ∈ H, g * ω * g⁻¹ = ω := by
      intro ω hωZ hω2 g hg
      by_contra hne
      obtain ⟨z, V, hn, -⟩ := exists_natural hv hωZ hω2 ⟨g, hg, hne⟩
      exact hno z V hn
    have hΩ : quasithinOmegaOneCenter (G₁ ⊓ G₂) ≤ Subgroup.centralizer (H : Set D) := by
      unfold quasithinOmegaOneCenter
      rw [Subgroup.closure_le]
      rintro ω ⟨hωZ, hω2⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro g hg
      have := hcentral ω hωZ hω2 g hg
      calc g * ω = (g * ω * g⁻¹) * g := by group
        _ = ω * g := by rw [this]
    exact (Subgroup.le_centralizer_iff.mp hΩ).trans (Subgroup.centralizer_le_normalizer _)
  exact ⟨key G₁ h.vertex_left h1, key G₂ h.vertex_right h2⟩

theorem IsNaturalAt.le_pCoreOf_of_centralizes (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) (hzG₂ : ∀ y ∈ G₂, y * z * y⁻¹ = z) :
    V ≤ pCoreOf 2 G₂ := by
  by_contra hV
  obtain ⟨v, hvV, hvQ⟩ : ∃ v ∈ V, v ∉ pCoreOf 2 G₂ := by
    by_contra hcon
    push Not at hcon
    exact hV (fun x hx => hcon x hx)
  have hvT : v ∈ G₁ ⊓ G₂ := h.pCoreOf_left_le (hn.le_pCoreOf hvV)
  refine h.vertex_right.false_of_transvection hn.z_mem hzG₂ hvT (hn.mul_self_of_mem hvV) hvQ ?_
  intro q hq
  exact hn.conj_cases inf_le_left (h.pCoreOf_right_le hq) hvV

theorem two_le_critDist_iff (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) :
    2 ≤ critDist (G₁ ⊔ G₂) G₁ G₂ V ↔ V ≤ pCoreOf 2 G₂ := by
  have hyp := h.amalgamHypV hn
  have hV : V ≠ ⊥ := hn.natural.ne_bot
  constructor
  · intro hb
    by_contra hVQ
    have := critDist_eq_one_of_not_le_pCoreOf hyp hV hVQ
    omega
  · exact two_le_critDist_of_le_pCoreOf hyp hV

theorem critDist_two_structure_of_natural (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) (hb : critDist (G₁ ⊔ G₂) G₁ G₂ V = 2) :
    V ≤ conjClosure V G₂ ∧ conjClosure V G₂ ≤ pCoreOf 2 G₂ ∧
      (pCoreOf 2 G₁).relIndex (conjClosure V G₂) = 2 ∧
      ∃ x ∈ G₂, conjSub x V ≤ conjClosure V G₂ ∧ conjSub x V ≤ G₁ ∧
        pCoreOf 2 G₁ ⊔ conjSub x V = G₁ ⊓ G₂ ∧ pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂ = G₁ ⊓ G₂ ∧
        ⁅V, conjSub x V⁆ = V ⊓ conjSub x V ∧
        V ⊓ conjSub x V = V ⊓ Subgroup.centralizer ((G₁ ⊓ G₂ : Subgroup D) : Set D) ∧
        Nat.card ↥(V ⊓ conjSub x V) = 2 ∧ ⁅⁅V, conjSub x V⁆, conjSub x V⁆ = ⊥ :=
  F112W.critDist_two_structure (h.amalgamHypV hn) hn.natural hb

theorem natural_step (h : GoldHyp G₁ G₂) {z : D} {V : Subgroup D}
    (hn : IsNaturalAt G₁ (G₁ ⊓ G₂) z V) :
    V ≤ pCoreOf 2 G₂ ∨ ∃ z₂ V₂, IsNaturalAt G₂ (G₁ ⊓ G₂) z₂ V₂ ∧ ¬ V ≤ pCoreOf 2 G₂ ∧
      z₂ ∈ conjClosure (Subgroup.zpowers z) G₂ := by
  by_cases hV : V ≤ pCoreOf 2 G₂
  · exact Or.inl hV
  · right
    have hmove : ∃ y ∈ G₂, y * z * y⁻¹ ≠ z := by
      by_contra hcon
      push Not at hcon
      exact hV (hn.le_pCoreOf_of_centralizes h hcon)
    obtain ⟨y, hy, hyz⟩ := hmove
    obtain ⟨z₂, V₂, hn₂, hz₂⟩ := exists_natural h.vertex_right hn.z_mem hn.z_sq ⟨y, hy, hyz⟩
    exact ⟨z₂, V₂, hn₂, hV, hz₂⟩

theorem l1_trichotomy (h : GoldHyp G₁ G₂) (hT : G₁ ⊓ G₂ ≠ ⊥) :
    (∃ z V, IsNaturalAt G₁ (G₁ ⊓ G₂) z V ∧ V ≤ pCoreOf 2 G₂) ∨
    (∃ z V, IsNaturalAt G₂ (G₁ ⊓ G₂) z V ∧ V ≤ pCoreOf 2 G₁) ∨
    (∃ z₁ V₁ z₂ V₂, IsNaturalAt G₁ (G₁ ⊓ G₂) z₁ V₁ ∧ IsNaturalAt G₂ (G₁ ⊓ G₂) z₂ V₂ ∧
      ¬ V₁ ≤ pCoreOf 2 G₂ ∧ ¬ V₂ ≤ pCoreOf 2 G₁) := by
  rcases exists_natural_vertex h hT with ⟨z, V, hn⟩ | ⟨z, V, hn⟩
  · rcases natural_step h hn with hV | ⟨z₂, V₂, hn₂, hV, -⟩
    · exact Or.inl ⟨z, V, hn, hV⟩
    · by_cases hV₂ : V₂ ≤ pCoreOf 2 G₁
      · exact Or.inr (Or.inl ⟨z₂, V₂, hn₂, hV₂⟩)
      · exact Or.inr (Or.inr ⟨z, V, z₂, V₂, hn, hn₂, hV, hV₂⟩)
  · have hn' : IsNaturalAt G₂ (G₂ ⊓ G₁) z V := by rw [inf_comm]; exact hn
    rcases natural_step h.symm hn' with hV | ⟨z₂, V₂, hn₂, hV, -⟩
    · exact Or.inr (Or.inl ⟨z, V, hn, hV⟩)
    · have hn₂' : IsNaturalAt G₁ (G₁ ⊓ G₂) z₂ V₂ := by rw [inf_comm]; exact hn₂
      by_cases hV₂ : V₂ ≤ pCoreOf 2 G₂
      · exact Or.inl ⟨z₂, V₂, hn₂', hV₂⟩
      · exact Or.inr (Or.inr ⟨z₂, V₂, z, V, hn₂', hn, hV₂, hV⟩)

end GoldAmL

end F6

end CFSG.Quasithin
