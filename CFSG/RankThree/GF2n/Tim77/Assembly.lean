module

public import CFSG.RankThree.GF2n.Tim77.Defs
public import CFSG.RankThree.GF2n.Tim77.Cor2Hyp
public import CFSG.RankThree.GF2n.Tim77.Cor2One
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.CGT.Timmesfeld75.WeaklyClosed
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld.RootInvolutions
open Subgroup
open scoped commutatorElement

section CoreAssembly

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

theorem Sec3Ctx.abar0_ne_bot (h : Sec3Ctx A Abar S₀ B) : Section3.Abar0 A Abar ≠ ⊥ :=
  h.nota.choice.2.1.1

theorem Sec3Ctx.abar0_ne (h : Sec3Ctx A Abar S₀ B) : Section3.Abar0 A Abar ≠ Abar :=
  h.nota.choice.2.1.2

theorem Sec3Ctx.two_le_q (h : Sec3Ctx A Abar S₀ B) : 2 ≤ Section3.q A Abar := by
  have h0 : Section3.q A Abar ≠ 0 := by
    unfold Section3.q Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h1 : Section3.q A Abar ≠ 1 := by
    unfold Section3.q
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    refine h.abar0_ne (le_antisymm ?_ h1)
    exact inf_le_left
  omega

omit [Finite G] in
theorem conjSubgroup_eq_of_mem_centralizer {b : G} (hb : b ∈ centralizer (A : Set G)) :
    conjSubgroup b A = A := by
  ext x
  rw [mem_conjSubgroup]
  have hc : ∀ h ∈ A, h * b = b * h := fun h hh => Subgroup.mem_centralizer_iff.1 hb h hh
  constructor
  · intro hy
    have hyb := hc _ hy
    have e : x = b⁻¹ * x * b := by
      calc x = b * (b⁻¹ * x * b) * b⁻¹ := by group
        _ = (b⁻¹ * x * b) * b * b⁻¹ := by rw [← hyb]
        _ = b⁻¹ * x * b := by group
    rw [e]; exact hy
  · intro hx
    have := hc _ hx
    have e : b⁻¹ * x * b = x := by
      calc b⁻¹ * x * b = b⁻¹ * (x * b) := by group
        _ = b⁻¹ * (b * x) := by rw [this]
        _ = x := by group
    rw [e]; exact hx

theorem exists_sChoice (h31 : Tim77Sec31Statement) (h : Sec3Ctx A Abar S₀ B) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) : ∃ s, Sec3SChoiceAt A Abar S₀ B b s := by
  by_cases hx : ∃ x ∈ Section3.Abar0 A Abar, x ≠ 1 ∧ (orderOf (x * b) = 2 ∨ orderOf (x * b) = 4)
  · exact ⟨b, hb, hb1, Or.inl ⟨hx, rfl⟩⟩
  · push Not at hx
    obtain ⟨x, hxA, hx1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot h.abar0_ne_bot
    have hno := hx x hxA hx1
    obtain ⟨s, hsc, hsS, hsC, hsne, hsc2, hso⟩ :=
      h31 G A Abar S₀ B h x hxA hx1 b hb hb1 hno.1 hno.2
    exact ⟨s, hb, hb1, Or.inr ⟨hx, x, hxA, hx1, hsc, hsS, hsC, hsne, hsc2, hso⟩⟩

theorem mem_normalizer_X_of_Y_eq (h : Sec3Ctx A Abar S₀ B) {b : G} (hb : b ∈ B)
    (hY : Section3.Y A Abar b = Section3.X A Abar) :
    b ∈ normalizer (Section3.X A Abar : Set G) := by
  have hbC : b ∈ centralizer (A : Set G) := (h.nota.le hb).2
  have hAb : conjSubgroup b A = A := conjSubgroup_eq_of_mem_centralizer hbC
  have hle : conjSubgroup b (Section3.X A Abar) ≤ Section3.X A Abar := by
    have e : conjSubgroup b (Section3.X A Abar) = conjSubgroup b A ⊔ conjSubgroup b Abar := by
      unfold Section3.X conjSubgroup
      exact Subgroup.map_sup _ _ _
    rw [e, hAb, ← hY]
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  exact mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le hle)

theorem sec36_of (h31 : Tim77Sec31Statement) (h33 : Tim77Sec33Statement)
    (h34 : Tim77Sec34Statement) (h35 : Tim77Sec35Statement) (h : Sec3Ctx A Abar S₀ B)
    (hq : 2 < Section3.q A Abar) : False := by
  refine h35 G A Abar S₀ B h fun b hb => ?_
  by_cases hb1 : b = 1
  · subst hb1; exact one_mem _
  obtain ⟨s, hs⟩ := exists_sChoice h31 h hb hb1
  have hY := h33 G A Abar S₀ B s h ⟨b, hs⟩ hq
  have hsb := h34 G A Abar S₀ B b s h hs hY
  subst hsb
  exact mem_normalizer_X_of_Y_eq h hb hY

theorem sec45_of (h43 : Tim77Sec43Statement) (h44 : Tim77Sec44Statement)
    (h35 : Tim77Sec35Statement) (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2) :
    ∃ b ∈ B, b ≠ 1 ∧ ¬ Group.IsSolvable ↥(A ⊔ Abar ⊔ conjSubgroup b Abar) := by
  by_contra hcon
  push Not at hcon
  refine h35 G A Abar S₀ B h fun b hb => ?_
  by_cases hb1 : b = 1
  · subst hb1; exact one_mem _
  obtain ⟨x, hxA, hx1, hxo⟩ := h44 G A Abar S₀ B h hq b hb hb1
  have hs : Sec3SChoiceAt A Abar S₀ B b b := ⟨hb, hb1, Or.inl ⟨⟨x, hxA, hx1, hxo⟩, rfl⟩⟩
  have hY := h43 G A Abar S₀ B b h ⟨b, hs⟩ hq (hcon b hb hb1)
  exact mem_normalizer_X_of_Y_eq h hb hY

end CoreAssembly

theorem card_abar0_eq_of_ctx {G : Type} [Group G] {A Abar S₀ B Abar' S₀' B' : Subgroup G}
    (h : Sec3Ctx A Abar S₀ B) (h' : Sec3Ctx A Abar' S₀' B') :
    Nat.card (Section3.Abar0 A Abar) = Nat.card (Section3.Abar0 A Abar') := by
  obtain ⟨⟨g, hg⟩, hne, hmax⟩ := h.nota.choice
  obtain ⟨⟨g', hg'⟩, hne', hmax'⟩ := h'.nota.choice
  unfold Section3.Abar0
  apply le_antisymm
  · have := hmax' g (by rw [← hg]; exact hne)
    rwa [← hg] at this
  · have := hmax g' (by rw [← hg']; exact hne')
    rwa [← hg'] at this

theorem section3_q_eq_of_ctx {G : Type} [Group G] [Finite G]
    {A Abar S₀ B Abar' S₀' B' : Subgroup G}
    (h' : Sec3Ctx A Abar' S₀' B') (h : Sec3Ctx A Abar S₀ B) :
    Section3.q A Abar' = Section3.q A Abar := by
  have hc := card_abar0_eq_of_ctx h h'
  obtain ⟨⟨g, hg⟩, -, -⟩ := h.nota.choice
  obtain ⟨⟨g', hg'⟩, -, -⟩ := h'.nota.choice
  have hA : Nat.card Abar = Nat.card Abar' := by
    rw [hg, hg', card_conjSubgroup, card_conjSubgroup]
  have hle : Section3.Abar0 A Abar ≤ Abar := by
    unfold Section3.Abar0 normalizerIn; exact inf_le_left
  have hle' : Section3.Abar0 A Abar' ≤ Abar' := by
    unfold Section3.Abar0 normalizerIn; exact inf_le_left
  have e1 := Subgroup.relIndex_mul_card (H := Section3.Abar0 A Abar) (K := Abar)
  have e2 := Subgroup.relIndex_mul_card (H := Section3.Abar0 A Abar') (K := Abar')
  rw [inf_of_le_left hle] at e1
  rw [inf_of_le_left hle'] at e2
  unfold Section3.q
  have hpos : 0 < Nat.card (Section3.Abar0 A Abar) := Nat.card_pos
  rw [← hA, ← hc] at e2
  exact Nat.eq_of_mul_eq_mul_right hpos (e2.trans e1.symm)

theorem core_of_steps (hNot : Tim77ExistsNotationStatement) (h31 : Tim77Sec31Statement)
    (h33 : Tim77Sec33Statement) (h34 : Tim77Sec34Statement) (h35 : Tim77Sec35Statement)
    (h415 : Tim77Sec415Statement) (h54 : Tim77Sec54Statement)
    (G : Type) [Group G] [Finite G] (A : Subgroup G)
    (hA : ElementaryAbelianTIRootCentralizerHypothesis A) (h1 : ¬ IsRootType 2 A)
    (h2 : ¬ ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) → conjSubgroup g A = A) :
    Cor2Alt3 A := by
  obtain ⟨Abar, S₀, B, hn⟩ := hNot G A hA h1 h2
  have h : Sec3Ctx A Abar S₀ B := ⟨hA, h1, h2, hn⟩
  by_cases hq : Section3.q A Abar = 2
  · by_cases hc : ∃ Abar' S₀' B' : Subgroup G, Sec3Ctx A Abar' S₀' B' ∧ Sec4A0LeCenterH A Abar'
    · obtain ⟨Abar', S₀', B', h', hc'⟩ := hc
      exact h415 G A Abar' S₀' B' h' (section3_q_eq_of_ctx h' h ▸ hq) hc'
    · push Not at hc
      exact (h54 G A Abar S₀ B h hq hc).elim
  · exact (sec36_of h31 h33 h34 h35 h (lt_of_le_of_ne h.two_le_q (Ne.symm hq))).elim

theorem thm1_of_core
    (hcore : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
      ElementaryAbelianTIRootCentralizerHypothesis A → ¬ IsRootType 2 A →
      (¬ ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) → conjSubgroup g A = A) →
        Cor2Alt3 A) : Tim77Thm1Statement := by
  intro G _ _ A hA
  by_cases h1 : IsRootType 2 A
  · exact Or.inl h1
  by_cases h2 : ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) → conjSubgroup g A = A
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (hcore G A hA h1 h2))

theorem tim77Cor2_of_steps (hA : TheoremAStmt) (hThm1 : Tim77Thm1Statement)
    (hα : Tim77AlphaBox) (hβ : Tim77BetaBox) : Tim77Cor2Statement := by
  rw [tim77Cor2_iff]
  intro G _ _ A hAe hTI hW hS'
  have hc2 : ElementaryAbelianTIWeakClosureHypothesis A := by
    refine ⟨hAe, hTI, ?_, (sylow_le_normalizer_iff A).1 hS'⟩
    rwa [← wac_eq_weakClosure]
  rcases hThm1 G A hc2.toRootCentralizer with hroot | hwc | h3
  · by_cases hd : ⁅WAC A, WAC A⁆ = ⊥
    · exact Or.inr (Or.inr (Or.inl ⟨hd, hβ G A hAe hTI hroot hd hS'⟩))
    · exact Or.inr (Or.inl (hα G A hAe hTI hroot hW hd))
  · exact Or.inl (cor2One_of_weaklyClosed hA hAe hTI hwc)
  · exact Or.inr (Or.inr (Or.inr h3))

theorem tim77Cor2_of_leaves (hA : TheoremAStmt) (h : Tim77Leaves) : Tim77Cor2Statement :=
  tim77Cor2_of_steps hA
    (thm1_of_core (core_of_steps h.exNotation h.sec31 h.sec33 h.sec34 h.sec35 h.sec415 h.sec54))
    h.alpha h.beta

end CFSG.RankThree.GF2n.Tim77
