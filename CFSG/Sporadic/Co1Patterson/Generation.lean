module

public import CFSG.Sporadic.Co1Patterson.GenerationClasses
public import CFSG.Sporadic.Co1Patterson.GenerationAlt
public import CFSG.Sporadic.Co1Patterson.Setting
public import CFSG.Timmesfeld.Bridge.StrongEmbedding
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.LargeExtraspecial.S14 CFSG.RankThree.PartTwo.Sec21
open CFSG.Blueprint (NativeSporadic.Co1)

variable {X : Type} [Group X] [Finite X] {t : X}

theorem ncard_fixed_eq_one_of_mem (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* NativeSporadic.Co1) (htY : t ∈ Y) :
    {q : X ⧸ Y | t • q = q}.ncard = 1 ∧ ∃ b c : Y, orderOf b = 2 ∧ orderOf c = 2 ∧
      Nat.card (centralizer ({b} : Set Y)) = 2012774400 ∧
      Nat.card (centralizer ({c} : Set Y)) = 389283840 ∧
      ¬ IsConj t (b : X) ∧ ¬ IsConj t (c : X) := by
  obtain ⟨a, b, c, hcls, hab, hac, hbc, -, hb, hc, hCa, hCb, hCc⟩ :=
    exists_involution_classes e
  obtain ⟨hfix, -, htb, htc⟩ := ncard_fixed_eq_one_of_classes h.orderOf_eq
    (card_centralizer h) (card_eq_of_mulEquiv_co1 e) htY hcls hab hac hbc hCa hCb hCc
  exact ⟨hfix, b, c, hb, hc, hCb, hCc, htb, htc⟩

theorem existsUnique_fixed_of_mem (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* NativeSporadic.Co1) (htY : t ∈ Y) :
    ∃! q : X ⧸ Y, t • q = q :=
  Set.singleton_iff_unique_mem.mp (Set.ncard_eq_one.mp (ncard_fixed_eq_one_of_mem h e htY).1)

theorem isConj_of_isConj_of_mem (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* NativeSporadic.Co1) (htY : t ∈ Y) {y : Y} (hy : IsConj t (y : X)) :
    IsConj (⟨t, htY⟩ : Y) y := by
  obtain ⟨a, b, c, hcls, hab, hac, hbc, -, -, -, hCa, hCb, hCc⟩ :=
    exists_involution_classes e
  obtain ⟨-, -, htb, htc⟩ := ncard_fixed_eq_one_of_classes h.orderOf_eq
    (card_centralizer h) (card_eq_of_mulEquiv_co1 e) htY hcls hab hac hbc hCa hCb hCc
  have key : ∀ x : Y, IsConj t (x : X) → IsConj a x := by
    intro x hx
    have hx2 : orderOf x = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hx
      rw [← Subgroup.orderOf_coe, ← hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
        h.orderOf_eq]
    have hback : ∀ r : Y, IsConj r x → IsConj t (r : X) := fun r hr =>
      hx.trans (Y.subtype.map_isConj hr.symm)
    rcases hcls x hx2 with hr | hr | hr
    · exact hr
    · exact absurd (hback b hr) htb
    · exact absurd (hback c hr) htc
  exact (key ⟨t, htY⟩ (IsConj.refl t)).symm.trans (key y hy)

theorem not_isStronglyEmbedded_of_mem (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* NativeSporadic.Co1) (htY : t ∈ Y) (M : Subgroup X) :
    ¬ CFSG.IsStronglyEmbedded M := by
  intro hM
  obtain ⟨-, b, -, hb, -, -, -, htb, -⟩ := ncard_fixed_eq_one_of_mem h e htY
  exact htb (CFSG.Timmesfeld.Bridge.isConj_of_orderOf_eq_two (M := M) hM h.orderOf_eq
    ((Subgroup.orderOf_coe b).trans hb))

theorem eq_top_of_mem (hHolt : HoltUniqueFixedPointSimple) (h : PattersonCo1Hyp X t)
    {Y : Subgroup X} (e : Y ≃* NativeSporadic.Co1) (htY : t ∈ Y) : Y = ⊤ := by
  by_contra hY
  have := h.simple
  rcases hHolt X h.noncomm Y hY t h.orderOf_eq (exists_sylow h)
      (existsUnique_fixed_of_mem h e htY) with ⟨M, hM⟩ | ⟨n, hn, ⟨φ⟩⟩
  · exact not_isStronglyEmbedded_of_mem h e htY M hM
  · exact false_of_mulEquiv_alternatingGroup h.orderOf_eq (card_centralizer h) hn φ

theorem eq_top_of_co1_le (hHolt : HoltUniqueFixedPointSimple) (h : PattersonCo1Hyp X t)
    {Y : Subgroup X} (e : Y ≃* NativeSporadic.Co1) (hCY : centralizer ({t} : Set X) ≤ Y) :
    Y = ⊤ :=
  eq_top_of_mem hHolt h e (hCY (mem_centralizer_singleton_iff.mpr rfl))

end CFSG.Sporadic.Co1Patterson
