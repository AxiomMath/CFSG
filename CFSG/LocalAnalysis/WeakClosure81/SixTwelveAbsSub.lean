module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveAbsDefs
public import CFSG.RankThree.GF2n.QuotPair

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.RankThree.GF2n (QuotPair pairConj)
open scoped commutatorElement

variable {X : Type} [Group X]

private theorem b612_trace_ne_bot {Y C : Subgroup X} (hCY : C ≤ Y) (hne : C ≠ ⊥) :
    C.subgroupOf Y ≠ ⊥ := by
  intro hbot
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  apply ha
  apply Subtype.ext
  have hmemA : (⟨(a : X), hCY a.2⟩ : ↥Y) ∈ C.subgroupOf Y :=
    Subgroup.mem_subgroupOf.2 a.2
  rw [hbot] at hmemA
  simpa using congrArg Subtype.val (Subgroup.mem_bot.1 hmemA)

namespace Abs612

variable {T T₁ Z E : Subgroup X}

theorem conjSubgroup_ne_of_mem (h : Abs612 T T₁ Z E) {s : X} (hs : s ∈ T₁) (hs1 : s ≠ 1) :
    conjSubgroup s T ≠ T := by
  intro heq
  exact hs1 (h.inf_normalizer s hs (CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.1 heq))

theorem quotPair_sub (h : Abs612 T T₁ Z E) {s : X} (hs : s ∈ T₁) (hs1 : s ≠ 1) :
    QuotPair (T.subgroupOf (T ⊔ conjSubgroup s T))
      ((conjSubgroup s T).subgroupOf (T ⊔ conjSubgroup s T)) := by
  set Y := T ⊔ conjSubgroup s T with hY
  have hTY : T ≤ Y := by rw [hY]; exact le_sup_left
  have hTsY : conjSubgroup s T ≤ Y := by rw [hY]; exact le_sup_right
  have hmem : ∀ U ∈ pairConj (T.subgroupOf Y) ((conjSubgroup s T).subgroupOf Y),
      ∃ x : X, U = (conjSubgroup x T).subgroupOf Y := by
    intro U hU
    obtain ⟨g, rfl | rfl⟩ := hU
    · exact ⟨(g : X), conjSubgroup_subgroupOf Y T g⟩
    · refine ⟨(g : X) * s, ?_⟩
      rw [conjSubgroup_subgroupOf Y (conjSubgroup s T) g,
        ← CFSG.RankThree.GF2n.conjSubgroup_mul (g : X) s T]
  have hne₁ : conjSubgroup s T ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (conjSubgroup s T) = 1 := by rw [hbot, Subgroup.card_bot]
    have hcardT : Nat.card T = 1 := by
      rw [← CFSG.RankThree.GF2n.card_conjSubgroup s T]; exact h1
    exact (by omega : ¬ (4 ≤ (1 : ℕ))) (by simpa [hcardT] using h.four_le)
  refine { elem := h.elem.subgroupOf Y
           elem₁ := (h.elem_conj s).subgroupOf Y
           ne_bot := b612_trace_ne_bot hTY h.ne_bot
           ne_bot₁ := b612_trace_ne_bot hTsY hne₁
           ne := ?_
           sup := ?_
           closed := ?_ }
  · intro heq
    apply h.conjSubgroup_ne_of_mem hs hs1
    have hinf : T ⊓ Y = conjSubgroup s T ⊓ Y := Subgroup.subgroupOf_inj.1 heq
    rw [inf_eq_left.2 hTY, inf_eq_left.2 hTsY] at hinf
    exact hinf.symm
  · rw [← Subgroup.subgroupOf_sup hTY hTsY, ← hY]
    exact Subgroup.subgroupOf_self Y
  · intro U hU V hV u hu hu1 v hv hv1 hcomm
    obtain ⟨x, rfl⟩ := hmem U hU
    obtain ⟨y, rfl⟩ := hmem V hV
    have huX : (u : X) ∈ conjSubgroup x T := Subgroup.mem_subgroupOf.1 hu
    have hu1X : (u : X) ≠ 1 := fun h' => hu1 (Subtype.ext h')
    have hvX : (v : X) ∈ conjSubgroup y T := Subgroup.mem_subgroupOf.1 hv
    have hv1X : (v : X) ≠ 1 := fun h' => hv1 (Subtype.ext h')
    have hcommX : (u : X) * (v : X) = (v : X) * (u : X) := by
      simpa using congrArg Subtype.val hcomm
    have hZ : ⁅(u : X), (v : X)⁆ ∈ Z := by
      rw [(commutatorElement_eq_one_iff_mul_comm).2 hcommX]
      exact Z.one_mem
    exact congrArg (fun C => C.subgroupOf Y)
      (h.closed x y (u : X) huX hu1X (v : X) hvX hv1X hZ)

theorem exists_conj_sub [Finite X] (h : Abs612 T T₁ Z E) {s : X} (hs : s ∈ T₁) (hs1 : s ≠ 1) :
    ∃ y ∈ T ⊔ conjSubgroup s T, conjSubgroup s T = conjSubgroup y T := by
  set Y := T ⊔ conjSubgroup s T with hY
  have hTY : T ≤ Y := by rw [hY]; exact le_sup_left
  have hTsY : conjSubgroup s T ≤ Y := by rw [hY]; exact le_sup_right
  obtain ⟨x, hx⟩ := (h.quotPair_sub hs hs1).exists_conj_eq
  have hx' : (conjSubgroup s T).subgroupOf Y =
      (conjSubgroup (x : X) T).subgroupOf Y := by
    rw [hx, conjSubgroup_subgroupOf Y T x]
  have hxY : conjSubgroup (x : X) T ≤ Y := conjSubgroup_le_of_le_of_mem hTY x.2
  refine ⟨(x : X), x.2, ?_⟩
  have hinf := Subgroup.subgroupOf_inj.1 hx'
  rw [inf_eq_left.2 hTsY, inf_eq_left.2 hxY] at hinf
  exact hinf

end Abs612

end CFSG.LocalAnalysis.WeakClosure81
