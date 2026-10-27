module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveAbsOdd
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveAbsF
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveAbsStep

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.RankThree.GF2n (QuotPair pairConj)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace Abs612

variable {T T₁ Z E : Subgroup X}

section Certified


theorem exists_mem_sup_conj_eq (h : Abs612 T T₁ Z E) {x : X}
    (hx : ∀ s ∈ T₁, conjSubgroup s (conjSubgroup x T) = conjSubgroup x T) {s : X} (hs : s ∈ T₁)
    (hs1 : s ≠ 1) :
    ∃ y ∈ T ⊔ conjSubgroup s T, conjSubgroup y T = conjSubgroup x T ∧
      ∃ t ∈ conjSubgroup x T, ∃ z ∈ Z, s = t * z := by
  obtain ⟨y₀, hy₀, hconj⟩ := h.exists_conj_sub hs hs1
  obtain ⟨y, hy, hfix⟩ := h.exists_fixed_orbit_sup hs ⟨y₀, hy₀, hconj⟩
  obtain ⟨t, ht, z, hz, hst⟩ := h.exists_eq_mul_central hs hs1 hy hfix
  have ht1 : t ≠ 1 := by
    intro ht1
    have hsz : s = z := by rw [hst, ht1, one_mul]
    have hsZ : s ∈ Z := by rw [hsz]; exact hz
    have hsinf : s ∈ T₁ ⊓ Z := Subgroup.mem_inf.2 ⟨hs, hsZ⟩
    rw [h.inf_Z₁, Subgroup.mem_bot] at hsinf
    exact hs1 hsinf
  have hne : conjSubgroup x T ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (conjSubgroup x T) = Nat.card T :=
      CFSG.RankThree.GF2n.card_conjSubgroup x T
    rw [hbot, Subgroup.card_bot] at hcard
    have h4 := h.four_le
    omega
  obtain ⟨⟨a, ha⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1 : a ≠ 1 := fun he => ha1' (Subtype.ext he)
  have hsa : s * a = a * s := h.commute_of_fix hs hs1 (hx s hs) ha
  have hza : a * z = z * a := Subgroup.mem_center_iff.1 (h.central hz) a
  have hat : a * t = t * a := by
    have h1 : a * (t * z) = (t * z) * a := by
      rw [← hst]
      exact hsa.symm
    have h2 : (a * t) * z = (t * a) * z := by
      calc (a * t) * z = a * (t * z) := by rw [mul_assoc]
        _ = (t * z) * a := h1
        _ = t * (z * a) := by rw [mul_assoc]
        _ = t * (a * z) := by rw [hza]
        _ = (t * a) * z := by rw [mul_assoc]
    exact mul_right_cancel h2
  have hZ : ⁅a, t⁆ ∈ Z := by
    rw [commutatorElement_eq_one_iff_mul_comm.2 hat]
    exact Z.one_mem
  have hcl : conjSubgroup x T = conjSubgroup y T := h.closed x y a ha ha1 t ht ht1 hZ
  exact ⟨y, hy, hcl.symm, t, hcl.symm ▸ ht, z, hz, hst⟩

theorem le_sup_central_of_fix (h : Abs612 T T₁ Z E) {x : X}
    (hx : ∀ s ∈ T₁, conjSubgroup s (conjSubgroup x T) = conjSubgroup x T) :
    T₁ ≤ conjSubgroup x T ⊔ Z := by
  intro s hs
  by_cases hs1 : s = 1
  · rw [hs1]
    exact Subgroup.one_mem _
  · obtain ⟨y, hy, -, t, ht, z, hz, hst⟩ := h.exists_mem_sup_conj_eq hx hs hs1
    rw [hst]
    exact Subgroup.mul_mem_sup ht hz

theorem eq_conj_of_fix (h : Abs612 T T₁ Z E) {x : X}
    (hx : ∀ s ∈ T₁, conjSubgroup s (conjSubgroup x T) = conjSubgroup x T) :
    T₁ = conjSubgroup x T := by
  have hcard : Nat.card T₁ = Nat.card (conjSubgroup x T) :=
    h.card_eq.trans (CFSG.RankThree.GF2n.card_conjSubgroup x T).symm
  have h4 : 4 ≤ Nat.card (conjSubgroup x T) := by
    rw [CFSG.RankThree.GF2n.card_conjSubgroup x T]
    exact h.four_le
  refine eq_of_le_sup_central (T' := conjSubgroup x T) (h.elem_conj x) h.central (h.inf_Z_conj x)
    h.inf_Z₁ hcard h4 (h.le_sup_central_of_fix hx) ?_ h.strongWC₁
  intro t ht ht1 t' ht' ht'1
  obtain ⟨⟨s, hs⟩, hs1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.ne_bot₁
  have hs1 : s ≠ 1 := fun he => hs1' (Subtype.ext he)
  obtain ⟨y, hy, hyx, -⟩ := h.exists_mem_sup_conj_eq hx hs hs1
  exact h.exists_conj_of_mem_conj_sub hs hs1 hy (hyx.symm ▸ ht) ht1 (hyx.symm ▸ ht') ht'1

theorem exists_conj_eq (h : Abs612 T T₁ Z E) : ∃ x : X, T₁ = conjSubgroup x T := by
  obtain ⟨x, hx⟩ := h.exists_fixed_orbit
  exact ⟨x, h.eq_conj_of_fix hx⟩

theorem quotPair (h : Abs612 T T₁ Z E) : QuotPair T T₁ := by
  obtain ⟨x, hx⟩ := h.exists_conj_eq
  refine ⟨h.elem, h.elem₁, h.ne_bot, h.ne_bot₁, ?_, h.sup, ?_⟩
  · intro hTT
    have hle : T₁ ≤ Subgroup.normalizer (T : Set X) := by
      intro s hs
      exact Subgroup.le_normalizer (hTT.symm ▸ hs)
    have hbot : T₁ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro s hs
      exact h.inf_normalizer s hs (hle hs)
    exact h.ne_bot₁ hbot
  · intro U hU V hV u hu hu1 v hv hv1 hcomm
    have hmem : ∀ W ∈ pairConj T T₁, ∃ g : X, W = conjSubgroup g T := by
      intro W hW
      obtain ⟨g, rfl | rfl⟩ := hW
      · exact ⟨g, rfl⟩
      · refine ⟨g * x, ?_⟩
        rw [hx, CFSG.RankThree.GF2n.conjSubgroup_mul]
    obtain ⟨g, rfl⟩ := hmem U hU
    obtain ⟨g', rfl⟩ := hmem V hV
    exact h.closed g g' u hu hu1 v hv hv1
      (by rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]; exact Z.one_mem)

end Certified

end Abs612

end CFSG.LocalAnalysis.WeakClosure81
