module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutJ
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutSteps

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G]


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem item217NotInLLocal_of_steps (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hS : Sec217OutSecond) (hE : Sec217OutElements) (hT : Sec217OutTransvection)
    (hJ : Sec217OutJCentral) : Item217NotInLLocal := by
  intro G _ _ A E U c L hp hq hc _ h81 hext
  have h : CoverOut A E U c L := ⟨hp, hq, hc, h81, hext⟩
  obtain ⟨a, U₀, K, hOS⟩ := hS G A E U c L h
  obtain ⟨u, v, huv⟩ := hE G A E U c L a U₀ K hOS
  obtain ⟨d, hd1, hzd, -, -, -, -, htr, hcom, hfix⟩ := hT G A E U c L a U₀ K hOS u v huv
  have hfr := hOS.frame
  have hfrd : Frame217 E c L d := (h.frame_of_zpowers_eq_inf h45 hfr hzd).2
  obtain ⟨x, hxLN, hxd⟩ : ∃ x ∈ L ⊓ Subgroup.normalizer (A : Set G),
      x ∉ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    have hnofix := sec217OutNoFix_holds h45 G A E U c L hp hq hc h81 hext d hfrd
    by_contra hno
    push Not at hno
    exact hnofix (fun x hx => hno x hx)
  have hEA : E ≤ A := hp.mem_E.2
  have hDA : dGroup a c ≤ A :=
    sup_le (Subgroup.zpowers_le.2 (hEA hfr.mem)) (Subgroup.zpowers_le.2 h.c_mem_A)
  have hdDL : d ∈ dGroup a c ⊓ L := hzd ▸ Subgroup.mem_zpowers d
  have hdA : d ∈ A := hDA hdDL.1
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have htA : u * v⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    mul_mem huv.mem_u.2 (inv_mem huv.mem_v.2)
  obtain ⟨hfixel, hcomel⟩ := transvection_elementwise htA hfix hcom
  have hJ1 := hJ G A E U c L a h hfr d hzd ⟨u * v⁻¹, htA, htr, hcom, hfix⟩
  refine out_final (A := A) (L := L) (D := dGroup a c) (c := c) (d := d) (t := u * v⁻¹) (x := x)
    h.c_mem_A (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)) h.c_comm hdA hdDL.2
    (hab.2 d hdA) (hzd ▸ le_rfl) hxLN.1 hxLN.2 hxd htA (IsTransvectionOn.pow_three htr)
    (fun y hy => (hfixel y hy.1).2 hy) hcomel ?_ ?_
  · intro hc'
    have := (hfixel c h.c_mem_A).1 hc'
    exact h.notMem this.2
  · exact fun s hs hsd _ => h.normalizes_D h48 h45 hfr hzd hJ1 s hs hsd

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
