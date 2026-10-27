module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G]

private theorem s16h_e3_inf_centralizer_eq_preTil {V L K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hK : K ≤ stabTil ⊥ V) :
    wSub ⊥ V hV L ⊓ Subgroup.centralizer (K : Set G) =
      preTil ⊥ V hV (wTil ⊥ V hV L ⊓ fixV (barSub ⊥ V hV K)) := by
  ext v
  rw [Subgroup.mem_inf, mem_preTil]
  constructor
  · rintro ⟨hvW, hvc⟩
    have hvV : v ∈ V := preTil_le ⊥ V hV (wTil ⊥ V hV L) hvW
    refine ⟨IntMod.mk hV ⟨v, hvV⟩, rfl, ?_⟩
    rw [Subgroup.mem_inf]
    refine ⟨(mem_preTil_iff_of_mem ⊥ V hV (wTil ⊥ V hV L) hvV).1 hvW, ?_⟩
    rw [s16c7_mem_fixV_barSub_iff V hV hK]
    intro y hy
    have h := (Subgroup.mem_centralizer_iff.1 hvc) y hy
    calc y * v * y⁻¹ = v * y * y⁻¹ := by rw [h]
      _ = v := by group
  · rintro ⟨x, hxe, hx⟩
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxw, hxfix⟩ := hx
    have hvV : x.val ∈ V := x.val_mem
    refine ⟨?_, ?_⟩
    · rw [← hxe]
      exact (mem_preTil_iff_of_mem ⊥ V hV (wTil ⊥ V hV L) hvV).2 hxw
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := (s16c7_mem_fixV_barSub_iff V hV hK x).1 hxfix y hy
      rw [← hxe]
      calc y * x.val = y * x.val * y⁻¹ * y := by group
        _ = x.val * y := by rw [h]

theorem s16h_e3_inf_centralizer_eq_of_barSub_eq {V L K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hL : L ≤ stabTil ⊥ V) (hK : K ≤ stabTil ⊥ V)
    (hbar : barSub ⊥ V hV L = barSub ⊥ V hV K) :
    wSub ⊥ V hV L ⊓ Subgroup.centralizer (K : Set G) =
      wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) := by
  rw [s16h_e3_inf_centralizer_eq_preTil hV hK,
    s16h_e3_inf_centralizer_eq_preTil hV hL, hbar]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
