module

public import CFSG.LocalAnalysis.StandardType.GGQ2ThreeEltOfPm
public import CFSG.LocalAnalysis.StandardType.GGQ2PmOfDatum
public import CFSG.LocalAnalysis.StandardType.GGQ2PmHeartA
public import CFSG.LocalAnalysis.StandardType.GGQ2LabelCartan
public import CFSG.LocalAnalysis.StandardType.GGQ2LDatumDims

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_threeElt_normW {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel} (hW : GGQ2LabelWeyl labL M.coxeter)
    (hlab : GGQ2TBLabel labL) (hne : labL.tag ≠ .twE6) (hsh : M.Shape) (hx : M.xV ≠ 0)
    (hev : Even (Module.finrank (ZMod 3) M.V)) (h6 : 6 ≤ Module.finrank (ZMod 3) M.V)
    (hhrt : Module.finrank (ZMod 3) M.V ≤ Fintype.card M.Λ →
      (labL.tag = .twA ∧ 3 ∣ labL.rank + 1) ∨ labL.tag = .twE6)
    (hNT : GGNoTransvection 3 Bs) (φ : MulAut ↥Bs) (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)))
    (hfix : ggLin (p := 3) M.model φ M.xV = M.xV) (h3 : φ ^ 3 = 1) :
    φ ∈ ggAutomizer L Bs := by
  by_cases hB : M.ShapeB
  ·
    have hdim : Module.finrank (ZMod 3) M.V = Fintype.card M.Λ :=
      ggQ2LD_dim_heart M (Or.inl hB)
    rcases hhrt (le_of_eq hdim) with ⟨htag, -⟩ | htwE6
    · rcases ggQ2_label_cartan M hW hlab with
        hA | hBC | hD | hE7 | hF4 | htwE6' | hE8
      · obtain ⟨-, e, hC⟩ := hA
        have hcard : Fintype.card M.Λ = labL.rank := by
          rw [ggQ2LD_card_lie hW hlab]
          simp [GGQ2LieRank, htag]
        have hr : 6 ≤ labL.rank := by
          rw [← hcard, ← hdim]
          exact h6
        exact ggQ2_threeElt_of_pm M hx hNT φ hφ hN hfix h3
          (ggQ2_pm_heartA M e hC (by omega) hB φ hN)
      · obtain ⟨hBCtag, -⟩ := hBC
        rcases hBCtag with hBtag | hCtag
        · rw [htag] at hBtag
          cases hBtag
        · rw [htag] at hCtag
          cases hCtag
      · obtain ⟨hDtag, -⟩ := hD
        rcases hDtag with hDtag | htwDtag
        · rw [htag] at hDtag
          cases hDtag
        · rw [htag] at htwDtag
          cases htwDtag
      · obtain ⟨hE7tag, -⟩ := hE7
        rw [htag] at hE7tag
        cases hE7tag
      · rw [htag] at hF4
        cases hF4
      · exact absurd htwE6' hne
      · rw [htag] at hE8
        cases hE8
    · exact absurd htwE6 hne
  ·
    have hpm := ggQ2_pm_of_datum M hW hlab hne hsh hx hev h6 hhrt hB hNT φ hN
    exact ggQ2_threeElt_of_pm M hx hNT φ hφ hN hfix h3 hpm

end CFSG.StandardType

end
