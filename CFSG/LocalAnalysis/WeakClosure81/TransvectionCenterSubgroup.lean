module

public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Open.StatedAPI CFSG.CGT.Timmesfeld75 Matrix

variable {m : ℕ} {F : Type} [Field F]

noncomputable def transvectionCenterSubgroup (m : ℕ) (F : Type) [Field F] [Finite F]
    (hm : 2 ≤ m) (a : Fin m → F) (ha : a ≠ 0) :
    Subgroup (StatedProj (StatedSL m F)) :=
  ((transvCenter m F a).subgroupOf (StatedSL m F)).map
    (QuotientGroup.mk' ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F)))

@[simp] theorem coe_transvectionCenterSubgroup (m : ℕ) (F : Type) [Field F] [Finite F]
    (hm : 2 ≤ m) (a : Fin m → F) (ha : a ≠ 0) :
    (transvectionCenterSubgroup m F hm a ha : Set (StatedProj (StatedSL m F))) =
      transvectionCenterSet m F a := by
  ext x
  change x ∈ (QuotientGroup.mk' ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F))) ''
      ((transvCenter m F a).subgroupOf (StatedSL m F)) ↔ x ∈ transvectionCenterSet m F a
  constructor
  · rintro ⟨g, hg, rfl⟩
    change (g : GL (Fin m) F) ∈ transvCenter m F a at hg
    obtain ⟨f, hfa, hg⟩ := hg
    exact ⟨g, rfl, f, hfa, hg⟩
  · rintro ⟨g, hgx, f, hfa, hg⟩
    refine ⟨g, ?_, ?_⟩
    · change (g : GL (Fin m) F) ∈ transvCenter m F a
      exact ⟨f, hfa, hg⟩
    · rw [QuotientGroup.mk'_apply]
      exact hgx

end CFSG.LocalAnalysis.WeakClosure81
