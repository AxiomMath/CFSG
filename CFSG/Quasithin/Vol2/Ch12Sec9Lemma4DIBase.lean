module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec8OneExist
public import CFSG.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint

section Base

variable {G : Type} [Group G] [Finite G]
variable {T L V V₁ V₂ K₁ : Subgroup G}

theorem sq_eq_one_of_cx (hcx : Cx1291 G T L V 4) : ∀ v ∈ V, v ^ 2 = 1 :=
  (Hyp1281One.card_sq hcx.hyp).2.1

theorem card_V₁ (hs : Setting1282One G T L V 4 V₁ V₂) : Nat.card V₁ = 2 := by
  have h := hs.v1.2.1
  norm_num at h
  exact h

theorem card_V₂ (hs : Setting1282One G T L V 4 V₁ V₂) : Nat.card V₂ = 4 := by
  have h := hs.v2.2.1
  norm_num at h
  exact h

theorem T_le_normalizer_V₁ (hs : Setting1282One G T L V 4 V₁ V₂) :
    T ≤ Subgroup.normalizer (V₁ : Set G) := hs.v1.2.2

theorem exists_a_mem (hs : Setting1282One G T L V 4 V₁ V₂) : ∃ a ∈ V₂, a ∉ V₁ := by
  by_contra hne
  push Not at hne
  have h1 := Subgroup.card_le_of_le (show V₂ ≤ V₁ from fun x hx => hne x hx)
  rw [card_V₂ hs, card_V₁ hs] at h1
  norm_num at h1

theorem K₁_le_normalizer (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G))) :
    K₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
  le_of_mem_cComp (show K₁ ∈ cComp _ from hK)

theorem p128_le_normalizer_V₂ (hs : Setting1282One G T L V 4 V₁ V₂) :
    p128 T L V ≤ Subgroup.normalizer (V₂ : Set G) := by
  intro g hg
  have h := Subgroup.mem_iInf.1 hg.2 V₂
  exact (Subgroup.mem_iInf.1 h ⟨2, by norm_num, hs.v2⟩)

end Base

end CFSG.Quasithin.H13.C1294
