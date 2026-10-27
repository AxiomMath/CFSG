module

public import CFSG.Quasithin.Vol2.Ch3T326J
public import CFSG.Quasithin.Vol2.Ch3T326Q
public import CFSG.Quasithin.Vol2.Ch3T326YB

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def CaseD321 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), Ctx T L V₀ →
    ∀ (_ : IsMulCommutative ↥(conjClosure V₀ T))
      (_ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)))),
      conjClosure V₀ T ≠
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) →
      Concl326C3 T L V₀

theorem stmt3_2_6C_of_cases (h331 : Stmt3_3_1)
    (h3222 : Vol2.Ch10.TmpL6_3_2_2_two) (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight)
    (h316 : Theorem316Statement) (hA37 : Vol2Native.A37ForSQTKCat)
    (hA38 : Vol2Native.A38ForSQTKCat) (hD37 : D37) (hD36 : D36c) (hL38 : D3L38)
    (hB48 : D36B48q) (h6 : Vol2.Ch11.TmpL6_3_2_2_six) (hG : T326ActsGlued)
    (hd321 : CaseD321) : Stmt3_2_6C := by
  intro G _ _ T L V₀ hfsu hne
  have c := Ctx.of h331 h3222 h3228 hfsu hne
  have := c.elemV.1
  have := c.elemVM.1
  obtain ⟨_, hq⟩ := qhat_VM h316 c
  refine ⟨qhat_V h316 c, c.elemVM.1, hq, ?_⟩
  by_cases hV : conjClosure V₀ T =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))
  · by_cases hV₀ : V₀ = conjClosure V₀ T
    · rcases c.case_d37 h316 hA37 hA38 hD37 hV₀ hV with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (c.case_d36 h316 hA37 hA38 hD36 hL38 hG hV₀ hV
        (fun s hs hsn x hx hDx hIlt htriv hU h32 =>
          c.concl_ii hA37 hA38 hB48 h6 hV s hs hsn x hx hDx hIlt htriv hU h32)))
  · exact Or.inr (Or.inr (hd321 G T L V₀ c inferInstance inferInstance hV))

end CFSG.Quasithin.H13.T326
