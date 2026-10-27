module

public import CFSG.Quasithin.Background.G10FifteenMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

theorem g10_15 (h10 : G1010Stmt) (h11 : G1011Stmt) (h12 : G1012Stmt) (h13 : G1013Stmt)
    (h1212 : G1212Stmt) (hOut : OuterGLInput) (hSimple : InspectSimple)
    (hOuter : InspectOuter) (hSylow : InspectSylow) (hSQT : SectionSQTInput) : G1015Stmt := by
  intro V _ _ _ B Γ v₁ W X X₀ L hyp hq
  have h10' := h10 V B Γ v₁ W X X₀ L hyp
  have h11' := h11 V B Γ v₁ W X X₀ L hyp
  have h12' := h12 V B Γ v₁ W X X₀ L hyp
  have h13' := h13 V B Γ v₁ W X X₀ L hyp
  obtain ⟨I, hI, hfix⟩ := hyp.exists_irr_fixed
  by_cases hall : ∀ x ∈ X, conjSub x I = I
  · refine hyp.case1 h10' h11' h13' hI fun k hk u hu => ?_
    have := apply_mem_conjSub (g := k) hu
    rwa [hall k hk] at this
  · push Not at hall
    obtain ⟨x, hx, hne⟩ := hall
    exact hyp.case2 hq hOut hSQT h1212 hSimple hOuter hSylow h10' h11' h12' hI hfix hx hne

end G11

end CFSG.Quasithin
