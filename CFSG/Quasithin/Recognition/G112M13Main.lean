module

public import CFSG.Quasithin.Recognition.G112M13Steps
public import CFSG.Quasithin.Recognition.G112M13Steps2
import CFSG.Quasithin.Background.SzG11TwoOm4
import CFSG.Quasithin.Background.SzG11TwoSp4
import CFSG.Quasithin.Background.SzG11TwoG2
import CFSG.Quasithin.Background.P3OrthoA8Fact
import CFSG.Quasithin.Background.E11Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace Canon

open CFSG.Quasithin.G11.G117

theorem g11_7_of_stepsM (Q : ConclPred) (hQ : QContainsM Q) (hApply : G93ApplyStmt)
    (hM12 : SzG11S.NoConfigM12) (hL2 : SzG11S.NoConfigL2) (hOm4m : SzG11S.NoConfigOm4Minus)
    (hSp4 : SzG11S.NoConfigSp4) (hOm4p : SzG11S.NoConfigOm4Plus)
    (hOm4p4 : SzG11S.NoConfigOm4PlusFour) (hM22 : AutHatM22Bound) (hA8 : A8OrthogonalFact)
    (hOm4Iso : Om4Plus4Iso) (s10 : Step10 Q) (sLt : StepLt Q) :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
      (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
      QSetup Q B Γ v₁ W X X₀ L → ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        ¬ FaithfulOn X I ∧ I ≠ ⊤ := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs I hI
  suffices hnf : ¬ FaithfulOn X I from
    ⟨hnf, fun htop => hnf (by
      rw [htop]
      exact faithfulOn_iff.2 fun k _ hk => LinearEquiv.ext fun v => hk v Submodule.mem_top)⟩
  intro hfaith
  obtain ⟨m, hm⟩ := hs.conf.h108.toG101Hyp.exists_card_X
  have c : QCtx Q B Γ v₁ W X X₀ L I m := ⟨hs, hI, hfaith, hm⟩
  have hconcl := c.g93 hApply
  have hsd := G93ConclDimensionOnly.of_selfDual hconcl
    (selfDual_restrictRange c.invariantH (props_selfDual hI))
  by_cases htop : I = ⊤
  · subst htop
    rcases hsd with h0 | h2 | h4 | h6 | h7 | h9 | h10 | h12 | h15 | h16
    · exact step0 hM12 c h0
    · exact step2M hQ hM22 c h2
    · exact step4M hQ c h4
    · exact step6M hQ hL2 c h6
    · exact step7M hQ hOm4m c h7
    · exact step9M hQ hSp4 c h9
    · exact s10 V B Γ v₁ W X X₀ L m c h10
    · exact step12M hQ hA8 c h12
    · exact step15M hQ hOm4p hOm4p4 hOm4Iso c h15
    · exact step16M hQ c h16
  · have h2d : 2 * Module.finrank (ZMod 2) ↥I ≤ Module.finrank (ZMod 2) V :=
      c.two_mul_finrank_le htop
    have hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1) := c.finrank_V_le
    rcases hsd with h0 | h2 | h4 | h6 | h7 | h9 | h10 | h12 | h15 | h16
    · obtain ⟨⟨hm4, hd10, -⟩, -⟩ := h0
      have hd10' : Module.finrank (ZMod 2) ↥I = 10 := hd10
      omega
    · obtain ⟨⟨hm5, hd12, -⟩, -⟩ := h2
      have hd12' : Module.finrank (ZMod 2) ↥I = 12 := hd12
      omega
    · obtain ⟨⟨hm2, hd6, hm3, -⟩, -⟩ := h4
      have hd6' : Module.finrank (ZMod 2) ↥I = 6 := hd6
      omega
    · obtain ⟨n, ⟨hn2, hdn, hnm, hmn, -⟩, -⟩ := h6
      have hdn' : Module.finrank (ZMod 2) ↥I = 2 * n := hdn
      omega
    · obtain ⟨a, ⟨ha1, hda, ham, hma, -⟩, -⟩ := h7
      have hda' : Module.finrank (ZMod 2) ↥I = 4 * a := hda
      omega
    · obtain ⟨n, ⟨hn1, hdn, hnm, hmn, -, hperm⟩, hend, -⟩ := h9
      have hdn' : Module.finrank (ZMod 2) ↥I = 4 * n := hdn
      have hn : n = 1 := by omega
      subst hn
      exact sLt V B Γ v₁ W X X₀ L I m c c.invariantH htop (by omega) (by omega) (by omega)
        (hperm rfl) hend
    · obtain ⟨n, ⟨hn1, hdn, hnm, hmn, -⟩, -⟩ := h10
      have hdn' : Module.finrank (ZMod 2) ↥I = 6 * n := hdn
      omega
    · obtain ⟨⟨hm2, hd6, hm4, -⟩, -⟩ := h12
      have hd6' : Module.finrank (ZMod 2) ↥I = 6 := hd6
      omega
    · obtain ⟨n, ⟨hn2, hdn, hnm, hmn, -⟩, -⟩ := h15
      have hdn' : Module.finrank (ZMod 2) ↥I = 4 * n := hdn
      omega
    · obtain ⟨⟨hm3, hd8, -⟩, -⟩ := h16
      have hd8' : Module.finrank (ZMod 2) ↥I = 8 := hd8
      omega

section G117Canon


theorem g11_7_canonM
    {Q : ConclPred} (hQ : QContainsM Q) :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
      (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
      QSetup Q B Γ v₁ W X X₀ L → ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        ¬ FaithfulOn X I ∧ I ≠ ⊤ :=
  g11_7_of_stepsM Q hQ (g93_apply Harris.g93StmtDimensionOnly_holds)
    SzG11S.noConfigM12 SzG11S.noConfigL2
    (SzG11S.noConfigOm4Minus_of_two SzG11S.noConfigOm4MinusTwo)
    (SzG11S.noConfigSp4_of_two SzG11S.noConfigSp4Two) SzG11S.noConfigOm4Plus
    SzG11S.noConfigOm4PlusFour G117.autHatM22Bound a8OrthogonalFact om4Plus4Iso
    (step10M hQ (SzG11S.noConfigG2_of_two SzG11S.noConfigG2Two) g22DerivedFacts)
    (stepLtM e11 G117.a6NormalizerBound G117.a6Facts hQ)

end G117Canon

end Canon

end G11

end CFSG.Quasithin
