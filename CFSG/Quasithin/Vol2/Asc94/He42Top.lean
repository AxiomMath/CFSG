module

public import CFSG.Quasithin.Vol2.Asc94.He42Ctx
public import CFSG.Quasithin.Vol2.Asc94.He42Main
public import CFSG.Quasithin.Vol2.Asc94.He42TI

public section

namespace CFSG.Quasithin.A94

open Subgroup CFSG.CGT.M24S CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS81

@[expose] def He42Input426 : Prop :=
  ∀ (hF6 : L52.F6Model) (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc),
    IsSimpleGroup G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ (S : Setting G z e) (h1 : normalizer (tr e L52.U1 : Set G) = Cz z)
      (h2 : normalizer (tr e L52.U2 : Set G) = Cz z) (a x : G)
      (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1)
      (hxN : x ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G))
      (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3),
      centralizer ((HeB e x : Subgroup G) : Set G) ≤ HeL e (HeB e x)

@[expose] def He42Input427 : Prop :=
  ∀ (hF6 : L52.F6Model) (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc),
    IsSimpleGroup G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ (S : Setting G z e) (h1 : normalizer (tr e L52.U1 : Set G) = Cz z)
      (h2 : normalizer (tr e L52.U2 : Set G) = Cz z) (a x : G)
      (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1)
      (hxN : x ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G))
      (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3),
      centralizer ({a} : Set G) ≤ normalizer ((HeB e x : Subgroup G) : Set G)

theorem he42_of_inputs
    (h422 : ∀ (hF6 : L52.F6Model) (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc),
        IsSimpleGroup G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ (S : Setting G z e) (h1
        : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z) (a
        x : G) (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1) (hxN : x ∈ normalizer
        ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) (hxa : x ∈ centralizer ({a} : Set G))
        (hx3 : orderOf x = 3) (y₁ y₂ : G), He42.YSpec (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN
        hxa hx3) y₁ y₂ → He42.Open422 (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3) y₁
        y₂) (h426 : He42Input426)
    (h427 : He42Input427) : He42 := by
  intro hF6 G _ _ z e hs hK S h1 h2
  obtain ⟨a, ha, ham⟩ := HeJ.exists_a e
  obtain ⟨x, hxN, hxa, hx3⟩ := (HeJ.data40 e hF6 S h1 h2 ha ham).exists_x
  refine ⟨a, x, ha, ham, hxN, hxa, hx3, ?_⟩
  set S0 := He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3 with hS0
  have hB := S0.baseFacts
  have hmain := S0.typeL34_main (fun y₁ y₂ hY => h422 hF6 G z e hs hK S h1 h2 a x ha ham hxN hxa hx3 y₁ y₂ hY)
  refine ⟨?_, hmain.2, ?_⟩
  ·
    refine le_antisymm (sup_le ?_ ?_) (h426 hF6 G z e hs hK S h1 h2 a x ha ham hxN hxa hx3)
    · exact inf_le_right
    · exact inf_le_right
  ·
    have hfus : S0.StepFus := by
      intro y hy y' hy' g hg
      exact (frame2 e S.ord hF6).fusion_B (a := y) (b := y') hy hy' hg
    exact S0.tightlyEmbedded_of hB hfus
      (fun c hc => h427 hF6 G z e hs hK S h1 h2 a x ha ham hxN hxa hx3
        (Subgroup.mem_centralizer_singleton_iff.mpr hc))

end CFSG.Quasithin.A94
