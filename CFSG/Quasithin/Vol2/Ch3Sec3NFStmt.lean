module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321Steps
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321W
public import CFSG.Quasithin.Background.FLc3Mod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open scoped IsMulCommutative

abbrev NFSite : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H : Subgroup G), Prop

@[expose] def sgn4 (q : ℕ) : ℤ := if q % 4 = 1 then 1 else -1

@[expose] def Obl3_3_13D12NF_outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), Hyp331 G T M L D → InH T H →
    H ≤ L ⊔ T → Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) → pCoreOf 2 (H ⊔ D) ≠ ⊥ →
    K ∈ cComp (H ⊔ D) → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    oTwoUpper H ≤ conjClosure K T → ¬ T ≤ Subgroup.normalizer (K : Set G) →
    (∃ q : ℕ, q.Prime ∧ (q % 24 = 11 ∨ q % 24 = 13) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1) →
    ¬ InducesInnerOn (T ⊓ Subgroup.normalizer (K : Set G)) K →
    D ≤ Subgroup.normalizer (oTwoUpper H : Set G)

@[expose] def Site3314 : NFSite := fun G _ _ T _ L _ _ =>
  ¬ T ≤ Subgroup.normalizer (L : Set G) ∧
    ∃ _ : IsMulCommutative ↥(vPlus L T), Case3_3_8_one T L ∧ IsPSL 3 2 1 ↥(autOn L (vPlus L T))

@[expose] def Site3314line : NFSite := fun G _ _ T M L D H =>
  Site3314 G T M L D H ∧
    ⁅vPlus L T, mPlus L T⁆ ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥

@[expose] def Site3314pt : NFSite := fun G _ _ T M L D H =>
  Site3314 G T M L D H ∧
    ⁅vPlus L T, mPlus L T⁆ ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≠ ⊥

@[expose] def Site3321a1 : NFSite := fun G _ _ T _ L _ H =>
  T ≤ Subgroup.normalizer (L : Set G) ∧
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
    ∃ _ : IsMulCommutative ↥(vPlus L T), Mod3321Sum T L ∧ ¬ InducesInnerOn T L ∧
      ∃ (α : ↥L →* L3321.SL4) (ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T))
        (U₁ U₂ : Subgroup ↥(vPlus L T)),
        Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
        ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4 ∧
        (∀ (l : ↥L) (hl : (l : G) ∈ Subgroup.normalizer (vPlus L T : Set G)),
          ρ (α l) = conjAct (vPlus L T) ⟨l, hl⟩) ∧
        IsIntDirect U₁ U₂ (commV (autOn L (vPlus L T))) ∧
        Nonempty (FLc.VModel 4 ρ U₁ ⊥ (Multiplicative (FLc.Vt 4))
          (fun g a => FLc.actM g a)) ∧
        Nonempty (FLc.VModel 4 ρ U₂ ⊥ (Multiplicative (FLc.Vt 4)) FLc.actDl) ∧
        H = L3316.liftPre α L3321.P2 ⊔ T

@[expose] def Site3321a2 : NFSite := fun G _ _ T _ L _ H =>
  T ≤ Subgroup.normalizer (L : Set G) ∧
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
    ∃ _ : IsMulCommutative ↥(vPlus L T), Mod3321Ext T L ∧ ¬ InducesInnerOn T L ∧
      H = (L ⊔ T) ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

@[expose] def Obl3_3_13D12NFOn (P : NFSite) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), Hyp331 G T M L D →
    P G T M L D H → InH T H → H ≤ L ⊔ T →
    Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) → pCoreOf 2 (H ⊔ D) ≠ ⊥ →
    K ∈ cComp (H ⊔ D) → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    oTwoUpper H ≤ conjClosure K T → ¬ T ≤ Subgroup.normalizer (K : Set G) →
    ¬ CFSG.Open.quasithinIsFaithfulLocal T K →
    InducesInnerOn (T ⊓ Subgroup.normalizer (K : Set G)) K →
    (∃ q : ℕ, q.Prime ∧ (q % 24 = 11 ∨ q % 24 = 13) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1) → False

@[expose] def Obl3_3_13D12NF_314 : Prop := Obl3_3_13D12NFOn Site3314

@[expose] def Obl3_3_13D12NF_314pt : Prop := Obl3_3_13D12NFOn Site3314pt

@[expose] def Obl3_3_13D12NF_a1 : Prop := Obl3_3_13D12NFOn Site3321a1

@[expose] def Obl3_3_13D12NF_a2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) →
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    ∀ _ : IsMulCommutative ↥(vPlus L T), Mod3321Ext T L → ¬ InducesInnerOn T L →
    H = (L ⊔ T) ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    InH T H → H ≤ L ⊔ T → Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) →
    pCoreOf 2 (H ⊔ D) ≠ ⊥ → K ∈ cComp (H ⊔ D) → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    oTwoUpper H ≤ conjClosure K T → ¬ T ≤ Subgroup.normalizer (K : Set G) →
    ¬ CFSG.Open.quasithinIsFaithfulLocal T K →
    InducesInnerOn (T ⊓ Subgroup.normalizer (K : Set G)) K →
    (∃ q : ℕ, q.Prime ∧ (q % 24 = 11 ∨ q % 24 = 13) ∧ ¬ (9 : ℤ) ∣ (q : ℤ) - sgn4 q ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1) → False

@[expose] def Obl3_3_13D12NF_a2_nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) →
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    ∀ _ : IsMulCommutative ↥(vPlus L T), Mod3321Ext T L → ¬ InducesInnerOn T L →
    H = (L ⊔ T) ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    InH T H → H ≤ L ⊔ T → Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) →
    pCoreOf 2 (H ⊔ D) ≠ ⊥ → K ∈ cComp (H ⊔ D) → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    oTwoUpper H ≤ conjClosure K T → ¬ T ≤ Subgroup.normalizer (K : Set G) →
    ¬ CFSG.Open.quasithinIsFaithfulLocal T K →
    InducesInnerOn (T ⊓ Subgroup.normalizer (K : Set G)) K →
    (∃ q : ℕ, q.Prime ∧ (q % 24 = 11 ∨ q % 24 = 13) ∧ (9 : ℤ) ∣ (q : ℤ) - sgn4 q ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1) → False

theorem obl3_3_13D12NFOn_a2_of (h : Obl3_3_13D12NF_a2) (hn : Obl3_3_13D12NF_a2_nine) :
    Obl3_3_13D12NFOn Site3321a2 := by
  intro G _ _ T M L D H K hyp hP hH hHLT he hO hK hKq hYK hTK hKf hin hq
  obtain ⟨hTL, ⟨e⟩, hc, hmod, hout, hHeq⟩ := hP
  obtain ⟨q, hq, h24, hmodel⟩ := hq
  by_cases h9 : (9 : ℤ) ∣ (q : ℤ) - sgn4 q
  · exact hn G T M L D H K hyp hTL ⟨e⟩ hc hmod hout hHeq hH hHLT he hO hK hKq hYK hTK hKf hin
      ⟨q, hq, h24, h9, hmodel⟩
  · exact h G T M L D H K hyp hTL ⟨e⟩ hc hmod hout hHeq hH hHLT he hO hK hKq hYK hTK hKf hin
      ⟨q, hq, h24, h9, hmodel⟩

end CFSG.Quasithin.H13
