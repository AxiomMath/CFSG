module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankExclusionFinishPart2

@[expose] public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.Open
open CFSG.StandardType.LieCore
open CFSG.StandardType.F4ExplicitPos.RankExclusion
open CFSG.StandardType.F4ExplicitPos.LowRankModels
open CFSG.StandardType.F4ExplicitPos.ComponentAttach
open CFSG.StandardType.F4ExplicitPos.CyclicFinish
open CFSG.StandardType.F4ExplicitPos.InnerDirect
open CFSG.StandardType.F4ExplicitPos.CenterProofFast
open CFSG.StandardType.F4ExplicitPos.CubicLiteral
open CFSG.StandardType.F4ExplicitPos.CubicAction
open CFSG.StandardType.F4ExplicitPos.AmbientAction
open CFSG.StandardType.F4ExplicitPos.Quasisimple
open CFSG.StandardType.F4ExplicitPos.CTNative
open scoped Pointwise

namespace CFSG.StandardType.F4ExplicitPos.RankExclusionFinish

theorem theta_eq_one_centralizes
    {Ω : Type} [Field Ω]
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X}
    [Algebra (GaloisField 2 f) Ω]
    {G0 B1 : Subgroup X}
    (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    {g0 : ModGL Tag.F4 Ω} {eB : B1}
    (hTheta : ThetaF4 (L := Ω) ψ G0 B1 hG0 hker hcenter hBN hinner g0 eB = 1) :
    (eB : X) ∈ Subgroup.centralizer (G0 : Set X) := by
  have hkerEq := CFSG.StandardType.F4ExplicitPos.ComponentAttach.ThetaF4_ker
    (L := Ω) ψ G0 B1 hG0 hker hcenter hBN hinner g0
  have hb : eB ∈ (ThetaF4 (L := Ω) ψ G0 B1 hG0 hker hcenter hBN hinner g0).ker := by
    rw [MonoidHom.mem_ker]
    exact hTheta
  rw [hkerEq, Subgroup.mem_subgroupOf] at hb
  exact hb

theorem component_eq_G0_of_theta_eq_one
    {Ω : Type} [Field Ω]
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X}
    [Algebra (GaloisField 2 f) Ω]
    {G0 B1 : Subgroup X}
    (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    {g0 : ModGL Tag.F4 Ω} {eB : B1}
    (hTheta : ThetaF4 (L := Ω) ψ G0 B1 hG0 hker hcenter hBN hinner g0 eB = 1)
    {K : Subgroup X} (hKG : K ≤ G0)
    (hKcomp : CFSG.Assembly.IsComponentOf K
      (Subgroup.centralizer ({(eB : X)} : Set X))) :
    K = G0 := by
  have heC := theta_eq_one_centralizes (Ω := Ω) hG0 hker hcenter hBN hinner hTheta
  have hU : CFSG.IsQuasisimple (ggU .F4 n f).K := by
    change CFSG.IsQuasisimple (adjointGroup .F4 (GaloisField 2 f))
    exact CFSG.StandardType.F4ExplicitPos.CTNative.isQuasisimple_f4_native
      (GaloisField 2 f)
  exact Quasisimple.component_eq_of_central_ker ψ G0 K (eB : X) hU hG0 hker hKG
    hKcomp heC

theorem neighbor_eq_G0_of_theta_eq_one
    {Ω : Type} [Field Ω]
    {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU .F4 n f).K →* X} {p : ℕ}
    [Algebra (GaloisField 2 f) Ω]
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp .F4 n f ψ p G₀ B₁ D J L x)
    {g0 : ModGL Tag.F4 Ω} {e : X} (he : e ∈ D)
    (hTheta : ThetaF4 (L := Ω) ψ G₀ B₁ (hH_range hH) (hH_ker hH)
        (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
        (f4_exists_inner_correction_hH hH) g0 ⟨e, hH_DB hH he⟩ = 1)
    {K : Subgroup X} (hKG : K ≤ G₀)
    (hKcomp : CFSG.Assembly.IsComponentOf K
      (Subgroup.centralizer ({e} : Set X))) :
    K = G₀ :=
  component_eq_G0_of_theta_eq_one (Ω := Ω) (hH_range hH) (hH_ker hH)
    (center_adjointGroup_f4_charTwo_eq_bot (k := GaloisField 2 f)) (hH_BN hH)
    (f4_exists_inner_correction_hH hH) hTheta hKG hKcomp

end CFSG.StandardType.F4ExplicitPos.RankExclusionFinish

end

end
