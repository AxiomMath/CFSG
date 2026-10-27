module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetLang

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld CFSG.LieType.Steinberg.Minuscule
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckRet_theta_step_gen
    {τ : Tag} {p₀ p₁ : ℕ} (S : LangSetup τ GGL p₀) (SK : LangSetup Tag.E6 GGL p₁)
    (hq : SK.D.q = S.D.q) {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetCompSpec β ι θ)
    (hρΨ : ∀ γ ∈ rootsOfFam β Set.univ, S.ρ γ ∈ rootsOfFam β Set.univ)
    (hρ : ∀ γ ∈ rootsOfFam β Set.univ, SK.ρ (ι γ) = ι (S.ρ γ)) (x : ↥(RetH τ β)) :
    ∃ hx : S.D.step (x : ModGL τ GGL) ∈ RetH τ β,
      θ ⟨S.D.step (x : ModGL τ GGL), hx⟩ = SK.D.step (θ x) := by
  classical
  obtain ⟨hgen, -, -, -⟩ := hθ
  obtain ⟨xv, hxv⟩ := x
  refine rckRet_rootSpan_induction (S := rootsOfFam β Set.univ)
    (P := fun y hy => ∃ hyb : S.D.step y ∈ RetH τ β,
      θ ⟨S.D.step y, hyb⟩ = SK.D.step (θ ⟨y, hy⟩)) ?_ ?_ ?_ hxv
  · intro α hα c hm
    have hαr : IsRoot τ α := hα.1
    have hρα : S.ρ α ∈ rootsOfFam β Set.univ := hρΨ α hα
    rw [rckRet_step_pinnedX S hαr c]
    have hmem : pinnedX τ GGL (S.ρ α) (c ^ S.D.q) ∈ RetH τ β :=
      (le_iSup₂_of_le (f := fun γ (_ : γ ∈ rootsOfFam β Set.univ) => rootSubgroup τ GGL γ)
        (S.ρ α) hρα le_rfl) (mem_rootSubgroup.2 ⟨_, rfl⟩)
    refine ⟨hmem, ?_⟩
    rw [hgen (S.ρ α) hρα (c ^ S.D.q) hmem, hgen α hα c hm,
      rckRet_step_pinnedX SK (hι.1.mapsTo hα) c, hρ α hα, hq]
  · have h1 : S.D.step (1 : ModGL τ GGL) = 1 := map_one _
    have hmem1 : S.D.step (1 : ModGL τ GGL) ∈ RetH τ β := by rw [h1]; exact one_mem _
    refine ⟨hmem1, ?_⟩
    have e : (⟨S.D.step (1 : ModGL τ GGL), hmem1⟩ : ↥(RetH τ β)) = 1 := Subtype.ext h1
    have e' : (⟨(1 : ModGL τ GGL), one_mem _⟩ : ↥(RetH τ β)) = 1 := rfl
    rw [e, e', map_one, map_one]
  · intro y z hy hz ⟨hyb, hθy⟩ ⟨hzb, hθz⟩
    have hyz : S.D.step (y * z) ∈ RetH τ β := by
      rw [map_mul]
      exact mul_mem hyb hzb
    refine ⟨hyz, ?_⟩
    have e : (⟨S.D.step (y * z), hyz⟩ : ↥(RetH τ β)) =
        ⟨S.D.step y, hyb⟩ * ⟨S.D.step z, hzb⟩ := Subtype.ext (map_mul _ _ _)
    have e' : (⟨y * z, mul_mem hy hz⟩ : ↥(RetH τ β)) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [e, map_mul, hθy, hθz, e']
    simp only [map_mul]

end CFSG.StandardType.RCKRP

end
