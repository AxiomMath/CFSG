module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaHost
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNative

public noncomputable section
namespace CFSG.StandardType.FrameRoute.FS81
open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open E7Frame


theorem exists_positioned_e7_of_twD7BetaHost_projection
    {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G)
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (π : twD7BetaHost b₀ K E B →* adjointGroup .E7 (ZMod 2))
    (hπ : Function.Surjective π)
    (hker : ∃ R₁ : Subgroup G, R₁ ≤ centralizer ({b₀} : Set G) ∧
      (R₁.subgroupOf (centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R₁ ∧
      π.ker ≤ R₁.subgroupOf (twD7BetaHost b₀ K E B) ⊔
        (zpowers (b₀ * B.b 1)).subgroupOf (twD7BetaHost b₀ K E B))
    (hmark : ∀ ha : b₀⁻¹ * B.b 1 ∈ twD7BetaHost b₀ K E B,
      ((π ⟨b₀⁻¹ * B.b 1, ha⟩ : adjointGroup .E7 (ZMod 2)) : ModGL .E7 (ZMod 2)) ∈ Jn 0)
    (τ : G) (hτE : τ ∈ normalizer (E : Set G))
    (hτβ : τ ∈ centralizer ({b₀ * B.b 1} : Set G))
    (hτ0 : τ * B.b 0 * τ⁻¹ = B.b 1) :
    ∃ J' : Subgroup G, ∃ ψ : ↥L7 ≃* ↥J', ∃ z : ↥L7,
      IsSimpleGroup ↥J' ∧ J' ≤ twD7BetaHost b₀ K E B ∧
      J' ≤ centralizer ({b₀} : Set G) ⊔ normalizer (E : Set G) ∧
      J' ≤ centralizer ({b₀ * B.b 1} : Set G) ∧
      Adapted B.twD7Beta (b₀ * B.b 1) J' E ∧
      ⁅centralizer ({B.b 1} : Set G) ⊓ K, centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J' ∧
      E ≤ zpowers (b₀ * B.b 1) ⊔ J' ∧
      (z : ModGL .E7 (ZMod 2)) ∈ Jn 0 ∧ ((ψ z : ↥J') : G) = b₀⁻¹ * B.b 1 ∧
      ((normalizer (zpowers (b₀ * B.b 1) : Set G) ⊓ normalizer (E : Set G)) ⊓
        normalizer ((⁅centralizer ({B.b 1} : Set G) ⊓ K,
          centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) ≤ normalizer (J' : Set G)) ∧
      ∀ R₁ : Subgroup G, R₁ ≤ centralizer ({b₀} : Set G) →
        (R₁.subgroupOf (centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R₁ →
        R₁ ≤ centralizer (J' : Set G) := by
  obtain ⟨J', hJH, hJgen, hJC, -, hAdapt, hMJ, hcore, hNJ, hJs, η, hη⟩ :=
    exists_attached_e7_of_twD7BetaHost_projection b₀ K E hstd B hB hrec π hπ hker
      τ hτE hτβ hτ0
  have hβ₁J : b₀⁻¹ * B.b 1 ∈ J' := by
    have h := hAdapt.2.2 1 (by decide)
    simpa only [Basis3.twD7Beta_b_one, hB.2.1] using h
  let aJ : J' := ⟨b₀⁻¹ * B.b 1, hβ₁J⟩
  let z : ↥L7 := η aJ
  let ψ : ↥L7 ≃* ↥J' := η.symm
  have hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0 := by
    have heq : z = π ⟨b₀⁻¹ * B.b 1, hJH hβ₁J⟩ := hη aJ (hJH hβ₁J)
    rw [heq]
    exact hmark (hJH hβ₁J)
  have hψz : ((ψ z : J') : G) = b₀⁻¹ * B.b 1 := by
    exact congrArg Subtype.val (η.symm_apply_apply aJ)
  have hEJ : E ≤ zpowers (b₀ * B.b 1) ⊔ J' := by
    rw [← hAdapt.1]
    change Subgroup.closure (Set.range B.twD7Beta.b) ≤ _
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = 0
    · subst i
      rw [hAdapt.2.1]
      exact (le_sup_left : zpowers (b₀ * B.b 1) ≤ zpowers (b₀ * B.b 1) ⊔ J')
        (Subgroup.mem_zpowers _)
    · exact (le_sup_right : J' ≤ zpowers (b₀ * B.b 1) ⊔ J') (hAdapt.2.2 i hi)
  exact ⟨J', ψ, z, hJs, hJH, hJgen, hJC, hAdapt, hMJ, hEJ, hz, hψz, hNJ, hcore⟩

end CFSG.StandardType.FrameRoute.FS81
