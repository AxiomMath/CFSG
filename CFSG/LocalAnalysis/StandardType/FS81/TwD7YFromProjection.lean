module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaPosition
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaY
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7TorusSwap
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QStd

public noncomputable section
namespace CFSG.StandardType.FrameRoute.FS81
open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open E7Frame

theorem twD7BetaHost_le_sup_normalizer {G : Type} [Group G] (b₀ : G) (K E : Subgroup G)
    (B : Basis3 G 8) : twD7BetaHost b₀ K E B ≤ K ⊔ normalizer (E : Set G) :=
  sup_le_sup ((Subgroup.commutator_le_self _).trans inf_le_right) inf_le_right

theorem exists_Y_gen_of_twD7BetaHost_projection
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
    ∃ Y : Subgroup G, IsEm 8 Y ∧ E ≤ Y ∧ centralizer ({B.b 1} : Set G) ⊓ K ≤ Y ∧
      Y ≤ K ⊔ normalizer (E : Set G) := by
  obtain ⟨J', ψ, z, -, hJH, hJgen, hJC, hAdapt, hMJ, -, hz, hψz, hNJ, -⟩ :=
    exists_positioned_e7_of_twD7BetaHost_projection b₀ K E hstd B hB hrec π hπ hker hmark
      τ hτE hτβ hτ0
  obtain ⟨Y, hY, hEY, hCKY, -, hYJK⟩ :=
    exists_Y_twD7_gen_of_attached hstd hB hrec ψ hJC hJgen hMJ hAdapt hNJ hz hψz
  exact ⟨Y, hY, hEY, hCKY,
    hYJK.trans (sup_le (hJH.trans (twD7BetaHost_le_sup_normalizer b₀ K E B)) le_sup_left)⟩

theorem exists_Y_of_twD7BetaHost_projection
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
    ∃ Y : Subgroup G, IsEm 8 Y ∧ E ≤ Y ∧ centralizer ({B.b 1} : Set G) ⊓ K ≤ Y ∧
      Y ≤ centralizer ({b₀} : Set G) ⊔ normalizer (E : Set G) := by
  obtain ⟨Y, hY, hEY, hCKY, hYK⟩ := exists_Y_gen_of_twD7BetaHost_projection b₀ K E hstd B hB hrec
    π hπ hker hmark τ hτE hτβ hτ0
  exact ⟨Y, hY, hEY, hCKY, hYK.trans (sup_le_sup_right hstd.2.1.1.2.1 _)⟩

theorem exists_Y_of_marked_twD7_projection
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
      ((π ⟨b₀⁻¹ * B.b 1, ha⟩ : adjointGroup .E7 (ZMod 2)) : ModGL .E7 (ZMod 2)) ∈ Jn 0) :
    ∃ Y : Subgroup G, IsEm 8 Y ∧ E ≤ Y ∧ centralizer ({B.b 1} : Set G) ⊓ K ≤ Y ∧
      Y ≤ centralizer ({b₀} : Set G) ⊔ normalizer (E : Set G) := by
  obtain ⟨τ, hτE, hτβ, hτpoint⟩ := exists_tau_swap_of_std_twD7 hstd B hB hrec
  have hτ0 : τ * B.b 0 * τ⁻¹ = B.b 1 := by
    simpa only [Equiv.swap_apply_left] using hτpoint 0
  exact exists_Y_of_twD7BetaHost_projection b₀ K E hstd B hB hrec π hπ hker hmark
    τ hτE hτβ hτ0

theorem l2ConstructY_twD7_of_marked_projection
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
      ((π ⟨b₀⁻¹ * B.b 1, ha⟩ : adjointGroup .E7 (ZMod 2)) : ModGL .E7 (ZMod 2)) ∈ Jn 0) :
    ∃ Y : Subgroup G, IsEm 8 Y ∧ centralizer ({b₀} : Set G) ⊓ Y = zpowers b₀ ⊔ K ∧
      ∀ R : Subgroup G, R ≤ centralizer ({b₀} : Set G) →
        (R.subgroupOf (centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
        R ≤ centralizer (Y : Set G) := by
  obtain ⟨Y, hY, hEY, hCY, hYgen⟩ :=
    exists_Y_of_marked_twD7_projection b₀ K E hstd B hB hrec π hπ hker hmark
  exact ⟨Y, hY, centralizer_inf_eq_and_le_centralizer_of_le_sup_normalizer
    hstd hB hrec hY hEY hCY hYgen⟩

theorem l2ConstructYAt_twD7_of_marked_projections
    (hproj : ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G)
      (_hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
      (_hB : Adapted B b₀ K E) (_hrec : RecOutTwD7 B b₀),
      ∃ π : twD7BetaHost b₀ K E B →* adjointGroup .E7 (ZMod 2),
        Function.Surjective π ∧
        (∃ R₁ : Subgroup G, R₁ ≤ centralizer ({b₀} : Set G) ∧
          (R₁.subgroupOf (centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R₁ ∧
          π.ker ≤ R₁.subgroupOf (twD7BetaHost b₀ K E B) ⊔
            (zpowers (b₀ * B.b 1)).subgroupOf (twD7BetaHost b₀ K E B)) ∧
        ∀ ha : b₀⁻¹ * B.b 1 ∈ twD7BetaHost b₀ K E B,
          ((π ⟨b₀⁻¹ * B.b 1, ha⟩ : adjointGroup .E7 (ZMod 2)) : ModGL .E7 (ZMod 2)) ∈ Jn 0) :
    L2ConstructYAt Row.twD7 := by
  intro G _ _ b₀ K E hstd B hB hrec
  obtain ⟨π, hπ, hker, hmark⟩ := hproj G b₀ K E hstd B hB hrec
  exact l2ConstructY_twD7_of_marked_projection b₀ K E hstd B hB hrec π hπ hker hmark

theorem l2ConstructYAt_twD7_holds : L2ConstructYAt Row.twD7 :=
  l2ConstructYAt_twD7_of_marked_projections fun _ _ _ _ _ _ hstd _ hB hrec =>
    exists_twD7BetaHost_projection_of_std hstd hB hrec

end CFSG.StandardType.FrameRoute.FS81
