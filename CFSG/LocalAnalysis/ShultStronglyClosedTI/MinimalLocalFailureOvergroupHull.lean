module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOvergroupHullClass
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOvergroupHullUnique

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OvergroupHull

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.FixedPointModel
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem minimalLocalFailure_proper_overgroup_full_point_hulls
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y : Subgroup G} (hY : Y < ⊤) (hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y) :
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let D := involutionPointClass z
    let q := Nat.card Q
    let L := Subgroup.closure (D ∩ (Y : Set G))
    let R := CFSG.oddCore L
    let α := rightCosetMk H 1
    let Δ := {ω : rightCosetSpace H | ∃ y ∈ Y, rightCosetTranslate H α y = ω}
    D ∩ (Y : Set G) = conjugacyWithin Y z ∧ conjugacyWithin Y z = conjugacyWithin L z ∧
      Group.IsPerfect L ∧ K ≤ L ∧ Q ≤ L ∧ R ≤ Subgroup.center L ∧
      Δ = {ω : rightCosetSpace H | ∃ l ∈ L, rightCosetTranslate H α l = ω} ∧
      (∃ ι : L ⧸ H.subgroupOf L → rightCosetSpace H, Function.Injective ι ∧
        Set.range ι = Δ ∧ ι (QuotientGroup.mk 1) = α ∧
        ∀ (l : L) (x : L ⧸ H.subgroupOf L),
          ι (l • x) = rightCosetTranslate H (ι x) (l : G)⁻¹) ∧
      ∃ j : ℕ, (j = 1 ∨ j = 2 ∨ j = 3) ∧ IsModelCosetAction L (H.subgroupOf L) q j ∧
        Nat.card Δ = q ^ j + 1 ∧
        (j = 1 → R = ⊥ ∧
          ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (L ≃* PSL(2, GaloisField 2 f))) ∧
        (j = 2 → R = ⊥ ∧ ∃ a : ℕ, 1 ≤ a ∧ q = 2 ^ (2 * a + 1) ∧ Nonempty (L ≃* Sz a)) ∧
        (j = 3 →
          ∃ (k : Type) (_ : Field k) (_ : Finite k) (J : HermitianForm 3 k)
            (_ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
            Nat.card k = q ^ 2 ∧ Nat.card {x : k // J.conj x = x} = q ∧
            (∀ A : J.specialSubgroup, A ∈ (PerfectOddCover.unitaryProj J).ker ↔
              ∃ c : k, ((A : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
                Matrix.scalar (Fin 3) c ∧ c ^ (q + 1) = 1 ∧ c ^ 3 = 1) ∧
            (PerfectOddCover.unitaryProj J).ker = Subgroup.center J.specialSubgroup ∧
            ∃ (C : Subgroup J.specialSubgroup) (_ : C.Normal),
              C ≤ (PerfectOddCover.unitaryProj J).ker ∧
              ∃ e : J.specialSubgroup ⧸ C ≃* L,
                ((PerfectOddCover.unitaryProj J).ker.map (QuotientGroup.mk' C)).map
                  e.toMonoidHom = R ∧
                Nat.card R ∣ Nat.gcd 3 (q + 1)) ∧
        ∀ V : Subgroup G, V ≤ Y → V = Subgroup.closure (D ∩ (V : Set G)) →
          IsUnitaryScalarQuotient q V → V = L ∧ j = 3 := by
  intro K Q D q L R α Δ
  have hDY : D ∩ (Y : Set G) = conjugacyWithin Y z :=
    overgroup_class_eq h hcomm hbeta ht hproper hKY
  have hL : L = Subgroup.closure (conjugacyWithin Y z) := congrArg Subgroup.closure hDY
  obtain ⟨hclass, hKL, hQL, hperfect, -, hstrong, hcenter, hcoreM, hmodel, hinvM, horbit⟩ :=
    overgroup_hull_structure h hcomm hsmallerR1 hbeta ht hproper hY hKY hL
  obtain ⟨ι, hιinj, hιrange, hι1, hι⟩ := orbit_coset_embedding H L
  rw [← horbit] at hιrange
  obtain ⟨-, -, j, hj, hindex⟩ :=
    fixed_point_model_recognition hstrong hcoreM hcenter hmodel hinvM
  have hΔcard : Nat.card Δ = q ^ j + 1 := by
    rw [← hindex]
    change Nat.card Δ = Nat.card (L ⧸ H.subgroupOf L)
    rw [show Δ = Set.range ι from hιrange.symm, Nat.card_range_of_injective hιinj]
  have hj123 : j = 1 ∨ j = 2 ∨ j = 3 := by
    rcases hj with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have : Group.IsPerfect L := hperfect
  refine ⟨hDY, hclass, hperfect, hKL, hQL, hcenter, horbit, ⟨ι, hιinj, hιrange, hι1, hι⟩, j,
    hj123, hj, hΔcard, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact linear_model_oddCore_eq_bot hcenter hj
  · rintro rfl
    exact suzuki_model_oddCore_eq_bot hcenter hj
  · rintro rfl
    exact unitary_model_scalar_cover hcenter hj
  · intro V hVY hVgen hV
    have hVL : V ≤ L := by
      rw [hVgen]
      exact Subgroup.closure_mono (Set.inter_subset_inter_right _ hVY)
    obtain ⟨htop, hj3⟩ := eq_top_of_isUnitaryScalarQuotient hcenter hj
      (hV.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hVL).symm)
    refine ⟨le_antisymm hVL fun x hx => ?_, hj3⟩
    have hxV : (⟨x, hx⟩ : L) ∈ V.subgroupOf L := htop ▸ Subgroup.mem_top _
    exact hxV

theorem minimalLocalFailure_proper_overgroup_unitary_hull_unique
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y : Subgroup G} (hY : Y < ⊤) (hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y)
    {V₁ V₂ : Subgroup G} (hV₁Y : V₁ ≤ Y) (hV₂Y : V₂ ≤ Y)
    (hV₁ : V₁ = Subgroup.closure (involutionPointClass z ∩ (V₁ : Set G)))
    (hV₂ : V₂ = Subgroup.closure (involutionPointClass z ∩ (V₂ : Set G)))
    (hU₁ : IsUnitaryScalarQuotient (Nat.card (minimalLocalFailurePairActionPointHull H z)) V₁)
    (hU₂ : IsUnitaryScalarQuotient (Nat.card (minimalLocalFailurePairActionPointHull H z)) V₂) :
    V₁ = V₂ := by
  obtain ⟨-, -, -, -, -, -, -, -, j, -, -, -, -, -, -, huniq⟩ :=
    minimalLocalFailure_proper_overgroup_full_point_hulls h hcomm hsmallerR1 hbeta ht hproper hY
      hKY
  exact (huniq V₁ hV₁Y hV₁ hU₁).1.trans (huniq V₂ hV₂Y hV₂ hU₂).1.symm

end CFSG.ShultStronglyClosedTI.OvergroupHull
