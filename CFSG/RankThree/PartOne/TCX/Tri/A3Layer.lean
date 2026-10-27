module

public import CFSG.RankThree.PartOne.TCX.Tri.A3Parts
public import CFSG.RankThree.PartOne.TCX.Tri.Skeleton
public import CFSG.RankThree.PartOne.TCX.Tri.E2A1
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KE.A5Interface
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E6TwFourKernel
public import CFSG.RankThree.PartOne.KE.E7ThreeA1
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KLCE.A2Sector
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartOne.TCX.Tri.A3Family
public import CFSG.RankThree.PartOne.TCX.Tri.E2Kernel
public import CFSG.RankThree.PartOne.TCX.Tri.Frame
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KLCE
open CFSG.RankThree.Classical (conjSL)

open CFSG.RankThree.PartOne.TCX.F4 (LayerClaimsF4)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.TCX
open scoped MatrixGroups

section Reorder

variable {M : Type*} [Group M]

theorem comm_reorder_pos {X₁ X₂ X₃ : M} (h12 : Commute X₁ X₂) (h13 : Commute X₁ X₃) :
    X₂ * X₃ * X₁ = X₁ * X₂ * X₃ := by
  calc X₂ * X₃ * X₁ = X₂ * (X₃ * X₁) := mul_assoc _ _ _
    _ = X₂ * (X₁ * X₃) := by rw [h13.eq]
    _ = X₂ * X₁ * X₃ := (mul_assoc _ _ _).symm
    _ = X₁ * X₂ * X₃ := by rw [h12.eq]

theorem comm_reorder_neg {X₁ X₂ X₃ : M} (h13 : Commute X₁ X₃) (h23 : Commute X₂ X₃) :
    X₃ * X₁ * X₂ = X₁ * X₂ * X₃ := by
  calc X₃ * X₁ * X₂ = X₃ * (X₁ * X₂) := mul_assoc _ _ _
    _ = X₁ * X₂ * X₃ := by
      rw [← mul_assoc, ← h13.eq, mul_assoc, ← h23.eq, ← mul_assoc]

end Reorder

section Shift

variable {L : Type} [Field L] [CharP L 2]

theorem F0_conj_rootSL2 {f₀ : ℕ} {n₀ : ModGL TwistTag.D4.tag L}
    {r s : Fin TwistTag.D4.tag.rank → ℤ}
    (hn : ∀ B : SL(2, L), n₀ * rootSL2 TwistTag.D4.tag L s B * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L s (WSL * B * WSL⁻¹))
    (hs : PAct L r s) (A : SL(2, L)) :
    n₀ * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r A) * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L s
        (twHom (iterateFrobenius L 2 f₀) (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) A) := by
  rw [triF0_apply, entrywise_rootSL2_of_field, hs, hn, twHom_apply,
    CFSG.RankThree.Chevalley.conjSL_toGL]

variable {r₁ r₂ r₃ : Fin TwistTag.D4.tag.rank → ℤ}

theorem F0_mu_pos {f₀ : ℕ} {n₀ : ModGL TwistTag.D4.tag L}
    (hn₁ : ∀ B : SL(2, L), n₀ * rootSL2 TwistTag.D4.tag L r₁ B * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L r₁ (WSL * B * WSL⁻¹))
    (hn₂ : ∀ B : SL(2, L), n₀ * rootSL2 TwistTag.D4.tag L r₂ B * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L r₂ (WSL * B * WSL⁻¹))
    (hn₃ : ∀ B : SL(2, L), n₀ * rootSL2 TwistTag.D4.tag L r₃ B * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L r₃ (WSL * B * WSL⁻¹))
    (hc12 : ∀ A B : SL(2, L), Commute (rootSL2 TwistTag.D4.tag L r₁ A)
      (rootSL2 TwistTag.D4.tag L r₂ B))
    (hc13 : ∀ A C : SL(2, L), Commute (rootSL2 TwistTag.D4.tag L r₁ A)
      (rootSL2 TwistTag.D4.tag L r₃ C))
    (a₁₂ : PAct L r₁ r₂) (a₂₃ : PAct L r₂ r₃) (a₃₁ : PAct L r₃ r₁)
    (A B C : SL(2, L)) :
    n₀ * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₁ A * rootSL2 TwistTag.D4.tag L r₂ B *
        rootSL2 TwistTag.D4.tag L r₃ C) * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L r₁
          (twHom (iterateFrobenius L 2 f₀) (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) C) *
        rootSL2 TwistTag.D4.tag L r₂
          (twHom (iterateFrobenius L 2 f₀) (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) A) *
        rootSL2 TwistTag.D4.tag L r₃
          (twHom (iterateFrobenius L 2 f₀) (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) B) := by
  have e1 := F0_conj_rootSL2 (f₀ := f₀) hn₂ a₁₂ A
  have e2 := F0_conj_rootSL2 (f₀ := f₀) hn₃ a₂₃ B
  have e3 := F0_conj_rootSL2 (f₀ := f₀) hn₁ a₃₁ C
  rw [map_mul, map_mul]
  calc n₀ * (triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₁ A) * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₂ B) *
        triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₃ C)) * n₀⁻¹
      = (n₀ * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₁ A) * n₀⁻¹) *
          (n₀ * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₂ B) * n₀⁻¹) *
            (n₀ * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₃ C) * n₀⁻¹) := by group
    _ = _ := by
      rw [e1, e2, e3]
      exact comm_reorder_pos (hc12 _ _) (hc13 _ _)

theorem F0_mu_neg {f₀ : ℕ} {n₀ : ModGL TwistTag.D4.tag L}
    (hn₁ : ∀ B : SL(2, L), n₀ * rootSL2 TwistTag.D4.tag L r₁ B * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L r₁ (WSL * B * WSL⁻¹))
    (hn₂ : ∀ B : SL(2, L), n₀ * rootSL2 TwistTag.D4.tag L r₂ B * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L r₂ (WSL * B * WSL⁻¹))
    (hn₃ : ∀ B : SL(2, L), n₀ * rootSL2 TwistTag.D4.tag L r₃ B * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L r₃ (WSL * B * WSL⁻¹))
    (hc13 : ∀ A C : SL(2, L), Commute (rootSL2 TwistTag.D4.tag L r₁ A)
      (rootSL2 TwistTag.D4.tag L r₃ C))
    (hc23 : ∀ B C : SL(2, L), Commute (rootSL2 TwistTag.D4.tag L r₂ B)
      (rootSL2 TwistTag.D4.tag L r₃ C))
    (a₁₃ : PAct L r₁ r₃) (a₃₂ : PAct L r₃ r₂) (a₂₁ : PAct L r₂ r₁)
    (A B C : SL(2, L)) :
    n₀ * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₁ A * rootSL2 TwistTag.D4.tag L r₂ B *
        rootSL2 TwistTag.D4.tag L r₃ C) * n₀⁻¹ =
      rootSL2 TwistTag.D4.tag L r₁
          (twHom (iterateFrobenius L 2 f₀) (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) B) *
        rootSL2 TwistTag.D4.tag L r₂
          (twHom (iterateFrobenius L 2 f₀) (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) C) *
        rootSL2 TwistTag.D4.tag L r₃
          (twHom (iterateFrobenius L 2 f₀) (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) A) := by
  have e1 := F0_conj_rootSL2 (f₀ := f₀) hn₃ a₁₃ A
  have e2 := F0_conj_rootSL2 (f₀ := f₀) hn₁ a₂₁ B
  have e3 := F0_conj_rootSL2 (f₀ := f₀) hn₂ a₃₂ C
  rw [map_mul, map_mul]
  calc n₀ * (triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₁ A) * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₂ B) *
        triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₃ C)) * n₀⁻¹
      = (n₀ * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₁ A) * n₀⁻¹) *
          (n₀ * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₂ B) * n₀⁻¹) *
            (n₀ * triF0 L f₀ (rootSL2 TwistTag.D4.tag L r₃ C) * n₀⁻¹) := by group
    _ = _ := by
      rw [e1, e2, e3]
      exact comm_reorder_neg (hc13 _ _) (hc23 _ _)

end Shift

section Layer

variable {C : Type} [Group C] [Finite C] {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
  {p f₀ : ℕ} {ι : C →* ModGL TwistTag.D4.tag L} {α₀ : MulAut C}

local notation "JJ" => (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)))
local notation "Θ₀" => twHom (iterateFrobenius L 2 f₀)
  (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)))
local notation "GG" => twHom (iterateFrobenius L 2 (f₀ * p))
  (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L)))

theorem tri_a3_layer (h : IsShintani p ι (triF0 L f₀) (triPhi L p f₀) α₀) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀)
    (hodd : ∀ t ∈ torusGroup TwistTag.D4.tag L, ∃ m : ℕ, Odd m ∧ t ^ m = 1)
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hg₀ : triF0 L f₀ g₀ = g₀ * triNeg L)
    {r₁ r₂ r₃ : Fin TwistTag.D4.tag.rank → ℤ} (h₁ : IsRoot TwistTag.D4.tag r₁)
    (h₂ : IsRoot TwistTag.D4.tag r₂) (h₃ : IsRoot TwistTag.D4.tag r₃)
    (hc12 : ∀ A B : SL(2, L), Commute (rootSL2 TwistTag.D4.tag L r₁ A)
      (rootSL2 TwistTag.D4.tag L r₂ B))
    (hc13 : ∀ A C : SL(2, L), Commute (rootSL2 TwistTag.D4.tag L r₁ A)
      (rootSL2 TwistTag.D4.tag L r₃ C))
    (hc23 : ∀ B C : SL(2, L), Commute (rootSL2 TwistTag.D4.tag L r₂ B)
      (rootSL2 TwistTag.D4.tag L r₃ C))
    (hρ : (p % 3 = 1 ∧ PAct L r₁ r₂ ∧ PAct L r₂ r₃ ∧ PAct L r₃ r₁) ∨
      (p % 3 = 2 ∧ PAct L r₁ r₃ ∧ PAct L r₃ r₂ ∧ PAct L r₂ r₁))
    {x : C} (hx : orderOf x = p) {c : C} (hcα : α₀ c = c)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g₀⁻¹ * ι (c * x * c⁻¹) * g₀)
    (hbT : rootDiagUnit TwistTag.D4.tag b ∈ twistedTorusOf (triNeg L) (triF0 L f₀))
    (hbS : rootCharKernel b ⊆ threeRootSet r₁ r₂ r₃)
    (hbc : rootDiagUnit TwistTag.D4.tag b ∈ Subgroup.centralizer
      (rootSpan TwistTag.D4.tag L (threeRootSet r₁ r₂ r₃) : Set (ModGL TwistTag.D4.tag L))) :
    SingleLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  classical
  have hp3 : 3 < p := by omega
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3' : p % 3 = 1 ∨ p % 3 = 2 := by rcases hρ with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hΦ₀c : ∀ c, iterateFrobenius L 2 f₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  obtain ⟨k₀, _, _, _, hk₀⟩ := exists_finite_field_into 2 f₀ hf₀ L
  obtain ⟨k₃, _, _, _, σ₃, hk₃, hσ₃ord, hσ₃⟩ :=
    exists_layer_field (L := L) hp hf₀ 3 (by norm_num)
  have : CharP k₃ 2 := ⟨fun x => by
    rw [← (algebraMap k₃ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have hK₃4 : 4 ≤ Nat.card k₃ := by
    rw [hk₃]
    have h2 : 2 ≤ p * (3 * f₀) := by nlinarith
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * (3 * f₀)) := Nat.pow_le_pow_right (by norm_num) h2
  set n₀ : ModGL TwistTag.D4.tag L := triNeg L with hn₀def
  have hn₀F : triF0 L f₀ n₀ = n₀ := triNeg_twistHom (iterateFrobenius L 2 f₀)
  have hn₀J : ∀ {r : Fin TwistTag.D4.tag.rank → ℤ}, IsRoot TwistTag.D4.tag r →
      ∀ B : SL(2, L), n₀ * rootSL2 TwistTag.D4.tag L r B * n₀⁻¹ =
        rootSL2 TwistTag.D4.tag L r (WSL * B * WSL⁻¹) := fun {r} hr =>
    conj_rootSL2_of_neg_rep (fun α hα c => triNeg_conj_pinnedX hα c) hr
  have hJpow : ∀ J' : SL(2, L), J' * J' = 1 → J' ^ p = J' := fun J' hJ => by
    obtain ⟨m, hm⟩ := hpo
    rw [hm, pow_succ, pow_mul, pow_two, hJ, one_pow, one_mul]
  have hNJ : ∀ {r : Fin TwistTag.D4.tag.rank → ℤ}, IsRoot TwistTag.D4.tag r →
      ∀ B : SL(2, L), n₀ ^ p * rootSL2 TwistTag.D4.tag L r B * (n₀ ^ p)⁻¹ =
        rootSL2 TwistTag.D4.tag L r (WSL * B * WSL⁻¹) := fun {r} hr B => by
    rw [pow_conj_rootSL2 (hn₀J hr) p B, hJpow WSL wsl_mul_self]
  have hPp : (∀ A : SL(2, L), triP L ^ p * rootSL2 TwistTag.D4.tag L r₁ A * (triP L ^ p)⁻¹ =
        rootSL2 TwistTag.D4.tag L r₂ A) ∧
      (∀ A : SL(2, L), triP L ^ p * rootSL2 TwistTag.D4.tag L r₂ A * (triP L ^ p)⁻¹ =
        rootSL2 TwistTag.D4.tag L r₃ A) ∧
      (∀ A : SL(2, L), triP L ^ p * rootSL2 TwistTag.D4.tag L r₃ A * (triP L ^ p)⁻¹ =
        rootSL2 TwistTag.D4.tag L r₁ A) := by
    rcases hρ with ⟨hp1, a12, a23, a31⟩ | ⟨hp2, a13, a32, a21⟩
    · exact ⟨PAct.pow_mod_one hp1 a12, PAct.pow_mod_one hp1 a23, PAct.pow_mod_one hp1 a31⟩
    · exact ⟨PAct.pow_mod_two hp2 a13 a32, PAct.pow_mod_two hp2 a21 a13,
        PAct.pow_mod_two hp2 a32 a21⟩
  obtain ⟨hPp12, hPp23, hPp31⟩ := hPp
  set n' : ModGL TwistTag.D4.tag L := n₀ ^ p * triP L ^ p with hn'def
  have hn'conj : ∀ (r s : Fin TwistTag.D4.tag.rank → ℤ), IsRoot TwistTag.D4.tag s →
      (∀ A : SL(2, L), triP L ^ p * rootSL2 TwistTag.D4.tag L r A * (triP L ^ p)⁻¹ =
        rootSL2 TwistTag.D4.tag L s A) → ∀ A : SL(2, L),
      n' * rootSL2 TwistTag.D4.tag L r A * n'⁻¹ =
        rootSL2 TwistTag.D4.tag L s (conjSL (Matrix.SpecialLinearGroup.toGL (WSL : SL(2, L))) A) :=
    fun r s hs hPr A => by
    have e : n' * rootSL2 TwistTag.D4.tag L r A * n'⁻¹ =
        n₀ ^ p * (triP L ^ p * rootSL2 TwistTag.D4.tag L r A * (triP L ^ p)⁻¹) * (n₀ ^ p)⁻¹ := by
      rw [hn'def]
      group
    rw [e, hPr A, hNJ hs A, CFSG.RankThree.Chevalley.conjSL_toGL]
  have e₁ := hn'conj r₁ r₂ h₂ hPp12
  have e₂ := hn'conj r₂ r₃ h₃ hPp23
  have e₃ := hn'conj r₃ r₁ h₁ hPp31
  obtain ⟨μ, hμ⟩ : ∃ μ : SL(2, L) × SL(2, L) × SL(2, L) →* ModGL TwistTag.D4.tag L,
      ∀ A B C, μ (A, B, C) = rootSL2 TwistTag.D4.tag L r₁ A * rootSL2 TwistTag.D4.tag L r₂ B *
        rootSL2 TwistTag.D4.tag L r₃ C :=
    ⟨(rootSL2 TwistTag.D4.tag L r₁).noncommCoprod
      ((rootSL2 TwistTag.D4.tag L r₂).noncommCoprod (rootSL2 TwistTag.D4.tag L r₃) hc23)
      fun A BC => (hc12 A BC.1).mul_right (hc13 A BC.2), fun A B C => (mul_assoc _ _ _).symm⟩
  have hΘ := three_A1_theta hc12 hc13 μ hμ (iterateFrobenius L 2 (f₀ * p)) n' JJ JJ JJ e₁ e₂ e₃
  obtain ⟨ν, hν⟩ : ∃ ν : SL(2, L) →* ModGL TwistTag.D4.tag L,
      ∀ X, ν X = μ (X, GG X, GG (GG X)) :=
    ⟨μ.comp (MonoidHom.prod (MonoidHom.id _) (MonoidHom.prod GG (MonoidHom.comp GG GG))),
      fun X => rfl⟩
  have hker : ∀ A B C : SL(2, L), μ (A, B, C) = 1 → A ∈ Subgroup.center SL(2, L) ∧
      B ∈ Subgroup.center SL(2, L) ∧ C ∈ Subgroup.center SL(2, L) := fun A B C h =>
    threeA1Tw_mem_center_of_mul_eq_one hc12 hc13 hc23 (by rw [← hμ]; exact h)
  have hνinj : Function.Injective ν := by
    rw [injective_iff_map_eq_one]
    intro X hX
    rw [hν] at hX
    exact center_sl2_eq_one (hker _ _ _ hX).1
  have hFrb : Function.Bijective (iterateFrobenius L 2 (f₀ * p)) := iterateFrobenius_bijective
  obtain ⟨P₀, hP₀⟩ := exists_P0_wsl (K := k₀) (iterateFrobenius L 2 f₀)
    (fun c => by rw [hk₀]; exact hΦ₀c c)
  have hFr₃c : ∀ c, iterateFrobenius L 2 (f₀ * (3 * p)) c = c ^ Nat.card k₃ := fun c => by
    rw [hk₃, show p * (3 * f₀) = f₀ * (3 * p) by ring]
    exact iterateFrobenius_def 2 (f₀ * (3 * p)) c
  have hFr3eq : (iterateFrobenius L 2 (f₀ * p)).comp ((iterateFrobenius L 2 (f₀ * p)).comp
      (iterateFrobenius L 2 (f₀ * p))) = iterateFrobenius L 2 (f₀ * (3 * p)) :=
    RingHom.ext fun c => by
      simp only [RingHom.comp_apply, iterateFrobenius_def]
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
  have hPm : P₀ * Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 (f₀ * (3 * p))) P₀⁻¹ =
      JJ * Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 (f₀ * p))
        (JJ * Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 (f₀ * p)) JJ) := by
    have h1 := P_frobenius_pow (map_toGL_wsl (iterateFrobenius L 2 f₀)) hP₀ (3 * p)
    rw [h1, toGL_wsl_pow_odd (by
      obtain ⟨m, hm⟩ := hpo
      exact ⟨3 * m + 1, by omega⟩), map_toGL_wsl, toGL_wsl_mul_self, map_one, mul_one]
  set S₃ : Subgroup SL(2, L) := (Matrix.SpecialLinearGroup.map (algebraMap k₃ L)).range.map
    (conjSL P₀) with hS₃def
  obtain ⟨hfin₃, hS₃, hq₃, hq₂, hq₁, hz₃, hz₂, hz₁⟩ := a3_lang_data hFrb JJ JJ JJ hK₃4 hFr₃c
    hFr3eq P₀ hPm S₃ hS₃def
  have : Finite S₃ := hfin₃
  obtain ⟨hfam, hjoinS⟩ := a3_family hc12 hc13 hc23 h₁ h₂ h₃ μ hμ (iterateFrobenius L 2 (f₀ * p))
    n' GG GG GG hΘ _ _ S₃ rfl rfl hS₃ hq₁ hq₂ hq₃ hz₁ hz₂ hz₃ ν hν
  have hNeq : nseq n₀ (triF0 L f₀) p = n₀ ^ p := nseq_eq_pow hn₀F p
  have hfam' : IsSigmaFamilyΦ (nseq n₀ (triF0 L f₀) p) (triPhi L p f₀)
      (threeRootSet r₁ r₂ r₃) (fun _ : Unit => S₃.map ν) := by
    rw [hNeq]
    exact isSigmaFamilyΦ_twPhi (n₀ ^ p) (triP L ^ p) (iterateFrobenius L 2 (f₀ * p))
      (threeRootSet r₁ r₂ r₃) _ hfam
  have hjoin : rootSpan TwistTag.D4.tag L (threeRootSet r₁ r₂ r₃) ⊓
      twistedFixedPoints (nseq n₀ (triF0 L f₀) p) (triPhi L p f₀) ≤
        (fun _ : Unit => S₃.map ν) () := by
    rw [hNeq]
    change rootSpan TwistTag.D4.tag L (threeRootSet r₁ r₂ r₃) ⊓
      twistedFixedPoints (n₀ ^ p) (twPhi (triP L ^ p) (iterateFrobenius L 2 (f₀ * p))) ≤
        S₃.map ν
    rw [twistedFixedPoints_twPhi]
    exact hjoinS
  have hPJ : JJ * Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 f₀) P₀ = P₀ := by
    rw [← hP₀, map_inv]
    group
  have hΘc : ∀ Z : SL(2, L), Θ₀ (conjSL P₀ Z) =
      conjSL P₀ (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f₀) Z) := fun Z => by
    rw [twHom_apply, map_conjSL_ringHom', ← CFSG.RankThree.Classical.conjSL_mul, hPJ]
  have hΘk : ∀ (k : ℕ) (Z : SL(2, L)), (⇑Θ₀)^[k] (conjSL P₀ Z) =
      conjSL P₀ (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 (f₀ * k)) Z) := by
    intro k
    induction k with
    | zero =>
      intro Z
      rw [Function.iterate_zero, id_eq, Nat.mul_zero, iterateFrobenius_zero]
      congr 1
    | succ k ih =>
      intro Z
      rw [Function.iterate_succ_apply', ih, hΘc, map_map_sl2,
        show f₀ * (k + 1) = f₀ + f₀ * k by ring, iterateFrobenius_add]
  have hGit : ∀ Z : SL(2, L), GG Z = (⇑Θ₀)^[p] Z := fun Z => by
    rw [twHom_iterate (map_toGL_wsl (iterateFrobenius L 2 f₀)) p Z, toGL_wsl_pow_odd hpo,
      twHom_apply]
  have hTadd : ∀ (m n : ℕ) (Z : SL(2, L)), (⇑Θ₀)^[m] ((⇑Θ₀)^[n] Z) = (⇑Θ₀)^[m + n] Z :=
    fun m n Z => (Function.iterate_add_apply (⇑Θ₀) m n Z).symm
  have hσ₃pow : ∀ (e : ℕ) (c : k₃), iterateFrobenius L 2 (f₀ * (3 * e)) (algebraMap k₃ L c) =
      algebraMap k₃ L ((σ₃ ^ e) c) := by
    intro e
    induction e with
    | zero => intro c; simp
    | succ e ih =>
      intro c
      rw [show f₀ * (3 * (e + 1)) = 3 * f₀ + f₀ * (3 * e) by ring, iterateFrobenius_add,
        RingHom.comp_apply, ih, hσ₃, pow_succ']
      rfl
  have hmapσ : ∀ (e : ℕ) (X : SL(2, k₃)), Matrix.SpecialLinearGroup.map (algebraMap k₃ L)
      (Matrix.SpecialLinearGroup.map (σ₃ ^ e).toRingHom X) =
        Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 (f₀ * (3 * e)))
          (Matrix.SpecialLinearGroup.map (algebraMap k₃ L) X) := by
    intro e X
    ext i j
    simp [hσ₃pow]
  have hY' : ∀ (e : ℕ) (X : SL(2, k₃)),
      conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L)
        (Matrix.SpecialLinearGroup.map (σ₃ ^ e).toRingHom X)) =
        (⇑Θ₀)^[3 * e] (conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L) X)) := by
    intro e X
    rw [hΘk, hmapσ]
  have hYmem : ∀ X : SL(2, k₃),
      conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L) X) ∈ S₃ :=
    fun X => ⟨_, ⟨X, rfl⟩, rfl⟩
  have hY3 : ∀ X : SL(2, k₃), (⇑Θ₀)^[3 * p]
      (conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L) X)) =
        conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L) X) := by
    intro X
    have h1 := (hS₃ _).1 (hYmem X)
    rw [hGit, hGit, hGit, hTadd, hTadd] at h1
    rw [show 3 * p = p + p + p by ring]
    exact h1
  have mk : ∀ e : ℕ, ¬ p ∣ e → (∀ X : SL(2, k₃),
      n₀ * triF0 L f₀ (ν (conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L) X))) *
          n₀⁻¹ =
        ν (conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L)
          (Matrix.SpecialLinearGroup.map (σ₃ ^ e).toRingHom X)))) →
      ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL TwistTag.D4.tag L) (τ' : D →* D),
        Function.Injective ρ' ∧ ρ'.range = (fun _ : Unit => S₃.map ν) () ∧
        (∀ d, n₀ * triF0 L f₀ (ρ' d) * n₀⁻¹ = ρ' (τ' d)) ∧
        ∀ {G' : Type} [Group G'] (α : MulAut G') (φ : D →* G'), Function.Injective φ →
          (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G', φ.range = Q →
            LayerClaimsF4 p α Q := by
    intro e he hcompat
    have hσ' : σ₃ ^ e ≠ 1 := fun h1 => he (by rw [← hσ₃ord]; exact orderOf_dvd_of_pow_eq_one h1)
    refine ⟨SL(2, k₃), inferInstance,
      ν.comp ((conjSL P₀).comp (Matrix.SpecialLinearGroup.map (algebraMap k₃ L))),
      Matrix.SpecialLinearGroup.map (σ₃ ^ e).toRingHom,
      hνinj.comp ((conjSL_injective P₀).comp (map_specialLinear_injective _)), ?_, hcompat, ?_⟩
    · rw [MonoidHom.range_comp, MonoidHom.range_comp]
    · intro G' _ α φ hφ hαφ Q hQ
      exact layerClaims_of_sl2 hp5 (f' := 3 * f₀) (by omega) hk₃ hσ' α φ hφ hαφ Q hQ
  have hmodel : ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL TwistTag.D4.tag L) (τ' : D →* D),
      Function.Injective ρ' ∧ ρ'.range = (fun _ : Unit => S₃.map ν) () ∧
      (∀ d, n₀ * triF0 L f₀ (ρ' d) * n₀⁻¹ = ρ' (τ' d)) ∧
      ∀ {G' : Type} [Group G'] (α : MulAut G') (φ : D →* G'), Function.Injective φ →
        (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G', φ.range = Q → LayerClaimsF4 p α Q := by
    rcases hρ with ⟨hp1, a12, a23, a31⟩ | ⟨hp2, a13, a32, a21⟩
    ·
      obtain ⟨e, he3⟩ : ∃ e, 3 * e = 1 + 2 * p := ⟨(1 + 2 * p) / 3, by omega⟩
      have hpe : ¬ p ∣ e := by
        intro hd
        obtain ⟨q, hq⟩ := hd
        have h1 : p ∣ 1 + 2 * p := ⟨3 * q, by rw [← he3, hq]; ring⟩
        exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_left (dvd_mul_left p 2)).1 h1))
      refine mk e hpe fun X => ?_
      set Y := conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L) X) with hYdef
      set Y' := conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L)
        (Matrix.SpecialLinearGroup.map (σ₃ ^ e).toRingHom X)) with hY'def
      have h3 : (⇑Θ₀)^[3 * p] Y = Y := hY3 X
      have hY'e : Y' = (⇑Θ₀)^[3 * e] Y := hY' e X
      have e1 : Y' = Θ₀ (GG (GG Y)) := by
        rw [hY'e, hGit (GG Y), hGit Y, hTadd p p Y]
        show (⇑Θ₀)^[3 * e] Y = (⇑Θ₀)^[1] ((⇑Θ₀)^[p + p] Y)
        rw [hTadd 1 (p + p) Y, show 3 * e = 1 + (p + p) by omega]
      have e2 : GG Y' = Θ₀ Y := by
        rw [hY'e, hGit, hTadd p (3 * e) Y, show p + 3 * e = 1 + 3 * p by omega,
          ← hTadd 1 (3 * p) Y, h3]
        rfl
      have e3 : GG (GG Y') = Θ₀ (GG Y) := by
        rw [e2, hGit, hGit Y]
        show (⇑Θ₀)^[p] ((⇑Θ₀)^[1] Y) = (⇑Θ₀)^[1] ((⇑Θ₀)^[p] Y)
        rw [hTadd, hTadd, add_comm]
      have hL := F0_mu_pos (f₀ := f₀) (hn₀J h₁) (hn₀J h₂) (hn₀J h₃) hc12 hc13 a12 a23 a31 Y
        (GG Y) (GG (GG Y))
      rw [hν Y, hν Y', hμ, hμ, hL, e3, e2, e1]
    ·
      obtain ⟨e, he3⟩ : ∃ e, 3 * e = 1 + p := ⟨(1 + p) / 3, by omega⟩
      have hpe : ¬ p ∣ e := by
        intro hd
        obtain ⟨q, hq⟩ := hd
        have h1 : p ∣ 1 + p := ⟨3 * q, by rw [← he3, hq]; ring⟩
        exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_left (dvd_refl p)).1 h1))
      refine mk e hpe fun X => ?_
      set Y := conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L) X) with hYdef
      set Y' := conjSL P₀ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L)
        (Matrix.SpecialLinearGroup.map (σ₃ ^ e).toRingHom X)) with hY'def
      have h3 : (⇑Θ₀)^[3 * p] Y = Y := hY3 X
      have hY'e : Y' = (⇑Θ₀)^[3 * e] Y := hY' e X
      have e1 : Y' = Θ₀ (GG Y) := by
        rw [hY'e, hGit Y]
        show (⇑Θ₀)^[3 * e] Y = (⇑Θ₀)^[1] ((⇑Θ₀)^[p] Y)
        rw [hTadd 1 p Y, he3]
      have e2 : GG Y' = Θ₀ (GG (GG Y)) := by
        rw [hY'e, hGit, hGit (GG Y), hGit Y, hTadd p (3 * e) Y, hTadd p p Y]
        show (⇑Θ₀)^[p + 3 * e] Y = (⇑Θ₀)^[1] ((⇑Θ₀)^[p + p] Y)
        rw [hTadd 1 (p + p) Y, show p + 3 * e = 1 + (p + p) by omega]
      have e3 : GG (GG Y') = Θ₀ Y := by
        rw [e2, hGit, hGit (GG Y), hGit Y]
        show (⇑Θ₀)^[p] ((⇑Θ₀)^[1] ((⇑Θ₀)^[p] ((⇑Θ₀)^[p] Y))) = (⇑Θ₀)^[1] Y
        rw [hTadd p p Y, hTadd 1 (p + p) Y, hTadd p (1 + (p + p)) Y,
          show p + (1 + (p + p)) = 1 + 3 * p by omega, ← hTadd 1 (3 * p) Y, h3]
      have hL := F0_mu_neg (f₀ := f₀) (hn₀J h₁) (hn₀J h₂) (hn₀J h₃) hc13 hc23 a13 a32 a21 Y
        (GG Y) (GG (GG Y))
      rw [hν Y, hν Y', hμ, hμ, hL, e3, e2, e1]
  have hS : ∀ α ∈ threeRootSet r₁ r₂ r₃, IsRoot TwistTag.D4.tag α := by
    intro α hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h₁, IsRoot.neg h₁, h₂, IsRoot.neg h₂, h₃, IsRoot.neg h₃]
  have hSn : ∀ α ∈ threeRootSet r₁ r₂ r₃, -α ∈ threeRootSet r₁ r₂ r₃ := by
    intro α hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [threeRootSet]
  exact tri_layer_of_frame h hp hp3 hodd hg₀C hg₀ hS hSn (fun _ : Unit => S₃.map ν) hfam' hjoin
    hx hcα hb hbT hbS hbc hmodel

end Layer
