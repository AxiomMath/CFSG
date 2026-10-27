module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcInnTypeA
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section LabelBase

open scoped MatrixGroups

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA.RationalModel
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.GLTheoremA.K1419E
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

private theorem mul_succ_injective : Function.Injective (fun n : ℕ => n * (n + 1)) := by
  intro a b h
  have hmono : ∀ x y : ℕ, x < y → x * (x + 1) < y * (y + 1) := by
    intro x y hxy
    have h1 : x * (x + 1) < y * (x + 1) := Nat.mul_lt_mul_of_pos_right hxy (by omega)
    have h2 : y * (x + 1) ≤ y * (y + 1) := Nat.mul_le_mul_left y (by omega)
    exact lt_of_lt_of_le h1 h2
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (ne_of_lt (hmono a b hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (hmono b a hgt))

private theorem largeEvenInLambda2_A (r f : ℕ) (hr : 1 ≤ r) (hf1 : 1 ≤ f)
    (hf2 : r = 1 → 2 ≤ f) :
    LargeEvenInLambda2 (⟨.A, r, f⟩ : LargeEvenLabel) :=
  ⟨hf1, hr, hf2⟩

private theorem largeEvenInLambda2_twA (r f : ℕ) (hr : 2 ≤ r) (hf1 : 1 ≤ f)
    (hf2 : r = 2 → 2 ≤ f) :
    LargeEvenInLambda2 (⟨.twA, r, f⟩ : LargeEvenLabel) :=
  ⟨hf1, hr, hf2⟩

private theorem ggHasLabel_A {X : Type} [Group X] (r f : ℕ)
    (h : StatedClassicalModel X .PSL (r + 1) 2 f) :
    GGHasLabel (⟨.A, r, f⟩ : LargeEvenLabel) X := by
  show LargeEvenRecipeLinear (r + 1) (2 ^ f) (fun R _ _ _ => Nonempty (X ≃* R))
  exact recipeLinear_of_statedClassicalModel h

private theorem ggHasLabel_twA {X : Type} [Group X] (r f : ℕ)
    (h : StatedClassicalModel X .PSU (r + 1) 2 f) :
    GGHasLabel (⟨.twA, r, f⟩ : LargeEvenLabel) X := by
  show LargeEvenRecipeUnitary (r + 1) (2 ^ f) (fun R _ _ _ => Nonempty (X ≃* R))
  exact recipeUnitary_of_statedClassicalModel h

theorem twistInner_of_splitFrame
    {τ : Tag} {L : Type} [Field L] {ν : ℕ}
    {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → CFSG.LieType.Steinberg.Adjoint.iform (σ a b) (σ a b) = 2 * κ)
    (φ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → φ (σ x y) = σ (π x) (π y)) :
    twistInner (frameRoots σ) φ := by
  obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
  refine ⟨w, hw, fun γ hγ => ?_⟩
  obtain ⟨x, y, hxy, rfl⟩ := hγ
  rw [hπ x y hxy, ← hwσ x y]

theorem not_twistInner_of_unitaryFrame
    {τ : Tag} {L : Type} [Field L] {ν : ℕ}
    {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hν : 3 ≤ ν) (hψ : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → CFSG.LieType.Steinberg.Adjoint.iform (σ a b) (σ a b) = 2 * κ)
    (φ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → φ (σ x y) = σ (π y) (π x)) :
    ¬ twistInner (frameRoots σ) φ :=
  fun hin => l3u3_inn_false_of_unitary hν hψ hκ hnorm φ π hπ hin

private theorem twistKind_ne_inner_of_not_twistInner
    {τ : Tag} {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (hni : ¬ twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]))
    (h2 : 2 ≤ compRank (componentRoots χ i))
    (hn : (componentRoots χ i).ncard = compRank (componentRoots χ i) *
      (compRank (componentRoots χ i) + 1)) :
    twistKind ρ χ i ≠ .inner := by
  intro h
  unfold twistKind at h
  rw [if_neg hni] at h
  have hnexc : ¬ ((compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
      (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
        ¬ twistInner (componentRoots χ i)
          ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ (componentRoots χ i)]))) := by
    rintro (⟨h6, h72⟩ | ⟨h4, h24, -⟩)
    · rw [h6] at hn; norm_num at hn; omega
    · rw [h4] at hn; norm_num at hn; omega
  have hntwoD : ¬ (4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = 2 * compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) - 1)) := by
    rintro ⟨h4, htwo⟩
    have hcpos : 0 < compRank (componentRoots χ i) := by omega
    have h1 : compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1) =
        compRank (componentRoots χ i) * (2 * (compRank (componentRoots χ i) - 1)) := by
      calc compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1)
          = (componentRoots χ i).ncard := hn.symm
        _ = 2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1) := htwo
        _ = compRank (componentRoots χ i) * (2 * (compRank (componentRoots χ i) - 1)) := by ring
    have h1' : compRank (componentRoots χ i) + 1 = 2 * (compRank (componentRoots χ i) - 1) :=
      Nat.eq_of_mul_eq_mul_left hcpos h1
    omega
  rw [if_neg hnexc, if_neg hntwoD, if_pos ⟨h2, hn⟩] at h
  exact absurd h (by decide)

theorem compRank_frameRoots_eq
    {τ : Tag} {L : Type} [Field L] {ν : ℕ}
    {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    {Ψ : Set (Fin τ.rank → ℤ)}
    (hψ : IsSLFrame ρ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → CFSG.LieType.Steinberg.Adjoint.iform (σ a b) (σ a b) = 2 * κ)
    (hΨ : Ψ = frameRoots σ)
    (hn : Ψ.ncard = compRank Ψ * (compRank Ψ + 1))
    (hν : 3 ≤ ν) :
    compRank Ψ = ν - 1 := by
  apply mul_succ_injective
  change compRank Ψ * (compRank Ψ + 1) = (ν - 1) * ((ν - 1) + 1)
  have hcard : Ψ.ncard = ν * (ν - 1) := by rw [hΨ, kd147c_frameRoots_ncard hψ hκ hnorm]
  have h := hn
  rw [hcard] at h
  rw [Nat.sub_add_cancel (by omega : 1 ≤ ν), Nat.mul_comm (ν - 1) ν]
  exact h.symm

end LabelBase

section LabelCert

open scoped MatrixGroups

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA.RationalModel
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.GLTheoremA.K1419E
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

private theorem label_A_rankOne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hr1 : compRank (componentRoots (rootCharHom a) i) = 1)
    (hn : (componentRoots (rootCharHom a) i).ncard = 2)
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ lab : LargeEvenLabel, lab.tag = .A ∧
      lab.rank = compRank (componentRoots (rootCharHom a) i) ∧
      2 ^ lab.n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨K, hfield, hfinite, f, hf1, hKcard, hfeq, -, hK4, g, hgsurj, hgker⟩ :=
    exists_slCover_rationalComponent_rankOne S hT i hr1 hn hq
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  have h2 : ringChar L = 2 := ringChar.eq L 2
  have hK2 : Nat.card K = 2 ^ f := by rw [hKcard, h2]
  have hperf : commutator (SL(2, K)) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds K 2 (by norm_num)
      (fun _ => by rw [← Nat.card_eq_fintype_card]; exact hK4)).perfect
  obtain ⟨e_quot⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hperf g hgsurj hgker
  have hmodel : StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSL 2 2 f := by
    refine ⟨⟨Nat.prime_two, hf1, by norm_num, ?_, ?_⟩, K, hfield, hfinite, hK2, ⟨?_⟩⟩
    · intro hcon
      exact absurd (congrArg Prod.snd hcon) (by omega)
    · intro hcon
      exact absurd (congrArg Prod.snd hcon) (by omega)
    · exact e_quot.symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)
  have h2f : 2 ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    rw [← h2, hfeq]
  have hf2 : 2 ≤ f := by
    rw [hK2] at hK4
    by_contra hlt
    simp only [not_le] at hlt
    interval_cases f <;> norm_num at hK4
  refine ⟨⟨.A, compRank (componentRoots (rootCharHom a) i), f⟩, rfl, rfl, h2f, ?_, ?_⟩
  · rw [hr1]
    exact largeEvenInLambda2_A 1 f (by norm_num) hf1 (fun _ => hf2)
  · have hmodel' : StatedClassicalModel
        (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        .PSL (compRank (componentRoots (rootCharHom a) i) + 1) 2 f := by
      rw [hr1]
      exact hmodel
    exact ggHasLabel_A (compRank (componentRoots (rootCharHom a) i)) f hmodel'

private theorem label_A_splitFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π x) (π y))
    (hcr : compRank (componentRoots (rootCharHom a) i) = ν - 1) :
    ∃ lab : LargeEvenLabel, lab.tag = .A ∧
      lab.rank = compRank (componentRoots (rootCharHom a) i) ∧
      2 ^ lab.n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨K, hfield, hfinite, f, hf1, hKcard, hfeq, -, g, hgsurj, hgker⟩ :=
    exists_slCover_rationalComponent_splitFrame S hT i hν hψ hΨ π hπ
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  have h2 : ringChar L = 2 := ringChar.eq L 2
  have hK2 : Nat.card K = 2 ^ f := by rw [hKcard, h2]
  have hperf : commutator (SL(ν, K)) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds K ν (by omega)
      (fun h => by omega)).perfect
  obtain ⟨e_quot⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hperf g hgsurj hgker
  have hmodel : StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSL ν 2 f := by
    refine ⟨⟨Nat.prime_two, hf1, by omega, ?_, ?_⟩, K, hfield, hfinite, hK2, ⟨?_⟩⟩
    · intro hcon
      exact absurd (congrArg Prod.fst hcon) (by omega)
    · intro hcon
      exact absurd (congrArg Prod.fst hcon) (by omega)
    · exact e_quot.symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj ν K)
  have h2f : 2 ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    rw [← h2, hfeq]
  refine ⟨⟨.A, compRank (componentRoots (rootCharHom a) i), f⟩, rfl, rfl, h2f, ?_, ?_⟩
  · rw [hcr]
    exact largeEvenInLambda2_A (ν - 1) f (by omega) hf1 (fun _ => by omega)
  · have hmodel' : StatedClassicalModel
        (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        .PSL (compRank (componentRoots (rootCharHom a) i) + 1) 2 f := by
      rw [hcr, Nat.sub_add_cancel (by omega : 1 ≤ ν)]
      exact hmodel
    exact ggHasLabel_A (compRank (componentRoots (rootCharHom a) i)) f hmodel'

private theorem label_twA_unitaryFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x))
    (hcr : compRank (componentRoots (rootCharHom a) i) = ν - 1)
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ lab : LargeEvenLabel, lab.tag = .twA ∧
      lab.rank = compRank (componentRoots (rootCharHom a) i) ∧
      2 ^ lab.n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨K, hfield, hfinite, f, hf1, hKcard, hfeq, -, h32, g, hgsurj, hgker⟩ :=
    exists_suCover_rationalComponent_unitaryFrame S hT i hν hψ hΨ π hπ hq
  letI : Field K := hfield
  letI : Finite K := hfinite
  have h2 : ringChar L = 2 := ringChar.eq L 2
  have hmodelL : StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSU ν (ringChar L) f :=
    statedClassicalModel_PSU_of_suCover (K := K) (p := ringChar L) (f := f) (ν := ν)
      (by rw [h2]; exact Nat.prime_two) hf1 hKcard hν h32 g hgsurj hgker
  have hmodel : StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSU ν 2 f := by
    rw [← h2]
    exact hmodelL
  have h2f : 2 ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    rw [← h2, hfeq]
  refine ⟨⟨.twA, compRank (componentRoots (rootCharHom a) i), f⟩, rfl, rfl, h2f, ?_, ?_⟩
  · rw [hcr]
    refine largeEvenInLambda2_twA (ν - 1) f (by omega) hf1 ?_
    intro h
    have hν3 : ν = 3 := by omega
    have hf_ne1 : f ≠ 1 := by
      intro hf1'
      apply h32
      rw [hν3, hf1', h2]
      norm_num
    omega
  · have hmodel' : StatedClassicalModel
        (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        .PSU (compRank (componentRoots (rootCharHom a) i) + 1) 2 f := by
      rw [hcr, Nat.sub_add_cancel (by omega : 1 ≤ ν)]
      exact hmodel
    exact ggHasLabel_twA (compRank (componentRoots (rootCharHom a) i)) f hmodel'

private theorem frameCases_tracked
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    (compRank (componentRoots (rootCharHom a) i) = 1 ∧
        (componentRoots (rootCharHom a) i).ncard = 2) ∨
      (∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ)
        (π : Equiv.Perm (Fin ν)) (κ : ℤ),
        3 ≤ ν ∧ IsSLFrame ψ σ ∧ κ ≠ 0 ∧
          (∀ x y, x ≠ y → CFSG.LieType.Steinberg.Adjoint.iform (σ x y) (σ x y) = 2 * κ) ∧
          componentRoots (rootCharHom a) i = frameRoots σ ∧
          ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)] (σ x y) = σ (π x) (π y)) ∨
      (∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ)
        (π : Equiv.Perm (Fin ν)) (κ : ℤ),
        3 ≤ ν ∧ IsSLFrame ψ σ ∧ κ ≠ 0 ∧
          (∀ x y, x ≠ y → CFSG.LieType.Steinberg.Adjoint.iform (σ x y) (σ x y) = 2 * κ) ∧
          componentRoots (rootCharHom a) i = frameRoots σ ∧
          ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x)) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  · exact Or.inl ⟨hr1, by rw [hA.2, hr1]⟩
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
      exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i h2 hA.2
    obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
    set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
    have hmaps : ∀ x y, x ≠ y →
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
      intro x y hxy
      have h1 : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]
        exact ⟨x, y, hxy, rfl⟩
      have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i :=
        ⟨_, h1, rfl⟩
      rw [hs, hΨ] at h2
      exact h2
    have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
        (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
      intro n
      induction n with
      | zero => exact fun γ => rfl
      | succ n ih =>
        intro γ
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exact Or.inr (Or.inl ⟨ν, ψ, σ, π, κ, hν, hψ, hκ, hnorm, hΨ, hπ⟩)
    · exact Or.inr (Or.inr ⟨ν, ψ, σ, π, κ, hν, hψ, hκ, hnorm, hΨ, hπ⟩)

end LabelCert

section LabelMain

open scoped MatrixGroups

open CFSG.LocalAnalysis.GLTheoremA.RationalModel

theorem rationalLabel_typeA
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      lab.rank = compRank (componentRoots (rootCharHom a) i) ∧
      (twistKind S.ρ (rootCharHom a) i = .inner → lab.tag = .A) ∧
      (twistKind S.ρ (rootCharHom a) i = .suN → lab.tag = .twA) ∧ RationalLabelIs S i lab := by
  classical
  rcases frameCases_tracked S hp hT hap h1 i hA with ⟨hr1, hn⟩ | hsplit | hunit
  · obtain ⟨lab, htag, hrank, hdeg, hlab, hhas⟩ := label_A_rankOne S hT i hr1 hn hQS
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner :=
      twistKind_eq_inner_of_compRank_eq_one S i hr1
    exact ⟨lab, hdeg, hrank, fun _ => htag, fun hsu => by
      rw [hkind] at hsu
      exact absurd hsu (by decide), hlab, hhas⟩
  · obtain ⟨ν, ψ, σ, π, κ, hν, hψ, hκ, hnorm, hΨ, hπ⟩ := hsplit
    have hcr : compRank (componentRoots (rootCharHom a) i) = ν - 1 :=
      compRank_frameRoots_eq hψ hκ hnorm hΨ hA.2 hν
    have hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) :=
      hΨ.symm ▸ twistInner_of_splitFrame hψ hκ hnorm
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) π hπ
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
      unfold twistKind
      rw [if_pos hinner]
    obtain ⟨lab, htag, hrank, hdeg, hlab, hhas⟩ :=
      label_A_splitFrame S hT i hν hψ hΨ π hπ hcr
    exact ⟨lab, hdeg, hrank, fun _ => htag, fun hsu => by
      rw [hkind] at hsu
      exact absurd hsu (by decide), hlab, hhas⟩
  · obtain ⟨ν, ψ, σ, π, κ, hν, hψ, hκ, hnorm, hΨ, hπ⟩ := hunit
    have hcr : compRank (componentRoots (rootCharHom a) i) = ν - 1 :=
      compRank_frameRoots_eq hψ hκ hnorm hΨ hA.2 hν
    have hni : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) :=
      hΨ.symm ▸ not_twistInner_of_unitaryFrame hν hψ hκ hnorm
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) π hπ
    have h2c : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by
      rw [hcr]
      omega
    have hkind_ne : twistKind S.ρ (rootCharHom a) i ≠ .inner :=
      twistKind_ne_inner_of_not_twistInner S.ρ (rootCharHom a) i hni h2c hA.2
    obtain ⟨lab, htag, hrank, hdeg, hlab, hhas⟩ :=
      label_twA_unitaryFrame S hT i hν hψ hΨ π hπ hcr hQS
    exact ⟨lab, hdeg, hrank, fun heq => absurd heq hkind_ne, fun _ => htag, hlab, hhas⟩

end LabelMain

end CFSG.StandardType.TablePThreeKG

end
