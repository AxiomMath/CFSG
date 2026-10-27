module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcOrbit
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLCat
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore
import CFSG.LocalAnalysis.StandardType.GGExcCompSLLen
import CFSG.LocalAnalysis.StandardType.GGInnerD4RALabels
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerUntw
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTypeA
import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFam
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.RatLayer
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Layer
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.StandardType.RecipeExcLang CFSG.StandardType.LangRat
  CFSG.StandardType.TableCRes
  CFSG.ComponentClassification.OuterAutomorphisms


private theorem q2cEA_label_eq_of_iso {lab lab' : LargeEvenLabel} (hsl : GGSLTag lab.tag)
    (hA : lab'.tag = .A) (hr : 4 ≤ lab'.rank) (h : GGLabelIso lab lab') : lab = lab' := by
  rcases h with h | ⟨hB, -⟩ | ⟨-, hA3⟩ | ⟨-, hD⟩ | ⟨-, hA3⟩ | ⟨-, hD⟩ | ⟨-, hA1⟩ | ⟨hD, -⟩
  · exact h
  · rcases hsl with h | h | h | h | h | h | h | h | h <;> simp_all
  · rw [hA3] at hr; simp_all
  · rw [hD] at hA; simp_all
  · rw [hA3] at hA; simp_all
  · rw [hD] at hA; simp_all
  · rw [hA1] at hr; simp_all
  · rw [hD] at hA; simp_all

private theorem q2cEA_slTag_componentLabel (r N n : ℕ) (k : TwistKind) :
    GGSLTag (componentLabel r N k n).tag := by
  cases k <;> simp only [componentLabel] <;> (try split_ifs) <;> simp [GGSLTag]

private theorem q2cEA_compLabel_A {r N e d n : ℕ} {k : TwistKind}
    (h : componentLabel r N k e = (⟨.A, d - 1, n⟩ : LargeEvenLabel)) :
    r = d - 1 ∧ N = r * (r + 1) := by
  cases k with
  | inner =>
    dsimp only [componentLabel] at h
    by_cases hN : N = r * (r + 1)
    · rw [if_pos hN] at h
      exact ⟨by simpa using congrArg LargeEvenLabel.rank h, hN⟩
    · rw [if_neg hN] at h
      by_cases hD : N = 2 * r * (r - 1)
      · rw [if_pos hD] at h
        exact absurd (congrArg LargeEvenLabel.tag h) (by simp)
      · rw [if_neg hD] at h
        by_cases h6 : r = 6
        · rw [if_pos h6] at h
          exact absurd (congrArg LargeEvenLabel.tag h) (by simp)
        · rw [if_neg h6] at h
          by_cases h7 : r = 7
          · rw [if_pos h7] at h
            exact absurd (congrArg LargeEvenLabel.tag h) (by simp)
          · rw [if_neg h7] at h
            exact absurd (congrArg LargeEvenLabel.tag h) (by simp)
  | suN =>
    dsimp only [componentLabel] at h
    exact absurd (congrArg LargeEvenLabel.tag h) (by simp)
  | twoD =>
    dsimp only [componentLabel] at h
    exact absurd (congrArg LargeEvenLabel.tag h) (by simp)
  | exc =>
    dsimp only [componentLabel] at h
    split_ifs at h <;> exact absurd (congrArg LargeEvenLabel.tag h) (by simp)

private theorem q2cEA_typeA_shape {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {d m : ℕ} (hd : 5 ≤ d) (hm : 2 ≤ m) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 2 ^ m)
    (θ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) :
    compRank (componentRoots (rootCharHom a) i) = d - 1 ∧
      (componentRoots (rootCharHom a) i).ncard = (d - 1) * d := by
  classical
  set Ψ : Set (Fin τ.rank → ℤ) := componentRoots (rootCharHom a) i with hΨ
  let a' : PUnit.{1} → Fin τ.rank → Lˣ := fun _ => a
  have hT' : ∀ u, rootDiagUnit τ (a' u) ∈ S.D.torus := fun _ => hT
  have hap' : ∀ u j, a' u j ^ p = 1 := fun _ j => hap j
  have hrange : (Set.range fun u : PUnit.{1} => rootDiagUnit τ (a' u)) = {rootDiagUnit τ a} := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact Set.mem_singleton _
    · rintro rfl
      exact ⟨PUnit.unit, rfl⟩
  have hK : CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u : PUnit.{1} => rootDiagUnit τ (a' u))) := by
    rw [hrange]
    exact CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.isComponentOf_rationalComponent S hT i hq
  obtain ⟨i', hi'⟩ := exists_componentRoots_eq (kernelRoots_famChar_punit_eq a).symm i
  have hspan : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ L (famOrbit S.ρ a' i') := by
    have hforb : famOrbit S.ρ a' i' = rationalRoots S.ρ (rootCharHom a) i := by
      ext γ
      simp only [famOrbit, rationalRoots, Set.mem_setOf_eq]
      rw [hi']
    rw [hforb]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  obtain ⟨f, -, hfq⟩ := CFSG.HardMathSupport.Dickson.Sec6.ssTw_exists_f S (ℓ := 2)
  obtain ⟨n, hn, hlab⟩ := langFamilyCompLabel_exc hτ S hp hp2 a' hT' hap' hK i' hspan
  rw [← hi'] at hn
  have hlab' : GGCompLabelAt (LabAt S.ρ f Ψ) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    rw [← hi'] at hlab
    have h2 : (2 : ℕ) ^ n = 2 ^ (componentOrbitLength S.ρ Ψ * f) := by
      rw [hn, hfq, ← pow_mul, mul_comm]
    have hnf := Nat.pow_right_injective (le_refl 2) h2
    unfold LabAt
    rw [← hnf]
    exact hlab
  haveI hsimple : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) :=
    θ.isSimpleGroup_congr.mp hq.2.1
  let eA : LargeEvenProj (LargeEvenSLGroup (Fin d) F₀) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL d F₀) :=
    (TypeA.recipeEquiv d F₀).trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          d F₀).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d F₀))
  obtain ⟨hlabA, hhasA⟩ :=
    S2MathAs51600RALabels.admissible_typeA_of_psl
      (Q := LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) (a := d) (m := m) (E := F₀)
      (by omega) hF₀ eA
  have hhasθ' : GGHasLabel (⟨.A, d - 1, m⟩ : LargeEvenLabel)
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
    unfold GGHasLabel at hhasA ⊢
    exact largeEvenRawDatum_mono (fun R _ I F ⟨e'⟩ => ⟨θ.trans e'⟩) hhasA
  have hIso : GGLabelIso (LabAt S.ρ f Ψ) (⟨.A, d - 1, m⟩ : LargeEvenLabel) :=
    ggLabelRigidInput_holds _ _ _ hlab'.1 hlabA hlab'.2.2.1 hhasθ'
  have hsl' : GGSLTag (LabAt S.ρ f Ψ).tag := by
    unfold LabAt
    exact q2cEA_slTag_componentLabel _ _ _ _
  have hEq : LabAt S.ρ f Ψ = (⟨.A, d - 1, m⟩ : LargeEvenLabel) :=
    q2cEA_label_eq_of_iso hsl' rfl (by change 4 ≤ d - 1; omega) hIso
  have hshape := q2cEA_compLabel_A (by simpa only [LabAt] using hEq)
  have hr : compRank Ψ = d - 1 := hshape.1
  have hN : Ψ.ncard = (d - 1) * d := by
    rw [hr] at hshape
    have h1' : d - 1 + 1 = d := by omega
    rw [h1'] at hshape
    exact hshape.2
  exact ⟨hr, hN⟩

private theorem q2cEA_field {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {d m : ℕ} (hd : 5 ≤ d) (hm : 2 ≤ m) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 2 ^ m)
    (θ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) :
    Nat.card F₀ = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
  classical
  have hfd := langRatCompFieldLenSL_holds τ L p₀ S hτ p hp hp2 a hT hap h1 i hq
  obtain ⟨lab, hlab, -, hdeg, hsl, hhas, R', hR'inst, hmm, ⟨eR'⟩⟩ := hfd
  haveI hsimple : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) :=
    θ.isSimpleGroup_congr.mp hq.2.1
  let eA : LargeEvenProj (LargeEvenSLGroup (Fin d) F₀) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL d F₀) :=
    (TypeA.recipeEquiv d F₀).trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          d F₀).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d F₀))
  obtain ⟨hlabA, hhasA⟩ :=
    S2MathAs51600RALabels.admissible_typeA_of_psl
      (Q := LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) (a := d) (m := m) (E := F₀)
      (by omega) hF₀ eA
  have hhasθ : GGHasLabel lab (LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) := by
    unfold GGHasLabel at hhas ⊢
    exact largeEvenRawDatum_mono (fun R _ I F ⟨e'⟩ => ⟨θ.symm.trans e'⟩) hhas
  have hIso : GGLabelIso lab ⟨.A, d - 1, m⟩ :=
    ggLabelRigidInput_holds lab ⟨.A, d - 1, m⟩
      (LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) hlab hlabA hhasθ hhasA
  have hlab_eq : lab = ⟨.A, d - 1, m⟩ :=
    q2cEA_label_eq_of_iso hsl rfl (by change 4 ≤ d - 1; omega) hIso
  rw [hlab_eq] at hdeg
  simp only [markDeg] at hdeg
  exact hF₀.trans hdeg

theorem q2cEA_compRank_eq {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {d m : ℕ} (hd : 5 ≤ d) (hm : 2 ≤ m) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 2 ^ m)
    (θ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) :
    compRank (componentRoots (rootCharHom a) i) = d - 1 :=
  (q2cEA_typeA_shape hτ S hp hp2 hT hap h1 i hq hd hm hF₀ θ).1

theorem q2cEA_E6_bound {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {d m : ℕ} (hd : 5 ≤ d) (hm : 2 ≤ m) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 2 ^ m)
    (θ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) :
    τ = .E6 → d ≤ 6 := by
  intro hτ6
  subst hτ6
  by_contra hd7
  have hd7' : 7 ≤ d := by omega
  obtain ⟨hr, hN⟩ := q2cEA_typeA_shape hτ S hp hp2 hT hap h1 i hq hd hm hF₀ θ
  have hℓ2 : ringChar L = 2 := ringChar.eq L 2
  have hpL : ((p : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓ2]; exact fun h => hp2 h.symm)
  have hTp : rootDiagUnit .E6 a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
  have hrank6 : (Tag.E6).rank = 6 := rfl
  have hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) *
      compRank (componentRoots (rootCharHom a) i) ≤ (Tag.E6).rank :=
    componentOrbitLength_mul_compRank_le S hT i
  have hs1 : 1 ≤ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
    (outer_componentOrbitLength_spec S hT i).1
  have hcomp6 : compRank (componentRoots (rootCharHom a) i) = 6 := by
    rw [hrank6, hr] at hs
    have hle : d - 1 ≤ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) * (d - 1) := by
      calc d - 1 = 1 * (d - 1) := (one_mul _).symm
        _ ≤ _ * (d - 1) := Nat.mul_le_mul_right _ hs1
    have hge : 6 ≤ d - 1 := by omega
    have hd1 : d - 1 = 6 := le_antisymm (hle.trans hs) hge
    omega
  have hc6 : c.length = 6 := by
    rw [← hrank]
    exact hcomp6
  have hd_eq : d = 7 := by omega
  have hno42 : ∀ c ∈ e6Conn, c.length = 6 →
      kacCount Tag.E6 ![1, 2, 2, 3, 2, 1]
        (c.map (idxNode (r := Tag.E6.rank))).toFinset ≠ 42 := by
    decide +kernel
  have hc42 : kacCount Tag.E6 kacE6.θ
      (c.map (idxNode (r := Tag.E6.rank))).toFinset = 42 := by
    rw [← hncard, hN, hd_eq]
  exact hno42 c hc hc6 hc42

theorem q2cEA_typeA_data {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {d m : ℕ} (hd : 5 ≤ d) (hm : 2 ≤ m) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 2 ^ m)
    (θ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) :
    compRank (componentRoots (rootCharHom a) i) = d - 1 ∧
      Nat.card F₀ = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      (τ = .E6 → d ≤ 6) :=
  ⟨q2cEA_compRank_eq hτ S hp hp2 hT hap h1 i hq hd hm hF₀ θ,
    q2cEA_field hτ S hp hp2 hT hap h1 i hq hd hm hF₀ θ,
    q2cEA_E6_bound hτ S hp hp2 hT hap h1 i hq hd hm hF₀ θ⟩

theorem q2c_exc_comp_typeA {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK2 : ringChar K = 2)
    (β : MulAut ↥(adjointGroup τ K))
    (hβ : ∃ h ∈ inndiagGroup τ K, ∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹)
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) (J : Subgroup ↥(adjointGroup τ K))
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β))
    {d m : ℕ} (hd : 5 ≤ d) (hm : 2 ≤ m) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 2 ^ m)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F₀)) :
    ∃ s : ℕ, 1 ≤ s ∧ Nat.card F₀ = Nat.card K ^ s ∧ s * (d - 1) ≤ τ.rank ∧ (τ = .E6 → d ≤ 6) := by
  classical
  obtain ⟨h, hh, hβh⟩ := hβ
  obtain ⟨h', hh', hβh', hp1⟩ := exists_inndiag_pow_eq_one hτ hp β hβp hh hβh
  have hh1 : h' ≠ 1 := by
    intro h1
    apply hβ1
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rw [hβh' c, h1]
    simp
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpℓ : p ≠ ringChar K := by rw [hK2]; exact hp2
  have hpK : ¬ p ∣ Nat.card K := fun hdvd =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow (hK ▸ hdvd)))
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hdvd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hdvd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hτ5 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl <;> simp) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (by rcases hτ with rfl | rfl | rfl <;> simp)
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (τ := τ) (Or.inr (Or.inr hτ)) hp hpK hp₀ hp₀K hq₀'
      hmon hperf β h' (baseChange_mem_adjointGroup_of_mem_inndiag hh') hβh' hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hℓ2 : ringChar (AlgebraicClosure K) = 2 := by rw [hℓL, hK2]
  haveI : CharP (AlgebraicClosure K) 2 := hℓ2 ▸ ringChar.charP (AlgebraicClosure K)
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := fun hG2 =>
    absurd hG2 (by rcases hτ with rfl | rfl | rfl <;> decide)
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  let θ' : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) F₀) :=
    (QuotientGroup.congr (Subgroup.center ↥J)
      (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) eJ
      (Subgroup.map_center_eq eJ)).symm.trans θ
  obtain ⟨hrank, hfield, hE6⟩ :=
    q2cEA_typeA_data hτ S hp hp2 hT hap h1 i hqs hd hm hF₀ θ'
  refine ⟨componentOrbitLength S.ρ (componentRoots (rootCharHom a) i), ?_, ?_, ?_, ?_⟩
  · have := (outer_componentOrbitLength_spec S hT i).1; omega
  · rw [hfield, ← hSq]
  · rw [← hrank]; exact componentOrbitLength_mul_compRank_le S hT i
  · exact hE6

end CFSG.StandardType
