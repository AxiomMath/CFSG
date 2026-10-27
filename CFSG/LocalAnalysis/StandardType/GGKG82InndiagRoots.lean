module

public import CFSG.LocalAnalysis.StandardType.GGKG82Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LieType.Chevalley.E6GraphRootSL2Basic
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.D4TripleA2Lemmas
public import CFSG.Blueprint.ChevalleyRootGroupsTriangular
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public section

namespace CFSG.StandardType.KG82

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix

@[expose] def leviRoot : Fin 3 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1]]

theorem leviRoot_facts :
    (∀ i, leviRoot i ∈ rootFinset TwistTag.E6.tag) ∧
      (∀ i, permLattice TwistTag.E6.perm (leviRoot i) = leviRoot i) ∧
      (∀ i, permLattice TwistTag.E6.perm (-leviRoot i) = -leviRoot i) ∧
      (∀ i, 0 < height (leviRoot i)) ∧ (∀ i, height (-leviRoot i) < 0) ∧
      (∀ i, leviRoot i ⬝ᵥ (TwistTag.E6.tag.symmetrizedCartan *ᵥ e6HighestRoot) = 0) ∧
      (∀ i, leviRoot i ≠ e6HighestRoot ∧ leviRoot i ≠ -e6HighestRoot) ∧
      (∀ i j, i ≠ j →
        leviRoot i ⬝ᵥ (TwistTag.E6.tag.symmetrizedCartan *ᵥ leviRoot j) = 0 ∧
          leviRoot i ≠ leviRoot j ∧ leviRoot i ≠ -leviRoot j) := by
  decide +kernel

theorem isRoot_leviRoot (i : Fin 3) :
    IsRoot TwistTag.E6.tag (leviRoot i) :=
  mem_rootFinset.1 (leviRoot_facts.1 i)

theorem commute_pinnedX_of_orth
    {K : Type} [Field K] {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β) (hne' : α ≠ -β)
    (h0 : α ⬝ᵥ (TwistTag.E6.tag.symmetrizedCartan *ᵥ β) = 0) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d) ∧
      Commute (pinnedX TwistTag.E6.tag K (-α) c) (pinnedX TwistTag.E6.tag K β d) ∧
      Commute (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K (-β) d) ∧
      Commute (pinnedX TwistTag.E6.tag K (-α) c) (pinnedX TwistTag.E6.tag K (-β) d) := by
  have hτ : TwistTag.E6.tag = .D4 ∨ TwistTag.E6.tag = .E6 ∨ TwistTag.E6.tag = .E7 ∨
      TwistTag.E6.tag = .E8 := Or.inr (Or.inl rfl)
  have h1 : (-α) ⬝ᵥ (TwistTag.E6.tag.symmetrizedCartan *ᵥ β) = 0 := by
    rw [neg_dotProduct, h0, neg_zero]
  have h2 : α ⬝ᵥ (TwistTag.E6.tag.symmetrizedCartan *ᵥ (-β)) = 0 := by
    rw [mulVec_neg, dotProduct_neg, h0, neg_zero]
  have h3 : (-α) ⬝ᵥ (TwistTag.E6.tag.symmetrizedCartan *ᵥ (-β)) = 0 := by
    rw [mulVec_neg, dotProduct_neg, neg_dotProduct, h0, neg_zero, neg_zero]
  refine ⟨pinnedX_commute_of_rootForm_nonneg hτ hα hβ hne h0.ge c d,
    pinnedX_commute_of_rootForm_nonneg hτ (IsRoot.neg hα) hβ ?_ h1.ge c d,
    pinnedX_commute_of_rootForm_nonneg hτ hα (IsRoot.neg hβ) hne' h2.ge c d,
    pinnedX_commute_of_rootForm_nonneg hτ (IsRoot.neg hα) (IsRoot.neg hβ) ?_ h3.ge c d⟩
  · intro h
    exact hne' (by rw [← h, neg_neg])
  · intro h
    exact hne (neg_injective h)

theorem pinnedX_mem_posUnipotent
    {K : Type} [Field K] {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hp : 0 < height α) (c : K) : pinnedX TwistTag.E6.tag K α c ∈ posUnipotent TwistTag.E6.tag K :=
  Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem ⟨hα, hp⟩ (mem_rootSubgroup.2 ⟨c, rfl⟩))

theorem pinnedX_mem_negUnipotent
    {K : Type} [Field K] {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hn : height α < 0) (c : K) : pinnedX TwistTag.E6.tag K α c ∈ negUnipotent TwistTag.E6.tag K :=
  Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem ⟨hα, hn⟩ (mem_rootSubgroup.2 ⟨c, rfl⟩))

@[expose] noncomputable def leviY
    (K : Type) [Field K] (γ : Fin TwistTag.E6.tag.rank → ℤ) : ModGL TwistTag.E6.tag K :=
  pinnedX TwistTag.E6.tag K γ 1 * pinnedX TwistTag.E6.tag K (-γ) 1

section RankOne

variable {K : Type} [Field K] [CharP K 2] {γ : Fin TwistTag.E6.tag.rank → ℤ}

theorem rootSL2_uSL_one
    (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    rootSL2 TwistTag.E6.tag K γ (uSL 1) = pinnedX TwistTag.E6.tag K γ 1 := by
  rw [rootSL2_uSL_eq]
  rcases pinnedSign_eq TwistTag.E6.tag γ with h | h <;> rw [h]
  · rw [one_smul]
  · rw [neg_smul, one_smul, CharTwo.neg_eq]

theorem rootSL2_vSL_one
    (hγ : IsRoot TwistTag.E6.tag γ) :
    rootSL2 TwistTag.E6.tag K γ (vSL 1) = pinnedX TwistTag.E6.tag K (-γ) 1 := by
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) hγ
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : (ε + 1) * (ε + 1) = 0 := by linear_combination hε + (1 + ε) * h2
    have h0 : ε + 1 = 0 := mul_self_eq_zero.1 hsq
    rw [← CharTwo.neg_eq (1 : K), ← sub_eq_zero, sub_neg_eq_add, h0]
  rw [hv, hε1, mul_one]

theorem rootSL2_uSL_mul_vSL
    (hγ : IsRoot TwistTag.E6.tag γ) :
    rootSL2 TwistTag.E6.tag K γ (uSL 1 * vSL 1) = leviY K γ := by
  rw [map_mul, rootSL2_uSL_one, rootSL2_vSL_one hγ, leviY]

theorem leviY_pow_three
    (hγ : IsRoot TwistTag.E6.tag γ) : leviY K γ ^ 3 = 1 := by
  rw [← rootSL2_uSL_mul_vSL hγ, ← map_pow,
    E6GraphRootSL2.uSL_mul_vSL_pow_three CharTwo.two_eq_zero, map_one]

theorem uSL_mul_vSL_mul_uSL : (uSL 1 * vSL 1 : SL2 K) * uSL 1 = vSL 1 * (uSL 1 * vSL 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine E6GraphRootSL2.SL2_ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [coe_uSL, coe_vSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    first | rfl | exact h2 | exact h2.symm | ring1 | linear_combination h2

theorem leviY_mul_pinnedX
    (hγ : IsRoot TwistTag.E6.tag γ) :
    leviY K γ * pinnedX TwistTag.E6.tag K γ 1 = pinnedX TwistTag.E6.tag K (-γ) 1 * leviY K γ := by
  have e := congrArg (rootSL2 TwistTag.E6.tag K γ) (uSL_mul_vSL_mul_uSL (K := K))
  simp only [map_mul, rootSL2_uSL_one, rootSL2_vSL_one hγ] at e
  rw [leviY]
  exact e

theorem not_commute_leviY
    (hγ : IsRoot TwistTag.E6.tag γ) (hp : 0 < height γ)
    (hn : height (-γ) < 0) : ¬ Commute (leviY K γ) (pinnedX TwistTag.E6.tag K γ 1) := by
  intro hc
  have e := leviY_mul_pinnedX (K := K) hγ
  have hx : pinnedX TwistTag.E6.tag K γ 1 = pinnedX TwistTag.E6.tag K (-γ) 1 :=
    mul_right_cancel (hc.eq.symm.trans e)
  have hneg := pinnedX_mem_negUnipotent (IsRoot.neg hγ) hn (1 : K)
  rw [← hx] at hneg
  have hmem : pinnedX TwistTag.E6.tag K γ 1 ∈
      posUnipotent TwistTag.E6.tag K ⊓ negUnipotent TwistTag.E6.tag K :=
    Subgroup.mem_inf.2 ⟨pinnedX_mem_posUnipotent hγ hp 1, hneg⟩
  rw [CFSG.Blueprint.Chevalley.posUnipotent_inf_negUnipotent, Subgroup.mem_bot] at hmem
  exact one_ne_zero (pinnedX_injective TwistTag.E6.tag K γ
    (hmem.trans (pinnedX_zero TwistTag.E6.tag K γ).symm))

end RankOne

section Orth

variable {K : Type} [Field K]

theorem commute_leviY_pinnedX
    {i j : Fin 3} (hij : i ≠ j) (c : K) :
    Commute (leviY K (leviRoot i)) (pinnedX TwistTag.E6.tag K (leviRoot j) c) ∧
      Commute (leviY K (leviRoot i)) (pinnedX TwistTag.E6.tag K (-leviRoot j) c) := by
  obtain ⟨h0, hne, hne'⟩ := leviRoot_facts.2.2.2.2.2.2.2 i j hij
  obtain ⟨a1, a2, a3, a4⟩ := commute_pinnedX_of_orth (isRoot_leviRoot i) (isRoot_leviRoot j) hne
    hne' h0 (1 : K) c
  exact ⟨a1.mul_left a2, a3.mul_left a4⟩

theorem commute_leviY_leviY
    (i j : Fin 3) :
    Commute (leviY K (leviRoot i)) (leviY K (leviRoot j)) := by
  by_cases hij : i = j
  · rw [hij]
  · obtain ⟨a1, a2⟩ := commute_leviY_pinnedX (K := K) hij 1
    exact a1.mul_right a2

theorem commute_leviY_highRoot
    (i : Fin 3) (c : K) :
    Commute (leviY K (leviRoot i)) (pinnedX TwistTag.E6.tag K e6HighestRoot c) := by
  obtain ⟨hne, hne'⟩ := leviRoot_facts.2.2.2.2.2.2.1 i
  obtain ⟨a1, a2, -, -⟩ := commute_pinnedX_of_orth (isRoot_leviRoot i) isRoot_e6HighestRoot hne
    hne' (leviRoot_facts.2.2.2.2.2.1 i) (1 : K) c
  exact a1.mul_left a2

theorem leviY_mem_graphFixedRootGroup
    [CharP K 2] (σ : K →+* K) (i : Fin 3) :
    leviY K (leviRoot i) ∈ graphFixedRootGroup TwistTag.E6 K σ :=
  mul_mem
    (CFSG.SeitzReduction.pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_leviRoot i)
      (leviRoot_facts.2.1 i) (map_one σ))
    (CFSG.SeitzReduction.pinnedX_mem_graphFixedRootGroup_of_fixed σ (IsRoot.neg (isRoot_leviRoot i))
      (leviRoot_facts.2.2.1 i) (map_one σ))

end Orth

section Diag

variable {K : Type} [Field K]

@[expose] def diagParam (ζ : Kˣ) (e : Fin TwistTag.E6.tag.rank → ℤ) :
    Fin TwistTag.E6.tag.rank → Kˣ :=
  fun i => ζ ^ e i

@[expose] def diagExp : Fin 2 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![1, 0, 0, 0, 0, -1], ![0, 0, 1, 0, -1, 0]]

theorem diagExp_facts :
    (∀ k i, diagExp k (TwistTag.E6.perm i) = -diagExp k i) ∧
      (∀ k, diagExp k ⬝ᵥ e6HighestRoot = 0) ∧ (∀ k i, diagExp k ⬝ᵥ leviRoot i = 0) ∧
      diagExp 0 ⬝ᵥ Pi.single 0 1 = 1 ∧ diagExp 0 ⬝ᵥ Pi.single 2 1 = 0 ∧
      diagExp 1 ⬝ᵥ Pi.single 2 1 = 1 := by
  decide

theorem rootChar_diagParam (ζ : Kˣ) (e γ : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (diagParam ζ e) γ = ζ ^ (e ⬝ᵥ γ) := by
  simp only [rootChar, diagParam, ← _root_.zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  rfl

theorem isCompatE6_diagParam {σ : K →+* K} {ζ : Kˣ} (hζ : Units.map σ.toMonoidHom ζ = ζ⁻¹)
    {e : Fin TwistTag.E6.tag.rank → ℤ} (he : ∀ i, e (TwistTag.E6.perm i) = -e i) :
    RecipeExcLang.IsCompatE6 σ (diagParam ζ e) := by
  intro i
  rw [diagParam, diagParam, he i, map_zpow, hζ, _root_.inv_zpow']

theorem diagParam_pow_three {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (e : Fin TwistTag.E6.tag.rank → ℤ) :
    diagParam ζ e ^ 3 = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply, diagParam, ← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm,
    _root_.zpow_mul, _root_.zpow_natCast, hζ, _root_.one_zpow]

end Diag

section DiagElt

variable {K : Type} [Field K]

theorem commute_rootDiagUnit_pinnedX
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (h : rootChar b γ = 1)
    (c : K) : Commute (rootDiagUnit TwistTag.E6.tag b) (pinnedX TwistTag.E6.tag K γ c) := by
  have e := rootDiagUnit_conj_pinnedX b hγ c
  rw [h, Units.val_one, one_mul] at e
  exact mul_inv_eq_iff_eq_mul.1 e

theorem not_commute_rootDiagUnit_pinnedX
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (h : rootChar b γ ≠ 1) :
    ¬ Commute (rootDiagUnit TwistTag.E6.tag b) (pinnedX TwistTag.E6.tag K γ 1) := by
  intro hc
  have e := rootDiagUnit_conj_pinnedX b hγ (1 : K)
  rw [hc.eq, mul_inv_cancel_right, mul_one] at e
  exact h (Units.ext (pinnedX_injective TwistTag.E6.tag K γ e).symm)

theorem commute_rootDiagUnit_leviY
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (h : rootChar b γ = 1) :
    Commute (rootDiagUnit TwistTag.E6.tag b) (leviY K γ) := by
  have h' : rootChar b (-γ) = 1 := by
    rw [← zero_sub, rootChar_sub, rootChar_zero, h, inv_one, one_mul]
  exact (commute_rootDiagUnit_pinnedX hγ h 1).mul_right
    (commute_rootDiagUnit_pinnedX (IsRoot.neg hγ) h' 1)

theorem commute_rootDiagUnit (a b : Fin TwistTag.E6.tag.rank → Kˣ) :
    Commute (rootDiagUnit TwistTag.E6.tag a) (rootDiagUnit TwistTag.E6.tag b) := by
  rw [Commute, SemiconjBy, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem rootDiagUnit_pow_three {b : Fin TwistTag.E6.tag.rank → Kˣ} (hb : b ^ 3 = 1) :
    rootDiagUnit TwistTag.E6.tag b ^ 3 = 1 := by
  have h := map_pow (rootDiagUnitHom TwistTag.E6.tag K) b 3
  rw [hb, map_one] at h
  exact h.symm

end DiagElt

end CFSG.StandardType.KG82
