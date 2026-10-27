module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyClosedLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsLeaf
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.RankThree.PartOne.S11c.EvenRootInverters
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Data
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.RankThree.Chevalley.SteinbergCFOddE6E7RootInverters

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

private theorem iform_self_eq_two_of_symm_one
    {τ : Tag} (hsym : ∀ i, τ.symmetrizer i i = 1) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    iform γ γ = 2 :=
  TableBExcTwo.iform_self_eq_two_of_isRoot hsym hγ

private theorem abs_iform_le_two_of_symm_one
    {τ : Tag} (hsym : ∀ i, τ.symmetrizer i i = 1) {β γ : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hγ : IsRoot τ γ) : |iform β γ| ≤ 2 := by
  have h := CFSG.ClassicalInvolution.ModelFacts.Levi.iform_sq_le β γ
  rw [iform_self_eq_two_of_symm_one hsym hβ,
    iform_self_eq_two_of_symm_one hsym hγ] at h
  rw [abs_le]
  constructor <;> nlinarith

private theorem eq_or_neg_of_iform_eq_two_of_symm_one
    {τ : Tag} (hsym : ∀ i, τ.symmetrizer i i = 1)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (h : iform α β = 2 ∨ iform α β = -2) : β = α ∨ β = -α := by
  have hαα := iform_self_eq_two_of_symm_one hsym hα
  have hββ := iform_self_eq_two_of_symm_one hsym hβ
  rcases h with h | h
  · left
    by_contra hne
    have hpos := iform_self_pos (sub_ne_zero.2 hne)
    rw [iform_sub_left, iform_sub_right, iform_sub_right, hαα, hββ, iform_comm β α, h] at hpos
    omega
  · right
    by_contra hne
    have hne' : β + α ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
    have hpos := iform_self_pos hne'
    rw [iform_add_left, iform_add_right, iform_add_right, hαα, hββ, iform_comm β α, h] at hpos
    omega

private theorem rootReflection_smul_eq_sub
    {τ : Tag} (hsym : ∀ i, τ.symmetrizer i i = 1) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (v : Fin τ.rank → ℤ) : rootReflection β • v = v - iform β v • β := by
  rw [rootReflection_smul hβ]
  have h2 : iform β β = 2 := iform_self_eq_two_of_symm_one hsym hβ
  have h := corootPair_mul hβ v
  rw [h2] at h
  have hcp : corootPair β v = iform β v :=
    mul_right_cancel₀ (two_ne_zero) (by rw [h]; ring)
  rw [hcp]

private theorem step_pinnedX_one_of_frobRootMap
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    (D : LangDatum τ L) {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    D.step (pinnedX τ L γ 1) = pinnedX τ L (ρ γ) 1 := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  obtain ⟨π, hπroot, -, -, hπ⟩ := exists_diagram_data (L := L) hP
  obtain ⟨w, hn⟩ := D.n_weyl
  obtain ⟨ε₁, hε₁, h₁⟩ := hπ γ hγ
  have hπγ : IsRoot τ (π γ) := (hπroot γ).2 hγ
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hπγ
  have e₁ := eq_one_of_mul_self_eq_one_of_charTwo hε₁
  have e₂ := eq_one_of_mul_self_eq_one_of_charTwo hε₂
  have hs : D.step (pinnedX τ L γ 1) = pinnedX τ L (w • π γ) 1 := by
    have h0 : D.step (pinnedX τ L γ 1) = D.n * D.Φ (pinnedX τ L γ 1) * D.n⁻¹ := by
      simp [LangDatum.step, MulAut.conj_apply]
    rw [h0, hΦ, units_map_entrywiseHom_pinnedX, map_one, h₁, e₁, one_mul, hn, h₂, e₂,
      one_mul]
  have hmem : D.step (pinnedX τ L γ 1) ∈ rootSubgroup τ L (ρ γ) := by
    rw [← hρ.map_rootSubgroup γ hγ]
    exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨1, rfl⟩)
  rw [hs] at hmem ⊢
  have hroot : IsRoot τ (w • π γ) := (isRoot_smul_iff w).2 hπγ
  rw [eq_of_pinnedX_one_mem_rootSubgroup hroot ((hρ.isRoot_iff γ).2 hγ) hmem]

private theorem familyKernel_finite {τ : Tag} {L : Type} [Field L]
    {ι : Type} (a : ι → Fin τ.rank → Lˣ) : (familyKernel a).Finite :=
  (finite_setOf_isRoot τ).subset fun _ hγ => hγ.1

private theorem rootChar_neg_unit {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    (v : Fin τ.rank → ℤ) : rootChar a (-v) = (rootChar a v)⁻¹ := by
  have h := rootChar_zsmul a (-1) v
  rw [neg_one_smul] at h
  simpa using h

private theorem familyKernel_neg {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {γ : Fin τ.rank → ℤ} (h : γ ∈ familyKernel a) :
    -γ ∈ familyKernel a := by
  refine ⟨IsRoot.neg h.1, fun i => ?_⟩
  rw [rootChar_neg_unit, h.2 i, inv_one]

private def famConn {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) (β γ : Fin τ.rank → ℤ) : Prop :=
  Relation.ReflTransGen
    (fun x y => x ∈ familyKernel a ∧ y ∈ familyKernel a ∧ iform x y ≠ 0) β γ

private theorem famConn_refl {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {β : Fin τ.rank → ℤ} :
    famConn a β β :=
  Relation.ReflTransGen.refl

private theorem famConn_step {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {β γ δ : Fin τ.rank → ℤ} (h : famConn a β γ)
    (hγ : γ ∈ familyKernel a) (hδ : δ ∈ familyKernel a) (hne : iform γ δ ≠ 0) :
    famConn a β δ :=
  Relation.ReflTransGen.tail h ⟨hγ, hδ, hne⟩

private theorem famConn_trans {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {β γ δ : Fin τ.rank → ℤ} (h1 : famConn a β γ)
    (h2 : famConn a γ δ) : famConn a β δ :=
  Relation.ReflTransGen.trans h1 h2

private theorem famConn_symm
    {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {β γ : Fin τ.rank → ℤ} (h : famConn a β γ) :
    famConn a γ β := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, fun h0 => hbc.2.2 (iform_comm _ _ ▸ h0)⟩ ih

private noncomputable def nref
    (τ : Tag) (L : Type) [Field L] (α : Fin τ.rank → ℤ) : ModGL τ L :=
  canonicalRep (coxeterSystem τ) L (rootReflection α)

private def FamilyKernelConjData
    {τ : Tag} {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (β γ : Fin τ.rank → ℤ) (n : ModGL τ L) : Prop :=
  n ∈ familyGroup (K := L) a ∧
    n * pinnedX τ L β 1 * n⁻¹ = pinnedX τ L γ 1 ∧
    n * pinnedX τ L (-β) 1 * n⁻¹ = pinnedX τ L (-γ) 1 ∧
    ∀ ε (_ : ε ∈ familyKernel a), iform β ε = 0 → iform γ ε = 0 →
      n * pinnedX τ L ε 1 * n⁻¹ = pinnedX τ L ε 1 ∧
      n * pinnedX τ L (-ε) 1 * n⁻¹ = pinnedX τ L (-ε) 1

private theorem nref_conj_pinnedX_one
    {τ : Tag} {L : Type} [Field L] (h2 : (2 : L) = 0)
    {α β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    nref τ L α * pinnedX τ L β 1 * (nref τ L α)⁻¹ =
      pinnedX τ L (rootReflection α • β) 1 :=
  canonicalRep_mul_pinnedX_mul_inv_of_two h2 (rootReflection α) hβ 1

private theorem nref_mem_familyGroup
    {τ : Tag} {L : Type} [Field L]
    {ι : Type} {a : ι → Fin τ.rank → Lˣ} {α : Fin τ.rank → ℤ}
    (hα : α ∈ familyKernel a) : nref τ L α ∈ familyGroup (K := L) a := by
  have h := CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.canonicalRep_rootReflection_mem
    (k := L) hα.1
  refine sup_le_sup_left (rootSpan_mono ?_) _ h
  rintro x (rfl | hx)
  · exact hα
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact familyKernel_neg hα

private theorem conjData_self
    {τ : Tag} {L : Type} [Field L] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    {β : Fin τ.rank → ℤ} : FamilyKernelConjData a β β (1 : ModGL τ L) := by
  refine ⟨one_mem _, by simp, by simp, ?_⟩
  intro ε _ _ _
  exact ⟨by simp, by simp⟩

private theorem conjData_neg
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ} {β : Fin τ.rank → ℤ}
    (hβ : β ∈ familyKernel a) : FamilyKernelConjData a β (-β) (nref τ L β) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hfix : rootReflection β • (-β) = -(-β) := by
    rw [smul_neg, rootReflection_smul_self hβ.1, neg_neg]
  refine ⟨nref_mem_familyGroup hβ, ?_, ?_, ?_⟩
  · rw [nref_conj_pinnedX_one h2 hβ.1, rootReflection_smul_self hβ.1]
  · rw [nref_conj_pinnedX_one h2 (IsRoot.neg hβ.1), hfix]
  · intro ε hε h1 _
    have hneg : iform β (-ε) = 0 := by rw [iform_neg_right, h1, neg_zero]
    constructor
    · rw [nref_conj_pinnedX_one h2 hε.1, rootReflection_smul_of_iform_eq_zero hβ.1 h1]
    · rw [nref_conj_pinnedX_one h2 (IsRoot.neg hε.1),
        rootReflection_smul_of_iform_eq_zero hβ.1 hneg]

private theorem rootReflection_smul_of_iform_eq_neg_one
    {τ : Tag} (hsym : ∀ i, τ.symmetrizer i i = 1)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (hif : iform β γ = -1) :
    rootReflection γ • β = β + γ ∧ rootReflection β • (β + γ) = γ ∧
      rootReflection γ • (-β) = -(β + γ) ∧ rootReflection β • (-(β + γ)) = -γ := by
  have hselfβ : iform β β = 2 := iform_self_eq_two_of_symm_one hsym hβ
  have hsγβ : rootReflection γ • β = β + γ := by
    rw [rootReflection_smul_eq_sub hsym hγ, iform_comm γ β, hif, neg_one_smul,
      sub_neg_eq_add]
  have hsβγ : rootReflection β • (β + γ) = γ := by
    rw [rootReflection_smul_eq_sub hsym hβ, iform_add_right, hselfβ, hif]
    rw [show (2 : ℤ) + -1 = 1 by norm_num, one_smul]
    abel
  exact ⟨hsγβ, hsβγ, by rw [smul_neg, hsγβ], by rw [smul_neg, hsβγ]⟩

private theorem nref_mul_nref_conj_pinnedX_pos_neg_one
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {β γ : Fin τ.rank → ℤ}
    (hsym : ∀ i, τ.symmetrizer i i = 1) (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hif : iform β γ = -1) :
    (nref τ L β * nref τ L γ) * pinnedX τ L β 1 * (nref τ L β * nref τ L γ)⁻¹ =
      pinnedX τ L γ 1 := by
  obtain ⟨hsγβ, hsβγ, -, -⟩ := rootReflection_smul_of_iform_eq_neg_one hsym hβ hγ hif
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  calc (nref τ L β * nref τ L γ) * pinnedX τ L β 1 * (nref τ L β * nref τ L γ)⁻¹
      = nref τ L β * (nref τ L γ * pinnedX τ L β 1 * (nref τ L γ)⁻¹) *
          (nref τ L β)⁻¹ := by group
    _ = nref τ L β * pinnedX τ L (rootReflection γ • β) 1 * (nref τ L β)⁻¹ := by
      rw [nref_conj_pinnedX_one h2 hβ]
    _ = pinnedX τ L (rootReflection β • (rootReflection γ • β)) 1 := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul hβ _)]
    _ = pinnedX τ L γ 1 := by rw [hsγβ, hsβγ]

private theorem nref_mul_nref_conj_pinnedX_neg_neg_one
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {β γ : Fin τ.rank → ℤ}
    (hsym : ∀ i, τ.symmetrizer i i = 1) (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hif : iform β γ = -1) :
    (nref τ L β * nref τ L γ) * pinnedX τ L (-β) 1 *
        (nref τ L β * nref τ L γ)⁻¹ = pinnedX τ L (-γ) 1 := by
  obtain ⟨-, -, hsγβ', hsβγ'⟩ := rootReflection_smul_of_iform_eq_neg_one hsym hβ hγ hif
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  calc (nref τ L β * nref τ L γ) * pinnedX τ L (-β) 1 *
        (nref τ L β * nref τ L γ)⁻¹
      = nref τ L β * (nref τ L γ * pinnedX τ L (-β) 1 * (nref τ L γ)⁻¹) *
          (nref τ L β)⁻¹ := by group
    _ = nref τ L β * pinnedX τ L (rootReflection γ • (-β)) 1 * (nref τ L β)⁻¹ := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.neg hβ)]
    _ = pinnedX τ L (rootReflection β • (rootReflection γ • (-β))) 1 := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul (IsRoot.neg hβ) _)]
    _ = pinnedX τ L (-γ) 1 := by rw [hsγβ', hsβγ']

private theorem nref_mul_nref_conj_pinnedX_fixing_neg_one_pos
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    {β γ ε : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hε : ε ∈ familyKernel a) (h1 : iform β ε = 0) (h2' : iform γ ε = 0) :
    (nref τ L β * nref τ L γ) * pinnedX τ L ε 1 * (nref τ L β * nref τ L γ)⁻¹ =
      pinnedX τ L ε 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  calc (nref τ L β * nref τ L γ) * pinnedX τ L ε 1 * (nref τ L β * nref τ L γ)⁻¹
      = nref τ L β * (nref τ L γ * pinnedX τ L ε 1 * (nref τ L γ)⁻¹) *
          (nref τ L β)⁻¹ := by group
    _ = nref τ L β * pinnedX τ L (rootReflection γ • ε) 1 * (nref τ L β)⁻¹ := by
      rw [nref_conj_pinnedX_one h2 hε.1]
    _ = pinnedX τ L (rootReflection β • (rootReflection γ • ε)) 1 := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul hε.1 _)]
    _ = pinnedX τ L ε 1 := by
      rw [rootReflection_smul_of_iform_eq_zero hγ h2',
        rootReflection_smul_of_iform_eq_zero hβ h1]

private theorem nref_mul_nref_conj_pinnedX_fixing_neg_one_neg
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    {β γ ε : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hε : ε ∈ familyKernel a) (h1 : iform β ε = 0) (h2' : iform γ ε = 0) :
    (nref τ L β * nref τ L γ) * pinnedX τ L (-ε) 1 *
        (nref τ L β * nref τ L γ)⁻¹ = pinnedX τ L (-ε) 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  calc (nref τ L β * nref τ L γ) * pinnedX τ L (-ε) 1 *
        (nref τ L β * nref τ L γ)⁻¹
      = nref τ L β * (nref τ L γ * pinnedX τ L (-ε) 1 * (nref τ L γ)⁻¹) *
          (nref τ L β)⁻¹ := by group
    _ = nref τ L β * pinnedX τ L (rootReflection γ • (-ε)) 1 * (nref τ L β)⁻¹ := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.neg hε.1)]
    _ = pinnedX τ L (rootReflection β • (rootReflection γ • (-ε))) 1 := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul (IsRoot.neg hε.1) _)]
    _ = pinnedX τ L (-ε) 1 := by
      rw [smul_neg, smul_neg,
        rootReflection_smul_of_iform_eq_zero hγ h2',
        rootReflection_smul_of_iform_eq_zero hβ h1]

private theorem nref_mul_nref_conj_pinnedX_fixing_neg_one
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) :
    ∀ ε, ε ∈ familyKernel a → iform β ε = 0 → iform γ ε = 0 →
      (nref τ L β * nref τ L γ) * pinnedX τ L ε 1 * (nref τ L β * nref τ L γ)⁻¹ =
          pinnedX τ L ε 1 ∧
        (nref τ L β * nref τ L γ) * pinnedX τ L (-ε) 1 * (nref τ L β * nref τ L γ)⁻¹ =
          pinnedX τ L (-ε) 1 :=
  fun ε hε h1 h2' =>
    ⟨nref_mul_nref_conj_pinnedX_fixing_neg_one_pos hβ hγ hε h1 h2',
      nref_mul_nref_conj_pinnedX_fixing_neg_one_neg hβ hγ hε h1 h2'⟩

private theorem conjData_minus_one
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ} {β γ : Fin τ.rank → ℤ}
    (hsym : ∀ i, τ.symmetrizer i i = 1) (hβ : β ∈ familyKernel a)
    (hγ : γ ∈ familyKernel a) (hif : iform β γ = -1) :
    FamilyKernelConjData a β γ (nref τ L β * nref τ L γ) :=
  ⟨mul_mem (nref_mem_familyGroup hβ) (nref_mem_familyGroup hγ),
    nref_mul_nref_conj_pinnedX_pos_neg_one hsym hβ.1 hγ.1 hif,
    nref_mul_nref_conj_pinnedX_neg_neg_one hsym hβ.1 hγ.1 hif,
    nref_mul_nref_conj_pinnedX_fixing_neg_one hβ.1 hγ.1⟩

private theorem rootReflection_smul_of_iform_eq_one_pos
    {τ : Tag} (hsym : ∀ i, τ.symmetrizer i i = 1)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (hif : iform β γ = 1) :
    rootReflection γ • β = β - γ ∧ rootReflection β • (β - γ) = -γ ∧
      rootReflection γ • (-γ) = γ := by
  have hselfβ : iform β β = 2 := iform_self_eq_two_of_symm_one hsym hβ
  have hselfγ : iform γ γ = 2 := iform_self_eq_two_of_symm_one hsym hγ
  have hsγβ : rootReflection γ • β = β - γ := by
    rw [rootReflection_smul_eq_sub hsym hγ, iform_comm γ β, hif, one_smul]
  have hsβ : rootReflection β • (β - γ) = -γ := by
    rw [rootReflection_smul_eq_sub hsym hβ, iform_sub_right, hselfβ, hif]
    rw [show (2 : ℤ) - 1 = 1 by norm_num, one_smul]
    abel
  exact ⟨hsγβ, hsβ, by rw [smul_neg, rootReflection_smul_self hγ, neg_neg]⟩

private theorem rootReflection_smul_of_iform_eq_one_neg
    {τ : Tag} (hsym : ∀ i, τ.symmetrizer i i = 1)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (hif : iform β γ = 1) :
    rootReflection γ • (-β) = γ - β ∧ rootReflection β • (γ - β) = γ ∧
      rootReflection γ • γ = -γ := by
  have hselfβ : iform β β = 2 := iform_self_eq_two_of_symm_one hsym hβ
  have hsγβ : rootReflection γ • β = β - γ := by
    rw [rootReflection_smul_eq_sub hsym hγ, iform_comm γ β, hif, one_smul]
  have hsβ' : rootReflection β • (γ - β) = γ := by
    rw [rootReflection_smul_eq_sub hsym hβ, iform_sub_right, hif, hselfβ]
    rw [show (1 : ℤ) - 2 = -1 by norm_num, neg_one_smul]
    abel
  refine ⟨?_, hsβ', rootReflection_smul_self hγ⟩
  rw [smul_neg, hsγβ]
  abel

private theorem nref3_conj_pinnedX_pos_one
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {β γ : Fin τ.rank → ℤ}
    (hsym : ∀ i, τ.symmetrizer i i = 1) (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hif : iform β γ = 1) :
    (nref τ L γ * nref τ L β * nref τ L γ) * pinnedX τ L β 1 *
        (nref τ L γ * nref τ L β * nref τ L γ)⁻¹ = pinnedX τ L γ 1 := by
  obtain ⟨hsγβ, hsβ, hsγγ⟩ := rootReflection_smul_of_iform_eq_one_pos hsym hβ hγ hif
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  calc (nref τ L γ * nref τ L β * nref τ L γ) * pinnedX τ L β 1 *
        (nref τ L γ * nref τ L β * nref τ L γ)⁻¹
      = nref τ L γ * (nref τ L β * (nref τ L γ * pinnedX τ L β 1 *
          (nref τ L γ)⁻¹) * (nref τ L β)⁻¹) * (nref τ L γ)⁻¹ := by group
    _ = nref τ L γ * (nref τ L β * pinnedX τ L (rootReflection γ • β) 1 *
          (nref τ L β)⁻¹) * (nref τ L γ)⁻¹ := by rw [nref_conj_pinnedX_one h2 hβ]
    _ = nref τ L γ * pinnedX τ L (rootReflection β • (rootReflection γ • β)) 1 *
          (nref τ L γ)⁻¹ := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul hβ _)]
    _ = pinnedX τ L (rootReflection γ • (rootReflection β •
          (rootReflection γ • β))) 1 := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul (IsRoot.smul hβ _) _)]
    _ = pinnedX τ L γ 1 := by rw [hsγβ, hsβ, hsγγ]

private theorem nref3_conj_pinnedX_neg_one
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {β γ : Fin τ.rank → ℤ}
    (hsym : ∀ i, τ.symmetrizer i i = 1) (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hif : iform β γ = 1) :
    (nref τ L γ * nref τ L β * nref τ L γ) * pinnedX τ L (-β) 1 *
        (nref τ L γ * nref τ L β * nref τ L γ)⁻¹ = pinnedX τ L (-γ) 1 := by
  obtain ⟨hsγβ', hsβ', hsγγ'⟩ := rootReflection_smul_of_iform_eq_one_neg hsym hβ hγ hif
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  calc (nref τ L γ * nref τ L β * nref τ L γ) * pinnedX τ L (-β) 1 *
        (nref τ L γ * nref τ L β * nref τ L γ)⁻¹
      = nref τ L γ * (nref τ L β * (nref τ L γ * pinnedX τ L (-β) 1 *
          (nref τ L γ)⁻¹) * (nref τ L β)⁻¹) * (nref τ L γ)⁻¹ := by group
    _ = nref τ L γ * (nref τ L β * pinnedX τ L (rootReflection γ • (-β)) 1 *
          (nref τ L β)⁻¹) * (nref τ L γ)⁻¹ := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.neg hβ)]
    _ = nref τ L γ * pinnedX τ L (rootReflection β • (rootReflection γ • (-β))) 1 *
          (nref τ L γ)⁻¹ := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul (IsRoot.neg hβ) _)]
    _ = pinnedX τ L (rootReflection γ • (rootReflection β •
          (rootReflection γ • (-β)))) 1 := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul (IsRoot.smul (IsRoot.neg hβ) _) _)]
    _ = pinnedX τ L (-γ) 1 := by rw [hsγβ', hsβ', hsγγ']

private theorem nref3_conj_pinnedX_fixing_one_pos
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    {β γ ε : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hε : ε ∈ familyKernel a) (h1 : iform β ε = 0) (h2' : iform γ ε = 0) :
    (nref τ L γ * nref τ L β * nref τ L γ) * pinnedX τ L ε 1 *
        (nref τ L γ * nref τ L β * nref τ L γ)⁻¹ = pinnedX τ L ε 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have e1 : rootReflection γ • ε = ε := rootReflection_smul_of_iform_eq_zero hγ h2'
  have e2 : rootReflection β • ε = ε := rootReflection_smul_of_iform_eq_zero hβ h1
  calc (nref τ L γ * nref τ L β * nref τ L γ) * pinnedX τ L ε 1 *
        (nref τ L γ * nref τ L β * nref τ L γ)⁻¹
      = nref τ L γ * (nref τ L β * (nref τ L γ * pinnedX τ L ε 1 *
          (nref τ L γ)⁻¹) * (nref τ L β)⁻¹) * (nref τ L γ)⁻¹ := by group
    _ = nref τ L γ * (nref τ L β * pinnedX τ L (rootReflection γ • ε) 1 *
          (nref τ L β)⁻¹) * (nref τ L γ)⁻¹ := by rw [nref_conj_pinnedX_one h2 hε.1]
    _ = nref τ L γ * pinnedX τ L (rootReflection β • (rootReflection γ • ε)) 1 *
          (nref τ L γ)⁻¹ := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul hε.1 _)]
    _ = pinnedX τ L (rootReflection γ • (rootReflection β •
          (rootReflection γ • ε))) 1 := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul (IsRoot.smul hε.1 _) _)]
    _ = pinnedX τ L ε 1 := by rw [e1, e2, e1]

private theorem nref3_conj_pinnedX_fixing_one_neg
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    {β γ ε : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hε : ε ∈ familyKernel a) (h1 : iform β ε = 0) (h2' : iform γ ε = 0) :
    (nref τ L γ * nref τ L β * nref τ L γ) * pinnedX τ L (-ε) 1 *
        (nref τ L γ * nref τ L β * nref τ L γ)⁻¹ = pinnedX τ L (-ε) 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have e1 : rootReflection γ • ε = ε := rootReflection_smul_of_iform_eq_zero hγ h2'
  have e2 : rootReflection β • ε = ε := rootReflection_smul_of_iform_eq_zero hβ h1
  have e1' : rootReflection γ • (-ε) = -ε := by rw [smul_neg, e1]
  have e2' : rootReflection β • (-ε) = -ε := by rw [smul_neg, e2]
  calc (nref τ L γ * nref τ L β * nref τ L γ) * pinnedX τ L (-ε) 1 *
        (nref τ L γ * nref τ L β * nref τ L γ)⁻¹
      = nref τ L γ * (nref τ L β * (nref τ L γ * pinnedX τ L (-ε) 1 *
          (nref τ L γ)⁻¹) * (nref τ L β)⁻¹) * (nref τ L γ)⁻¹ := by group
    _ = nref τ L γ * (nref τ L β * pinnedX τ L (rootReflection γ • (-ε)) 1 *
          (nref τ L β)⁻¹) * (nref τ L γ)⁻¹ := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.neg hε.1)]
    _ = nref τ L γ * pinnedX τ L (rootReflection β • (rootReflection γ • (-ε))) 1 *
          (nref τ L γ)⁻¹ := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul (IsRoot.neg hε.1) _)]
    _ = pinnedX τ L (rootReflection γ • (rootReflection β •
          (rootReflection γ • (-ε)))) 1 := by
      rw [nref_conj_pinnedX_one h2 (IsRoot.smul (IsRoot.smul (IsRoot.neg hε.1) _) _)]
    _ = pinnedX τ L (-ε) 1 := by rw [e1', e2', e1']

private theorem nref3_conj_pinnedX_fixing_one
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) :
    ∀ ε, ε ∈ familyKernel a → iform β ε = 0 → iform γ ε = 0 →
      (nref τ L γ * nref τ L β * nref τ L γ) * pinnedX τ L ε 1 *
          (nref τ L γ * nref τ L β * nref τ L γ)⁻¹ = pinnedX τ L ε 1 ∧
        (nref τ L γ * nref τ L β * nref τ L γ) * pinnedX τ L (-ε) 1 *
          (nref τ L γ * nref τ L β * nref τ L γ)⁻¹ = pinnedX τ L (-ε) 1 :=
  fun ε hε h1 h2' =>
    ⟨nref3_conj_pinnedX_fixing_one_pos hβ hγ hε h1 h2',
      nref3_conj_pinnedX_fixing_one_neg hβ hγ hε h1 h2'⟩

private theorem conjData_plus_one
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ} {β γ : Fin τ.rank → ℤ}
    (hsym : ∀ i, τ.symmetrizer i i = 1) (hβ : β ∈ familyKernel a)
    (hγ : γ ∈ familyKernel a) (hif : iform β γ = 1) :
    FamilyKernelConjData a β γ (nref τ L γ * nref τ L β * nref τ L γ) :=
  ⟨mul_mem (mul_mem (nref_mem_familyGroup hγ) (nref_mem_familyGroup hβ))
      (nref_mem_familyGroup hγ),
    nref3_conj_pinnedX_pos_one hsym hβ.1 hγ.1 hif,
    nref3_conj_pinnedX_neg_one hsym hβ.1 hγ.1 hif,
    nref3_conj_pinnedX_fixing_one hβ.1 hγ.1⟩

private theorem local_conj
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hsym : ∀ i, τ.symmetrizer i i = 1) {β γ : Fin τ.rank → ℤ}
    (hβ : β ∈ familyKernel a) (hγ : γ ∈ familyKernel a) (hne : iform β γ ≠ 0) :
    ∃ n, FamilyKernelConjData a β γ n := by
  by_cases h1 : γ = β
  · subst h1
    exact ⟨1, conjData_self⟩
  by_cases h2 : γ = -β
  · subst h2
    exact ⟨nref τ L β, conjData_neg hβ⟩
  have hb := abs_iform_le_two_of_symm_one hsym hβ.1 hγ.1
  rw [abs_le] at hb
  have hnot2 : iform β γ ≠ 2 := fun h =>
    (eq_or_neg_of_iform_eq_two_of_symm_one hsym hβ.1 hγ.1 (Or.inl h)).elim h1 h2
  have hnotm2 : iform β γ ≠ -2 := fun h =>
    (eq_or_neg_of_iform_eq_two_of_symm_one hsym hβ.1 hγ.1 (Or.inr h)).elim h1 h2
  have hval : iform β γ = -1 ∨ iform β γ = 1 := by omega
  rcases hval with hv | hv
  · exact ⟨nref τ L β * nref τ L γ, conjData_minus_one hsym hβ hγ hv⟩
  · exact ⟨nref τ L γ * nref τ L β * nref τ L γ, conjData_plus_one hsym hβ hγ hv⟩

private theorem famKernel_conj_mul_conj {G : Type*} [Group G] {m n x y z : G}
    (hn : n * x * n⁻¹ = y) (hm : m * y * m⁻¹ = z) : (m * n) * x * (m * n)⁻¹ = z := by
  rw [show (m * n) * x * (m * n)⁻¹ = m * (n * x * n⁻¹) * m⁻¹ by group, hn, hm]

private theorem exists_conj_of_famConn
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hsym : ∀ i, τ.symmetrizer i i = 1) {β γ : Fin τ.rank → ℤ}
    (hconn : famConn a β γ) :
    ∃ n ∈ familyGroup (K := L) a,
      n * pinnedX τ L β 1 * n⁻¹ = pinnedX τ L γ 1 ∧
      n * pinnedX τ L (-β) 1 * n⁻¹ = pinnedX τ L (-γ) 1 ∧
      ∀ ε (_ : ε ∈ familyKernel a), ¬ famConn a β ε →
        n * pinnedX τ L ε 1 * n⁻¹ = pinnedX τ L ε 1 ∧
        n * pinnedX τ L (-ε) 1 * n⁻¹ = pinnedX τ L (-ε) 1 := by
  induction hconn with
  | refl =>
    exact ⟨1, one_mem _, by simp, by simp, fun ε _ _ => ⟨by simp, by simp⟩⟩
  | @tail δ γ' h1 hstep ih =>
    obtain ⟨hδ, hγ', hne⟩ := hstep
    obtain ⟨n, hnM, hnβ, hnβ', hnfix⟩ := ih
    obtain ⟨m, hmM, hmδ, hmδ', hmfix⟩ := local_conj hsym hδ hγ' hne
    refine ⟨m * n, mul_mem hmM hnM, famKernel_conj_mul_conj hnβ hmδ,
      famKernel_conj_mul_conj hnβ' hmδ', ?_⟩
    intro ε hε hnot
    have h0δ : iform δ ε = 0 := by
      by_contra h0; exact hnot (famConn_step h1 hδ hε h0)
    have h0γ : iform γ' ε = 0 := by
      by_contra h0; exact hnot (famConn_step (famConn_step h1 hδ hγ' hne) hγ' hε h0)
    obtain ⟨hnε, hnε'⟩ := hnfix ε hε hnot
    obtain ⟨hmε, hmε'⟩ := hmfix ε hε h0δ h0γ
    exact ⟨famKernel_conj_mul_conj hnε hmε, famKernel_conj_mul_conj hnε' hmε'⟩

private theorem exists_iterate_fixed_of_familyKernel
    {τ : Tag} {L : Type} [Field L] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρΨ : Set.MapsTo ρ (familyKernel a) (familyKernel a))
    {β : Fin τ.rank → ℤ} (hβ : β ∈ familyKernel a) :
    ∃ N, 0 < N ∧ ρ^[N] β = β := by
  let s := familyKernel a
  let f : {γ // γ ∈ s} → {γ // γ ∈ s} := fun x => ⟨ρ x.1, hρΨ x.2⟩
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (ρ.injective (congrArg Subtype.val hxy))
  have hval : ∀ (k : ℕ) (x : {γ // γ ∈ s}), ((f^[k]) x).1 = (ρ^[k]) x.1 := by
    intro k x
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change ρ ↑(f^[k] x) = ρ ((⇑ρ)^[k] ↑x)
      rw [ih]
  haveI : Fintype {γ // γ ∈ s} := (familyKernel_finite a).fintype
  have hid := Function.injective_iff_iterate_factorial_card_eq_id.1 hf
  refine ⟨(Fintype.card {γ // γ ∈ s}).factorial, Nat.factorial_pos _, ?_⟩
  have hx : (f^[(Fintype.card {γ // γ ∈ s}).factorial]) ⟨β, hβ⟩ = ⟨β, hβ⟩ := by
    rw [hid]
    rfl
  have hxval := congrArg Subtype.val hx
  rw [hval] at hxval
  simpa using hxval

private theorem list_prod_sq_eq_one_of_pairwise_commute {G : Type*} [Monoid G] {l : List G}
    (hpair : l.Pairwise Commute) (hinv : ∀ x ∈ l, x ^ 2 = 1) : l.prod ^ 2 = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hpair
    obtain ⟨hcomm, hpair'⟩ := hpair
    have hca : Commute a l.prod := Commute.list_prod_right l a hcomm
    have ha : a ^ 2 = 1 := hinv a (by simp)
    have hl : l.prod ^ 2 = 1 := ih hpair' (fun x hx => hinv x (by simp [hx]))
    rw [List.prod_cons]
    calc (a * l.prod) ^ 2 = a * (l.prod * a) * l.prod := by
          rw [pow_two]; simp only [mul_assoc]
      _ = a * (a * l.prod) * l.prod := by rw [hca.eq.symm]
      _ = a ^ 2 * l.prod ^ 2 := by rw [pow_two, pow_two]; simp only [mul_assoc]
      _ = 1 := by rw [ha, hl, one_mul]

private theorem list_prod_pow_eq_one_of_pairwise_commute {G : Type*} [Monoid G] {l : List G} {k : ℕ}
    (hpair : l.Pairwise Commute) (hinv : ∀ x ∈ l, x ^ k = 1) : l.prod ^ k = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hpair
    obtain ⟨hcomm, hpair'⟩ := hpair
    have hca : Commute a l.prod := Commute.list_prod_right l a hcomm
    have ha : a ^ k = 1 := hinv a (by simp)
    have hl : l.prod ^ k = 1 := ih hpair' (fun x hx => hinv x (by simp [hx]))
    rw [List.prod_cons, hca.mul_pow, ha, hl, one_mul]

private theorem prod_range_mul_prod_range {G : Type*} [Group G] (f g : ℕ → G) (m : ℕ)
    (hcomm : ∀ i j, i < m → j < m → i ≠ j → Commute (f i) (g j)) :
    (List.map f (List.range m)).prod * (List.map g (List.range m)).prod =
      (List.map (fun i => f i * g i) (List.range m)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcm : Commute (f m) (List.map g (List.range m)).prod := by
      refine Commute.list_prod_right _ _ ?_
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      rw [List.mem_range] at hj
      exact hcomm m j (by omega) (by omega) (by omega)
    have ih' := ih (fun i j hi hj hij => hcomm i j (by omega) (by omega) hij)
    simp only [List.prod_range_succ]
    calc (List.map f (List.range m)).prod * f m *
          ((List.map g (List.range m)).prod * g m)
        = (List.map f (List.range m)).prod * (f m *
            (List.map g (List.range m)).prod) * g m := by group
      _ = (List.map f (List.range m)).prod * ((List.map g (List.range m)).prod *
            f m) * g m := by rw [hcm.eq]
      _ = ((List.map f (List.range m)).prod * (List.map g (List.range m)).prod) *
            (f m * g m) := by group
      _ = (List.map (fun i => f i * g i) (List.range m)).prod * (f m * g m) := by
            rw [ih']

private theorem prod_range_shift_of_pairwise_commute {G : Type*} [Monoid G] (f : ℕ → G) (n : ℕ)
    (hcomm : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Commute (f i) (f j)) :
    (List.map f (List.range (n + 1))).prod =
      (List.map (fun i => f (i + 1)) (List.range n)).prod * f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun i j hi hj hij => hcomm i j (by omega) (by omega) hij)
    have h0 : Commute (f 0) (f (n + 1)) :=
      hcomm 0 (n + 1) (by omega) (by omega) (by omega)
    rw [List.prod_range_succ]
    conv_rhs => rw [List.prod_range_succ]
    rw [ih', mul_assoc, h0.eq, ← mul_assoc]

private theorem step_eq_frobTwistGL
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    (D : LangDatum τ L) {f : ℕ} {P : ModGL τ L}
    (hΦ : ∀ g, D.Φ g = P * Units.map (entrywiseHom (iterateFrobenius L 2 f)) g * P⁻¹) :
    D.step = frobTwistGL τ L 2 f (D.n * P) := by
  apply MonoidHom.ext
  intro g
  rw [frobTwistGL_apply]
  change D.n * D.Φ g * D.n⁻¹ =
    (D.n * P) * Units.map (entrywiseHom (iterateFrobenius L 2 f)) g * (D.n * P)⁻¹
  rw [hΦ g]
  group

private theorem famKernel_step_mem_torusGroup
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ} {D : LangDatum τ L}
    {Q : ModGL τ L} (hstep : D.step = frobTwistGL τ L 2 f Q)
    (hQ : Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L))) :
    (torusGroup τ L).map D.step ≤ torusGroup τ L := by
  haveI : PerfectRing L 2 := IsAlgClosed.perfectRing L 2
  rw [hstep, map_frobTwistGL_torusGroup 2 f hQ]

private theorem famKernel_step_mem_rootSpan
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hρΨ : Set.MapsTo ρ (familyKernel a) (familyKernel a)) :
    (rootSpan τ L (familyKernel a)).map D.step ≤ rootSpan τ L (familyKernel a) := by
  have hmap : (rootSpan τ L (familyKernel a)).map D.step =
      rootSpan τ L (ρ '' familyKernel a) := by
    simp only [rootSpan, Subgroup.map_iSup]
    rw [iSup_image]
    exact iSup_congr fun γ => iSup_congr fun hγ => hρ.map_rootSubgroup γ hγ.1
  rw [hmap]
  exact rootSpan_mono hρΨ.image_subset

private theorem n_mul_P_mem_normalizer
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    {P : ModGL τ L}
    (hP : P = 1 ∨ ∃ (t : TwistTag) (h : t.tag = τ), P = diagramAt τ L t h) :
    D.n * P ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) := by
  obtain ⟨w, hn⟩ := D.n_weyl
  refine mul_mem ?_ ?_
  · rw [hn]
    exact canonicalRep_mem_normalizer (R := L) w
  · rcases hP with rfl | ⟨t, ht, rfl⟩
    · exact Subgroup.one_mem _
    · subst ht
      exact diagramMap_mem_normalizer t

private theorem step_mem_familyGroup
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L) {f : ℕ} (hq : D.q = 2 ^ f)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hρΨ : Set.MapsTo ρ (familyKernel a) (familyKernel a))
    {g : ModGL τ L} (hg : g ∈ familyGroup (K := L) a) :
    D.step g ∈ familyGroup (K := L) a := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  have hFr_eq : Fr = iterateFrobenius L 2 f := by
    ext c
    rw [hFr, hq, iterateFrobenius_def]
  have hΦ' : ∀ g, D.Φ g =
      P * Units.map (entrywiseHom (iterateFrobenius L 2 f)) g * P⁻¹ := by
    intro g
    rw [hΦ g, hFr_eq]
  have hstep : D.step = frobTwistGL τ L 2 f (D.n * P) := step_eq_frobTwistGL D hΦ'
  have htorus := famKernel_step_mem_torusGroup hstep (n_mul_P_mem_normalizer D hP)
  have hrootspan := famKernel_step_mem_rootSpan hρ hρΨ
  have hle : (familyGroup (K := L) a).map D.step ≤ familyGroup (K := L) a := by
    rw [familyGroup, Subgroup.map_sup]
    exact sup_le (htorus.trans le_sup_left) (hrootspan.trans le_sup_right)
  exact hle (Subgroup.mem_map_of_mem _ hg)

private theorem centralizer_empty_eq_top {G : Type*} [Group G] :
    Subgroup.centralizer (∅ : Set G) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  simp at hy

private theorem famKernel_frobTwistGL_mem_familyGroup_inf_centralizer
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {f : ℕ}
    {D : LangDatum τ L} {Q : ModGL τ L} {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hstepEq : D.step = frobTwistGL τ L 2 f Q)
    (hstep : ∀ g ∈ familyGroup (K := L) a, D.step g ∈ familyGroup (K := L) a) :
    ∀ g ∈ familyGroup (K := L) a ⊓ Subgroup.centralizer (∅ : Set (ModGL τ L)),
      frobTwistGL τ L 2 f Q g ∈
        familyGroup (K := L) a ⊓ Subgroup.centralizer (∅ : Set (ModGL τ L)) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg ⊢
  refine ⟨?_, ?_⟩
  · rw [← hstepEq]
    exact hstep g hg.1
  · rw [centralizer_empty_eq_top]
    exact Subgroup.mem_top _

private theorem exists_lang_solution_of_familyGroup
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    {f : ℕ} (hf : 1 ≤ f) (hq : D.q = 2 ^ f) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hstep : ∀ g ∈ familyGroup (K := L) a, D.step g ∈ familyGroup (K := L) a)
    {n₀ : ModGL τ L} (hn₀ : n₀ ∈ familyGroup (K := L) a) :
    ∃ ζ ∈ familyGroup (K := L) a, ζ⁻¹ * D.step ζ = n₀ := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  have hFr_eq : Fr = iterateFrobenius L 2 f := by
    ext c
    rw [hFr, hq, iterateFrobenius_def]
  have hΦ' : ∀ g, D.Φ g =
      P * Units.map (entrywiseHom (iterateFrobenius L 2 f)) g * P⁻¹ := by
    intro g
    rw [hΦ g, hFr_eq]
  have hstepEq : D.step = frobTwistGL τ L 2 f (D.n * P) := step_eq_frobTwistGL D hΦ'
  have hS := famKernel_frobTwistGL_mem_familyGroup_inf_centralizer hstepEq hstep
  have hcl : closedIdentityComponent (familyGroup (K := L) a ⊓
      Subgroup.centralizer (∅ : Set (ModGL τ L))) = familyGroup (K := L) a := by
    rw [centralizer_empty_eq_top, inf_top_eq, closedIdentityComponent_familyGroup]
  obtain ⟨ζ, hζ, hζeq⟩ :=
    exists_inv_mul_frobTwistGL_familyGroup_inf_centralizer (p := 2) a
      (∅ : Set (ModGL τ L)) hf (D.n * P) hS n₀ (by rw [hcl]; exact hn₀)
  exact ⟨ζ, by rwa [hcl] at hζ, by rwa [← hstepEq] at hζeq⟩

private theorem mapsTo_familyKernel_of_frobRootMap
    {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (D : LangDatum τ L) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap D ρ) (ha : ∀ i, rootDiagUnit τ (a i) ∈ D.torus) :
    Set.MapsTo ρ (familyKernel a) (familyKernel a) := by
  intro γ hγ
  refine ⟨(hρ.isRoot_iff γ).2 hγ.1, fun i => ?_⟩
  rw [hρ.rootChar_eq (a i) (ha i) γ hγ.1, hγ.2 i, one_pow]

private theorem iform_iterate_eq
    {τ : Tag} {L : Type} [Field L] (D : LangDatum τ L)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) (k : ℕ)
    (x y : Fin τ.rank → ℤ) : iform (ρ^[k] x) (ρ^[k] y) = iform x y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hρ.iform_eq, ih]

private theorem conj_prod_eq_of_forall {G : Type*} [Group G] {n : G} {l : List G}
    (h : ∀ x ∈ l, n * x * n⁻¹ = x) : n * l.prod * n⁻¹ = l.prod := by
  change (MulAut.conj n).toMonoidHom l.prod = l.prod
  rw [map_list_prod]
  congr 1
  rw [List.map_congr_left (g := id) (fun x hx => by
    simpa [MulAut.conj_apply] using h x hx), List.map_id]

private noncomputable def famKernelOrbitX
    {τ : Tag} (L : Type) [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (β : Fin τ.rank → ℤ) (i : ℕ) : ModGL τ L :=
  pinnedX τ L (ρ^[i] β) 1

private noncomputable def famKernelOrbitNegX
    {τ : Tag} (L : Type) [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (β : Fin τ.rank → ℤ) (i : ℕ) : ModGL τ L :=
  pinnedX τ L (-(ρ^[i] β)) 1

private noncomputable def famKernelOrbitEvenH
    {τ : Tag} (L : Type) [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (β : Fin τ.rank → ℤ) (i : ℕ) : ModGL τ L :=
  evenH τ L (ρ^[i] β)

private noncomputable def famKernelOrbitU
    {τ : Tag} (L : Type) [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (β : Fin τ.rank → ℤ) (m : ℕ) : ModGL τ L :=
  (List.map (famKernelOrbitX L ρ β) (List.range m)).prod

private noncomputable def famKernelOrbitV
    {τ : Tag} (L : Type) [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (β : Fin τ.rank → ℤ) (m : ℕ) : ModGL τ L :=
  (List.map (famKernelOrbitNegX L ρ β) (List.range m)).prod

private noncomputable def famKernelOrbitH
    {τ : Tag} (L : Type) [Field L] (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (β : Fin τ.rank → ℤ) (m : ℕ) : ModGL τ L :=
  (List.map (famKernelOrbitEvenH L ρ β) (List.range m)).prod

private theorem famKernel_orbit_min {τ : Tag} {L : Type}
    [Field L] {ι : Type} {a : ι → Fin τ.rank → Lˣ} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρΨ : Set.MapsTo ρ (familyKernel a) (familyKernel a))
    {β : Fin τ.rank → ℤ} (hβ : β ∈ familyKernel a) :
    ∃ m, 0 < m ∧ famConn a β (ρ^[m] β) ∧
      ∀ k, 0 < k → k < m → ¬ famConn a β (ρ^[k] β) := by
  classical
  obtain ⟨N, hNpos, hNfix⟩ := exists_iterate_fixed_of_familyKernel ρ hρΨ hβ
  let P : ℕ → Prop := fun k => 0 < k ∧ famConn a β (ρ^[k] β)
  have hex : ∃ k, P k := ⟨N, hNpos, by rw [hNfix]; exact famConn_refl⟩
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun k hk0 hkm hc => absurd (Nat.find_min' hex ⟨hk0, hc⟩) (by omega)⟩

private theorem famKernel_orbit_orthogonal
    {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (D : LangDatum τ L) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap D ρ) (hρΨ : Set.MapsTo ρ (familyKernel a) (familyKernel a))
    {β : Fin τ.rank → ℤ} (hβ : β ∈ familyKernel a) {m : ℕ}
    (hmin : ∀ k, 0 < k → k < m → ¬ famConn a β (ρ^[k] β)) :
    (∀ i, ρ^[i] β ∈ familyKernel a) ∧
      ∀ i j, i < j → j < m → iform (ρ^[i] β) (ρ^[j] β) = 0 := by
  have hb : ∀ i, ρ^[i] β ∈ familyKernel a := fun i => Set.MapsTo.iterate hρΨ i hβ
  refine ⟨hb, ?_⟩
  intro i j hij hjm
  have hk0 : 0 < j - i := Nat.sub_pos_of_lt hij
  have hklt : j - i < m := by omega
  have hnot := hmin (j - i) hk0 hklt
  have hji : j = i + (j - i) := by omega
  rw [hji, Function.iterate_add_apply, iform_iterate_eq D hρ i]
  by_contra hne
  exact hnot (famConn_step famConn_refl hβ (hb (j - i)) hne)

private theorem famKernel_orbit_commute_X
    {τ : Tag} {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ}
    (hsym : ∀ i, τ.symmetrizer i i = 1) (hroot : ∀ i, IsRoot τ (ρ^[i] β))
    (hortho : ∀ i j, i < j → j < m → iform (ρ^[i] β) (ρ^[j] β) = 0) :
    ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitX L ρ β i) (famKernelOrbitX L ρ β j) := by
  intro i j hi hj hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact TableBExcTwo.commute_pinnedX_of_iform_eq_zero L hsym (hroot i) (hroot j)
      (hortho i j h hj) 1 1
  · exact (TableBExcTwo.commute_pinnedX_of_iform_eq_zero L hsym (hroot j) (hroot i)
      (hortho j i h hi) 1 1).symm

private theorem famKernel_orbit_commute_X_neg
    {τ : Tag} {L : Type} [Field L] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} {m : ℕ} (hsym : ∀ i, τ.symmetrizer i i = 1)
    (hroot : ∀ i, IsRoot τ (ρ^[i] β))
    (hortho : ∀ i j, i < j → j < m → iform (ρ^[i] β) (ρ^[j] β) = 0) :
    ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitX L ρ β i) (famKernelOrbitNegX L ρ β j) := by
  intro i j hi hj hij
  have h0 : iform (ρ^[i] β) (-(ρ^[j] β)) = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [iform_neg_right, hortho i j h hj, neg_zero]
    · rw [iform_neg_right, iform_comm, hortho j i h hi, neg_zero]
  exact TableBExcTwo.commute_pinnedX_of_iform_eq_zero L hsym (hroot i)
    (IsRoot.neg (hroot j)) h0 1 1

private theorem famKernel_orbit_commute_negX
    {τ : Tag} {L : Type} [Field L] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} {m : ℕ} (hsym : ∀ i, τ.symmetrizer i i = 1)
    (hroot : ∀ i, IsRoot τ (ρ^[i] β))
    (hortho : ∀ i j, i < j → j < m → iform (ρ^[i] β) (ρ^[j] β) = 0) :
    ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitNegX L ρ β i) (famKernelOrbitNegX L ρ β j) := by
  intro i j hi hj hij
  have h0 : iform (-(ρ^[i] β)) (-(ρ^[j] β)) = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [iform_neg_left, iform_neg_right, hortho i j h hj, neg_zero, neg_zero]
    · rw [iform_neg_left, iform_neg_right, iform_comm, hortho j i h hi, neg_zero, neg_zero]
  exact TableBExcTwo.commute_pinnedX_of_iform_eq_zero L hsym (IsRoot.neg (hroot i))
    (IsRoot.neg (hroot j)) h0 1 1

private theorem famKernel_orbit_commute_evenH
    {τ : Tag} {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ}
    (hXX : ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitX L ρ β i) (famKernelOrbitX L ρ β j))
    (hXn : ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitX L ρ β i) (famKernelOrbitNegX L ρ β j))
    (hnn : ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitNegX L ρ β i) (famKernelOrbitNegX L ρ β j)) :
    ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitEvenH L ρ β i) (famKernelOrbitEvenH L ρ β j) := by
  intro i j hi hj hij
  have h1 := hXX i j hi hj hij
  have h2 := hXn i j hi hj hij
  have h3 : Commute (famKernelOrbitNegX L ρ β i) (famKernelOrbitX L ρ β j) :=
    (hXn j i hj hi (Ne.symm hij)).symm
  have h4 := hnn i j hi hj hij
  change Commute (pinnedX τ L (ρ^[i] β) 1 * pinnedX τ L (-(ρ^[i] β)) 1)
    (pinnedX τ L (ρ^[j] β) 1 * pinnedX τ L (-(ρ^[j] β)) 1)
  exact (h1.mul_right h2).mul_left (h3.mul_right h4)

private theorem famKernel_pairwise_commute {G : Type*} [Monoid G] {f : ℕ → G} {m : ℕ}
    (h : ∀ i j, i < m → j < m → i ≠ j → Commute (f i) (f j)) :
    (List.map f (List.range m)).Pairwise Commute := by
  rw [List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < m := by simpa using hi
  have hj' : j < m := by simpa using hj
  simp only [List.getElem_range]
  exact h i j hi' hj' (by omega)

private theorem famKernel_orbit_prod_mem_sq
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {β : Fin τ.rank → ℤ} {m : ℕ} (hb : ∀ i, ρ^[i] β ∈ familyKernel a)
    (hpairF : (List.map (famKernelOrbitX L ρ β) (List.range m)).Pairwise Commute)
    (hpairG : (List.map (famKernelOrbitNegX L ρ β) (List.range m)).Pairwise Commute) :
    famKernelOrbitU L ρ β m ∈ familyGroup (K := L) a ∧
      famKernelOrbitV L ρ β m ∈ familyGroup (K := L) a ∧
      famKernelOrbitU L ρ β m ^ 2 = 1 ∧ famKernelOrbitV L ρ β m ^ 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine list_prod_mem fun x hx => ?_
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.mem_sup_right (pinnedX_mem_rootSpan (τ := τ) (K := L) (hb i) (1 : L))
  · refine list_prod_mem fun x hx => ?_
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.mem_sup_right (pinnedX_mem_rootSpan (τ := τ) (K := L)
      (familyKernel_neg (hb i)) (1 : L))
  · refine list_prod_sq_eq_one_of_pairwise_commute hpairF ?_
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_one_pow_two _
  · refine list_prod_sq_eq_one_of_pairwise_commute hpairG ?_
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_one_pow_two _

private theorem famKernel_orbit_uv_eq_prod
    {τ : Tag} {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ}
    (hcomm : ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitX L ρ β i) (famKernelOrbitNegX L ρ β j)) :
    famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m = famKernelOrbitH L ρ β m := by
  rw [show famKernelOrbitU L ρ β m =
      (List.map (famKernelOrbitX L ρ β) (List.range m)).prod from rfl,
    show famKernelOrbitV L ρ β m =
      (List.map (famKernelOrbitNegX L ρ β) (List.range m)).prod from rfl,
    prod_range_mul_prod_range (famKernelOrbitX L ρ β) (famKernelOrbitNegX L ρ β) m hcomm]
  rfl

private theorem famKernel_orbit_prod_cube
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ}
    (hpairH : (List.map (famKernelOrbitEvenH L ρ β) (List.range m)).Pairwise Commute)
    (hroot : ∀ i, IsRoot τ (ρ^[i] β))
    (huv : famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m = famKernelOrbitH L ρ β m) :
    (famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m) ^ 3 = 1 := by
  rw [huv]
  refine list_prod_pow_eq_one_of_pairwise_commute hpairH ?_
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
  rw [← orderOf_evenH (τ := τ) (K := L) (hroot i)]
  exact pow_orderOf_eq_one _

private theorem famKernel_orbit_H_split
    {τ : Tag} {L : Type} [Field L] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} {m : ℕ} (hm : 0 < m) :
    famKernelOrbitH L ρ β m = famKernelOrbitEvenH L ρ β 0 *
      (List.map (fun i => famKernelOrbitEvenH L ρ β (i + 1)) (List.range (m - 1))).prod := by
  rw [show famKernelOrbitH L ρ β m =
    (List.map (famKernelOrbitEvenH L ρ β) (List.range m)).prod from rfl]
  conv_lhs => rw [show m = (m - 1) + 1 by omega, List.range_succ_eq_map,
    List.map_cons, List.prod_cons]
  rw [List.map_map]
  rfl

private theorem nref_conj_evenH_of_pos
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} {m : ℕ} (hβ : β ∈ familyKernel a)
    (hroot : ∀ i, IsRoot τ (ρ^[i] β))
    (hortho : ∀ i j, i < j → j < m → iform (ρ^[i] β) (ρ^[j] β) = 0) :
    ∀ j, 1 ≤ j → j < m → nref τ L β * famKernelOrbitEvenH L ρ β j * (nref τ L β)⁻¹ =
      famKernelOrbitEvenH L ρ β j := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  intro j hj1 hjm
  have h0 : iform β (ρ^[j] β) = 0 := hortho 0 j (by omega) hjm
  have h0' : iform β (-(ρ^[j] β)) = 0 := by rw [iform_neg_right, h0, neg_zero]
  have e1 : nref τ L β * famKernelOrbitX L ρ β j * (nref τ L β)⁻¹ =
      famKernelOrbitX L ρ β j := by
    rw [show famKernelOrbitX L ρ β j = pinnedX τ L (ρ^[j] β) 1 from rfl,
      nref_conj_pinnedX_one h2 (hroot j), rootReflection_smul_of_iform_eq_zero hβ.1 h0]
  have e2 : nref τ L β * famKernelOrbitNegX L ρ β j * (nref τ L β)⁻¹ =
      famKernelOrbitNegX L ρ β j := by
    rw [show famKernelOrbitNegX L ρ β j = pinnedX τ L (-(ρ^[j] β)) 1 from rfl,
      nref_conj_pinnedX_one h2 (IsRoot.neg (hroot j)),
      rootReflection_smul_of_iform_eq_zero hβ.1 h0']
  calc nref τ L β * famKernelOrbitEvenH L ρ β j * (nref τ L β)⁻¹
      = (nref τ L β * famKernelOrbitX L ρ β j * (nref τ L β)⁻¹) *
          (nref τ L β * famKernelOrbitNegX L ρ β j * (nref τ L β)⁻¹) := by
        rw [show famKernelOrbitEvenH L ρ β j =
          famKernelOrbitX L ρ β j * famKernelOrbitNegX L ρ β j from rfl]; group
    _ = famKernelOrbitX L ρ β j * famKernelOrbitNegX L ρ β j := by rw [e1, e2]
    _ = famKernelOrbitEvenH L ρ β j := rfl

private theorem nref_conj_pinnedX_zero
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} (hβ : β ∈ familyKernel a) :
    nref τ L β * famKernelOrbitX L ρ β 0 * (nref τ L β)⁻¹ = famKernelOrbitNegX L ρ β 0 ∧
      nref τ L β * famKernelOrbitNegX L ρ β 0 * (nref τ L β)⁻¹ =
        famKernelOrbitX L ρ β 0 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  constructor
  · change nref τ L β * pinnedX τ L β 1 * (nref τ L β)⁻¹ = pinnedX τ L (-β) 1
    rw [nref_conj_pinnedX_one h2 hβ.1, rootReflection_smul_self hβ.1]
  · change nref τ L β * pinnedX τ L (-β) 1 * (nref τ L β)⁻¹ = pinnedX τ L β 1
    rw [nref_conj_pinnedX_one h2 (IsRoot.neg hβ.1),
      show rootReflection β • (-β) = β by
        rw [smul_neg, rootReflection_smul_self hβ.1, neg_neg]]

private theorem nref_conj_evenH_zero
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} (hβ : β ∈ familyKernel a) :
    nref τ L β * famKernelOrbitEvenH L ρ β 0 * (nref τ L β)⁻¹ =
      (famKernelOrbitEvenH L ρ β 0)⁻¹ := by
  obtain ⟨e1, e2⟩ := nref_conj_pinnedX_zero (ρ := ρ) hβ
  have hfi : (famKernelOrbitX L ρ β 0)⁻¹ = famKernelOrbitX L ρ β 0 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact pinnedX_one_pow_two (ρ^[0] β))
  have hgi : (famKernelOrbitNegX L ρ β 0)⁻¹ = famKernelOrbitNegX L ρ β 0 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact pinnedX_one_pow_two (-(ρ^[0] β)))
  calc nref τ L β * famKernelOrbitEvenH L ρ β 0 * (nref τ L β)⁻¹
      = (nref τ L β * famKernelOrbitX L ρ β 0 * (nref τ L β)⁻¹) *
          (nref τ L β * famKernelOrbitNegX L ρ β 0 * (nref τ L β)⁻¹) := by
        rw [show famKernelOrbitEvenH L ρ β 0 =
          famKernelOrbitX L ρ β 0 * famKernelOrbitNegX L ρ β 0 from rfl]
        group
    _ = famKernelOrbitNegX L ρ β 0 * famKernelOrbitX L ρ β 0 := by rw [e1, e2]
    _ = (famKernelOrbitX L ρ β 0 * famKernelOrbitNegX L ρ β 0)⁻¹ := by
      rw [mul_inv_rev, hfi, hgi]
    _ = (famKernelOrbitEvenH L ρ β 0)⁻¹ := rfl

private theorem nref_conj_H_shift
    {τ : Tag} {L : Type} [Field L] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} {m : ℕ}
    (hnH : ∀ j, 1 ≤ j → j < m → nref τ L β * famKernelOrbitEvenH L ρ β j *
      (nref τ L β)⁻¹ = famKernelOrbitEvenH L ρ β j) :
    nref τ L β * (List.map (fun i => famKernelOrbitEvenH L ρ β (i + 1))
        (List.range (m - 1))).prod * (nref τ L β)⁻¹ =
      (List.map (fun i => famKernelOrbitEvenH L ρ β (i + 1)) (List.range (m - 1))).prod := by
  refine conj_prod_eq_of_forall ?_
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  rw [List.mem_range] at hi
  exact hnH (i + 1) (by omega) (by omega)

private theorem sq_eq_one_of_inv_mul_inv_eq_one {G : Type*} [Group G] {x : G}
    (h : x⁻¹ * x⁻¹ = 1) : x ^ 2 = 1 := by
  have h3 : ((x ^ 2))⁻¹ = 1 := by rw [pow_two, mul_inv_rev]; exact h
  exact inv_injective (by rw [h3, inv_one])

private theorem ne_one_of_sq_eq_one_of_orderOf_eq_three {G : Type*} [Group G] {x : G}
    (hsq : x ^ 2 = 1) (hord : orderOf x = 3) : False := by
  have h3 : x ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hx : x = 1 := by
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, hsq, inv_one, one_mul]
  rw [hx] at hord
  simp at hord

private theorem famKernel_orbit_ne_one
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ}
    (hroot : ∀ i, IsRoot τ (ρ^[i] β))
    (huv : famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m = famKernelOrbitH L ρ β m)
    {P1 : ModGL τ L} (hsplit : famKernelOrbitH L ρ β m =
      famKernelOrbitEvenH L ρ β 0 * P1)
    (hnH0 : nref τ L β * famKernelOrbitEvenH L ρ β 0 * (nref τ L β)⁻¹ =
      (famKernelOrbitEvenH L ρ β 0)⁻¹)
    (hnP1 : nref τ L β * P1 * (nref τ L β)⁻¹ = P1) :
    famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m ≠ 1 := by
  intro h1
  have h1' : famKernelOrbitH L ρ β m = 1 := by rw [← huv]; exact h1
  have hP1 : famKernelOrbitEvenH L ρ β 0 * P1 = 1 := by rw [← hsplit, h1']
  have hP1inv : P1 = (famKernelOrbitEvenH L ρ β 0)⁻¹ :=
    (inv_eq_of_mul_eq_one_right hP1).symm
  have hconj : nref τ L β * famKernelOrbitH L ρ β m * (nref τ L β)⁻¹ =
      (famKernelOrbitEvenH L ρ β 0)⁻¹ * P1 := by
    rw [hsplit, show nref τ L β * (famKernelOrbitEvenH L ρ β 0 * P1) * (nref τ L β)⁻¹ =
      (nref τ L β * famKernelOrbitEvenH L ρ β 0 * (nref τ L β)⁻¹) *
        (nref τ L β * P1 * (nref τ L β)⁻¹) by group, hnH0, hnP1]
  rw [h1', hP1inv] at hconj
  have hsq : (famKernelOrbitEvenH L ρ β 0) ^ 2 = 1 := by
    apply sq_eq_one_of_inv_mul_inv_eq_one
    rw [← hconj]
    group
  exact ne_one_of_sq_eq_one_of_orderOf_eq_three hsq
    (orderOf_evenH (τ := τ) (K := L) (hroot 0))

private theorem famKernel_orbit_step_X
    {τ : Tag} {L : Type} [Field L]
    [CharP L 2] (D : LangDatum τ L) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap D ρ) {β : Fin τ.rank → ℤ} {m : ℕ}
    (hroot : ∀ i, IsRoot τ (ρ^[i] β)) :
    D.step (famKernelOrbitU L ρ β m) =
      (List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range m)).prod := by
  rw [show famKernelOrbitU L ρ β m =
    (List.map (famKernelOrbitX L ρ β) (List.range m)).prod from rfl, ← List.prod_hom]
  congr 1
  rw [List.map_map]
  congr 1
  funext i
  change D.step (famKernelOrbitX L ρ β i) = famKernelOrbitX L ρ β (i + 1)
  dsimp only [famKernelOrbitX]
  have h := step_pinnedX_one_of_frobRootMap D hρ (hroot i)
  rw [Function.iterate_succ_apply']
  exact h

private theorem famKernel_orbit_step_negX
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (D : LangDatum τ L)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) {β : Fin τ.rank → ℤ} {m : ℕ}
    (hroot : ∀ i, IsRoot τ (ρ^[i] β)) :
    D.step (famKernelOrbitV L ρ β m) =
      (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1)) (List.range m)).prod := by
  rw [show famKernelOrbitV L ρ β m =
    (List.map (famKernelOrbitNegX L ρ β) (List.range m)).prod from rfl, ← List.prod_hom]
  congr 1
  rw [List.map_map]
  congr 1
  funext i
  change D.step (famKernelOrbitNegX L ρ β i) = famKernelOrbitNegX L ρ β (i + 1)
  dsimp only [famKernelOrbitNegX]
  have h := step_pinnedX_one_of_frobRootMap D hρ (IsRoot.neg (hroot i))
  rw [hρ.neg_eq] at h
  rw [Function.iterate_succ_apply']
  exact h

private theorem famKernel_orbit_conj_step_X
    {τ : Tag} {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ} {n : ModGL τ L}
    {D : LangDatum τ L}
    (hnx : n * famKernelOrbitX L ρ β m * n⁻¹ = famKernelOrbitX L ρ β 0)
    (hfix : n * (List.map (fun i => famKernelOrbitX L ρ β (i + 1))
        (List.range (m - 1))).prod * n⁻¹ =
      (List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range (m - 1))).prod)
    (hstep : D.step (famKernelOrbitU L ρ β m) =
      (List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range m)).prod)
    (hsplit : famKernelOrbitU L ρ β m =
      (List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range (m - 1))).prod *
        famKernelOrbitX L ρ β 0)
    (hm : 0 < m) :
    n * D.step (famKernelOrbitU L ρ β m) * n⁻¹ = famKernelOrbitU L ρ β m := by
  have hsp : (List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range m)).prod =
      (List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range (m - 1))).prod *
        famKernelOrbitX L ρ β m := by
    rw [show m = (m - 1) + 1 by omega]
    exact List.prod_range_succ _ _
  rw [hstep, hsp, hsplit]
  calc n * ((List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range (m - 1))).prod *
        famKernelOrbitX L ρ β m) * n⁻¹
      = (n * (List.map (fun i => famKernelOrbitX L ρ β (i + 1))
            (List.range (m - 1))).prod * n⁻¹) * (n * famKernelOrbitX L ρ β m * n⁻¹) := by
        group
    _ = (List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range (m - 1))).prod *
        famKernelOrbitX L ρ β 0 := by rw [hfix, hnx]

private theorem famKernel_orbit_conj_step_negX
    {τ : Tag} {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ} {n : ModGL τ L}
    {D : LangDatum τ L}
    (hnx : n * famKernelOrbitNegX L ρ β m * n⁻¹ = famKernelOrbitNegX L ρ β 0)
    (hfix : n * (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1))
        (List.range (m - 1))).prod * n⁻¹ =
      (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1)) (List.range (m - 1))).prod)
    (hstep : D.step (famKernelOrbitV L ρ β m) =
      (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1)) (List.range m)).prod)
    (hsplit : famKernelOrbitV L ρ β m =
      (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1)) (List.range (m - 1))).prod *
        famKernelOrbitNegX L ρ β 0)
    (hm : 0 < m) :
    n * D.step (famKernelOrbitV L ρ β m) * n⁻¹ = famKernelOrbitV L ρ β m := by
  have hsp : (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1)) (List.range m)).prod =
      (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1)) (List.range (m - 1))).prod *
        famKernelOrbitNegX L ρ β m := by
    rw [show m = (m - 1) + 1 by omega]
    exact List.prod_range_succ _ _
  rw [hstep, hsp, hsplit]
  calc n * ((List.map (fun i => famKernelOrbitNegX L ρ β (i + 1))
          (List.range (m - 1))).prod * famKernelOrbitNegX L ρ β m) * n⁻¹
      = (n * (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1))
            (List.range (m - 1))).prod * n⁻¹) *
          (n * famKernelOrbitNegX L ρ β m * n⁻¹) := by group
    _ = (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1)) (List.range (m - 1))).prod *
        famKernelOrbitNegX L ρ β 0 := by rw [hfix, hnx]

private theorem famKernel_orbit_commute_all
    {τ : Tag} {L : Type} [Field L] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} {m : ℕ} (hsym : ∀ i, τ.symmetrizer i i = 1)
    (hroot : ∀ i, IsRoot τ (ρ^[i] β))
    (hortho : ∀ i j, i < j → j < m → iform (ρ^[i] β) (ρ^[j] β) = 0) :
    (∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitX L ρ β i) (famKernelOrbitX L ρ β j)) ∧
    (∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitX L ρ β i) (famKernelOrbitNegX L ρ β j)) ∧
    (∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitNegX L ρ β i) (famKernelOrbitNegX L ρ β j)) ∧
    (∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitEvenH L ρ β i) (famKernelOrbitEvenH L ρ β j)) := by
  have h1 := famKernel_orbit_commute_X (L := L) (ρ := ρ) (β := β) (m := m) hsym hroot hortho
  have h2 := famKernel_orbit_commute_X_neg (L := L) (ρ := ρ) (β := β) (m := m)
    hsym hroot hortho
  have h3 := famKernel_orbit_commute_negX (L := L) (ρ := ρ) (β := β) (m := m)
    hsym hroot hortho
  exact ⟨h1, h2, h3,
    famKernel_orbit_commute_evenH (L := L) (ρ := ρ) (β := β) (m := m) h1 h2 h3⟩

private theorem famKernel_orbit_static_data
    {τ : Tag} {L : Type} [Field L]
    (D : LangDatum τ L) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap D ρ) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (ha : ∀ i, rootDiagUnit τ (a i) ∈ D.torus)
    (hsym : ∀ i, τ.symmetrizer i i = 1) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ familyKernel a) :
    ∃ m, 0 < m ∧ famConn a β (ρ^[m] β) ∧
      (∀ k, 0 < k → k < m → ¬ famConn a β (ρ^[k] β)) ∧
      (∀ i, ρ^[i] β ∈ familyKernel a) ∧ (∀ i, IsRoot τ (ρ^[i] β)) ∧
      (∀ i j, i < j → j < m → iform (ρ^[i] β) (ρ^[j] β) = 0) ∧
      (∀ i j, i < m → j < m → i ≠ j →
        Commute (famKernelOrbitX L ρ β i) (famKernelOrbitX L ρ β j)) ∧
      (∀ i j, i < m → j < m → i ≠ j →
        Commute (famKernelOrbitX L ρ β i) (famKernelOrbitNegX L ρ β j)) ∧
      (∀ i j, i < m → j < m → i ≠ j →
        Commute (famKernelOrbitNegX L ρ β i) (famKernelOrbitNegX L ρ β j)) ∧
      (∀ i j, i < m → j < m → i ≠ j →
        Commute (famKernelOrbitEvenH L ρ β i) (famKernelOrbitEvenH L ρ β j)) := by
  have hρΨ := mapsTo_familyKernel_of_frobRootMap D hρ ha
  obtain ⟨m, hm0, hconn, hmin⟩ := famKernel_orbit_min ρ hρΨ hβ
  obtain ⟨hb, hortho⟩ := famKernel_orbit_orthogonal D hρ hρΨ hβ hmin
  have hroot : ∀ i, IsRoot τ (ρ^[i] β) := fun i => (hb i).1
  obtain ⟨hXX, hXn, hnn, hH⟩ :=
    famKernel_orbit_commute_all (L := L) (ρ := ρ) (β := β) (m := m) hsym hroot hortho
  exact ⟨m, hm0, hconn, hmin, hb, hroot, hortho, hXX, hXn, hnn, hH⟩

private theorem famKernel_orbit_product_data
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ}
    (hb : ∀ i, ρ^[i] β ∈ familyKernel a) (hroot : ∀ i, IsRoot τ (ρ^[i] β))
    (hpairF : (List.map (famKernelOrbitX L ρ β) (List.range m)).Pairwise Commute)
    (hpairG : (List.map (famKernelOrbitNegX L ρ β) (List.range m)).Pairwise Commute)
    (hpairH : (List.map (famKernelOrbitEvenH L ρ β) (List.range m)).Pairwise Commute)
    (hcomm : ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitX L ρ β i) (famKernelOrbitNegX L ρ β j)) :
    famKernelOrbitU L ρ β m ∈ familyGroup (K := L) a ∧
      famKernelOrbitV L ρ β m ∈ familyGroup (K := L) a ∧
      famKernelOrbitU L ρ β m ^ 2 = 1 ∧ famKernelOrbitV L ρ β m ^ 2 = 1 ∧
      famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m = famKernelOrbitH L ρ β m ∧
      (famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m) ^ 3 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := famKernel_orbit_prod_mem_sq ρ hb hpairF hpairG
  have huv := famKernel_orbit_uv_eq_prod hcomm
  exact ⟨h1, h2, h3, h4, huv, famKernel_orbit_prod_cube hpairH hroot huv⟩

private theorem famKernel_orbit_prod_ne_one
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ}
    (hβ : β ∈ familyKernel a) (hroot : ∀ i, IsRoot τ (ρ^[i] β))
    (hortho : ∀ i j, i < j → j < m → iform (ρ^[i] β) (ρ^[j] β) = 0)
    (huv : famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m =
      famKernelOrbitH L ρ β m) (hm : 0 < m) :
    famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m ≠ 1 := by
  have hsplit := famKernel_orbit_H_split (L := L) (ρ := ρ) (β := β) hm
  have hnH := nref_conj_evenH_of_pos hβ hroot hortho
  have hnH0 := nref_conj_evenH_zero (L := L) (ρ := ρ) hβ
  exact famKernel_orbit_ne_one hroot huv hsplit hnH0 (nref_conj_H_shift hnH)

private theorem famKernel_orbit_conj_data_X
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {ι : Type} {a : ι → Fin τ.rank → Lˣ} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} {m : ℕ} {n : ModGL τ L}
    (hb : ∀ i, ρ^[i] β ∈ familyKernel a)
    (hXX : ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitX L ρ β i) (famKernelOrbitX L ρ β j))
    (hstep : D.step (famKernelOrbitU L ρ β m) =
      (List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range m)).prod)
    (hnx : n * famKernelOrbitX L ρ β m * n⁻¹ = famKernelOrbitX L ρ β 0)
    (hnfix : ∀ ε, ε ∈ familyKernel a → ¬ famConn a (ρ^[m] β) ε →
      n * pinnedX τ L ε 1 * n⁻¹ = pinnedX τ L ε 1 ∧
        n * pinnedX τ L (-ε) 1 * n⁻¹ = pinnedX τ L (-ε) 1)
    (hnotconn : ∀ j, 1 ≤ j → j < m → ¬ famConn a (ρ^[m] β) (ρ^[j] β))
    (hm : 0 < m) :
    n * D.step (famKernelOrbitU L ρ β m) * n⁻¹ = famKernelOrbitU L ρ β m := by
  have hfix : n * (List.map (fun i => famKernelOrbitX L ρ β (i + 1))
      (List.range (m - 1))).prod * n⁻¹ =
      (List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range (m - 1))).prod := by
    refine conj_prod_eq_of_forall ?_
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hi
    exact (hnfix (ρ^[i + 1] β) (hb (i + 1))
      (hnotconn (i + 1) (by omega) (by omega))).1
  have hsplit : famKernelOrbitU L ρ β m =
      (List.map (fun i => famKernelOrbitX L ρ β (i + 1)) (List.range (m - 1))).prod *
        famKernelOrbitX L ρ β 0 := by
    rw [show famKernelOrbitU L ρ β m =
      (List.map (famKernelOrbitX L ρ β) (List.range m)).prod from rfl]
    rw [show m = (m - 1) + 1 by omega]
    exact prod_range_shift_of_pairwise_commute _ _
      (fun i j hi hj hij => hXX i j (by omega) (by omega) hij)
  exact famKernel_orbit_conj_step_X (L := L) (ρ := ρ) (β := β) (m := m)
    hnx hfix hstep hsplit hm

private theorem famKernel_orbit_conj_data_negX
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {ι : Type} {a : ι → Fin τ.rank → Lˣ} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} {m : ℕ} {n : ModGL τ L}
    (hb : ∀ i, ρ^[i] β ∈ familyKernel a)
    (hnn : ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitNegX L ρ β i) (famKernelOrbitNegX L ρ β j))
    (hstep : D.step (famKernelOrbitV L ρ β m) =
      (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1)) (List.range m)).prod)
    (hnx : n * famKernelOrbitNegX L ρ β m * n⁻¹ = famKernelOrbitNegX L ρ β 0)
    (hnfix : ∀ ε, ε ∈ familyKernel a → ¬ famConn a (ρ^[m] β) ε →
      n * pinnedX τ L ε 1 * n⁻¹ = pinnedX τ L ε 1 ∧
        n * pinnedX τ L (-ε) 1 * n⁻¹ = pinnedX τ L (-ε) 1)
    (hnotconn : ∀ j, 1 ≤ j → j < m → ¬ famConn a (ρ^[m] β) (ρ^[j] β))
    (hm : 0 < m) :
    n * D.step (famKernelOrbitV L ρ β m) * n⁻¹ = famKernelOrbitV L ρ β m := by
  have hfix : n * (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1))
      (List.range (m - 1))).prod * n⁻¹ =
      (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1)) (List.range (m - 1))).prod := by
    refine conj_prod_eq_of_forall ?_
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hi
    exact (hnfix (ρ^[i + 1] β) (hb (i + 1))
      (hnotconn (i + 1) (by omega) (by omega))).2
  have hsplit : famKernelOrbitV L ρ β m =
      (List.map (fun i => famKernelOrbitNegX L ρ β (i + 1)) (List.range (m - 1))).prod *
        famKernelOrbitNegX L ρ β 0 := by
    rw [show famKernelOrbitV L ρ β m =
      (List.map (famKernelOrbitNegX L ρ β) (List.range m)).prod from rfl]
    rw [show m = (m - 1) + 1 by omega]
    exact prod_range_shift_of_pairwise_commute _ _
      (fun i j hi hj hij => hnn i j (by omega) (by omega) hij)
  exact famKernel_orbit_conj_step_negX (L := L) (ρ := ρ) (β := β) (m := m)
    hnx hfix hstep hsplit hm

private theorem famKernel_not_conn_last {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} {m : ℕ} (hconn : famConn a β (ρ^[m] β))
    (hmin : ∀ k, 0 < k → k < m → ¬ famConn a β (ρ^[k] β)) :
    ∀ j, 1 ≤ j → j < m → ¬ famConn a (ρ^[m] β) (ρ^[j] β) := by
  intro j hj1 hjm hc
  exact hmin j hj1 hjm (famConn_trans hconn hc)

private theorem famKernel_orbit_orderOf
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ}
    (hβ : β ∈ familyKernel a) (hroot : ∀ i, IsRoot τ (ρ^[i] β))
    (hortho : ∀ i j, i < j → j < m → iform (ρ^[i] β) (ρ^[j] β) = 0)
    (hpairH : (List.map (famKernelOrbitEvenH L ρ β) (List.range m)).Pairwise Commute)
    (huv : famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m =
      famKernelOrbitH L ρ β m) (hm : 0 < m) :
    orderOf (famKernelOrbitU L ρ β m * famKernelOrbitV L ρ β m) = 3 :=
  orderOf_eq_prime (famKernel_orbit_prod_cube hpairH hroot huv)
    (famKernel_orbit_prod_ne_one hβ hroot hortho huv hm)

private theorem famKernel_orbit_pairwise_data
    {τ : Tag} {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} {m : ℕ}
    (hXX : ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitX L ρ β i) (famKernelOrbitX L ρ β j))
    (hnn : ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitNegX L ρ β i) (famKernelOrbitNegX L ρ β j))
    (hH : ∀ i j, i < m → j < m → i ≠ j →
      Commute (famKernelOrbitEvenH L ρ β i) (famKernelOrbitEvenH L ρ β j)) :
    (List.map (famKernelOrbitX L ρ β) (List.range m)).Pairwise Commute ∧
      (List.map (famKernelOrbitNegX L ρ β) (List.range m)).Pairwise Commute ∧
      (List.map (famKernelOrbitEvenH L ρ β) (List.range m)).Pairwise Commute :=
  ⟨famKernel_pairwise_commute hXX, famKernel_pairwise_commute hnn,
    famKernel_pairwise_commute hH⟩

private theorem exists_uv_data_of_familyKernel
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (D : LangDatum τ L)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (ha : ∀ i, rootDiagUnit τ (a i) ∈ D.torus)
    (hsym : ∀ i, τ.symmetrizer i i = 1) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ familyKernel a) :
    ∃ (n u v : ModGL τ L), n ∈ familyGroup (K := L) a ∧
      u ∈ familyGroup (K := L) a ∧ v ∈ familyGroup (K := L) a ∧
      u ^ 2 = 1 ∧ v ^ 2 = 1 ∧ orderOf (u * v) = 3 ∧
      n * D.step u * n⁻¹ = u ∧ n * D.step v * n⁻¹ = v := by
  obtain ⟨m, hm0, hconn, hmin, hb, hroot, hortho, hXX, hXn, hnn, hH⟩ :=
    famKernel_orbit_static_data D hρ ha hsym hβ
  obtain ⟨hpairF, hpairG, hpairH⟩ := famKernel_orbit_pairwise_data hXX hnn hH
  obtain ⟨huM, hvM, hu2, hv2, huv, hcube⟩ :=
    famKernel_orbit_product_data hb hroot hpairF hpairG hpairH hXn
  have hord := famKernel_orbit_orderOf hβ hroot hortho hpairH huv hm0
  obtain ⟨n, hnM, hnx, hnx', hnfix⟩ :=
    exists_conj_of_famConn hsym (famConn_symm hconn)
  have hnotconn := famKernel_not_conn_last hconn hmin
  have hstepu := famKernel_orbit_step_X (L := L) (ρ := ρ) (β := β) (m := m) D hρ hroot
  have hstepv := famKernel_orbit_step_negX (L := L) (ρ := ρ) (β := β) (m := m) D hρ hroot
  have hnu := famKernel_orbit_conj_data_X hb hXX hstepu hnx hnfix hnotconn hm0
  have hnv := famKernel_orbit_conj_data_negX hb hnn hstepv hnx' hnfix hnotconn hm0
  exact ⟨n, famKernelOrbitU L ρ β m, famKernelOrbitV L ρ β m, hnM, huM, hvM,
    hu2, hv2, hord, hnu, hnv⟩

private theorem famKernel_conj_sq_eq_one {G : Type*} [Group G] {ζ u : G} (hu : u ^ 2 = 1) :
    (ζ * u * ζ⁻¹) ^ 2 = 1 := by
  have h1 : ζ * u * ζ⁻¹ = (MulAut.conj ζ) u := by rw [MulAut.conj_apply]
  rw [h1, ← map_pow, hu, map_one]

private theorem famKernel_conj_orderOf {G : Type*} [Group G] (ζ x : G) :
    orderOf (ζ * x * ζ⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj ζ).toMonoidHom (MulAut.conj ζ).injective x
  change orderOf ((MulAut.conj ζ) x) = orderOf x at h
  rwa [MulAut.conj_apply] at h

private theorem map_conj_fixed {G : Type*} [Group G] (F : G →* G) {ζ n u : G}
    (hζ : F ζ = ζ * n) (hn : n * F u * n⁻¹ = u) : F (ζ * u * ζ⁻¹) = ζ * u * ζ⁻¹ := by
  calc F (ζ * u * ζ⁻¹) = F ζ * F u * (F ζ)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = (ζ * n) * F u * (ζ * n)⁻¹ := by rw [hζ]
    _ = ζ * (n * F u * n⁻¹) * ζ⁻¹ := by group
    _ = ζ * u * ζ⁻¹ := by rw [hn]

private theorem exists_fixed_involutions_of_familyKernel
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    {f : ℕ} (hf : 1 ≤ f) (hq : D.q = 2 ^ f) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap D ρ) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (ha : ∀ i, rootDiagUnit τ (a i) ∈ D.torus)
    (hsym : ∀ i, τ.symmetrizer i i = 1) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ familyKernel a) :
    ∃ x ∈ familyGroup (K := L) a, ∃ y ∈ familyGroup (K := L) a, x ^ 2 = 1 ∧
      y ^ 2 = 1 ∧ orderOf (x * y) = 3 ∧ D.step x = x ∧ D.step y = y := by
  obtain ⟨n, u, v, hnM, huM, hvM, hu2, hv2, hord, hnu, hnv⟩ :=
    exists_uv_data_of_familyKernel D hρ ha hsym hβ
  have hρΨ := mapsTo_familyKernel_of_frobRootMap D hρ ha
  have hstepM : ∀ g ∈ familyGroup (K := L) a, D.step g ∈ familyGroup (K := L) a :=
    fun g hg => step_mem_familyGroup D hq hρ hρΨ hg
  obtain ⟨ζ, hζM, hζeq⟩ := exists_lang_solution_of_familyGroup D hf hq hstepM hnM
  have hstepζ : D.step ζ = ζ * n := by
    calc D.step ζ = ζ * (ζ⁻¹ * D.step ζ) := by group
      _ = ζ * n := by rw [hζeq]
  have hxM : ζ * u * ζ⁻¹ ∈ familyGroup (K := L) a :=
    mul_mem (mul_mem hζM huM) (inv_mem hζM)
  have hyM : ζ * v * ζ⁻¹ ∈ familyGroup (K := L) a :=
    mul_mem (mul_mem hζM hvM) (inv_mem hζM)
  have hxy : (ζ * u * ζ⁻¹) * (ζ * v * ζ⁻¹) = ζ * (u * v) * ζ⁻¹ := by group
  exact ⟨ζ * u * ζ⁻¹, hxM, ζ * v * ζ⁻¹, hyM, famKernel_conj_sq_eq_one hu2,
    famKernel_conj_sq_eq_one hv2,
    by rw [hxy, famKernel_conj_orderOf, hord],
    map_conj_fixed D.step hstepζ hnu, map_conj_fixed D.step hstepζ hnv⟩

private theorem symmetrizer_E6_eq_one : ∀ i, Tag.E6.symmetrizer i i = 1 := by
  intro i
  rw [show Tag.E6.symmetrizer = 1 from rfl]
  simp

private theorem symmetrizer_E7_eq_one : ∀ i, Tag.E7.symmetrizer i i = 1 := by
  intro i
  rw [show Tag.E7.symmetrizer = 1 from rfl]
  simp

theorem exists_step_fixed_involutions_of_familyKernel_nonempty
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (D : LangDatum τ L) (hq : ∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (ha : ∀ i, rootDiagUnit τ (a i) ∈ D.torus)
    (hΦ : (familyKernel a).Nonempty) :
    ∃ x ∈ familyGroup a, ∃ y ∈ familyGroup a, x ^ 2 = 1 ∧ y ^ 2 = 1 ∧
      orderOf (x * y) = 3 ∧ D.step x = x ∧ D.step y = y := by
  obtain ⟨f, hf, hq⟩ := hq
  obtain ⟨β, hβ⟩ := hΦ
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  rcases hτ with rfl | rfl
  · exact exists_fixed_involutions_of_familyKernel D hf hq hρ ha symmetrizer_E6_eq_one hβ
  · exact exists_fixed_involutions_of_familyKernel D hf hq hρ ha symmetrizer_E7_eq_one hβ

end CFSG.StandardType
