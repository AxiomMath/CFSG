module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcPin
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
  CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint

private abbrev e6D4J : Set (Fin Tag.E6.rank) :=
  {j | j ∉ ({0, 5} : Finset (Fin Tag.E6.rank))}

private def e6D4Psi0 : Set (Fin Tag.E6.rank → ℤ) := parabolicRoots Tag.E6 e6D4J

private theorem mem_e6D4Psi0 {α : Fin Tag.E6.rank → ℤ} :
    α ∈ e6D4Psi0 ↔ IsRoot Tag.E6 α ∧ ∀ i ∉ e6D4J, α i = 0 := Iff.rfl

private theorem zero_notMem_e6D4J : (0 : Fin Tag.E6.rank) ∉ e6D4J := by decide

private theorem five_notMem_e6D4J : (5 : Fin Tag.E6.rank) ∉ e6D4J := by decide

private theorem eq_zero_or_eq_five_of_notMem {i : Fin Tag.E6.rank} (hi : i ∉ e6D4J) :
    i = 0 ∨ i = 5 := by
  have h : i ∈ ({0, 5} : Finset (Fin Tag.E6.rank)) := by
    by_contra h
    exact hi h
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

private theorem neg_mem_e6D4Psi0 {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ e6D4Psi0) :
    -δ ∈ e6D4Psi0 :=
  ⟨CFSG.LieType.Chevalley.IsRoot.neg hδ.1,
    fun i hi => by rw [Pi.neg_apply, hδ.2 i hi, neg_zero]⟩

private theorem e6D4Psi0_ncard : e6D4Psi0.ncard = 24 :=
  ncard_parabolicRoots_eq (J := e6D4J)
    (P := fun i => i ∈ ({1, 2, 3, 4} : Finset (Fin Tag.E6.rank))) (by decide)
    (by decide +kernel)

private theorem e6D4Psi0_compRank :
    compRank e6D4Psi0 = 4 := by
  let C : Finset (Option (Fin Tag.E6.rank)) := {some 1, some 2, some 3, some 4}
  have hnone : none ∉ C := by decide
  have hCJ : ∀ j, some j ∈ C ↔ j ∈ e6D4J := by
    intro j
    simp only [e6D4J, Set.mem_setOf_eq]
    revert j
    decide
  have hCcard : C.card = 4 := by decide
  have hroots : kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) = e6D4Psi0 := by
    ext γ
    rw [mem_rootsOf_iff kacE6 facts_E6 ⟨none, hnone⟩]
    constructor
    · rintro ⟨hγ, htest⟩
      refine ⟨hγ, fun i hi => ?_⟩
      rcases htest with h | ⟨hnone', -⟩
      · exact h i (fun hc => hi ((hCJ i).1 hc))
      · exact absurd hnone' hnone
    · rintro ⟨hγ, hJ⟩
      exact ⟨hγ, Or.inl fun j hj => hJ j (fun hj' => hj ((hCJ j).2 hj'))⟩
  calc compRank e6D4Psi0
      = compRank (kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank)))) := by rw [hroots]
    _ = C.card := compRank_rootsOf kacE6 facts_E6 ⟨none, hnone⟩
    _ = 4 := hCcard

private def e6D4Form (x y : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ i, x i * ∑ j, Tag.E6.cartan i j * y j

private theorem e6D4_symmetrizedCartan : Tag.E6.symmetrizedCartan = Tag.E6.cartan := by
  rw [Tag.symmetrizedCartan, Tag.symmetrizer, one_mul]

private theorem e6_iform_eq_e6Form (x y : Fin Tag.E6.rank → ℤ) :
    iform x y = e6D4Form x y := by
  simp only [iform, e6D4Form, e6D4_symmetrizedCartan, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem e6_iform_self_e6RootVec :
    ∀ m : Fin 72, iform (e6RootVec m) (e6RootVec m) = 2 := by
  decide +kernel

private theorem e6D4_iform_self
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) : iform γ γ = 2 := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hγ
  exact e6_iform_self_e6RootVec m

private theorem e6_corootPair_eq_iform
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (x : Fin Tag.E6.rank → ℤ) :
    corootPair β x = iform β x := by
  have h2 : iform β β = 2 := e6D4_iform_self hβ
  rw [corootPair, h2]
  omega

private def e6D4Theta : Fin Tag.E6.rank → ℤ :=
  Pi.single 1 1 + Pi.single 2 1 + Pi.single 4 1 + (2 : ℤ) • Pi.single 3 1

private def e6Leaf1 : Fin Tag.E6.rank → ℤ := Pi.single 1 1
private def e6Leaf2 : Fin Tag.E6.rank → ℤ := Pi.single 2 1
private def e6Leaf4 : Fin Tag.E6.rank → ℤ := Pi.single 4 1

private theorem e6Theta_isRoot : IsRoot Tag.E6 e6D4Theta := by
  rw [isRoot_iff_exists_e6RootVec]
  decide +kernel

private theorem e6Theta_mem : e6D4Theta ∈ e6D4Psi0 := by
  refine mem_e6D4Psi0.2 ⟨e6Theta_isRoot, fun i hi => ?_⟩
  rcases eq_zero_or_eq_five_of_notMem hi with rfl | rfl <;> decide

private theorem e6Leaf1_mem : e6Leaf1 ∈ e6D4Psi0 := by
  refine mem_e6D4Psi0.2 ⟨IsRoot.basis 1, fun i hi => ?_⟩
  rcases eq_zero_or_eq_five_of_notMem hi with rfl | rfl <;> decide

private theorem e6Leaf2_mem : e6Leaf2 ∈ e6D4Psi0 := by
  refine mem_e6D4Psi0.2 ⟨IsRoot.basis 2, fun i hi => ?_⟩
  rcases eq_zero_or_eq_five_of_notMem hi with rfl | rfl <;> decide

private theorem e6Leaf4_mem : e6Leaf4 ∈ e6D4Psi0 := by
  refine mem_e6D4Psi0.2 ⟨IsRoot.basis 4, fun i hi => ?_⟩
  rcases eq_zero_or_eq_five_of_notMem hi with rfl | rfl <;> decide

private noncomputable def e6D4W0 : WeylGroup Tag.E6 :=
  rootReflection e6D4Theta * rootReflection e6Leaf1 * rootReflection e6Leaf2 *
    rootReflection e6Leaf4

private def e6rF (β x : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ := x - e6D4Form β x • β

private theorem e6W0_smul_eq
    (x : Fin Tag.E6.rank → ℤ) :
    e6D4W0 • x = e6rF e6D4Theta (e6rF e6Leaf1 (e6rF e6Leaf2 (e6rF e6Leaf4 x))) := by
  simp only [e6D4W0, e6rF, e6Leaf1, e6Leaf2, e6Leaf4, mul_smul, rootReflection_smul e6Theta_isRoot,
    rootReflection_smul (IsRoot.basis 1), rootReflection_smul (IsRoot.basis 2),
    rootReflection_smul (IsRoot.basis 4), e6_corootPair_eq_iform e6Theta_isRoot,
    e6_corootPair_eq_iform (IsRoot.basis 1), e6_corootPair_eq_iform (IsRoot.basis 2),
    e6_corootPair_eq_iform (IsRoot.basis 4), e6_iform_eq_e6Form]

private theorem e6W0_smul_e6RootVec :
    ∀ m : Fin 72, e6RootVec m 0 = 0 → e6RootVec m 5 = 0 →
      e6D4W0 • e6RootVec m = -e6RootVec m := by
  simp only [e6W0_smul_eq]
  decide +kernel

private theorem e6W0_smul_mem
    {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ e6D4Psi0) : e6D4W0 • δ = -δ := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hδ.1
  exact e6W0_smul_e6RootVec m (hδ.2 0 zero_notMem_e6D4J) (hδ.2 5 five_notMem_e6D4J)

private theorem e6W0_conj_mem
    (v : WeylGroup Tag.E6) :
    v * e6D4W0 * v⁻¹ ∈
      Subgroup.closure {s : WeylGroup Tag.E6 |
        ∃ γ ∈ (fun α => v • α) '' e6D4Psi0, s = rootReflection γ} := by
  have hgen : ∀ β ∈ e6D4Psi0, v * rootReflection β * v⁻¹ ∈
      Subgroup.closure {s : WeylGroup Tag.E6 |
        ∃ γ ∈ (fun α => v • α) '' e6D4Psi0, s = rootReflection γ} := by
    intro β hβ
    refine Subgroup.subset_closure ⟨v • β, ⟨β, hβ, rfl⟩, ?_⟩
    exact (rootReflection_smul_root v hβ.1).symm
  have hprod : v * e6D4W0 * v⁻¹ =
      (v * rootReflection e6D4Theta * v⁻¹) * (v * rootReflection e6Leaf1 * v⁻¹) *
        (v * rootReflection e6Leaf2 * v⁻¹) * (v * rootReflection e6Leaf4 * v⁻¹) := by
    simp only [e6D4W0]
    group
  rw [hprod]
  exact mul_mem (mul_mem (mul_mem (hgen _ e6Theta_mem) (hgen _ e6Leaf1_mem))
    (hgen _ e6Leaf2_mem)) (hgen _ e6Leaf4_mem)

private theorem e6D4_twistInner
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hρ : ∀ α, ρ α = -α) (v : WeylGroup Tag.E6) :
    twistInner ((fun α => v • α) '' e6D4Psi0) ρ := by
  refine ⟨v * e6D4W0 * v⁻¹, e6W0_conj_mem v, fun γ hγ => ?_⟩
  rcases hγ with ⟨δ, hδ, rfl⟩
  calc ρ (v • δ) = -(v • δ) := hρ _
    _ = v • (-δ) := (smul_neg v δ).symm
    _ = v • (e6D4W0 • δ) := by rw [e6W0_smul_mem hδ]
    _ = (v * e6D4W0 * v⁻¹) • (v • δ) := by simp only [mul_smul, inv_smul_smul]

private theorem e6D4_componentOrbitLength (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ α, ρ α = -α) (v : WeylGroup Tag.E6) :
    componentOrbitLength ρ ((fun α => v • α) '' e6D4Psi0) = 1 := by
  rw [componentOrbitLength]
  have himage : ρ '' ((fun α => v • α) '' e6D4Psi0) = (fun α => v • α) '' e6D4Psi0 := by
    have hρ' : ρ = fun α : Fin Tag.E6.rank → ℤ => -α := funext hρ
    rw [hρ']
    ext β
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      rcases hγ with ⟨δ, hδ, rfl⟩
      exact ⟨-δ, neg_mem_e6D4Psi0 hδ, smul_neg v δ⟩
    · rintro ⟨δ, hδ, rfl⟩
      exact ⟨v • (-δ), ⟨-δ, neg_mem_e6D4Psi0 hδ, rfl⟩, by simp only [smul_neg, neg_neg]⟩
  have hmem : (1 : ℕ) ∈ {s : ℕ | 0 < s ∧
      (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] ''
        ((fun α => v • α) '' e6D4Psi0) = (fun α => v • α) '' e6D4Psi0} := by
    refine ⟨by norm_num, ?_⟩
    rw [Function.iterate_one]
    exact himage
  refine le_antisymm (Nat.sInf_le hmem) ?_
  obtain ⟨hs, -⟩ := Nat.sInf_mem ⟨1, hmem⟩
  omega

private theorem e6D4_twistInner_iterate
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hρ : ∀ α, ρ α = -α) (v : WeylGroup Tag.E6) :
    twistInner ((fun α => v • α) '' e6D4Psi0)
      ((ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[
        componentOrbitLength ρ ((fun α => v • α) '' e6D4Psi0)]) := by
  rw [e6D4_componentOrbitLength ρ hρ v, Function.iterate_one]
  exact e6D4_twistInner ρ hρ v

theorem e6D4_compRank_smul
    (v : WeylGroup Tag.E6) :
    compRank ((fun α => v • α) ''
      parabolicRoots Tag.E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}) = 4 := by
  change compRank ((fun α => v • α) '' e6D4Psi0) = 4
  rw [compRank_image]
  exact e6D4Psi0_compRank

theorem e6D4_ncard_smul
    (v : WeylGroup Tag.E6) :
    ((fun α => v • α) ''
      parabolicRoots Tag.E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}).ncard = 24 := by
  change ((fun α => v • α) '' e6D4Psi0).ncard = 24
  rw [ncard_image_smul]
  exact e6D4Psi0_ncard

theorem e6D4_twistKindOf_neg
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hρ : ∀ α, ρ α = -α) (v : WeylGroup Tag.E6) :
    twistKindOf ρ ((fun α => v • α) ''
      parabolicRoots Tag.E6 {j | j ∉ ({0, 5} : Finset (Fin 6))}) = TwistKind.inner := by
  change twistKindOf ρ ((fun α => v • α) '' e6D4Psi0) = TwistKind.inner
  rw [twistKindOf]
  exact if_pos (e6D4_twistInner_iterate ρ hρ v)

theorem twistKindOf_id_eq_inner {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hρ : ∀ α, ρ α = α) (Ψ : Set (Fin τ.rank → ℤ)) : twistKindOf ρ Ψ = TwistKind.inner := by
  have hρ' : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) = fun α => α := funext hρ
  have hmem : (1 : ℕ) ∈ {s : ℕ | 0 < s ∧
      (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' Ψ = Ψ} := by
    refine ⟨by norm_num, ?_⟩
    rw [Function.iterate_one, hρ', Set.image_id']
  have horb : componentOrbitLength ρ Ψ = 1 := by
    rw [componentOrbitLength]
    refine le_antisymm (Nat.sInf_le hmem) ?_
    obtain ⟨hs, -⟩ := Nat.sInf_mem ⟨1, hmem⟩
    omega
  rw [twistKindOf, horb, Function.iterate_one]
  exact if_pos ⟨1, Subgroup.one_mem _, fun γ _ => by rw [hρ', one_smul]⟩

end CFSG.StandardType

end
