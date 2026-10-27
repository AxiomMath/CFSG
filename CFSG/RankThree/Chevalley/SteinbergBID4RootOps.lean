module

public import CFSG.RankThree.Chevalley.SteinbergBID4RegularCentralizer
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem d4RootVec_of_root :
    ∀ k' < 24, ∃ k : Fin 24, d4RootVec k = Tag.D4.rootCertificate.root k' := by
  decide +kernel

theorem exists_d4RootVec_eq {v : Fin Tag.D4.rank → ℤ} (hv : IsRoot Tag.D4 v) :
    ∃ k : Fin 24, d4RootVec k = v := by
  obtain ⟨k', hk', rfl⟩ := RootCertificate.exists_root_eq Tag.D4.rootCertificate_check hv
  exact d4RootVec_of_root k' hk'

theorem isRoot_iff_exists_d4RootVec {v : Fin Tag.D4.rank → ℤ} :
    IsRoot Tag.D4 v ↔ ∃ k : Fin 24, d4RootVec k = v :=
  ⟨exists_d4RootVec_eq, fun ⟨k, hk⟩ => hk ▸ isRoot_d4RootVec k⟩

theorem d4_root_strings : ∀ (k : Fin 24) (i : Fin Tag.D4.rank),
    d4RootVec k ≠ Pi.single i 1 → d4RootVec k ≠ -Pi.single i 1 →
      (¬∃ k', d4RootVec k' = d4RootVec k + (2 : ℤ) • Pi.single i 1) ∧
      (¬∃ k', d4RootVec k' = d4RootVec k - (2 : ℤ) • Pi.single i 1) ∧
      ¬((∃ k', d4RootVec k' = d4RootVec k + Pi.single i 1) ∧
        (∃ k', d4RootVec k' = d4RootVec k - Pi.single i 1)) := by
  decide +kernel

theorem stringUp_add_stringDown_D4 {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α)
    {i : Fin Tag.D4.rank} (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    stringUp Tag.D4 i α ≤ 1 ∧ stringDown Tag.D4 i α ≤ 1 ∧
      stringUp Tag.D4 i α + stringDown Tag.D4 i α ≤ 1 := by
  obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  obtain ⟨k, rfl⟩ := exists_d4RootVec_eq hα
  obtain ⟨hp2, hq2, hpq⟩ := d4_root_strings k i h₁ h₂
  have hp : stringUp Tag.D4 i (d4RootVec k) ≤ 1 := by
    by_contra h
    exact hp2 (isRoot_iff_exists_d4RootVec.mp ((hs 2).mpr ⟨by omega, by omega⟩))
  have hq : stringDown Tag.D4 i (d4RootVec k) ≤ 1 := by
    by_contra h
    have := (hs (-2)).mpr ⟨by omega, by omega⟩
    rw [neg_smul, ← sub_eq_add_neg] at this
    exact hq2 (isRoot_iff_exists_d4RootVec.mp this)
  refine ⟨hp, hq, ?_⟩
  by_contra h
  have h1 : stringUp Tag.D4 i (d4RootVec k) = 1 := by omega
  have h2 : stringDown Tag.D4 i (d4RootVec k) = 1 := by omega
  have hu := (hs 1).mpr ⟨by omega, by omega⟩
  have hd := (hs (-1)).mpr ⟨by omega, by omega⟩
  rw [one_smul] at hu
  rw [neg_smul, one_smul, ← sub_eq_add_neg] at hd
  exact hpq ⟨isRoot_iff_exists_d4RootVec.mp hu, isRoot_iff_exists_d4RootVec.mp hd⟩

variable {R : Type*} [CommRing R]

theorem rootVec_eq_single_D4 {β : Fin Tag.D4.rank → ℤ} (hβ : IsRoot Tag.D4 β) :
    rootVec Tag.D4 R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 := by
  rw [rootVec, dite_eq_left hβ]

theorem rootVec_eq_zero_of_not_D4 {β : Fin Tag.D4.rank → ℤ} (hβ : ¬IsRoot Tag.D4 β) :
    rootVec Tag.D4 R β = 0 := by
  rw [rootVec, dite_eq_right hβ]

theorem xOp_rootVec_D4 (i : Fin Tag.D4.rank) (c : R) {α : Fin Tag.D4.rank → ℤ}
    (hα : IsRoot Tag.D4 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp Tag.D4 R i c (rootVec Tag.D4 R α) =
      rootVec Tag.D4 R α + c • rootVec Tag.D4 R (α + Pi.single i 1) := by
  obtain ⟨hp, -, hpq⟩ := stringUp_add_stringDown_D4 hα h₁ h₂
  rw [rootVec_eq_single_D4 hα, xOp, Finsupp.linearCombination_single, one_smul]
  simp only [ite_eq_right h₁, ite_eq_right h₂]
  rw [← rootVec_eq_single_D4 hα]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with h0 | h1
  · rw [h0, Finset.sum_range_one]
    have hnot : ¬IsRoot Tag.D4 (α + Pi.single i 1) := by
      intro h
      obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
      have := (hs 1).mp (by rwa [one_smul])
      omega
    simp [rootVec_eq_zero_of_not_D4 hnot]
  · have hq : stringDown Tag.D4 i α = 0 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_one, hq]
    simp

theorem yOp_rootVec_D4 (i : Fin Tag.D4.rank) (c : R) {α : Fin Tag.D4.rank → ℤ}
    (hα : IsRoot Tag.D4 α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp Tag.D4 R i c (rootVec Tag.D4 R α) =
      rootVec Tag.D4 R α + c • rootVec Tag.D4 R (α - Pi.single i 1) := by
  obtain ⟨-, hq, hpq⟩ := stringUp_add_stringDown_D4 hα h₁ h₂
  rw [rootVec_eq_single_D4 hα, yOp, Finsupp.linearCombination_single, one_smul]
  simp only [ite_eq_right h₁, ite_eq_right h₂]
  rw [← rootVec_eq_single_D4 hα]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with h0 | h1
  · rw [h0, Finset.sum_range_one]
    have hnot : ¬IsRoot Tag.D4 (α - Pi.single i 1) := by
      intro h
      obtain ⟨-, hs⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
      have := (hs (-1)).mp (by rwa [neg_smul, one_smul, ← sub_eq_add_neg])
      omega
    simp [rootVec_eq_zero_of_not_D4 hnot]
  · have hp : stringUp Tag.D4 i α = 0 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_one, hp]
    simp

theorem mem_of_mem_subsystemGroup' {τ : Tag} {K : Type} [Field K] {X : Set (Fin τ.rank)}
    {M : Submodule K (RootModule τ K)}
    (hx : ∀ i ∈ X, ∀ c : K, ∀ v ∈ M, xOp τ K i c v ∈ M)
    (hy : ∀ i ∈ X, ∀ c : K, ∀ v ∈ M, yOp τ K i c v ∈ M)
    {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K X) :
    ∀ v ∈ M, (g : Module.End K (RootModule τ K)) v ∈ M := by
  induction hg using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · exact hx i hi c
    · exact hy i hi c
  | inv_mem g hg =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hg
    · intro v hv
      rw [coe_xUnit_inv]
      exact hx i hi (-c) v hv
    · intro v hv
      rw [coe_yUnit_inv]
      exact hy i hi (-c) v hv
  | one => exact fun v hv => hv
  | mul g h _ _ hg hh => exact fun v hv => hg _ (hh v hv)

theorem list_prod_weylElt_rootVec {τ : Tag} {K : Type} [Field K] (ω : List (Fin τ.rank))
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : ∃ ε : K, ε ≠ 0 ∧
      (((ω.map fun i => weylElt τ K i 1).prod : ModGL τ K) :
        Module.End K (RootModule τ K)) (rootVec τ K β) =
      ε • rootVec τ K ((coxeterSystem τ).wordProd ω • β) := by
  induction ω with
  | nil => exact ⟨1, one_ne_zero, by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ := ih
    refine ⟨ε * ((-1) ^ stringDown τ i ((coxeterSystem τ).wordProd ω • β) *
      (((1 : Kˣ) ^ (-∑ j, τ.cartan i j * ((coxeterSystem τ).wordProd ω • β) j) : Kˣ) :
        K)), mul_ne_zero hε (by simp), ?_⟩
    have e : (coxeterSystem τ).wordProd (i :: ω) • β =
        reflect τ i ((coxeterSystem τ).wordProd ω • β) := by
      rw [CoxeterSystem.wordProd_cons, mul_smul]
      exact simple_smul i _
    rw [e, List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, h, map_smul,
      weylElt_rootVec i 1 (IsRoot.smul hβ _), smul_smul]

theorem canonicalRep_rootVec {τ : Tag} {K : Type} [Field K] (w : WeylGroup τ)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : ∃ ε : K, ε ≠ 0 ∧
      (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K))
        (rootVec τ K β) = ε • rootVec τ K (w • β) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact list_prod_weylElt_rootVec ω hβ

end CFSG.RankThree.Chevalley
