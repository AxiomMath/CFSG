module

public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
public import CFSG.RankThree.Chevalley.OddExceptionalRealRootElement

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.OddToralOrdinary (orderOf_pinnedX_one)

@[expose] def IsFourRootInverterData (τ : Tag) (K : Type) [Field K] (ℓ : ℕ)
    (α : Fin 4 → Fin τ.rank → ℤ) (j : Fin 4 → Fin τ.rank) (t s : Fin τ.rank) : Prop :=
  (∀ i, IsRoot τ (α i)) ∧
  (∀ i, pinnedX τ K (α i) 1 ∈ adjointGroup τ K ∧ orderOf (pinnedX τ K (α i) 1) = ℓ) ∧
  (∀ i i', pinnedX τ K (α i) 1 * pinnedX τ K (α i') 1 =
    pinnedX τ K (α i') 1 * pinnedX τ K (α i) 1) ∧
  (∀ i, torusElt τ K (j i) (-1) ∈ adjointGroup τ K ∧ orderOf (torusElt τ K (j i) (-1)) = 2) ∧
  (∀ i, torusElt τ K (j i) (-1) * pinnedX τ K (α i) 1 * (torusElt τ K (j i) (-1))⁻¹ =
    (pinnedX τ K (α i) 1)⁻¹) ∧
  (∀ i i', i ≠ i' → torusElt τ K (j i) (-1) * pinnedX τ K (α i') 1 *
    (torusElt τ K (j i) (-1))⁻¹ = pinnedX τ K (α i') 1) ∧
  torusElt τ K t (-1) ∈ adjointGroup τ K ∧ orderOf (torusElt τ K t (-1)) = 2 ∧
  (∀ i, torusElt τ K t (-1) * pinnedX τ K (α i) 1 * (torusElt τ K t (-1))⁻¹ =
    pinnedX τ K (α i) 1) ∧
  (torusElt τ K t (-1) : Module.End K (RootModule τ K)) (rootVec τ K (Pi.single s 1)) ≠
    rootVec τ K (Pi.single s 1)

@[expose] def IsFourRootInverterCheck (τ : Tag) (α : Fin 4 → Fin τ.rank → ℤ)
    (j : Fin 4 → Fin τ.rank) (t s : Fin τ.rank) : Prop :=
  (∀ i, RootOps.isRootB τ (α i) = true) ∧
  (∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ -α i' ∧ RootOps.isRootB τ (α i + α i') = false) ∧
  (∀ i i', (∑ k, τ.cartan (j i) k * α i' k) % 2 = if i = i' then 1 else 0) ∧
  (∀ i, (∑ k, τ.cartan t k * α i k) % 2 = 0) ∧
  τ.cartan t s = -1

theorem torusElt_neg_one_conj_pinnedX {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    torusElt τ K i (-1) * pinnedX τ K α c * (torusElt τ K i (-1))⁻¹ =
      pinnedX τ K α (if (∑ k, τ.cartan i k * α k) % 2 = 0 then c else -c) := by
  rw [root_torus_conjugation i hα]
  split_ifs with h
  · rw [(Int.even_iff.2 h).neg_one_zpow, Units.val_one, one_mul]
  · rw [(Int.odd_iff.2 (by omega)).neg_one_zpow, Units.val_neg, Units.val_one, neg_one_mul]

theorem isFourRootInverterData_of_check {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (K : Type) [Field K] [CharP K ℓ]
    {α : Fin 4 → Fin τ.rank → ℤ} {j : Fin 4 → Fin τ.rank} {t s : Fin τ.rank}
    (h : IsFourRootInverterCheck τ α j t s) : IsFourRootInverterData τ K ℓ α j t s := by
  obtain ⟨hroot, hpair, hpar, hcent, hts⟩ := h
  have hα : ∀ i, IsRoot τ (α i) := fun i => RootOps.isRootB_iff.1 (hroot i)
  have hchar : ringChar K = ℓ := ringChar.eq K ℓ
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (hchar ▸ hℓ)
  have hneg : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hmove : ∀ i, pinnedX τ K (α i) (-1) ≠ pinnedX τ K (α i) 1 := fun i h =>
    hneg (pinnedX_injective τ K (α i) h)
  have hconj := fun i i' => torusElt_neg_one_conj_pinnedX (K := K) (j i) (hα i') 1
  have hconjt := fun i => torusElt_neg_one_conj_pinnedX (K := K) t (hα i) 1
  have hw : ∀ i, torusElt τ K (j i) (-1) * pinnedX τ K (α i) 1 * (torusElt τ K (j i) (-1))⁻¹ =
      (pinnedX τ K (α i) 1)⁻¹ := fun i => by
    rw [hconj i i, hpar i i, ite_eq_left rfl, ite_eq_right (by norm_num), pinnedX_neg]
  have hw' : ∀ i i', i ≠ i' → torusElt τ K (j i) (-1) * pinnedX τ K (α i') 1 *
      (torusElt τ K (j i) (-1))⁻¹ = pinnedX τ K (α i') 1 := fun i i' hii' => by
    rw [hconj i i', hpar i i', ite_eq_right hii', ite_eq_left rfl]
  have hz : ∀ i, torusElt τ K t (-1) * pinnedX τ K (α i) 1 * (torusElt τ K t (-1))⁻¹ =
      pinnedX τ K (α i) 1 := fun i => by
    rw [hconjt i, hcent i, ite_eq_left rfl]
  have hzs : (torusElt τ K t (-1) : Module.End K (RootModule τ K)) (rootVec τ K (Pi.single s 1)) =
      -rootVec τ K (Pi.single s 1) := by
    have hsum : ∑ k, τ.cartan t k * (Pi.single s 1 : Fin τ.rank → ℤ) k = -1 := by
      simp [Pi.single_apply, hts]
    rw [torusElt_rootVec t (-1) (isRoot_single τ s), hsum,
      show ((-1 : Kˣ) ^ (-1 : ℤ)) = -1 by simp, Units.val_neg, Units.val_one, neg_one_smul]
  have hv0 : rootVec τ K (Pi.single s 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single τ s)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have hzv : (torusElt τ K t (-1) : Module.End K (RootModule τ K)) (rootVec τ K (Pi.single s 1)) ≠
      rootVec τ K (Pi.single s 1) := by
    rw [hzs]
    intro h
    apply hv0
    have h2v : (2 : K) • rootVec τ K (Pi.single s 1) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      exact neg_add_cancel _
    exact (smul_eq_zero.1 h2v).resolve_left h2
  refine ⟨hα, fun i => ⟨pinnedX_mem_adjointGroup _ _, orderOf_pinnedX_one τ K ℓ _⟩,
    fun i i' => ?_, fun i => ⟨torusElt_mem_adjointGroup _ _, ?_⟩, hw, hw',
    torusElt_mem_adjointGroup _ _, ?_, hz, hzv⟩
  · by_cases hii' : i = i'
    · rw [hii']
    · obtain ⟨hne, hne', hnr⟩ := hpair i i' hii'
      have hnot : ¬ IsRoot τ (α i + α i') := fun hr => by
        rw [← RootOps.isRootB_iff, hnr] at hr
        exact Bool.false_ne_true hr
      exact ((simply_laced_root_commutator_unit τ hτ (hα i) (hα i') hne hne').2 hnot K _
        (mem_rootSubgroup.2 ⟨1, rfl⟩) _ (mem_rootSubgroup.2 ⟨1, rfl⟩)).eq
  · refine orderOf_eq_prime (torusElt_neg_one_sq _) fun h1 => hmove i ?_
    have := hw i
    rw [h1, one_mul, inv_one, mul_one, pinnedX_neg] at this
    exact this.symm
  · refine orderOf_eq_prime (torusElt_neg_one_sq _) fun h1 => hzv ?_
    rw [h1, Units.val_one, Module.End.one_apply]

theorem odd_E6_E7_four_commuting_root_elements_with_inverters {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ 2) (K : Type) [Field K] [CharP K ℓ] :
    IsFourRootInverterData .E6 K ℓ
      ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![1, 2, 2, 3, 2, 1]]
      ![⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨1, by decide⟩] ⟨5, by decide⟩
      ⟨4, by decide⟩ ∧
    IsFourRootInverterData .E7 K ℓ
      ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1],
        ![2, 2, 3, 4, 3, 2, 1]]
      ![⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨0, by decide⟩] ⟨1, by decide⟩
      ⟨3, by decide⟩ :=
  ⟨isFourRootInverterData_of_check (Or.inr (Or.inl rfl)) hℓ K
      (by unfold IsFourRootInverterCheck; decide +kernel),
    isFourRootInverterData_of_check (Or.inr (Or.inr (Or.inl rfl))) hℓ K
      (by unfold IsFourRootInverterCheck; decide +kernel)⟩

end CFSG.RankThree.Chevalley
