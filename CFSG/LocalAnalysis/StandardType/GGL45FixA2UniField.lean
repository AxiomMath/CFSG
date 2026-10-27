module

public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem gffa2_exists_psuField {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))) :
    ∃ σ : K ≃+* K,
      f = MulAut.congr (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)) (psuField h σ) := by
  obtain ⟨σ, hσ⟩ := hf
  let ε : unitaryPSU h 3 ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)) :=
    unitaryPSUEquiv h (by norm_num : 1 ≤ 3)
  have key : f = MulAut.congr ε (psuField h σ) := by
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    have hmem : (QuotientGroup.mk g : LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) =
        ε (unitaryProj h 3 g) :=
      (unitaryPSUEquiv_unitaryProj h (by norm_num : 1 ≤ 3) g).symm
    have e1 : ε.symm (QuotientGroup.mk g :
        LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) = unitaryProj h 3 g := by
      rw [hmem, MulEquiv.symm_apply_apply]
    rw [e1]
    have h2 : psuField h σ (unitaryProj h 3 g) =
        ((suField h σ g : unitarySU 2 n K 3) : unitaryPSU h 3) :=
      psuField_mk (h := h) σ g
    rw [h2]
    have h3 : ε ((suField h σ g : unitarySU 2 n K 3) : unitaryPSU h 3) =
        (QuotientGroup.mk (suField h σ g) :
          LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) :=
      unitaryPSUEquiv_unitaryProj h (by norm_num : 1 ≤ 3) (suField h σ g)
    rw [h3]
    exact hσ g (suField h σ g) rfl
  exact ⟨σ, key⟩

theorem gffa2_orderOf_congr_psuField {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K)
    (σ : K ≃+* K) :
    orderOf (MulAut.congr (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)) (psuField h σ)) =
      orderOf σ := by
  have hinj : Function.Injective (psuField h) := by
    rw [injective_iff_map_eq_one]
    intro τ hτ
    exact psuField_mem_range_psuConj_iff.mp (by rw [hτ]; exact Subgroup.one_mem _)
  exact orderOf_injective
    ((MulAut.congr (unitaryPSUEquiv h (by norm_num : 1 ≤ 3))).toMonoidHom.comp (psuField h))
    ((MulAut.congr (unitaryPSUEquiv h (by norm_num : 1 ≤ 3))).injective.comp hinj) σ

theorem gffa2_unitary_fixed_equiv {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K)
    {X : Type} [Group X]
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
    (hZ : Subgroup.center X = ⊥) (ψ : MulAut X)
    (hind : ∃ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n))),
      ∃ u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
          (LargeEvenGUSet (Fin 3) K (2 ^ n)),
        orderOf f = 3 ∧ LargeEvenInduces θ (fun k k' => k' = ψ k) (u * f * u⁻¹)) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      Nonempty (↥(ggAutFixedSubgroup ψ) ≃* ↥(ggAutFixedSubgroup (psuField h σ))) := by
  obtain ⟨f, hf, u, hu, hord, hind⟩ := hind
  obtain ⟨σ, rfl⟩ := gffa2_exists_psuField h hf
  refine ⟨σ, (gffa2_orderOf_congr_psuField h σ).symm.trans hord, ?_⟩
  obtain ⟨E₁⟩ := gffa2_fixedEquiv θ hZ ψ _ u hind
  obtain ⟨E₂⟩ := gffa2_fixedEquiv_of_congr (unitaryPSUEquiv h (by norm_num : 1 ≤ 3))
    (psuField h σ) (MulAut.congr (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)) (psuField h σ))
    (fun x => by simp [MulAut.congr_apply])
  exact ⟨E₁.trans E₂⟩

end CFSG.StandardType
